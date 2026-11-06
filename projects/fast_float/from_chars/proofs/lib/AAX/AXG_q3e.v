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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp AXG_gp2 AXG_gp3 AXG_gp4 AXG_gf1 AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.

Module AXF_qnewpe.
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
Definition sr_qnewpe := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x43af8)) 9 (e_QC)) 10 (e_QC)) 11 (e_CA)) 13 (e_mp)) 14 (e_sz)) 22 (e_mx)).
Definition kn_qnewpe : list kentry :=
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
Definition scr_qnewpe : scripts := SCR [false] [] [].
Definition ss_qnewpe := SS 0x43b04 sr_qnewpe [] kn_qnewpe 43.
Definition RUN_qnewpe := sym_exec SEGS 100 true [0x43af8] scr_qnewpe ss_qnewpe [].

Definition scr_pnewp : scripts := SCR [false] [] [].
Definition RES_pnewp := Eval vm_compute in sym_exec SEGS 100 true [0x43af8] scr_pnewp ss_qnewpe [].
Lemma RES_pnewp_ok : sym_exec SEGS 100 true [0x43af8] scr_pnewp (SS 0x43b04 sr_qnewpe [] kn_qnewpe 43) [] = RES_pnewp.
Proof. vm_compute. reflexivity. Qed.
End AXF_qnewpe.

Module AXF_qnewpez.
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

Section QNEWPE.
Context {fx : FPState}.

Definition VALS_qnewpe (QC CA cnt qb csz sz mp mx cp SB st : Z) : list Z := [QC; CA; cnt; qb; csz; sz; mp; mx; cp; SB; st].

Record qnewpe_pre (regs : bvmap 5 word) (m : word -> option byte) (QC CA cnt qb csz sz mp mx cp SB st : Z) : Prop := {
  qnewpe_R1 : getr regs 1 = wa 277240 ;
  qnewpe_R9 : getr regs 9 = wa QC ;
  qnewpe_R10 : getr regs 10 = wa QC ;
  qnewpe_R11 : getr regs 11 = wa CA ;
  qnewpe_R13 : getr regs 13 = wa mp ;
  qnewpe_R14 : getr regs 14 = wa sz ;
  qnewpe_R22 : getr regs 22 = wa mx ;
  qnewpe_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qnewpe_rng_QC : 1 <= QC <= 2^47 ;
  qnewpe_rng_CA : 1 <= CA <= 2^47 ;
  qnewpe_rng_cnt : 1 <= cnt <= 16 ;
  qnewpe_rng_qb : 0 <= qb <= 2^62 ;
  qnewpe_rng_csz : 0 <= csz <= 2^64-1 ;
  qnewpe_rng_sz : 0 <= sz <= 2^40 ;
  qnewpe_rng_mp : 0 <= mp <= 2^64-1 ;
  qnewpe_rng_mx : 0 <= mx <= 2^62 ;
  qnewpe_rng_cp : 0 <= cp <= 2^32-1 ;
  qnewpe_rng_SB : 4194304 <= SB <= 2^47 ;
  qnewpe_rng_st : 0 <= st <= 2^64-1 ;
  qnewpe_ka2 : CA mod 16 = 0 ;
  qnewpe_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qnewpe_ka5 : SB mod 4096 = 0 ;
  qnewpe_kw6 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  qnewpe_kw7 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qnewpe_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (QC + 0 + d)) k = true ;
  qnewpe_kw9 : rdn SEGS m (wa (CA + 1920)) 4 = Some (word_to_le_bytes 4 (wa cnt)) ;
  qnewpe_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + 1920 + d)) k = true ;
  qnewpe_kw11 : rdn SEGS m (wa (CA + 1928)) 8 = Some (word_to_le_bytes 8 (wa csz)) ;
  qnewpe_kw12 : rdn SEGS m (wa (CA + Z.shiftr ((((4294967296 * ext_Z true 0 4 cnt) + -4294967296)) mod 2^64) 30 + 1936)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  qnewpe_kw13 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  qnewpe_kw14 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  qnewpe_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true ;
  qnewpe_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8192 -> store_ok SEGS m (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104 + d)) k = true
}.


#[using="Type"] Lemma qnewpe_setup : forall regs m QC CA cnt qb csz sz mp mx cp SB st, qnewpe_pre regs m QC CA cnt qb csz sz mp mx cp SB st ->
  regs_ok (Ez regs (VALS_qnewpe QC CA cnt qb csz sz mp mx cp SB st)) AXF_qnewpe.sr_qnewpe regs /\ know_ok SEGS (Ez regs (VALS_qnewpe QC CA cnt qb csz sz mp mx cp SB st)) m AXF_qnewpe.kn_qnewpe.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC CA cnt qb csz sz mp mx cp SB st P. destruct P as [qnewpe_R1 qnewpe_R9 qnewpe_R10 qnewpe_R11 qnewpe_R13 qnewpe_R14 qnewpe_R22 qnewpe_HSTK qnewpe_rng_QC qnewpe_rng_CA qnewpe_rng_cnt qnewpe_rng_qb qnewpe_rng_csz qnewpe_rng_sz qnewpe_rng_mp qnewpe_rng_mx qnewpe_rng_cp qnewpe_rng_SB qnewpe_rng_st qnewpe_ka2 qnewpe_kr3 qnewpe_ka5 qnewpe_kw6 qnewpe_kw7 qnewpe_kwr8 qnewpe_kw9 qnewpe_kwr10 qnewpe_kw11 qnewpe_kw12 qnewpe_kw13 qnewpe_kw14 qnewpe_kwr15 qnewpe_kwr16].
  set (E := Ez regs (VALS_qnewpe QC CA cnt qb csz sz mp mx cp SB st)).
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
  { unfold AXF_qnewpe.sr_qnewpe.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite qnewpe_R1. reflexivity.
    - rewrite qnewpe_R9. reflexivity.
    - rewrite qnewpe_R10. reflexivity.
    - rewrite qnewpe_R11. reflexivity.
    - rewrite qnewpe_R13. reflexivity.
    - rewrite qnewpe_R14. reflexivity.
    - rewrite qnewpe_R22. reflexivity. }
  unfold know_ok, AXF_qnewpe.kn_qnewpe.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qnewpe.e_QC AXF_qnewpe.e_CA AXF_qnewpe.e_cnt AXF_qnewpe.e_qb AXF_qnewpe.e_csz AXF_qnewpe.e_sz AXF_qnewpe.e_mp AXF_qnewpe.e_mx AXF_qnewpe.e_cp AXF_qnewpe.e_SB AXF_qnewpe.e_st AXF_qnewpe.CHP AXF_qnewpe.BAT AXF_qnewpe.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qnewpe_rng_QC eq_refl eq_refl), ?(mod64_of_range CA _ _ qnewpe_rng_CA eq_refl eq_refl), ?(mod64_of_range cnt _ _ qnewpe_rng_cnt eq_refl eq_refl), ?(mod64_of_range qb _ _ qnewpe_rng_qb eq_refl eq_refl), ?(mod64_of_range sz _ _ qnewpe_rng_sz eq_refl eq_refl), ?(mod64_of_range mx _ _ qnewpe_rng_mx eq_refl eq_refl), ?(mod64_of_range cp _ _ qnewpe_rng_cp eq_refl eq_refl), ?(mod64_of_range SB _ _ qnewpe_rng_SB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qnewpe_kwr8 | apply qnewpe_kwr10 | apply qnewpe_kwr15 | apply qnewpe_kwr16]; assumption).
  all: try (clear - qnewpe_rng_QC qnewpe_rng_CA qnewpe_rng_cnt qnewpe_rng_qb qnewpe_rng_csz qnewpe_rng_sz qnewpe_rng_mp qnewpe_rng_mx qnewpe_rng_cp qnewpe_rng_SB qnewpe_rng_st qnewpe_ka2 qnewpe_kr3 qnewpe_ka5 HQ HP; lia).
  all: first [lia].
Qed.


Definition qnewpe_mem_pnewp (m : word -> option byte) (regs : bvmap 5 word) (QC CA cnt qb csz sz mp mx cp SB st : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277240))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa QC))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (CA + 1920)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 cnt + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (csz + st)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104)) (word_to_le_bytes 8 (wa 0))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215112)) (word_to_le_bytes 8 (wa (sz + 8192)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215120)) (word_to_le_bytes 8 (wa 1))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215128)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 16)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa ((qb + sz) + 8192))).

#[using="Type"] Theorem qnewpe_pnewp : forall regs m rom QC CA cnt qb csz sz mp mx cp SB st, qnewpe_pre regs m QC CA cnt qb csz sz mp mx cp SB st ->
  scs_denot SEGS m (Ez regs (VALS_qnewpe QC CA cnt qb csz sz mp mx cp SB st)) (snd (fst AXF_qnewpe.RES_pnewp)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43af8) (qnewpe_mem_pnewp m regs QC CA cnt qb csz sz mp mx cp SB st) rom) /\
    getr R 1 = wa 277240 /\ getr R 9 = wa QC /\ getr R 10 = wa QC /\ getr R 11 = wa ((qb + sz) + 8192) /\ getr R 12 = wa 1 /\ getr R 13 = wa mp /\ getr R 14 = wa (sz + 8192) /\ getr R 15 = wa 0 /\ getr R 16 = wa 103079215104 /\ getr R 22 = wa mx /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC CA cnt qb csz sz mp mx cp SB st P Hsc. destruct (qnewpe_setup regs m QC CA cnt qb csz sz mp mx cp SB st P) as [HR HK].
  set (E := Ez regs (VALS_qnewpe QC CA cnt qb csz sz mp mx cp SB st)) in *. destruct P as [qnewpe_R1 qnewpe_R9 qnewpe_R10 qnewpe_R11 qnewpe_R13 qnewpe_R14 qnewpe_R22 qnewpe_HSTK qnewpe_rng_QC qnewpe_rng_CA qnewpe_rng_cnt qnewpe_rng_qb qnewpe_rng_csz qnewpe_rng_sz qnewpe_rng_mp qnewpe_rng_mx qnewpe_rng_cp qnewpe_rng_SB qnewpe_rng_st qnewpe_ka2 qnewpe_kr3 qnewpe_ka5 qnewpe_kw6 qnewpe_kw7 qnewpe_kwr8 qnewpe_kw9 qnewpe_kwr10 qnewpe_kw11 qnewpe_kw12 qnewpe_kw13 qnewpe_kw14 qnewpe_kwr15 qnewpe_kwr16].
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
  destruct (run_sound SEGS 100 [0x43af8] AXF_qnewpe.scr_pnewp 0x43b04 AXF_qnewpe.sr_qnewpe AXF_qnewpe.kn_qnewpe 43 _ _ _ E m rom regs AXF_qnewpe.RES_pnewp_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qnewpe.RES_pnewp fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qnewpe_mem_pnewp m regs QC CA cnt qb csz sz mp mx cp SB st) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qnewpe_mem_pnewp. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End QNEWPE.
End AXF_qnewpez.

Module AXG_q2e.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp AXG_gp2 AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Local Ltac lenq := rewrite ?length_N_to_le_bytes; change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.
Local Ltac znq := change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.

Section SCQ2E.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variable SPa : Z.
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.
#[using="HSPa"] Lemma sc_qnewpe : forall QC CA cnt qb csz sz mp mx cp SB st, q_geo SPa QC CA SB ->
  1 <= cnt <= 8 /\ 0 <= qb <= 2^62 /\ 0 <= sz <= 2^40 /\ 0 <= mx <= 2^62 /\ 0 <= cp <= 16383 ->
  scs_denot SEGS m (Ez R (AXF_qnewpez.VALS_qnewpe QC CA cnt qb csz sz mp mx cp SB st)) (snd (fst AXF_qnewpe.RES_pnewp)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros QC CA cnt qb csz sz mp mx cp SB st HG HH. unfold q_geo in HG. unfold AXF_qnewpez.VALS_qnewpe.
  assert (HD : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC) by tauto.
  assert (HPL : (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : CA + 2592 <= SB) by (clear - HPL HG; lia). assert (HH2 := conj HPL (conj HD1 (conj HG HH))); clear HH HG HD HD1 HPL.
    sc_refl [SPr; (EVar 32, (4176, 61520)); (EVar 33, LOW); (EVar 34, (1, 8)); (EVar 35, (0, 2^62)); (EVar 37, (0, 2^40)); (EVar 39, (0, 2^62));
              (EVar 40, (0, 16383)); (EVar 41, (17594333495296, 2^47))]
             [(EVar 33, EVar 32, 128); (EVar 32, EVar 33, -128); (EVar 2, EVar 33, 2912); (EVar 2, EVar 32, 3040); (EVar 2, EVar 41, 137438957888);
              (EVar 41, EVar 33, 2592); (EVar 41, EVar 32, 2720)] R HSPa HSPa HH2.
  - destruct HD as [HD|HD]; assert (HH2 := conj HPL (conj HD (conj HG HH))); clear HH HG HD HPL.
    + sc_refl [SPr; (EVar 32, (6529104, 2^47)); (EVar 33, HIGH); (EVar 34, (1, 8)); (EVar 35, (0, 2^62)); (EVar 37, (0, 2^40)); (EVar 39, (0, 2^62));
                (EVar 40, (0, 16383)); (EVar 41, (17594333495296, 2^47))]
               [(EVar 33, EVar 32, 128); (EVar 32, EVar 33, -128); (EVar 2, EVar 33, 2912); (EVar 2, EVar 32, 3040); (EVar 2, EVar 41, 137438957888);
                (EVar 41, EVar 33, 2592); (EVar 41, EVar 32, 2720)] R HSPa HSPa HH2.
    + sc_refl [SPr; (EVar 32, (6529104, 2^47)); (EVar 33, HIGH); (EVar 34, (1, 8)); (EVar 35, (0, 2^62)); (EVar 37, (0, 2^40)); (EVar 39, (0, 2^62));
                (EVar 40, (0, 16383)); (EVar 41, (17594333495296, 2^47))]
               [(EVar 33, EVar 32, 128); (EVar 32, EVar 33, -128); (EVar 2, EVar 33, 2912); (EVar 2, EVar 32, 3040); (EVar 2, EVar 41, 137438957888);
                (EVar 32, EVar 41, 137438957568); (EVar 33, EVar 41, 137438957696)] R HSPa HSPa HH2.
Qed.
End SCQ2E.

(* [comment removed for export] *)
Section QPOPE.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC CA SB nc newc j qj fsz mp mx SP : Z).
Hypothesis IQ : q_inv m QC SB qj 0 0.
Hypothesis I : INV_G m CA SB 24 8192 nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis Hcnt : 1 <= cnt_of nc j.
Hypothesis H1 : getr regs 1 = wa 277240.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis H9 : getr regs 9 = wa QC.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis H22 : getr regs 22 = wa mx.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis HQC : QC = CA - 128.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hsz : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62.
Hypothesis Hwq : wr m QC 32.
Hypothesis Hwb : wr m (SB + 103079215104 + 8192 * j) 8192.

#[using="qj mx IQ I Hj Hcnt H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb"] Lemma qpop_e :
  exists R m', msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43af8) m' rom) /\
    (forall k, In k KQ -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB j 1 (fsz + 8192) /\ INV_G m' CA SB 24 8192 nc newc (j + 1) /\
    rd m' (SB + 103079215104 + 8192 * j) 8 0 /\ rd m' (SB + 103079215104 + 8192 * j + 24) 8 mp /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB 24 x -> ~ (QC <= x < QC + 32) ->
       ~ (SB + 103079215104 + 8192 * j <= x < SB + 103079215104 + 8192 * j + 32) -> m' (wa x) = m (wa x)) /\
    mem_grows m m'.
Proof. LiaFast.lf_pins (fun (qj mx IQ I Hj Hcnt H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb : LiaFast.U) => LiaFast.u0).
  destruct IQ as (_ & Rqb & [(_ & _ & Rq0)|(Hq1 & _)]); [|lia].
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcntr.
  set (cnt := cnt_of nc j) in *.
  destruct Ist as (st & Hst & Rst).
  change (8192 / 16) with 512 in *.
  set (cp := j * 512).
  set (B := SB + 103079215104 + 8192 * j) in *.
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 /\ QC = CA - 128 /\
               17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC) /\ 1 <= cnt < nc /\ 1 <= nc <= 8 /\ 0 <= st < 2^64 /\
               1 <= j /\ j <= 31 /\ cp = j * 512 /\ B = SB + 103079215104 + 8192 * j /\
               0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62) by (unfold cp, B; slia).
  clear HCA HSB HSEP Hsz HQC Hst. clearbody cp B.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  assert (P : AXF_qnewpez.qnewpe_pre regs m QC CA cnt 0 8192 fsz mp mx cp SB st).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [lia | exact HSTK].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rq0.
    - intros d k Hd Hk. rewrite Z.add_0_r. apply Hwq; assumption.
    - intros d k Hd Hk. replace (CA + 1920 + d) with (REC CA 24 + d) by ring. apply Iwrec; lia.
    - replace (CA + 1928) with (REC CA 24 + 8) by ring. exact Isz.
    - rewrite chp_off by (zlh HZ). replace (CA + 4 * (cnt - 1) + 1936) with (REC CA 24 + 16 + 4 * (cnt - 1)) by ring.
      pose proof (Ich (cnt - 1) ltac:(zlh HZ)) as R7. replace ((j + cnt - 1 - (cnt - 1)) * 512) with cp in R7 by (zlh HZ). exact R7.
    - intros d k Hd Hk. replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; lia.
    - intros d k Hd Hk. rewrite ext_Z_u32 by (zlh HZ). replace (SB + 16 * cp + 103079215104 + d) with (B + d) by (zlh HZ). apply Hwb; assumption. }
  destruct (AXF_qnewpez.qnewpe_pnewp regs m rom QC CA cnt 0 8192 fsz mp mx cp SB st P
              (sc_qnewpe regs m SP HSPa QC CA cnt 0 8192 fsz mp mx cp SB st ltac:(unfold q_geo; zlh HZ) ltac:(zlh HZ)))
    as (R & Hms & A1 & A9 & _ & _ & _ & _ & _ & _ & _ & A22 & KK).
  clear P.
  set (v8 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) in *. set (v18 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) in *.
  set (v19 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) in *. set (v20 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) in *.
  set (v21 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) in *.
  set (m1 := wchainS m SP (LQD 277240 v8 QC v18 v19 v20 v21)).
  set (mp0 := wbytes (wbytes m1 (wa (CA + 1920)) (word_to_le_bytes 4 (wa (cnt - 1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (8192 + st)))).
  set (m' := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mp0
               (wa B) (word_to_le_bytes 8 (wa 0))) (wa (B + 8)) (word_to_le_bytes 8 (wa (fsz + 8192)))) (wa (B + 16)) (word_to_le_bytes 8 (wa 1)))
               (wa (B + 24)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa B))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 1)))
               (wa (QC + 16)) (word_to_le_bytes 8 (wa B))) (wa (QC + 24)) (word_to_le_bytes 8 (wa (fsz + 8192)))).
  assert (EM : AXF_qnewpez.qnewpe_mem_pnewp m regs QC CA cnt 0 8192 fsz mp mx cp SB st = m').
  { unfold AXF_qnewpez.qnewpe_mem_pnewp, m', mp0, m1, LQD. cbn [wchainS]. rewrite HSPa, ext_Z_lo32_small, ext_Z_u32 by (zlh HZ). rewrite ?addneg.
    replace (SB + 16 * cp + 103079215104) with B by (zlh HZ). replace (SB + 16 * cp + 103079215112) with (B + 8) by (zlh HZ).
    replace (SB + 16 * cp + 103079215120) with (B + 16) by (zlh HZ). replace (SB + 16 * cp + 103079215128) with (B + 24) by (zlh HZ).
    replace (0 + fsz + 8192) with (fsz + 8192) by ring. reflexivity. }
  rewrite EM in Hms. clear EM.
  assert (G1 : mem_grows m m1) by (apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 56 <= x < SP) -> m1 (wa x) = m (wa x)) by (intros x Hx Hn; apply qd_frame; [zlh HZ | exact Hx | exact Hn]).
  assert (FR0 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (REC CA 24 <= x < REC CA 24 + 4) -> ~ (CA + 2576 <= x < CA + 2584) -> mp0 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3. unfold mp0. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q2 Q3; lia)]). apply F1; [exact Hx | clear - Q1; lia]. }
  assert (G0 : mem_grows m mp0) by (unfold mp0; do 2 apply grows_wb; exact G1).
  assert (FR1 : forall x, 0 <= x < 2^64 -> ~ (QC <= x < QC + 32) -> ~ (B <= x < B + 32) -> m' (wa x) = mp0 (wa x)).
  { intros x Hx Q1 Q2. unfold m'. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q1 Q2; lia)]). reflexivity. }
  assert (G01 : mem_grows mp0 m') by (unfold m'; do 8 apply grows_wb; apply mem_grows_refl).
  assert (G : mem_grows m m') by (exact (mem_grows_trans _ _ _ G0 G01)).
  assert (IG0 : INV_G mp0 CA SB 24 8192 nc newc (j + 1)).
  { apply (inv_pop m mp0 CA SB 24 8192 nc newc j SP I Hj ltac:(zlh HZ) ltac:(zlh HZ) ltac:(zlh HZ) G0 Hcnt FR0).
    - unfold mp0. apply wb_rd_other; [(zlh HZ) | lenq; (zlh HZ) | (zlh HZ) | lenq; (zlh HZ) | lenq; (zlh HZ) |].
      replace (REC CA 24) with (CA + 1920) by ring. apply wb_rd_hit; lenq; (zlh HZ).
    - exists ((8192 + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd, mp0.
      rewrite (wa_eqm ((8192 + st) mod 2^64) (8192 + st)) by (apply Z.mod_mod; lia). apply (wb_rd_hit _ _ 8 (8192 + st)); lenq; (zlh HZ). }
  exists R, m'. split; [exact Hms|].
  split.
  { intros k Hk. cbn [KQ In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [first [ apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]
                                           | (transitivity (wa 277240); [exact A1 | symmetry; exact H1])
                                           | (transitivity (wa QC); [exact A9 | symmetry; exact H9])
                                           | (transitivity (wa mx); [exact A22 | symmetry; exact H22]) ]|]).
    destruct Hk. }
  split.
  { unfold q_inv. replace (SB + 103079215104 + 8192 * j) with B by (zlh HZ). split; [zlh HZ|]. split.
    { unfold m'. apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    right. split; [lia|]. split; [zlh HZ|].
    split.
    { unfold m'. do 2 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      rewrite (Z.add_0_r QC). apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { unfold m'. do 3 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { unfold m'. apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { unfold m'. do 6 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { unfold m'. do 5 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Hwb; assumption. }
  split.
  { apply (INV_G_frame mp0 m' CA SB 24 8192 nc newc (j + 1)); [zlh HZ | zlh HZ | zlh HZ | zlh HZ | exact G01 | | exact IG0].
    intros x Hx. assert (Hn : newc <= 32) by (clear - Igeo; lia). apply FR1; unfold foot_G in Hx; clear - HZ Hx Hn; lia. }
  split.
  { unfold m'. do 7 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
    apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
  split.
  { unfold m'. do 4 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
    apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
  split; [|exact G].
  intros x Hx Q1 Q2 Q3 Q4. rewrite FR1 by assumption. apply FR0; [exact Hx | exact Q1 | |]; unfold owned_C in Q2; clear - HZ Q2; lia.
Qed.
End QPOPE.
End AXG_q2e.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3e.AXG_q2e.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.

Module AXF_qngte.
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
Definition sr_qngte := (sr_upd (sr_upd (sr_upd sr_id 8 (RI)) 14 (e_n)) 19 (ELit 2305843009213693952)).
Definition kn_qngte : list kentry :=
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
Definition scr_qngte : scripts := SCR [] [] [].
Definition ss_qngte := SS 0x446c0 sr_qngte [] kn_qngte 56.
Definition RUN_qngte := sym_exec SEGS 160 true [0x43af8] scr_qngte ss_qngte [].

Definition scr_pngt : scripts := SCR [] [] [].
Definition RES_pngt := Eval vm_compute in sym_exec SEGS 160 true [0x43af8] scr_pngt ss_qngte [].
Lemma RES_pngt_ok : sym_exec SEGS 160 true [0x43af8] scr_pngt (SS 0x446c0 sr_qngte [] kn_qngte 56) [] = RES_pngt.
Proof. vm_compute. reflexivity. Qed.
End AXF_qngte.


Module AXF_qngtez.
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

Section QNGTE.
Context {fx : FPState}.

Definition VALS_qngte (CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 : Z) : list Z := [CA; QC; n; SB; RIB; na; cp; csz; st; qb; sz; mp; mx; stk; g7; g8; g9; g10; g11; c0; c2; c3; c4; c5].

Record qngte_pre (regs : bvmap 5 word) (m : word -> option byte) (CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 : Z) : Prop := {
  qngte_R8 : getr regs 8 = wa (RIB + 3072) ;
  qngte_R14 : getr regs 14 = wa n ;
  qngte_R19 : getr regs 19 = wa 2305843009213693952 ;
  qngte_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qngte_rng_CA : 1 <= CA <= 2^47 ;
  qngte_rng_QC : 1 <= QC <= 2^47 ;
  qngte_rng_n : 1 <= n <= 8 ;
  qngte_rng_SB : 4194304 <= SB <= 2^47 ;
  qngte_rng_RIB : 1 <= RIB <= 2^47 ;
  qngte_rng_na : 0 <= na <= 2^64-1 ;
  qngte_rng_cp : 0 <= cp <= 2^32-1 ;
  qngte_rng_csz : 0 <= csz <= 2^64-1 ;
  qngte_rng_st : 0 <= st <= 2^64-1 ;
  qngte_rng_qb : 0 <= qb <= 2^62 ;
  qngte_rng_sz : 0 <= sz <= 2^40 ;
  qngte_rng_mp : 0 <= mp <= 2^64-1 ;
  qngte_rng_mx : 0 <= mx <= 2^62 ;
  qngte_rng_stk : 0 <= stk <= 2^64-1 ;
  qngte_rng_g7 : 0 <= g7 <= 2^64-1 ;
  qngte_rng_g8 : 0 <= g8 <= 2^64-1 ;
  qngte_rng_g9 : 0 <= g9 <= 2^64-1 ;
  qngte_rng_g10 : 0 <= g10 <= 2^64-1 ;
  qngte_rng_g11 : 0 <= g11 <= 2^64-1 ;
  qngte_rng_c0 : 0 <= c0 <= 2^64-1 ;
  qngte_rng_c2 : 0 <= c2 <= 2^64-1 ;
  qngte_rng_c3 : 0 <= c3 <= 2^64-1 ;
  qngte_rng_c4 : 0 <= c4 <= 2^64-1 ;
  qngte_rng_c5 : 0 <= c5 <= 2^64-1 ;
  qngte_ka1 : CA mod 16 = 0 ;
  qngte_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qngte_ka5 : RIB mod 128 = 0 ;
  qngte_ka7 : SB mod 4096 = 0 ;
  qngte_kw8 : rdn SEGS m (wa (RIB + 3144)) 8 = Some (word_to_le_bytes 8 (wa na)) ;
  qngte_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + 3144 + d)) k = true ;
  qngte_kw10 : rdn SEGS m (wa (RIB + 3072)) 8 = Some (word_to_le_bytes 8 (wa 1152921504606846976)) ;
  qngte_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + 3072 + d)) k = true ;
  qngte_kw12 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 120)) 8 = Some (word_to_le_bytes 8 (wa 279672)) ;
  qngte_kw13 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 112)) 8 = Some (word_to_le_bytes 8 (wa (CA + 1920))) ;
  qngte_kw14 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 104)) 8 = Some (word_to_le_bytes 8 (wa n)) ;
  qngte_kw15 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 96)) 8 = Some (word_to_le_bytes 8 (wa mp)) ;
  qngte_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa QC)) ;
  qngte_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa stk)) ;
  qngte_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  qngte_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64)) 8 = Some (word_to_le_bytes 8 (wa mx)) ;
  qngte_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa g7)) ;
  qngte_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa g8)) ;
  qngte_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa g9)) ;
  qngte_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa g10)) ;
  qngte_kw24 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa g11)) ;
  qngte_kw25 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 136)) 8 = Some (word_to_le_bytes 8 (wa CA)) ;
  qngte_kw26 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 144)) 8 = Some (word_to_le_bytes 8 (wa (CA + 1920))) ;
  qngte_kw27 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 152)) 8 = Some (word_to_le_bytes 8 (wa 277592)) ;
  qngte_kw28 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 168)) 8 = Some (word_to_le_bytes 8 (wa c5)) ;
  qngte_kw29 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 176)) 8 = Some (word_to_le_bytes 8 (wa c4)) ;
  qngte_kw30 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 184)) 8 = Some (word_to_le_bytes 8 (wa c3)) ;
  qngte_kw31 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 192)) 8 = Some (word_to_le_bytes 8 (wa c2)) ;
  qngte_kw32 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 200)) 8 = Some (word_to_le_bytes 8 (wa QC)) ;
  qngte_kw33 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 208)) 8 = Some (word_to_le_bytes 8 (wa c0)) ;
  qngte_kw34 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 216)) 8 = Some (word_to_le_bytes 8 (wa 277240)) ;
  qngte_kwr35 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + 1920 + d)) k = true ;
  qngte_kw36 : rdn SEGS m (wa (CA + 1928)) 8 = Some (word_to_le_bytes 8 (wa csz)) ;
  qngte_kw37 : rdn SEGS m (wa (CA + Z.shiftr ((((4294967296 * ext_Z true 0 4 n) + -4294967296)) mod 2^64) 30 + 1936)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  qngte_kw38 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  qngte_kw39 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  qngte_kwr40 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true ;
  qngte_kw41 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  qngte_kw42 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qngte_kwr43 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (QC + 0 + d)) k = true ;
  qngte_kwr44 : forall d k, 0 <= d -> d + Z.of_nat k <= 8192 -> store_ok SEGS m (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104 + d)) k = true ;
  qngte_kimg45 : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None
}.


#[using="Type"] Lemma qngte_setup : forall regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5, qngte_pre regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 ->
  regs_ok (Ez regs (VALS_qngte CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) AXF_qngte.sr_qngte regs /\ know_ok SEGS (Ez regs (VALS_qngte CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) m AXF_qngte.kn_qngte.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 P. destruct P as [qngte_R8 qngte_R14 qngte_R19 qngte_HSTK qngte_rng_CA qngte_rng_QC qngte_rng_n qngte_rng_SB qngte_rng_RIB qngte_rng_na qngte_rng_cp qngte_rng_csz qngte_rng_st qngte_rng_qb qngte_rng_sz qngte_rng_mp qngte_rng_mx qngte_rng_stk qngte_rng_g7 qngte_rng_g8 qngte_rng_g9 qngte_rng_g10 qngte_rng_g11 qngte_rng_c0 qngte_rng_c2 qngte_rng_c3 qngte_rng_c4 qngte_rng_c5 qngte_ka1 qngte_kr3 qngte_ka5 qngte_ka7 qngte_kw8 qngte_kwr9 qngte_kw10 qngte_kwr11 qngte_kw12 qngte_kw13 qngte_kw14 qngte_kw15 qngte_kw16 qngte_kw17 qngte_kw18 qngte_kw19 qngte_kw20 qngte_kw21 qngte_kw22 qngte_kw23 qngte_kw24 qngte_kw25 qngte_kw26 qngte_kw27 qngte_kw28 qngte_kw29 qngte_kw30 qngte_kw31 qngte_kw32 qngte_kw33 qngte_kw34 qngte_kwr35 qngte_kw36 qngte_kw37 qngte_kw38 qngte_kw39 qngte_kwr40 qngte_kw41 qngte_kw42 qngte_kwr43 qngte_kwr44 qngte_kimg45].
  set (E := Ez regs (VALS_qngte CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)).
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
  { unfold AXF_qngte.sr_qngte.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite qngte_R8, zeval_sound. cbn [zeval edenot AXF_qngte.e_CA AXF_qngte.e_QC AXF_qngte.e_n AXF_qngte.e_SB AXF_qngte.e_RIB AXF_qngte.e_na AXF_qngte.e_cp AXF_qngte.e_csz AXF_qngte.e_st AXF_qngte.e_qb AXF_qngte.e_sz AXF_qngte.e_mp AXF_qngte.e_mx AXF_qngte.e_stk AXF_qngte.e_g7 AXF_qngte.e_g8 AXF_qngte.e_g9 AXF_qngte.e_g10 AXF_qngte.e_g11 AXF_qngte.e_c0 AXF_qngte.e_c2 AXF_qngte.e_c3 AXF_qngte.e_c4 AXF_qngte.e_c5 AXF_qngte.REC AXF_qngte.RI AXF_qngte.CHP AXF_qngte.BAT AXF_qngte.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite qngte_R14. reflexivity.
    - rewrite qngte_R19. reflexivity. }
  unfold know_ok, AXF_qngte.kn_qngte.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qngte.e_CA AXF_qngte.e_QC AXF_qngte.e_n AXF_qngte.e_SB AXF_qngte.e_RIB AXF_qngte.e_na AXF_qngte.e_cp AXF_qngte.e_csz AXF_qngte.e_st AXF_qngte.e_qb AXF_qngte.e_sz AXF_qngte.e_mp AXF_qngte.e_mx AXF_qngte.e_stk AXF_qngte.e_g7 AXF_qngte.e_g8 AXF_qngte.e_g9 AXF_qngte.e_g10 AXF_qngte.e_g11 AXF_qngte.e_c0 AXF_qngte.e_c2 AXF_qngte.e_c3 AXF_qngte.e_c4 AXF_qngte.e_c5 AXF_qngte.REC AXF_qngte.RI AXF_qngte.CHP AXF_qngte.BAT AXF_qngte.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ qngte_rng_CA eq_refl eq_refl), ?(mod64_of_range QC _ _ qngte_rng_QC eq_refl eq_refl), ?(mod64_of_range n _ _ qngte_rng_n eq_refl eq_refl), ?(mod64_of_range SB _ _ qngte_rng_SB eq_refl eq_refl), ?(mod64_of_range RIB _ _ qngte_rng_RIB eq_refl eq_refl), ?(mod64_of_range cp _ _ qngte_rng_cp eq_refl eq_refl), ?(mod64_of_range qb _ _ qngte_rng_qb eq_refl eq_refl), ?(mod64_of_range sz _ _ qngte_rng_sz eq_refl eq_refl), ?(mod64_of_range mx _ _ qngte_rng_mx eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qngte_kwr9 | apply qngte_kwr11 | apply qngte_kwr35 | apply qngte_kwr40 | apply qngte_kwr43 | apply qngte_kwr44]; assumption).
  all: try (clear - qngte_rng_CA qngte_rng_QC qngte_rng_n qngte_rng_SB qngte_rng_RIB qngte_rng_na qngte_rng_cp qngte_rng_csz qngte_rng_st qngte_rng_qb qngte_rng_sz qngte_rng_mp qngte_rng_mx qngte_rng_stk qngte_rng_g7 qngte_rng_g8 qngte_rng_g9 qngte_rng_g10 qngte_rng_g11 qngte_rng_c0 qngte_rng_c2 qngte_rng_c3 qngte_rng_c4 qngte_rng_c5 qngte_ka1 qngte_kr3 qngte_ka5 qngte_ka7 HQ HP; lia).
  all: first [lia].
Qed.


Definition qngte_mem_pngt (m : word -> option byte) (regs : bvmap 5 word) (CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (RIB + 3144)) (word_to_le_bytes 8 (wa (n + na)))) (wa (RIB + 3072)) (word_to_le_bytes 8 (wa 0))) (wa (CA + 1920)) (word_to_le_bytes 4 (wa n))) (wa (CA + 1920)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 n + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (csz + st)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215104)) (word_to_le_bytes 8 (wa 0))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215112)) (word_to_le_bytes 8 (wa (sz + 8192)))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215120)) (word_to_le_bytes 8 (wa 1))) (wa (SB + (16 * ext_Z false 0 4 cp) + 103079215128)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 16)) (word_to_le_bytes 8 (wa ((SB + (16 * ext_Z false 0 4 cp)) + 103079215104)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa ((qb + sz) + 8192))).

#[using="Type"] Theorem qngte_pngt : forall regs m rom CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5, qngte_pre regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 ->
  scs_denot SEGS m (Ez regs (VALS_qngte CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) (snd (fst AXF_qngte.RES_pngt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x446c0) m rom) (mkst R (wa 0x43af8) (qngte_mem_pngt m regs CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5) rom) /\
    getr R 1 = wa 277240 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 224) /\ getr R 5 = wa 4611686018427387904 /\ getr R 6 = wa 0 /\ getr R 7 = wa 1152921504606846976 /\ getr R 8 = wa c0 /\ getr R 9 = wa QC /\ getr R 10 = wa QC /\ getr R 11 = wa ((qb + sz) + 8192) /\ getr R 12 = wa 1 /\ getr R 13 = wa mp /\ getr R 14 = wa (sz + 8192) /\ getr R 15 = wa 0 /\ getr R 16 = wa 103079215104 /\ getr R 17 = wa 18446742974197923840 /\ getr R 18 = wa c2 /\ getr R 19 = wa c3 /\ getr R 20 = wa c4 /\ getr R 21 = wa c5 /\ getr R 22 = wa mx /\ getr R 23 = wa g7 /\ getr R 24 = wa g8 /\ getr R 25 = wa g9 /\ getr R 26 = wa g10 /\ getr R 27 = wa g11 /\ getr R 28 = wa 0 /\ (forall k, In k [3; 4; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 P Hsc. destruct (qngte_setup regs m CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 P) as [HR HK].
  set (E := Ez regs (VALS_qngte CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) in *. destruct P as [qngte_R8 qngte_R14 qngte_R19 qngte_HSTK qngte_rng_CA qngte_rng_QC qngte_rng_n qngte_rng_SB qngte_rng_RIB qngte_rng_na qngte_rng_cp qngte_rng_csz qngte_rng_st qngte_rng_qb qngte_rng_sz qngte_rng_mp qngte_rng_mx qngte_rng_stk qngte_rng_g7 qngte_rng_g8 qngte_rng_g9 qngte_rng_g10 qngte_rng_g11 qngte_rng_c0 qngte_rng_c2 qngte_rng_c3 qngte_rng_c4 qngte_rng_c5 qngte_ka1 qngte_kr3 qngte_ka5 qngte_ka7 qngte_kw8 qngte_kwr9 qngte_kw10 qngte_kwr11 qngte_kw12 qngte_kw13 qngte_kw14 qngte_kw15 qngte_kw16 qngte_kw17 qngte_kw18 qngte_kw19 qngte_kw20 qngte_kw21 qngte_kw22 qngte_kw23 qngte_kw24 qngte_kw25 qngte_kw26 qngte_kw27 qngte_kw28 qngte_kw29 qngte_kw30 qngte_kw31 qngte_kw32 qngte_kw33 qngte_kw34 qngte_kwr35 qngte_kw36 qngte_kw37 qngte_kw38 qngte_kw39 qngte_kwr40 qngte_kw41 qngte_kw42 qngte_kwr43 qngte_kwr44 qngte_kimg45].
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
  destruct (run_sound SEGS 160 [0x43af8] AXF_qngte.scr_pngt 0x446c0 AXF_qngte.sr_qngte AXF_qngte.kn_qngte 56 _ _ _ E m rom regs AXF_qngte.RES_pngt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qngte.RES_pngt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qngte_mem_pngt m regs CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qngte_mem_pngt. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End QNGTE.
End AXF_qngtez.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Local Ltac lenq := rewrite ?length_N_to_le_bytes; change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.
Local Ltac znq := change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.

Section SCQ3E.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variable SPa : Z.
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.
(* [comment removed for export] *)
#[using="HSPa"] Lemma sc_qngte : forall CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5,
  2^46 <= SPa <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ QC = CA - 128 /\ CA + 2592 + 256 <= SPa /\
  17594333495296 <= SB /\ RIB = SB + 137438953472 /\ RIB + 4096 + 256 <= SPa /\ (CA + 2592 <= SB \/ RIB + 4096 <= QC) /\
  1 <= n <= 8 /\ 0 <= cp <= 16383 /\ 0 <= qb <= 2^62 /\ 0 <= sz <= 2^40 /\ 0 <= mx <= 2^62 ->
  scs_denot SEGS m (Ez R (AXF_qngtez.VALS_qngte CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5)) (snd (fst AXF_qngte.RES_pngt)).
Proof. LiaFast.lf_pins (fun (HSPa : LiaFast.U) => LiaFast.u0).
  intros CA QC n SB RIB na cp csz st qb sz mp mx stk g7 g8 g9 g10 g11 c0 c2 c3 c4 c5 HH. unfold AXF_qngtez.VALS_qngte.
  assert (HD : CA + 2592 <= SB \/ RIB + 4096 <= QC) by tauto.
  assert (HPL : (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) by tauto.
  destruct HPL as [HPL|HPL].
  - assert (HD1 : CA + 2592 <= SB) by (clear - HPL HH; lia). assert (HH2 := conj HPL (conj HD1 HH)); clear HH HD HD1 HPL.
    sc_refl [SPr; (EVar 32, LOW); (EVar 33, (4176, 61520)); (EVar 34, (1, 8)); (EVar 35, (17594333495296, 2^47)); (EVar 36, (17594333495296, 2^47)); (EVar 38, (0, 16383));
              (EVar 41, (0, 2^62)); (EVar 42, (0, 2^40)); (EVar 44, (0, 2^62))]
             [(EVar 32, EVar 33, 128); (EVar 33, EVar 32, -128); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472);
              (EVar 2, EVar 32, 2848); (EVar 2, EVar 33, 2976); (EVar 2, EVar 36, 4352); (EVar 2, EVar 35, 137438957824);
              (EVar 35, EVar 32, 2592); (EVar 35, EVar 33, 2720); (EVar 36, EVar 32, 137438956064); (EVar 36, EVar 33, 137438956192)] R HSPa HSPa HH2.
  - destruct HD as [HD|HD]; assert (HH2 := conj HPL (conj HD HH)); clear HH HD HPL.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (6529104, 2^47)); (EVar 34, (1, 8)); (EVar 35, (17594333495296, 2^47)); (EVar 36, (17594333495296, 2^47)); (EVar 38, (0, 16383));
                (EVar 41, (0, 2^62)); (EVar 42, (0, 2^40)); (EVar 44, (0, 2^62))]
               [(EVar 32, EVar 33, 128); (EVar 33, EVar 32, -128); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472);
                (EVar 2, EVar 32, 2848); (EVar 2, EVar 33, 2976); (EVar 2, EVar 36, 4352); (EVar 2, EVar 35, 137438957824);
                (EVar 35, EVar 32, 2592); (EVar 35, EVar 33, 2720); (EVar 36, EVar 32, 137438956064); (EVar 36, EVar 33, 137438956192)] R HSPa HSPa HH2.
    + sc_refl [SPr; (EVar 32, HIGH); (EVar 33, (6529104, 2^47)); (EVar 34, (1, 8)); (EVar 35, (17594333495296, 2^47)); (EVar 36, (17594333495296, 2^47)); (EVar 38, (0, 16383));
                (EVar 41, (0, 2^62)); (EVar 42, (0, 2^40)); (EVar 44, (0, 2^62))]
               [(EVar 32, EVar 33, 128); (EVar 33, EVar 32, -128); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472);
                (EVar 2, EVar 32, 2848); (EVar 2, EVar 33, 2976); (EVar 2, EVar 36, 4352); (EVar 2, EVar 35, 137438957824);
                (EVar 33, EVar 36, 4096); (EVar 32, EVar 36, 4224); (EVar 33, EVar 35, 137438957568); (EVar 32, EVar 35, 137438957696)] R HSPa HSPa HH2.
Qed.
End SCQ3E.

(* [comment removed for export] *)
Section QREFILLE.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC CA c SB nc newc j qj fsz mp mx SP : Z).
Hypothesis Hc24 : c = 24.
Hypothesis IQ : q_inv m QC SB qj 0 0.
Hypothesis I : INV_G m CA SB c 8192 nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis Hcnt0 : cnt_of nc j = 0.
Hypothesis H1 : getr regs 1 = wa 277240.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis H9 : getr regs 9 = wa QC.
Hypothesis H10 : getr regs 10 = wa QC.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H13 : getr regs 13 = wa mp.
Hypothesis H14 : getr regs 14 = wa fsz.
Hypothesis H22 : getr regs 22 = wa mx.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis HQC : QC = CA - 128.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hsz : 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62.
Hypothesis Hwq : wr m QC 32.
Hypothesis Hwb : wr m (SB + 103079215104 + 8192 * j) 8192.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="qj mx Hc24 IQ I Hj Hcnt0 H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb HIMG"] Lemma q_refill_e :
  exists R m', msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43af8) m' rom) /\
    (forall k, In k KQC -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB j 1 (fsz + 8192) /\ INV_G m' CA SB c 8192 nc newc (j + 1) /\
    rd m' (SB + 103079215104 + 8192 * j) 8 0 /\ rd m' (SB + 103079215104 + 8192 * j + 24) 8 mp /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> ~ (QC <= x < QC + 32) ->
       ~ (SB + 103079215104 + 8192 * j <= x < SB + 103079215104 + 8192 * j + 32) -> m' (wa x) = m (wa x)) /\
    mem_grows m m'.
Proof. LiaFast.lf_pins (fun (qj mx Hc24 IQ I Hj Hcnt0 H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb HIMG : LiaFast.U) => LiaFast.u0).
  destruct IQ as (_ & Rqb & [(_ & _ & Rq0)|(Hq1 & _)]); [|lia].
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (refill_step nc j ltac:(slia) ltac:(slia) Hcnt0) as (Ej & Eb & Ec).
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb.
  rewrite Hcnt0 in Icnt. clear Ich.
  set (b := b_of nc j) in *. set (nf := newc - nc * b) in *.
  destruct Ist as (st & Hst & Rst). destruct Ina as (na & Hna & Rna).
  change (8192 / 16) with 512 in *.
  set (B := SB + 103079215104 + 8192 * j) in *.
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 /\ QC = CA - 128 /\
               17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ c = 24 /\
               1 <= nc <= 8 /\ nc <= nf <= newc /\ newc <= 32 /\ 0 <= st < 2^64 /\ 0 <= na < 2^64 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC) /\ j = nc * b /\ 1 <= j /\ j <= 31 /\
               B = SB + 103079215104 + 8192 * j /\ 0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62) by (unfold nf, B; slia).
  clear Igeo HCA HSB HSEP Hst Hna HSP Hsz HQC. clearbody B.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  set (v1 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) in *. set (v8 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) in *.
  set (v9 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) in *. set (v18 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) in *.
  set (v19 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) in *. set (v20 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) in *.
  set (v21 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) in *. set (v12 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) in *.
  set (g22 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) in *. set (g23 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) in *.
  set (g24 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) in *. set (g25 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) in *.
  set (g26 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) in *. set (g27 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) in *.
  assert (H1z : getr regs (Z_to_bv 5 (Z.of_nat 1)) = wa 277240) by (pose proof H1 as X; regzH X; exact X).
  assert (H2z : getr regs (Z_to_bv 5 (Z.of_nat 2)) = wa SP) by (pose proof H2 as X; regzH X; exact X).
  assert (H9z : getr regs (Z_to_bv 5 (Z.of_nat 9)) = wa QC) by (pose proof H9 as X; regzH X; exact X).
  assert (H22z : getr regs (Z_to_bv 5 (Z.of_nat 22)) = wa mx) by (pose proof H22 as X; regzH X; exact X).
  assert (Ev1 : v1 = 277240) by (unfold v1; rewrite H1z, u_wa_small by lia; reflexivity).
  assert (Ev9 : v9 = QC) by (unfold v9; rewrite H9z, u_wa_small by (zlh HZ); reflexivity).
  assert (Eg22 : g22 = mx) by (unfold g22; rewrite H22z, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_pre regs m QC CA fsz mp).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [lia | exact HSTK].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rq0.
    - replace (CA + 1920) with (REC CA c) by (zlh HZ). exact Icnt. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_phead regs m rom QC CA fsz mp P0 (sc_qhead regs m SP HSPa QC CA fsz mp ltac:(zlh HZ)))
    as (R0 & Hms0 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A18 & A19 & A20 & A21 & KK0).
  clear P0.
  set (m1 := m1q m SP v1 v8 v9 v18 v19 v20 v21).
  assert (EM1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_mem_phead m regs QC CA fsz mp = m1) by (unfold m1, m1q, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qheadz.qhead_mem_phead; rewrite HSPa; nsub; reflexivity).
  rewrite EM1 in Hms0. clear EM1.
  assert (G1 : mem_grows m m1) by apply m1q_grows.
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 56 <= x < SP) -> m1 (wa x) = m (wa x)) by (intros x Hx H; apply m1q_frame; [(zlh HZ) | exact Hx | exact H]).
  assert (HSP0 : bv_unsigned (getr R0 (Z_to_bv 5 (Z.of_nat 2))) = SP - 64) by (rgz; rewrite A2, HSPa, u_wa_small by (zlh HZ); ring).
  regzH A8. regzH A9. regzH A18. regzH A19. regzH A20. regzH A21.
  (* [comment removed for export] *)
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_pre R0 m1 CA c (2 * nc)).
  { constructor; [exact A10 | rewrite A11; f_equal; (zlh HZ) | exact A12 | rewrite A13; f_equal; (zlh HZ) | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP0; (zlh HZ) | ].
    - replace (getr R0 2) with (wa (SP - 64)) by (rgz; rewrite A2, HSPa; f_equal; ring).
      apply (stk_ok_move m1 SP (SP - 64) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_pnpr R0 m1 rom CA c (2 * nc) P1 (sc_qnpr R0 m1 (SP - 64) HSP0 CA c (2 * nc) ltac:((zlh HZ))))
    as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & KK2).
  clear P1 C1.
  pose proof (msteps_trans SEGS _ _ _ Hms0 Hms2) as Hms12. clear Hms0 Hms2.
  regzH C2. regzH C8. regzH C9.
  assert (Vn : bv_unsigned (edenot (Ez R0 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.VALS_qnpr CA c (2 * nc))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = nc).
  { rewrite (AXG_gf1.gsrlw1 R0 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.VALS_qnpr CA c (2 * nc)) (2 * nc) eq_refl ltac:((zlh HZ))). replace (2 * nc) with (nc * 2) by ring. apply Z.div_mul. lia. }
  rewrite Vn in C9, C14.
  assert (V18 : bv_unsigned (getr R0 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite A8, u_wa_small by (zlh HZ); (zlh HZ)).
  assert (V19 : bv_unsigned (getr R0 (Z_to_bv 5 (Z.of_nat 9))) = CA) by (rewrite A9, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := m2q m1 SP (CA + 80 * c) CA).
  assert (EM2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_mem_pnpr m1 R0 CA c (2 * nc) = m2) by (unfold m2, m2q, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1.AXF_qnprz.qnpr_mem_pnpr; rewrite HSP0, V18, V19; nsub; reflexivity).
  rewrite EM2 in Hms12. clear EM2.
  assert (HSP2 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 2))) = SP - 96) by (rewrite C2, HSP0, u_wa_small by (zlh HZ); ring).
  assert (G2 : mem_grows m m2) by (exact (mem_grows_trans _ _ _ G1 (m2q_grows m1 SP (CA + 80 * c) CA))).
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 88 <= x < SP) -> m2 (wa x) = m (wa x)).
  { intros x Hx H. unfold m2. rewrite m2q_frame by (clear - HZ Hx H; lia). apply F1; clear - HZ Hx H; lia. }
  (* [comment removed for export] *)
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0z.gng0_pre R2 m2 CA c nc SB (SB + 137438953472) nf).
  { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | exact C14 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP2; (zlh HZ) | (zlh HZ) | | | | | | ].
    - rewrite ?(ri_comm c SB). replace (getr R2 2) with (wa (SP - 96)) by (rgz; rewrite C2, HSP0; f_equal; ring).
      apply (stk_ok_move m2 SP (SP - 96) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact ISB].
    - rewrite ?(ri_comm c SB). apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact IRIB].
    - rewrite ?(ri_comm c SB). rewrite Z.add_0_r. apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact Imu].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m2 _ G2). apply Iwri; (clear - HZ Hd Hk; lia).
    - rewrite ?(ri_comm c SB). apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact Inf].
    - rewrite ?(ri_comm c SB). intros d k Hd Hk. apply (store_ok_mono SEGS k m m2 _ G2). replace (SB + 137438953472 + 128 * c + 16 + d) with (SB + 137438953472 + 128 * c + (16 + d)) by ring. apply Iwri; (clear - HZ Hd Hk; lia). }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0z.gng0_png0 R2 m2 rom CA c nc SB (SB + 137438953472) nf P2
              (sc_gng0 R2 m2 (SP - 96) HSP2 CA c nc SB (SB + 137438953472) nf ltac:((zlh HZ))))
    as (R3 & Hms3 & D1 & D2 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & KK3).
  clear P2 D1 D5 D6 D7 D9 D10 D12 D15 D16 D17 D21 D22 D23 D24 D25.
  pose proof (msteps_trans SEGS _ _ _ Hms12 Hms3) as Hms13. clear Hms12 Hms3.
  assert (V28 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite C8, u_wa_small by (zlh HZ); reflexivity).
  assert (V29 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 9))) = nc) by (rewrite C9, u_wa_small by (zlh HZ); reflexivity).
  assert (V218 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18))) = mp) by (rewrite (KK2 18%nat ltac:(cbn; memb')), A18, u_wa_small by (zlh HZ); reflexivity).
  assert (V219 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19))) = QC) by (rewrite (KK2 19%nat ltac:(cbn; memb')), A19, u_wa_small by (zlh HZ); reflexivity).
  assert (V220 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20))) = v12) by (rewrite (KK2 20%nat ltac:(cbn; memb')), A20; apply u_wa_small; unfold v12; pose proof (u_rng64 (getr regs (Z_to_bv 5 (Z.of_nat 12)))); lia).
  assert (V221 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 21))) = fsz) by (rewrite (KK2 21%nat ltac:(cbn; memb')), A21, u_wa_small by (zlh HZ); reflexivity).
  assert (W22 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22))) = g22) by (rewrite (KK2 22%nat ltac:(cbn; memb')), (KK0 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 23))) = g23) by (rewrite (KK2 23%nat ltac:(cbn; memb')), (KK0 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 24))) = g24) by (rewrite (KK2 24%nat ltac:(cbn; memb')), (KK0 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 25))) = g25) by (rewrite (KK2 25%nat ltac:(cbn; memb')), (KK0 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 26))) = g26) by (rewrite (KK2 26%nat ltac:(cbn; memb')), (KK0 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 27))) = g27) by (rewrite (KK2 27%nat ltac:(cbn; memb')), (KK0 27%nat ltac:(cbn; memb')); reflexivity).
  set (m3 := m3q m2 SP (CA + 80 * c) nc mp QC v12 fsz g22 g23 g24 g25 g26 g27 (SB + 137438953472 + 128 * c) nf).
  assert (EM3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0z.gng0_mem_png0 m2 R2 CA c nc SB (SB + 137438953472) nf = m3).
  { unfold m3, m3q, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXF_gng0z.gng0_mem_png0. rewrite ?(ri_comm c SB). rewrite HSP2, V28, V29, V218, V219, V220, V221, W22, W23, W24, W25, W26, W27. nsub. rewrite ?Z.add_0_r. reflexivity. }
  rewrite EM3 in Hms13. clear EM3 V28 V29 V218 V219 V220 V221 W22 W23 W24 W25 W26 W27 C8 C9 C10 C11 C12 C13 C14.
  assert (G3 : mem_grows m m3) by (exact (mem_grows_trans _ _ _ G2 (m3q_grows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))).
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 200 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1' H3. unfold m3. rewrite m3q_frame by (clear - HZ Hx H1' H3; lia). apply F12; clear - HZ Hx H1' H3; lia. }
  destruct (m3q_RI m2 SP (CA + 80 * c) nc mp QC v12 fsz g22 g23 g24 g25 g26 g27 (SB + 137438953472 + 128 * c) nf ltac:((zlh HZ)) ltac:((zlh HZ))) as [R3mu R3nf].
  fold m3 in R3mu, R3nf.
  (* [comment removed for export] *)
  regzH D2. regzH D8. regzH D14. regzH D19. rewrite ?(ri_comm c SB) in D8.
  assert (L11 : getr R3 11 = wa (CA + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat nc))) by (rewrite D11, Z2Nat.id by (zlh HZ); f_equal; ring).
  assert (L13 : getr R3 13 = wa (CA + 80 * c + 16)) by (rewrite D13; reflexivity).
  assert (L20 : getr R3 20 = wa (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc))) by (rewrite D20; f_equal; ring).
  clear D11 D13 D20.
  assert (LW : forall i, 0 <= i < Z.of_nat (Z.to_nat nc) -> 0 <= (newc - 1 - (nf - nc + i)) * 512 < 2^31 /\
                 rd m3 (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc) + 4 * i) 4 ((newc - 1 - (nf - nc + i)) * 512)).
  { intros i Hi. rewrite Z2Nat.id in Hi by (zlh HZ). split.
    - clear - HZ Hi. lia.
    - pose proof (Ifa (nf - nc + i) ltac:(clear - HZ Hi; lia)) as Rf. replace (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc) + 4 * i) with (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc + i)) by ring.
      apply (rd_frame m m3); [clear - HZ Hi; lia | lenq; clear - HZ Hi; lia | intros x Hx; znq; apply F13; clear - HZ Hi Hx; lia | exact Rf]. }
  assert (LWR : wr m3 (CA + 80 * c + 16) (4 * Z.of_nat (Z.to_nat nc))).
  { intros d k Hd Hk. rewrite Z2Nat.id in Hk by (clear - HZ Hd Hk; lia). apply (store_ok_mono SEGS k m m3 _ G3). replace (CA + 80 * c + 16 + d) with (CA + 80 * c + (16 + d)) by ring. apply Iwrec; clear - HZ Hd Hk; lia. }
  destruct (ngl_loop rom (Z.to_nat nc) R3 m3 (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc)) (CA + 80 * c + 16)
              (fun i => (newc - 1 - (nf - nc + i)) * 512) ltac:((zlh HZ)) L11 L13 L20
              ltac:((zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) ltac:((zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) LW LWR)
    as (R4 & m4 & Hms4 & E13 & E20 & KK4 & RD4 & F4 & G4).
  rewrite Z2Nat.id in RD4, F4 by (zlh HZ). clear LW LWR L11 L13 L20 E13 E20.
  pose proof (msteps_trans SEGS _ _ _ Hms13 Hms4) as Hms14. clear Hms13 Hms4.
  assert (G14 : mem_grows m m4) by exact (mem_grows_trans _ _ _ G3 G4).
  assert (F14 : forall x, 0 <= x < 2^64 -> ~ (SP - 200 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> m4 (wa x) = m (wa x)).
  { intros x Hx H1' H3 H4. rewrite F4 by assumption. apply F13; assumption. }
  (* [comment removed for export] *)
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 224) by (rewrite (KK4 2%nat ltac:(cbn; memb')), D2, HSP2, u_wa_small by (zlh HZ); ring).
  set (cp := j * 512).
  destruct (qslots_ok m SP v1 v8 v9 v18 v19 v20 v21 (CA + 80 * c) CA nc mp QC v12 fsz g22 g23 g24 g25 g26 g27 (SB + 137438953472 + 128 * c) nf ltac:((zlh HZ)) ltac:((zlh HZ)))
    as (S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31 & S32).
  fold m1 m2 m3 in S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32.
  assert (HZ4 : 2^46 + 4096 <= SP <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 <= SP - 2048 /\ c = 24 /\ 1 <= nc <= 8) by (zlh HZ).
  assert (SL : forall o v, 0 <= o <= 216 -> rd m3 (SP - 224 + o) 8 v -> rdn SEGS m4 (wa (bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) + o)) 8 = Some (word_to_le_bytes 8 (wa v))).
  { intros o v Ho Hr. rewrite HSP4. apply (rd_frame m3 m4); [clear - HZ4 Ho; lia | lenq; clear - HZ4 Ho; lia | intros x Hx; znq; apply F4; clear - HZ4 Ho Hx; lia | exact Hr]. }
  assert (P4 : AXF_qngtez.qngte_pre R4 m4 CA QC nc SB (SB + 137438953472) na cp 8192 st 0 fsz mp mx v12 g23 g24 g25 g26 g27 v8 v18 v19 v20 v21).
  { constructor.
    all: try ((zlh HZ) || (unfold cp; zlh HZ) || apply u_rng64 || (rewrite HSP4; (zlh HZ))).
    - regzG. rewrite (KK4 8%nat ltac:(cbn; memb')), D8. f_equal. (zlh HZ).
    - regzG. rewrite (KK4 14%nat ltac:(cbn; memb')). exact D14.
    - regzG. rewrite (KK4 19%nat ltac:(cbn; memb')). exact D19.
    - replace (getr R4 2) with (wa (SP - 224)) by (regzG; rewrite (KK4 2%nat ltac:(cbn; memb')), D2, HSP2; f_equal; ring).
      apply (stk_ok_move m4 SP (SP - 224) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m4 (wa SP) 2048 G14 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - replace (SB + 137438953472 + 3144) with (SB + 137438953472 + 128 * c + 72) by (zlh HZ).
      apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rna].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (SB + 137438953472 + 3144 + d) with (SB + 137438953472 + 128 * c + (72 + d)) by (zlh HZ). apply Iwri; clear - HZ Hd Hk; lia.
    - replace (SB + 137438953472 + 3072) with (SB + 137438953472 + 128 * c) by (zlh HZ).
      apply (rd_frame m3 m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F4; clear - HZ Hx; lia | exact R3mu].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (SB + 137438953472 + 3072 + d) with (SB + 137438953472 + 128 * c + d) by (zlh HZ). apply Iwri; clear - HZ Hd Hk; lia.
    - apply SL; [clear; lia | exact S10].
    - apply SL; [clear; lia |]. replace (CA + 1920) with (CA + 80 * c) by (zlh HZ). exact S11.
    - apply SL; [clear; lia | exact S12].
    - apply SL; [clear; lia | exact S13].
    - apply SL; [clear; lia | exact S14].
    - apply SL; [clear; lia | exact S15].
    - apply SL; [clear; lia | exact S16].
    - apply SL; [clear; lia |]. rewrite <- Eg22. exact S17.
    - apply SL; [clear; lia | exact S18].
    - apply SL; [clear; lia | exact S19].
    - apply SL; [clear; lia | exact S20].
    - apply SL; [clear; lia | exact S21].
    - apply SL; [clear; lia | exact S22].
    - apply SL; [clear; lia | exact S23].
    - apply SL; [clear; lia |]. replace (CA + 1920) with (CA + 80 * c) by (zlh HZ). exact S24.
    - apply SL; [clear; lia | exact S25].
    - apply SL; [clear; lia | exact S26].
    - apply SL; [clear; lia | exact S27].
    - apply SL; [clear; lia | exact S28].
    - apply SL; [clear; lia | exact S29].
    - apply SL; [clear; lia |]. rewrite <- Ev9. exact S30.
    - apply SL; [clear; lia | exact S31].
    - apply SL; [clear; lia |]. rewrite <- Ev1. exact S32.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (CA + 1920 + d) with (REC CA c + d) by (zlh HZ). apply Iwrec; clear - HZ Hd Hk; lia.
    - replace (CA + 1928) with (REC CA c + 8) by (zlh HZ). apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Isz].
    - rewrite chp_off by (zlh HZ). pose proof (RD4 (nc - 1) ltac:((zlh HZ))) as R7.
      replace (CA + 80 * c + 16 + 4 * (nc - 1)) with (CA + 4 * (nc - 1) + 1936) in R7 by (zlh HZ).
      replace ((newc - 1 - (nf - nc + (nc - 1))) * 512) with cp in R7 by (unfold cp, nf; zlh HZ). exact R7.
    - apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact ISB].
    - apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rst].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; clear - HZ Hd Hk; lia.
    - rewrite Z.add_0_r. apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rq0].
    - apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rqb].
    - intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m4 _ G14). apply Hwq; assumption.
    - intros d k Hd Hk. rewrite ext_Z_u32 by (unfold cp; zlh HZ). apply (store_ok_mono SEGS k m m4 _ G14).
      replace (SB + 16 * cp + 103079215104 + d) with (B + d) by (unfold cp; zlh HZ). apply Hwb; assumption.
    - intros i Hi. change (Z_to_bv 64 i) with (wa i). rewrite F14 by (clear - HZ Hi; lia). apply HIMG. exact Hi. }
  destruct (AXF_qngtez.qngte_pngt R4 m4 rom CA QC nc SB (SB + 137438953472) na cp 8192 st 0 fsz mp mx v12 g23 g24 g25 g26 g27 v8 v18 v19 v20 v21 P4
              (sc_qngte R4 m4 (SP - 224) HSP4 CA QC nc SB (SB + 137438953472) na cp 8192 st 0 fsz mp mx v12 g23 g24 g25 g26 g27 v8 v18 v19 v20 v21 ltac:(unfold cp; zlh HZ)))
    as (R5 & Hms5 & T1 & T2 & _ & _ & _ & T8 & T9 & _ & _ & _ & _ & _ & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & _ & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms14 Hms5) as Hms. clear Hms14 Hms5.
  set (m5 := m5q m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na st B fsz mp QC).
  assert (EM5 : AXF_qngtez.qngte_mem_pngt m4 R4 CA QC nc SB (SB + 137438953472) na cp 8192 st 0 fsz mp mx v12 g23 g24 g25 g26 g27 v8 v18 v19 v20 v21 = m5).
  { unfold m5, m5q, AXF_qngtez.qngte_mem_pngt. rewrite ext_Z_lo32_small, ext_Z_u32 by (unfold cp; zlh HZ). rewrite ?addneg.
    replace (SB + 137438953472 + 3144) with (SB + 137438953472 + 128 * c + 72) by (zlh HZ).
    replace (SB + 137438953472 + 3072) with (SB + 137438953472 + 128 * c) by (zlh HZ).
    replace (CA + 1920) with (CA + 80 * c) by (zlh HZ).
    replace (SB + 16 * cp + 103079215104) with B by (unfold cp; zlh HZ). replace (SB + 16 * cp + 103079215112) with (B + 8) by (unfold cp; zlh HZ).
    replace (SB + 16 * cp + 103079215120) with (B + 16) by (unfold cp; zlh HZ). replace (SB + 16 * cp + 103079215128) with (B + 24) by (unfold cp; zlh HZ).
    replace (0 + fsz + 8192) with (fsz + 8192) by ring. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  assert (G5 : mem_grows m m5) by (exact (mem_grows_trans _ _ _ G14 (m5q_grows _ _ _ _ _ _ _ _ _ _ _))).
  assert (FX5 : forall x, 0 <= x < 2^64 -> ~ (SP - 200 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (SB + 137438953472 + 128 * c + 72 <= x < SB + 137438953472 + 128 * c + 80) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> ~ (CA + 2576 <= x < CA + 2584) -> ~ (B <= x < B + 32) -> ~ (QC <= x < QC + 32) -> m5 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8. unfold m5. rewrite m5q_frame by (clear - HZ Hx Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8; lia). apply F14; assumption. }
  (* [comment removed for export] *)
  set (m5a := m5c m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na 8192 st).
  assert (E5a : m5 = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m5a (wa B) (word_to_le_bytes 8 (wa 0))) (wa (B + 8)) (word_to_le_bytes 8 (wa (fsz + 8192))))
                       (wa (B + 16)) (word_to_le_bytes 8 (wa 1))) (wa (B + 24)) (word_to_le_bytes 8 (wa mp))) (wa (QC + 8)) (word_to_le_bytes 8 (wa B)))
                       (wa (QC + 0)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 16)) (word_to_le_bytes 8 (wa B))) (wa (QC + 24)) (word_to_le_bytes 8 (wa (fsz + 8192)))) by reflexivity.
  assert (G5a : mem_grows m m5a) by (exact (mem_grows_trans _ _ _ G14 (m5c_grows _ _ _ _ _ _ _ _))).
  assert (G5b : mem_grows m5a m5) by (rewrite E5a; do 8 apply grows_wb; apply mem_grows_refl).
  assert (FXa : forall x, 0 <= x < 2^64 -> ~ (SP - 200 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (SB + 137438953472 + 128 * c + 72 <= x < SB + 137438953472 + 128 * c + 80) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> ~ (CA + 2576 <= x < CA + 2584) -> m5a (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5 Q6. unfold m5a. rewrite m5c_frame by (clear - HZ Hx Q1 Q2 Q3 Q4 Q5 Q6; lia). apply F14; assumption. }
  assert (FXb : forall x, 0 <= x < 2^64 -> ~ (B <= x < B + 32) -> ~ (QC <= x < QC + 32) -> m5 (wa x) = m5a (wa x)).
  { intros x Hx Q1 Q2. rewrite E5a. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q1 Q2; lia)]). reflexivity. }
  destruct (m5c_rd m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na 8192 st ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)))
    as (Rc5 & Rmu5 & Rna5 & Rst5).
  fold m5a in Rc5, Rmu5, Rna5, Rst5.
  assert (HZI : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 <= SP - 2048) by (zlh HZ).
  assert (HZS : 4194304 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\ SP <= 2^47) by (zlh HZ).
  assert (HZP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by (zlh HZ).
  assert (IGa : INV_G m5a CA SB c 8192 nc newc (j + 1)).
  { apply (inv_refill m m5a CA SB c 8192 nc newc j SP I Hj HZI HZS HZP G5a Hcnt0).
    - intros x Hx Q1 Q2. unfold owned_C in Q2. apply FXa; clear - HZ Hx Q1 Q2; lia.
    - exact Rc5.
    - apply (rd_frame m m5a); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply FXa; clear - HZ Hx; lia | exact Imc].
    - apply (rd_frame m m5a); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply FXa; clear - HZ Hx; lia | exact Isz].
    - intros i Hi. change (8192 / 16) with 512. pose proof (RD4 i Hi) as Ri. replace ((newc - 1 - (nf - nc + i)) * 512) with ((j + nc - 1 - i) * 512) in Ri by (unfold nf; zlh HZ).
      apply (rd_frame m4 m5a); [clear - HZ Hi; lia | lenq; clear - HZ Hi; lia | intros x Hx; znq; unfold m5a; apply m5c_frame; clear - HZ Hi Hx; lia | exact Ri].
    - exact Rmu5.
    - replace (newc - nc * b_of nc j - nc) with (-1 * nc + nf) by (unfold nf, b; ring).
      apply (rd_frame m3 m5a); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; unfold m5a; rewrite m5c_frame by (clear - HZ Hx; lia); apply F4; clear - HZ Hx; lia | exact R3nf].
    - exists ((nc + na) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((nc + na) mod 2^64) (nc + na)) by (apply Z.mod_mod; lia). exact Rna5.
    - exists ((8192 + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((8192 + st) mod 2^64) (8192 + st)) by (apply Z.mod_mod; lia). exact Rst5. }
  exists R5, m5. split; [exact Hms|].
  regzH T2. regzH T8. regzH T9. regzH T18. regzH T19. regzH T20. regzH T21. regzH T22. regzH T23. regzH T24. regzH T25. regzH T26. regzH T27. regzH T1.
  split.
  { intros k Hk. cbn [KQC In] in Hk.
    destruct Hk as [<-|Hk]; [rewrite T1, H1z; reflexivity|].
    destruct Hk as [<-|Hk]; [rewrite T2, HSP4, H2z; f_equal; ring|].
    destruct Hk as [<-|Hk]; [rewrite (KK5 3%nat ltac:(cbn; memb')), (KK4 3%nat ltac:(cbn; memb')), (KK3 3%nat ltac:(cbn; memb')), (KK2 3%nat ltac:(cbn; memb')), (KK0 3%nat ltac:(cbn; memb')); reflexivity|].
    destruct Hk as [<-|Hk]; [rewrite (KK5 4%nat ltac:(cbn; memb')), (KK4 4%nat ltac:(cbn; memb')), (KK3 4%nat ltac:(cbn; memb')), (KK2 4%nat ltac:(cbn; memb')), (KK0 4%nat ltac:(cbn; memb')); reflexivity|].
    destruct Hk as [<-|Hk]; [rewrite T8; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T9, H9z; reflexivity|].
    destruct Hk as [<-|Hk]; [rewrite T18; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T19; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T20; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T21; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T22, H22z; reflexivity|].
    destruct Hk as [<-|Hk]; [rewrite T23; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T24; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T25; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T26; apply wa_u|].
    destruct Hk as [<-|Hk]; [rewrite T27; apply wa_u|].
    destruct Hk. }
  split.
  { unfold q_inv. replace (SB + 103079215104 + 8192 * j) with B by (zlh HZ). split; [zlh HZ|]. split.
    { rewrite E5a. apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    right. split; [lia|]. split; [zlh HZ|].
    split.
    { rewrite E5a. do 2 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      rewrite (Z.add_0_r QC). apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { rewrite E5a. do 3 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { rewrite E5a. apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|].
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { rewrite E5a. do 6 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    split.
    { rewrite E5a. do 5 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
      apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
    intros d k Hd Hk. apply (store_ok_mono SEGS k m m5 _ G5). apply Hwb; assumption. }
  split.
  { apply (INV_G_frame m5a m5 CA SB c 8192 nc newc (j + 1)); [zlh HZ | zlh HZ | zlh HZ | zlh HZ | exact G5b | | exact IGa].
    intros x Hx. apply FXb; unfold foot_G in Hx; clear - HZ Hx; lia. }
  split.
  { rewrite E5a. do 7 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
    apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
  split.
  { rewrite E5a. do 4 (apply wb_rd_other; [zlh HZ | lenq; zlh HZ | zlh HZ | lenq; zlh HZ | lenq; zlh HZ|]).
    apply wb_rd_hit; [lia | zlh HZ | lenq; zlh HZ]. }
  split; [|exact G5].
  intros x Hx Q1 Q2 Q3 Q4. unfold owned_C in Q2. apply FX5; clear - HZ Hx Q1 Q2 Q3 Q4; lia.
Qed.
End QREFILLE.

(* [comment removed for export] *)
Theorem qnew_e : forall {fx : FPState} rom m regs QC CA SB nc newc j qj fsz mp mx SP,
  q_inv m QC SB qj 0 0 -> INV_G m CA SB 24 8192 nc newc j -> j + 1 + nc <= newc ->
  getr regs 1 = wa 277240 -> getr regs 2 = wa SP -> getr regs 9 = wa QC -> getr regs 10 = wa QC -> getr regs 11 = wa CA ->
  getr regs 13 = wa mp -> getr regs 14 = wa fsz -> getr regs 22 = wa mx ->
  2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0 -> stk_ok SEGS m (wa SP) 2048 -> QC = CA - 128 ->
  ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 ->
  17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 ->
  (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC) ->
  0 <= fsz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 ->
  wr m QC 32 -> wr m (SB + 103079215104 + 8192 * j) 8192 ->
  (forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None) ->
  exists R m', msteps SEGS (mkst regs (wa 0x43b04) m rom) (mkst R (wa 0x43af8) m' rom) /\
    (forall k, In k KQC -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB j 1 (fsz + 8192) /\ INV_G m' CA SB 24 8192 nc newc (j + 1) /\
    rd m' (SB + 103079215104 + 8192 * j) 8 0 /\ rd m' (SB + 103079215104 + 8192 * j + 24) 8 mp /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB 24 x -> ~ (QC <= x < QC + 32) ->
       ~ (SB + 103079215104 + 8192 * j <= x < SB + 103079215104 + 8192 * j + 32) -> m' (wa x) = m (wa x)) /\
    mem_grows m m'.
Proof.
  intros fx rom m regs QC CA SB nc newc j qj fsz mp mx SP IQ I Hj H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb HIMG.
  pose proof (cnt_of_range nc j ltac:(destruct I as [Igeo]; lia) ltac:(destruct I as [Igeo]; lia)) as Hcr.
  destruct (Z.eq_dec (cnt_of nc j) 0) as [E0|E0].
  - exact (q_refill_e rom m regs QC CA 24 SB nc newc j qj fsz mp mx SP eq_refl IQ I Hj E0 H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb HIMG).
  - destruct (qpop_e rom m regs QC CA SB nc newc j qj fsz mp mx SP IQ I Hj ltac:(lia) H1 H2 H9 H10 H11 H13 H14 H22 HSP HSTK HQC HCA HSB HSEP Hsz Hwq Hwb)
      as (R & m' & Hms & KK & X).
    exists R, m'. split; [exact Hms|]. split; [|exact X].
    intros k Hk. apply KK. clear - Hk. cbn [KQC KQ In] in *. intuition.
Qed.

