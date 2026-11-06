(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan AXG_put AXG_put2.

Module AXF_np0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_cnt := EVar 34.
Definition e_sz := EVar 35.
Definition e_cp := EVar 36.
Definition e_SB := EVar 37.
Definition e_st := EVar 38.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition CHP := EAlu ALU_ADD e_CA (EAlu ALU_ADD (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))) (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_cnt)) (ELit (-4294967296))) (ELit 30))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_np0 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 929816)) 11 (e_CA)) 12 (e_ND)) 13 (ELit 8)).
Definition kn_np0 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 0) 4 e_cnt;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA CHP 16) 4 e_cp;
    KWord (SA (ELit 0) 929848) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_np0 : scripts := SCR [false] [] [].
Definition ss_np0 := SS 0x44004 sr_np0 [] kn_np0 39.
Definition RUN_np0 := sym_exec SEGS 80 true [0x44224; 0x442b0] scr_np0 ss_np0 [].

Definition scr_pnp0p : scripts := SCR [false] [] [].
Definition RES_pnp0p := Eval vm_compute in sym_exec SEGS 80 true [0x44224; 0x442b0] scr_pnp0p ss_np0 [].
Lemma RES_pnp0p_ok : sym_exec SEGS 80 true [0x44224; 0x442b0] scr_pnp0p (SS 0x44004 sr_np0 [] kn_np0 39) [] = RES_pnp0p.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_np0.


Module AXF_np0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section NP0.
Context {fx : FPState}.

Definition VALS_np0 (CA ND cnt sz cp SB st : Z) : list Z := [CA; ND; cnt; sz; cp; SB; st].

Record np0_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND cnt sz cp SB st : Z) : Prop := {
  np0_R10 : getr regs 10 = wa 929816 ;
  np0_R11 : getr regs 11 = wa CA ;
  np0_R12 : getr regs 12 = wa ND ;
  np0_R13 : getr regs 13 = wa 8 ;
  np0_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  np0_rng_CA : 1 <= CA <= 2^47 ;
  np0_rng_ND : 33 <= ND <= 512 ;
  np0_rng_cnt : 0 <= cnt <= 2^32-1 ;
  np0_rng_sz : 0 <= sz <= 2^64-1 ;
  np0_rng_cp : 0 <= cp <= 2^32-1 ;
  np0_rng_SB : 0 <= SB <= 2^64-1 ;
  np0_rng_st : 0 <= st <= 2^64-1 ;
  np0_ka1 : CA mod 16 = 0 ;
  np0_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  np0_kw4 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) 4 = Some (word_to_le_bytes 4 (wa cnt)) ;
  np0_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  np0_kw6 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 8)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  np0_kw7 : rdn SEGS m (wa (CA + ((80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + Z.shiftr ((((4294967296 * ext_Z true 0 4 cnt) + -4294967296)) mod 2^64) 30) + 16)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  np0_kw8 : rdn SEGS m (wa (0 + 929848)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  np0_kw9 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  np0_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true
}.


#[using="Type"] Lemma np0_setup : forall regs m CA ND cnt sz cp SB st, np0_pre regs m CA ND cnt sz cp SB st ->
  regs_ok (Ez regs (VALS_np0 CA ND cnt sz cp SB st)) AXF_np0.sr_np0 regs /\ know_ok SEGS (Ez regs (VALS_np0 CA ND cnt sz cp SB st)) m AXF_np0.kn_np0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND cnt sz cp SB st P. destruct P as [np0_R10 np0_R11 np0_R12 np0_R13 np0_HSTK np0_rng_CA np0_rng_ND np0_rng_cnt np0_rng_sz np0_rng_cp np0_rng_SB np0_rng_st np0_ka1 np0_kr3 np0_kw4 np0_kwr5 np0_kw6 np0_kw7 np0_kw8 np0_kw9 np0_kwr10].
  set (E := Ez regs (VALS_np0 CA ND cnt sz cp SB st)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 cnt + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_np0.sr_np0.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite np0_R10. reflexivity.
    - rewrite np0_R11. reflexivity.
    - rewrite np0_R12. reflexivity.
    - rewrite np0_R13. reflexivity. }
  unfold know_ok, AXF_np0.kn_np0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_np0.e_CA AXF_np0.e_ND AXF_np0.e_cnt AXF_np0.e_sz AXF_np0.e_cp AXF_np0.e_SB AXF_np0.e_st AXF_np0.REC AXF_np0.CHP AXF_np0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ np0_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ np0_rng_ND eq_refl eq_refl), ?(mod64_of_range cnt _ _ np0_rng_cnt eq_refl eq_refl), ?(mod64_of_range cp _ _ np0_rng_cp eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply np0_kwr5 | apply np0_kwr10]; assumption).
  all: try (clear - np0_rng_CA np0_rng_ND np0_rng_cnt np0_rng_sz np0_rng_cp np0_rng_SB np0_rng_st np0_ka1 np0_kr3 HC HP; lia).
  all: first [lia].
Qed.


Definition np0_mem_pnp0p (m : word -> option byte) (regs : bvmap 5 word) (CA ND cnt sz cp SB st : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 cnt + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))).

#[using="Type"] Theorem np0_pnp0p : forall regs m rom CA ND cnt sz cp SB st, np0_pre regs m CA ND cnt sz cp SB st ->
  scs_denot SEGS m (Ez regs (VALS_np0 CA ND cnt sz cp SB st)) (snd (fst AXF_np0.RES_pnp0p)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x44224) (np0_mem_pnp0p m regs CA ND cnt sz cp SB st) rom) /\
    getr R 10 = wa (SB + ((4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5) + (16 * ext_Z false 0 4 cp))) /\ getr R 11 = wa 9 /\ getr R 12 = wa sz /\ getr R 13 = wa 8 /\ getr R 14 = wa (16 * ext_Z false 0 4 cp) /\ getr R 15 = wa 65536 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND cnt sz cp SB st P Hsc. destruct (np0_setup regs m CA ND cnt sz cp SB st P) as [HR HK].
  set (E := Ez regs (VALS_np0 CA ND cnt sz cp SB st)) in *. destruct P as [np0_R10 np0_R11 np0_R12 np0_R13 np0_HSTK np0_rng_CA np0_rng_ND np0_rng_cnt np0_rng_sz np0_rng_cp np0_rng_SB np0_rng_st np0_ka1 np0_kr3 np0_kw4 np0_kwr5 np0_kw6 np0_kw7 np0_kw8 np0_kw9 np0_kwr10].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 cnt + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 cnt + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 80 [0x44224; 0x442b0] AXF_np0.scr_pnp0p 0x44004 AXF_np0.sr_np0 AXF_np0.kn_np0 39 _ _ _ E m rom regs AXF_np0.RES_pnp0p_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_np0.RES_pnp0p fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (np0_mem_pnp0p m regs CA ND cnt sz cp SB st) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold np0_mem_pnp0p. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NP0.
(* [comment removed for export] *)
End AXF_np0z.


Module AXF_np0r.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_cnt := EVar 34.
Definition e_sz := EVar 35.
Definition e_SB := EVar 36.
Definition e_st := EVar 37.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_np0r := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 929816)) 11 (e_CA)) 12 (e_ND)) 13 (ELit 8)).
Definition kn_np0r : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 0) 4 e_cnt;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA (ELit 0) 929848) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_np0r : scripts := SCR [false] [] [].
Definition ss_np0r := SS 0x44004 sr_np0r [] kn_np0r 38.
Definition RUN_np0r := sym_exec SEGS 80 true [0x44224; 0x442b0] scr_np0r ss_np0r [].

Definition scr_pnp0r : scripts := SCR [true] [] [].
Definition RES_pnp0r := Eval vm_compute in sym_exec SEGS 80 true [0x44224; 0x442b0] scr_pnp0r ss_np0r [].
Lemma RES_pnp0r_ok : sym_exec SEGS 80 true [0x44224; 0x442b0] scr_pnp0r (SS 0x44004 sr_np0r [] kn_np0r 38) [] = RES_pnp0r.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_np0r.


Module AXF_np0rz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section NP0R.
Context {fx : FPState}.

Definition VALS_np0r (CA ND cnt sz SB st : Z) : list Z := [CA; ND; cnt; sz; SB; st].

Record np0r_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND cnt sz SB st : Z) : Prop := {
  np0r_R10 : getr regs 10 = wa 929816 ;
  np0r_R11 : getr regs 11 = wa CA ;
  np0r_R12 : getr regs 12 = wa ND ;
  np0r_R13 : getr regs 13 = wa 8 ;
  np0r_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  np0r_rng_CA : 1 <= CA <= 2^47 ;
  np0r_rng_ND : 33 <= ND <= 512 ;
  np0r_rng_cnt : 0 <= cnt <= 2^32-1 ;
  np0r_rng_sz : 0 <= sz <= 2^64-1 ;
  np0r_rng_SB : 0 <= SB <= 2^64-1 ;
  np0r_rng_st : 0 <= st <= 2^64-1 ;
  np0r_ka1 : CA mod 16 = 0 ;
  np0r_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  np0r_kw4 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) 4 = Some (word_to_le_bytes 4 (wa cnt)) ;
  np0r_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  np0r_kw6 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 8)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  np0r_kw7 : rdn SEGS m (wa (0 + 929848)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  np0r_kw8 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  np0r_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true
}.


#[using="Type"] Lemma np0r_setup : forall regs m CA ND cnt sz SB st, np0r_pre regs m CA ND cnt sz SB st ->
  regs_ok (Ez regs (VALS_np0r CA ND cnt sz SB st)) AXF_np0r.sr_np0r regs /\ know_ok SEGS (Ez regs (VALS_np0r CA ND cnt sz SB st)) m AXF_np0r.kn_np0r.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND cnt sz SB st P. destruct P as [np0r_R10 np0r_R11 np0r_R12 np0r_R13 np0r_HSTK np0r_rng_CA np0r_rng_ND np0r_rng_cnt np0r_rng_sz np0r_rng_SB np0r_rng_st np0r_ka1 np0r_kr3 np0r_kw4 np0r_kwr5 np0r_kw6 np0r_kw7 np0r_kw8 np0r_kwr9].
  set (E := Ez regs (VALS_np0r CA ND cnt sz SB st)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_np0r.sr_np0r.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite np0r_R10. reflexivity.
    - rewrite np0r_R11. reflexivity.
    - rewrite np0r_R12. reflexivity.
    - rewrite np0r_R13. reflexivity. }
  unfold know_ok, AXF_np0r.kn_np0r.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_np0r.e_CA AXF_np0r.e_ND AXF_np0r.e_cnt AXF_np0r.e_sz AXF_np0r.e_SB AXF_np0r.e_st AXF_np0r.REC AXF_np0r.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ np0r_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ np0r_rng_ND eq_refl eq_refl), ?(mod64_of_range cnt _ _ np0r_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply np0r_kwr5 | apply np0r_kwr9]; assumption).
  all: try (clear - np0r_rng_CA np0r_rng_ND np0r_rng_cnt np0r_rng_sz np0r_rng_SB np0r_rng_st np0r_ka1 np0r_kr3 HC; lia).
  all: first [lia].
Qed.


Definition np0r_mem_pnp0r (m : word -> option byte) (regs : bvmap 5 word) (CA ND cnt sz SB st : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))).

#[using="Type"] Theorem np0r_pnp0r : forall regs m rom CA ND cnt sz SB st, np0r_pre regs m CA ND cnt sz SB st ->
  scs_denot SEGS m (Ez regs (VALS_np0r CA ND cnt sz SB st)) (snd (fst AXF_np0r.RES_pnp0r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x442b0) (np0r_mem_pnp0r m regs CA ND cnt sz SB st) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48) /\ getr R 8 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 9 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 12 = wa 929816 /\ getr R 13 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 14 = wa (ND + 31) /\ getr R 15 = wa 65536 /\ getr R 18 = wa 8 /\ getr R 19 = wa CA /\ getr R 20 = wa 929816 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND cnt sz SB st P Hsc. destruct (np0r_setup regs m CA ND cnt sz SB st P) as [HR HK].
  set (E := Ez regs (VALS_np0r CA ND cnt sz SB st)) in *. destruct P as [np0r_R10 np0r_R11 np0r_R12 np0r_R13 np0r_HSTK np0r_rng_CA np0r_rng_ND np0r_rng_cnt np0r_rng_sz np0r_rng_SB np0r_rng_st np0r_ka1 np0r_kr3 np0r_kw4 np0r_kwr5 np0r_kw6 np0r_kw7 np0r_kw8 np0r_kwr9].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 80 [0x44224; 0x442b0] AXF_np0r.scr_pnp0r 0x44004 AXF_np0r.sr_np0r AXF_np0r.kn_np0r 38 _ _ _ E m rom regs AXF_np0r.RES_pnp0r_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_np0r.RES_pnp0r fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (np0r_mem_pnp0r m regs CA ND cnt sz SB st) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold np0r_mem_pnp0r. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NP0R.
(* [comment removed for export] *)
End AXF_np0rz.


Module AXF_npr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_mc := EVar 34.
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_npr := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 929816)) 13 (CC)).
Definition kn_npr : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 e_mc;
    KWr STK (ELit 1024) ].
Definition scr_npr : scripts := SCR [false] [] [].
Definition ss_npr := SS 0x442b0 sr_npr [] kn_npr 35.
Definition RUN_npr := sym_exec SEGS 40 true [0x44790] scr_npr ss_npr [].

Definition scr_pnpr : scripts := SCR [false] [] [].
Definition RES_pnpr := Eval vm_compute in sym_exec SEGS 40 true [0x44790] scr_pnpr ss_npr [].
Lemma RES_pnpr_ok : sym_exec SEGS 40 true [0x44790] scr_pnpr (SS 0x442b0 sr_npr [] kn_npr 35) [] = RES_pnpr.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_npr.


Module AXF_nprz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section NPR.
Context {fx : FPState}.

Definition VALS_npr (CA ND mc : Z) : list Z := [CA; ND; mc].

Record npr_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND mc : Z) : Prop := {
  npr_R10 : getr regs 10 = wa CA ;
  npr_R11 : getr regs 11 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) ;
  npr_R12 : getr regs 12 = wa 929816 ;
  npr_R13 : getr regs 13 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) ;
  npr_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  npr_rng_CA : 1 <= CA <= 2^47 ;
  npr_rng_ND : 33 <= ND <= 512 ;
  npr_rng_mc : 2 <= mc <= 16 ;
  npr_ka1 : CA mod 16 = 0 ;
  npr_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  npr_kw4 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 4)) 4 = Some (word_to_le_bytes 4 (wa mc))
}.


#[using="Type"] Lemma npr_setup : forall regs m CA ND mc, npr_pre regs m CA ND mc ->
  regs_ok (Ez regs (VALS_npr CA ND mc)) AXF_npr.sr_npr regs /\ know_ok SEGS (Ez regs (VALS_npr CA ND mc)) m AXF_npr.kn_npr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND mc P. destruct P as [npr_R10 npr_R11 npr_R12 npr_R13 npr_HSTK npr_rng_CA npr_rng_ND npr_rng_mc npr_ka1 npr_kr3 npr_kw4].
  set (E := Ez regs (VALS_npr CA ND mc)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_npr.sr_npr.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite npr_R10. reflexivity.
    - rewrite npr_R11, zeval_sound. cbn [zeval edenot AXF_npr.e_CA AXF_npr.e_ND AXF_npr.e_mc AXF_npr.CC AXF_npr.REC AXF_npr.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite npr_R12. reflexivity.
    - rewrite npr_R13, zeval_sound. cbn [zeval edenot AXF_npr.e_CA AXF_npr.e_ND AXF_npr.e_mc AXF_npr.CC AXF_npr.REC AXF_npr.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_npr.kn_npr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_npr.e_CA AXF_npr.e_ND AXF_npr.e_mc AXF_npr.CC AXF_npr.REC AXF_npr.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ npr_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ npr_rng_ND eq_refl eq_refl), ?(mod64_of_range mc _ _ npr_rng_mc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - npr_rng_CA npr_rng_ND npr_rng_mc npr_ka1 npr_kr3 HC; lia).
  all: first [lia].
Qed.


Definition npr_mem_pnpr (m : word -> option byte) (regs : bvmap 5 word) (CA ND mc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 279220))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))).

#[using="Type"] Theorem npr_pnpr : forall regs m rom CA ND mc, npr_pre regs m CA ND mc ->
  scs_denot SEGS m (Ez regs (VALS_npr CA ND mc)) (snd (fst AXF_npr.RES_pnpr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x442b0) m rom) (mkst R (wa 0x44790) (npr_mem_pnpr m regs CA ND mc) rom) /\
    getr R 1 = wa 279220 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 8 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 9 = wa (bv_unsigned (edenot (Ez regs (VALS_npr CA ND mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ getr R 10 = wa 929816 /\ getr R 11 = wa (CA + 2560) /\ getr R 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) /\ getr R 14 = wa (bv_unsigned (edenot (Ez regs (VALS_npr CA ND mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ (forall k, In k [3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND mc P Hsc. destruct (npr_setup regs m CA ND mc P) as [HR HK].
  set (E := Ez regs (VALS_npr CA ND mc)) in *. destruct P as [npr_R10 npr_R11 npr_R12 npr_R13 npr_HSTK npr_rng_CA npr_rng_ND npr_rng_mc npr_ka1 npr_kr3 npr_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 40 [0x44790] AXF_npr.scr_pnpr 0x442b0 AXF_npr.sr_npr AXF_npr.kn_npr 35 _ _ _ E m rom regs AXF_npr.RES_pnpr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_npr.RES_pnpr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (npr_mem_pnpr m regs CA ND mc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold npr_mem_pnpr. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NPR.
(* [comment removed for export] *)
End AXF_nprz.


Module AXF_ng0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition e_nf := EVar 37.
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition RI := EAlu ALU_ADD e_RIB (EMd M_MUL (ELit 128) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_ng0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 929816)) 11 (EAlu ALU_ADD e_CA (ELit 2560))) 12 (CC)) 13 (EAlu ALU_ADD REC (ELit 16))) 14 (e_n)).
Definition kn_ng0 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KWord (SA (ELit 0) 929848) 8 e_SB;
    KWord (SA (ELit 0) 929864) 8 e_RIB;
    KWord (SA RI 0) 8 (ELit 0);
    KWr (SA RI 0) (ELit 8);
    KWord (SA RI 16) 8 e_nf;
    KWr (SA RI 16) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_ng0 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition ss_ng0 := SS 0x44790 sr_ng0 [] kn_ng0 38.
Definition RUN_ng0 := sym_exec SEGS 60 true [0x449c8; 0x449dc] scr_ng0 ss_ng0 [].

Definition scr_png0 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition RES_png0 := Eval vm_compute in sym_exec SEGS 60 true [0x449c8; 0x449dc] scr_png0 ss_ng0 [].
Lemma RES_png0_ok : sym_exec SEGS 60 true [0x449c8; 0x449dc] scr_png0 (SS 0x44790 sr_ng0 [] kn_ng0 38) [] = RES_png0.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_ng0.


Module AXF_ng0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section NG0.
Context {fx : FPState}.

Definition VALS_ng0 (CA ND n SB RIB nf : Z) : list Z := [CA; ND; n; SB; RIB; nf].

Record ng0_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND n SB RIB nf : Z) : Prop := {
  ng0_R10 : getr regs 10 = wa 929816 ;
  ng0_R11 : getr regs 11 = wa (CA + 2560) ;
  ng0_R12 : getr regs 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) ;
  ng0_R13 : getr regs 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) ;
  ng0_R14 : getr regs 14 = wa n ;
  ng0_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  ng0_rng_CA : 1 <= CA <= 2^47 ;
  ng0_rng_ND : 33 <= ND <= 512 ;
  ng0_rng_n : 1 <= n <= 8 ;
  ng0_rng_SB : 0 <= SB <= 2^64-1 ;
  ng0_rng_RIB : 1 <= RIB <= 2^47 ;
  ng0_rng_nf : 0 <= nf <= 2^64-1 ;
  ng0_ka1 : CA mod 16 = 0 ;
  ng0_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  ng0_ka5 : RIB mod 128 = 0 ;
  ng0_kw6 : rdn SEGS m (wa (0 + 929848)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  ng0_kw7 : rdn SEGS m (wa (0 + 929864)) 8 = Some (word_to_le_bytes 8 (wa RIB)) ;
  ng0_kw8 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ng0_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  ng0_kw10 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 16)) 8 = Some (word_to_le_bytes 8 (wa nf)) ;
  ng0_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 16 + d)) k = true
}.


#[using="Type"] Lemma ng0_setup : forall regs m CA ND n SB RIB nf, ng0_pre regs m CA ND n SB RIB nf ->
  regs_ok (Ez regs (VALS_ng0 CA ND n SB RIB nf)) AXF_ng0.sr_ng0 regs /\ know_ok SEGS (Ez regs (VALS_ng0 CA ND n SB RIB nf)) m AXF_ng0.kn_ng0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND n SB RIB nf P. destruct P as [ng0_R10 ng0_R11 ng0_R12 ng0_R13 ng0_R14 ng0_HSTK ng0_rng_CA ng0_rng_ND ng0_rng_n ng0_rng_SB ng0_rng_RIB ng0_rng_nf ng0_ka1 ng0_kr3 ng0_ka5 ng0_kw6 ng0_kw7 ng0_kw8 ng0_kwr9 ng0_kw10 ng0_kwr11].
  set (E := Ez regs (VALS_ng0 CA ND n SB RIB nf)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_ng0.sr_ng0.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite ng0_R10. reflexivity.
    - rewrite ng0_R11, zeval_sound. cbn [zeval edenot AXF_ng0.e_CA AXF_ng0.e_ND AXF_ng0.e_n AXF_ng0.e_SB AXF_ng0.e_RIB AXF_ng0.e_nf AXF_ng0.CC AXF_ng0.REC AXF_ng0.RI AXF_ng0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ng0_R12, zeval_sound. cbn [zeval edenot AXF_ng0.e_CA AXF_ng0.e_ND AXF_ng0.e_n AXF_ng0.e_SB AXF_ng0.e_RIB AXF_ng0.e_nf AXF_ng0.CC AXF_ng0.REC AXF_ng0.RI AXF_ng0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ng0_R13, zeval_sound. cbn [zeval edenot AXF_ng0.e_CA AXF_ng0.e_ND AXF_ng0.e_n AXF_ng0.e_SB AXF_ng0.e_RIB AXF_ng0.e_nf AXF_ng0.CC AXF_ng0.REC AXF_ng0.RI AXF_ng0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ng0_R14. reflexivity. }
  unfold know_ok, AXF_ng0.kn_ng0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ng0.e_CA AXF_ng0.e_ND AXF_ng0.e_n AXF_ng0.e_SB AXF_ng0.e_RIB AXF_ng0.e_nf AXF_ng0.CC AXF_ng0.REC AXF_ng0.RI AXF_ng0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ ng0_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ ng0_rng_ND eq_refl eq_refl), ?(mod64_of_range n _ _ ng0_rng_n eq_refl eq_refl), ?(mod64_of_range RIB _ _ ng0_rng_RIB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ng0_kwr9 | apply ng0_kwr11]; assumption).
  all: try (clear - ng0_rng_CA ng0_rng_ND ng0_rng_n ng0_rng_SB ng0_rng_RIB ng0_rng_nf ng0_ka1 ng0_kr3 ng0_ka5 HC; lia).
  all: first [lia].
Qed.


Definition ng0_mem_png0 (m : word -> option byte) (regs : bvmap 5 word) (CA ND n SB RIB nf : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 280468))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 8 (wa 1152921504606846976))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 16)) (word_to_le_bytes 8 (wa ((-1 * n) + nf))).

#[using="Type"] Theorem ng0_png0 : forall regs m rom CA ND n SB RIB nf, ng0_pre regs m CA ND n SB RIB nf ->
  scs_denot SEGS m (Ez regs (VALS_ng0 CA ND n SB RIB nf)) (snd (fst AXF_ng0.RES_png0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44790) m rom) (mkst R (wa 0x449c8) (ng0_mem_png0 m regs CA ND n SB RIB nf) rom) /\
    getr R 1 = wa 280468 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128) /\ getr R 5 = wa 0 /\ getr R 6 = wa 1152921504606846976 /\ getr R 7 = wa 0 /\ getr R 8 = wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 9 = wa 929816 /\ getr R 10 = wa ((RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 8) /\ getr R 11 = wa ((CA + ((4 * n) + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5))) + 16) /\ getr R 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) /\ getr R 14 = wa n /\ getr R 15 = wa ((-4 * n) + (4 * nf)) /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 19 = wa 2305843009213693952 /\ getr R 20 = wa (((-4 * n) + (SB + ((4 * nf) + (4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5)))) + 3758096384) /\ getr R 21 = wa 1099511627776 /\ getr R 22 = wa 1152921504607895551 /\ getr R 23 = wa 1152921504606846976 /\ getr R 24 = wa 1500 /\ getr R 25 = wa 16140901064495857663 /\ (forall k, In k [3; 4; 18; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND n SB RIB nf P Hsc. destruct (ng0_setup regs m CA ND n SB RIB nf P) as [HR HK].
  set (E := Ez regs (VALS_ng0 CA ND n SB RIB nf)) in *. destruct P as [ng0_R10 ng0_R11 ng0_R12 ng0_R13 ng0_R14 ng0_HSTK ng0_rng_CA ng0_rng_ND ng0_rng_n ng0_rng_SB ng0_rng_RIB ng0_rng_nf ng0_ka1 ng0_kr3 ng0_ka5 ng0_kw6 ng0_kw7 ng0_kw8 ng0_kwr9 ng0_kw10 ng0_kwr11].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 60 [0x449c8; 0x449dc] AXF_ng0.scr_png0 0x44790 AXF_ng0.sr_ng0 AXF_ng0.kn_ng0 38 _ _ _ E m rom regs AXF_ng0.RES_png0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ng0.RES_png0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ng0_mem_png0 m regs CA ND n SB RIB nf) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ng0_mem_png0. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NG0.
(* [comment removed for export] *)
End AXF_ng0z.


Module AXF_ngl.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

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
Definition ss_ngl := SS 0x449c8 sr_ngl [] kn_ngl 36.
Definition RUN_ngl := sym_exec SEGS 10 true [0x449c8; 0x449dc] scr_ngl ss_ngl [].

Definition scr_pnglc : scripts := SCR [true] [] [].
Definition RES_pnglc := Eval vm_compute in sym_exec SEGS 10 true [0x449c8; 0x449dc] scr_pnglc ss_ngl [].
Lemma RES_pnglc_ok : sym_exec SEGS 10 true [0x449c8; 0x449dc] scr_pnglc (SS 0x449c8 sr_ngl [] kn_ngl 36) [] = RES_pnglc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnglx : scripts := SCR [false] [] [].
Definition RES_pnglx := Eval vm_compute in sym_exec SEGS 10 true [0x449c8; 0x449dc] scr_pnglx ss_ngl [].
Lemma RES_pnglx_ok : sym_exec SEGS 10 true [0x449c8; 0x449dc] scr_pnglx (SS 0x449c8 sr_ngl [] kn_ngl 36) [] = RES_pnglx.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_ngl.


Module AXF_nglz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x449c8) m rom) (mkst R (wa 0x449c8) (ngl_mem_pnglc m regs FP CP EN w) rom) /\
    getr R 11 = wa EN /\ getr R 12 = wa (ext_Z true 0 4 w) /\ getr R 13 = wa (CP + 4) /\ getr R 20 = wa (FP + 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom FP CP EN w P Hsc. destruct (ngl_setup regs m FP CP EN w P) as [HR HK].
  set (E := Ez regs (VALS_ngl FP CP EN w)) in *. destruct P as [ngl_R11 ngl_R13 ngl_R20 ngl_rng_FP ngl_rng_CP ngl_rng_EN ngl_rng_w ngl_kw3 ngl_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = FP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x449c8; 0x449dc] AXF_ngl.scr_pnglc 0x449c8 AXF_ngl.sr_ngl AXF_ngl.kn_ngl 36 _ _ _ E m rom regs AXF_ngl.RES_pnglc_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  exists R, msteps SEGS (mkst regs (wa 0x449c8) m rom) (mkst R (wa 0x449dc) (ngl_mem_pnglx m regs FP CP EN w) rom) /\
    getr R 11 = wa EN /\ getr R 12 = wa (ext_Z true 0 4 w) /\ getr R 13 = wa (CP + 4) /\ getr R 20 = wa (FP + 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom FP CP EN w P Hsc. destruct (ngl_setup regs m FP CP EN w P) as [HR HK].
  set (E := Ez regs (VALS_ngl FP CP EN w)) in *. destruct P as [ngl_R11 ngl_R13 ngl_R20 ngl_rng_FP ngl_rng_CP ngl_rng_EN ngl_rng_w ngl_kw3 ngl_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = FP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = CP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x449c8; 0x449dc] AXF_ngl.scr_pnglx 0x449c8 AXF_ngl.sr_ngl AXF_ngl.kn_ngl 36 _ _ _ E m rom regs AXF_ngl.RES_pnglx_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
End AXF_nglz.


Module AXF_ngt.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition e_na := EVar 37.
Definition e_cp := EVar 38.
Definition e_sz := EVar 39.
Definition e_st := EVar 40.
Definition e_g1 := EVar 41.
Definition e_g2 := EVar 42.
Definition e_g3 := EVar 43.
Definition e_g4 := EVar 44.
Definition e_g5 := EVar 45.
Definition e_g6 := EVar 46.
Definition e_g7 := EVar 47.
Definition e_g8 := EVar 48.
Definition e_g9 := EVar 49.
Definition e_g10 := EVar 50.
Definition e_g11 := EVar 51.
Definition e_c1 := EVar 52.
Definition e_c2 := EVar 53.
Definition e_c3 := EVar 54.
Definition e_c4 := EVar 55.
Definition e_c5 := EVar 56.
Definition e_cra := EVar 57.
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition RI := EAlu ALU_ADD e_RIB (EMd M_MUL (ELit 128) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_ngt := (sr_upd (sr_upd (sr_upd sr_id 8 (RI)) 14 (e_n)) 19 (ELit 2305843009213693952)).
Definition kn_ngt : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KWord (SA RI 72) 8 e_na;
    KWr (SA RI 72) (ELit 8);
    KWord (SA RI 0) 8 (ELit 1152921504606846976);
    KWr (SA RI 0) (ELit 8);
    KWord (SA (EVar 2) 120) 8 (ELit 280468);
    KWord (SA (EVar 2) 112) 8 REC;
    KWord (SA (EVar 2) 104) 8 e_n;
    KWord (SA (EVar 2) 96) 8 (ELit 8);
    KWord (SA (EVar 2) 88) 8 e_CA;
    KWord (SA (EVar 2) 80) 8 (ELit 929816);
    KWord (SA (EVar 2) 72) 8 e_g5;
    KWord (SA (EVar 2) 64) 8 e_g6;
    KWord (SA (EVar 2) 56) 8 e_g7;
    KWord (SA (EVar 2) 48) 8 e_g8;
    KWord (SA (EVar 2) 40) 8 e_g9;
    KWord (SA (EVar 2) 32) 8 e_g10;
    KWord (SA (EVar 2) 24) 8 e_g11;
    KWord (SA (EVar 2) 136) 8 REC;
    KWord (SA (EVar 2) 144) 8 CC;
    KWord (SA (EVar 2) 152) 8 (ELit 279220);
    KWord (SA (EVar 2) 160) 8 e_c4;
    KWord (SA (EVar 2) 168) 8 e_c3;
    KWord (SA (EVar 2) 176) 8 e_c2;
    KWord (SA (EVar 2) 184) 8 e_c1;
    KWord (SA (EVar 2) 192) 8 e_c5;
    KWord (SA (EVar 2) 200) 8 e_cra;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA (EAlu ALU_ADD e_CA (EAlu ALU_ADD (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))) (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_n)) (ELit (-4294967296))) (ELit 30)))) 16) 4 e_cp;
    KWord (SA (ELit 0) 929848) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KImg 65536 143360;
    KWr STK (ELit 1024) ].
Definition scr_ngt : scripts := SCR [false; false; false; false; false; false; false; false] [] [].
Definition ss_ngt := SS 0x449dc sr_ngt [] kn_ngt 58.
Definition RUN_ngt := sym_exec SEGS 120 true [0x44224] scr_ngt ss_ngt [].

Definition scr_pngt : scripts := SCR [false; false; false; false; false; false; false; false] [] [].
Definition RES_pngt := Eval vm_compute in sym_exec SEGS 120 true [0x44224] scr_pngt ss_ngt [].
Lemma RES_pngt_ok : sym_exec SEGS 120 true [0x44224] scr_pngt (SS 0x449dc sr_ngt [] kn_ngt 58) [] = RES_pngt.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_ngt.


Module AXF_ngtz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section NGT.
Context {fx : FPState}.

Definition VALS_ngt (CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra : Z) : list Z := [CA; ND; n; SB; RIB; na; cp; sz; st; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; c1; c2; c3; c4; c5; cra].

Record ngt_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra : Z) : Prop := {
  ngt_R8 : getr regs 8 = wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) ;
  ngt_R14 : getr regs 14 = wa n ;
  ngt_R19 : getr regs 19 = wa 2305843009213693952 ;
  ngt_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  ngt_rng_CA : 1 <= CA <= 2^47 ;
  ngt_rng_ND : 33 <= ND <= 512 ;
  ngt_rng_n : 1 <= n <= 8 ;
  ngt_rng_SB : 0 <= SB <= 2^64-1 ;
  ngt_rng_RIB : 1 <= RIB <= 2^47 ;
  ngt_rng_na : 0 <= na <= 2^64-1 ;
  ngt_rng_cp : 0 <= cp <= 2^32-1 ;
  ngt_rng_sz : 0 <= sz <= 2^64-1 ;
  ngt_rng_st : 0 <= st <= 2^64-1 ;
  ngt_rng_g1 : 0 <= g1 <= 2^64-1 ;
  ngt_rng_g2 : 0 <= g2 <= 2^64-1 ;
  ngt_rng_g3 : 0 <= g3 <= 2^64-1 ;
  ngt_rng_g4 : 0 <= g4 <= 2^64-1 ;
  ngt_rng_g5 : 0 <= g5 <= 2^64-1 ;
  ngt_rng_g6 : 0 <= g6 <= 2^64-1 ;
  ngt_rng_g7 : 0 <= g7 <= 2^64-1 ;
  ngt_rng_g8 : 0 <= g8 <= 2^64-1 ;
  ngt_rng_g9 : 0 <= g9 <= 2^64-1 ;
  ngt_rng_g10 : 0 <= g10 <= 2^64-1 ;
  ngt_rng_g11 : 0 <= g11 <= 2^64-1 ;
  ngt_rng_c1 : 0 <= c1 <= 2^64-1 ;
  ngt_rng_c2 : 0 <= c2 <= 2^64-1 ;
  ngt_rng_c3 : 0 <= c3 <= 2^64-1 ;
  ngt_rng_c4 : 0 <= c4 <= 2^64-1 ;
  ngt_rng_c5 : 0 <= c5 <= 2^64-1 ;
  ngt_rng_cra : 0 <= cra <= 2^64-1 ;
  ngt_ka1 : CA mod 16 = 0 ;
  ngt_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  ngt_ka5 : RIB mod 128 = 0 ;
  ngt_kw6 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 72)) 8 = Some (word_to_le_bytes 8 (wa na)) ;
  ngt_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 72 + d)) k = true ;
  ngt_kw8 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) 8 = Some (word_to_le_bytes 8 (wa 1152921504606846976)) ;
  ngt_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  ngt_kw10 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 120)) 8 = Some (word_to_le_bytes 8 (wa 280468)) ;
  ngt_kw11 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 112)) 8 = Some (word_to_le_bytes 8 (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)))) ;
  ngt_kw12 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 104)) 8 = Some (word_to_le_bytes 8 (wa n)) ;
  ngt_kw13 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 96)) 8 = Some (word_to_le_bytes 8 (wa 8)) ;
  ngt_kw14 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa CA)) ;
  ngt_kw15 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa 929816)) ;
  ngt_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa g5)) ;
  ngt_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64)) 8 = Some (word_to_le_bytes 8 (wa g6)) ;
  ngt_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa g7)) ;
  ngt_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa g8)) ;
  ngt_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa g9)) ;
  ngt_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa g10)) ;
  ngt_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa g11)) ;
  ngt_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 136)) 8 = Some (word_to_le_bytes 8 (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)))) ;
  ngt_kw24 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 144)) 8 = Some (word_to_le_bytes 8 (wa (Z.shiftr (((ND + 31)) mod 2^64) 5))) ;
  ngt_kw25 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 152)) 8 = Some (word_to_le_bytes 8 (wa 279220)) ;
  ngt_kw26 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 160)) 8 = Some (word_to_le_bytes 8 (wa c4)) ;
  ngt_kw27 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 168)) 8 = Some (word_to_le_bytes 8 (wa c3)) ;
  ngt_kw28 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 176)) 8 = Some (word_to_le_bytes 8 (wa c2)) ;
  ngt_kw29 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 184)) 8 = Some (word_to_le_bytes 8 (wa c1)) ;
  ngt_kw30 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 192)) 8 = Some (word_to_le_bytes 8 (wa c5)) ;
  ngt_kw31 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 200)) 8 = Some (word_to_le_bytes 8 (wa cra)) ;
  ngt_kwr32 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  ngt_kw33 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 8)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  ngt_kw34 : rdn SEGS m (wa (CA + ((80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + Z.shiftr ((((4294967296 * ext_Z true 0 4 n) + -4294967296)) mod 2^64) 30) + 16)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  ngt_kw35 : rdn SEGS m (wa (0 + 929848)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  ngt_kw36 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  ngt_kwr37 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true ;
  ngt_kimg38 : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None
}.


#[using="Type"] Lemma ngt_setup : forall regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, ngt_pre regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra ->
  regs_ok (Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) AXF_ngt.sr_ngt regs /\ know_ok SEGS (Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) m AXF_ngt.kn_ngt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra P. destruct P as [ngt_R8 ngt_R14 ngt_R19 ngt_HSTK ngt_rng_CA ngt_rng_ND ngt_rng_n ngt_rng_SB ngt_rng_RIB ngt_rng_na ngt_rng_cp ngt_rng_sz ngt_rng_st ngt_rng_g1 ngt_rng_g2 ngt_rng_g3 ngt_rng_g4 ngt_rng_g5 ngt_rng_g6 ngt_rng_g7 ngt_rng_g8 ngt_rng_g9 ngt_rng_g10 ngt_rng_g11 ngt_rng_c1 ngt_rng_c2 ngt_rng_c3 ngt_rng_c4 ngt_rng_c5 ngt_rng_cra ngt_ka1 ngt_kr3 ngt_ka5 ngt_kw6 ngt_kwr7 ngt_kw8 ngt_kwr9 ngt_kw10 ngt_kw11 ngt_kw12 ngt_kw13 ngt_kw14 ngt_kw15 ngt_kw16 ngt_kw17 ngt_kw18 ngt_kw19 ngt_kw20 ngt_kw21 ngt_kw22 ngt_kw23 ngt_kw24 ngt_kw25 ngt_kw26 ngt_kw27 ngt_kw28 ngt_kw29 ngt_kw30 ngt_kw31 ngt_kwr32 ngt_kw33 ngt_kw34 ngt_kw35 ngt_kw36 ngt_kwr37 ngt_kimg38].
  set (E := Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = na) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = g1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = g2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = g3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = g4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = g5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = g6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = g7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = g8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = g9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = g10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = g11) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = c1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z53 : bv_unsigned (ev E 53) = c2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z54 : bv_unsigned (ev E 54) = c3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z55 : bv_unsigned (ev E 55) = c4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z56 : bv_unsigned (ev E 56) = c5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z57 : bv_unsigned (ev E 57) = cra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 n + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 n + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_ngt.sr_ngt.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite ngt_R8, zeval_sound. cbn [zeval edenot AXF_ngt.e_CA AXF_ngt.e_ND AXF_ngt.e_n AXF_ngt.e_SB AXF_ngt.e_RIB AXF_ngt.e_na AXF_ngt.e_cp AXF_ngt.e_sz AXF_ngt.e_st AXF_ngt.e_g1 AXF_ngt.e_g2 AXF_ngt.e_g3 AXF_ngt.e_g4 AXF_ngt.e_g5 AXF_ngt.e_g6 AXF_ngt.e_g7 AXF_ngt.e_g8 AXF_ngt.e_g9 AXF_ngt.e_g10 AXF_ngt.e_g11 AXF_ngt.e_c1 AXF_ngt.e_c2 AXF_ngt.e_c3 AXF_ngt.e_c4 AXF_ngt.e_c5 AXF_ngt.e_cra AXF_ngt.CC AXF_ngt.REC AXF_ngt.RI AXF_ngt.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z56, ?Z57, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ngt_R14. reflexivity.
    - rewrite ngt_R19. reflexivity. }
  unfold know_ok, AXF_ngt.kn_ngt.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ngt.e_CA AXF_ngt.e_ND AXF_ngt.e_n AXF_ngt.e_SB AXF_ngt.e_RIB AXF_ngt.e_na AXF_ngt.e_cp AXF_ngt.e_sz AXF_ngt.e_st AXF_ngt.e_g1 AXF_ngt.e_g2 AXF_ngt.e_g3 AXF_ngt.e_g4 AXF_ngt.e_g5 AXF_ngt.e_g6 AXF_ngt.e_g7 AXF_ngt.e_g8 AXF_ngt.e_g9 AXF_ngt.e_g10 AXF_ngt.e_g11 AXF_ngt.e_c1 AXF_ngt.e_c2 AXF_ngt.e_c3 AXF_ngt.e_c4 AXF_ngt.e_c5 AXF_ngt.e_cra AXF_ngt.CC AXF_ngt.REC AXF_ngt.RI AXF_ngt.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z56, ?Z57, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ ngt_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ ngt_rng_ND eq_refl eq_refl), ?(mod64_of_range n _ _ ngt_rng_n eq_refl eq_refl), ?(mod64_of_range RIB _ _ ngt_rng_RIB eq_refl eq_refl), ?(mod64_of_range cp _ _ ngt_rng_cp eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ngt_kwr7 | apply ngt_kwr9 | apply ngt_kwr32 | apply ngt_kwr37]; assumption).
  all: try (clear - ngt_rng_CA ngt_rng_ND ngt_rng_n ngt_rng_SB ngt_rng_RIB ngt_rng_na ngt_rng_cp ngt_rng_sz ngt_rng_st ngt_rng_g1 ngt_rng_g2 ngt_rng_g3 ngt_rng_g4 ngt_rng_g5 ngt_rng_g6 ngt_rng_g7 ngt_rng_g8 ngt_rng_g9 ngt_rng_g10 ngt_rng_g11 ngt_rng_c1 ngt_rng_c2 ngt_rng_c3 ngt_rng_c4 ngt_rng_c5 ngt_rng_cra ngt_ka1 ngt_kr3 ngt_ka5 HC HP; lia).
  all: first [lia].
Qed.


Definition ngt_mem_pngt (m : word -> option byte) (regs : bvmap 5 word) (CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 72)) (word_to_le_bytes 8 (wa (n + na)))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 8 (wa 0))) (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 4 (wa n))) (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 n + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))).

#[using="Type"] Theorem ngt_pngt : forall regs m rom CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, ngt_pre regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra ->
  scs_denot SEGS m (Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst AXF_ngt.RES_pngt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x449dc) m rom) (mkst R (wa 0x44224) (ngt_mem_pngt m regs CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra) rom) /\
    getr R 1 = wa cra /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 208) /\ getr R 5 = wa 4611686018427387904 /\ getr R 6 = wa 0 /\ getr R 7 = wa 1152921504606846976 /\ getr R 8 = wa c5 /\ getr R 9 = wa c1 /\ getr R 10 = wa (SB + ((4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5) + (16 * ext_Z false 0 4 cp))) /\ getr R 11 = wa 9 /\ getr R 12 = wa sz /\ getr R 13 = wa 8 /\ getr R 14 = wa (16 * ext_Z false 0 4 cp) /\ getr R 15 = wa 17293822569102704639 /\ getr R 16 = wa 1152920405095219200 /\ getr R 17 = wa 18446742974197923840 /\ getr R 18 = wa c2 /\ getr R 19 = wa c3 /\ getr R 20 = wa c4 /\ getr R 21 = wa g5 /\ getr R 22 = wa g6 /\ getr R 23 = wa g7 /\ getr R 24 = wa g8 /\ getr R 25 = wa g9 /\ getr R 26 = wa g10 /\ getr R 27 = wa g11 /\ getr R 28 = wa 0 /\ (forall k, In k [3; 4; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra P Hsc. destruct (ngt_setup regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra P) as [HR HK].
  set (E := Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) in *. destruct P as [ngt_R8 ngt_R14 ngt_R19 ngt_HSTK ngt_rng_CA ngt_rng_ND ngt_rng_n ngt_rng_SB ngt_rng_RIB ngt_rng_na ngt_rng_cp ngt_rng_sz ngt_rng_st ngt_rng_g1 ngt_rng_g2 ngt_rng_g3 ngt_rng_g4 ngt_rng_g5 ngt_rng_g6 ngt_rng_g7 ngt_rng_g8 ngt_rng_g9 ngt_rng_g10 ngt_rng_g11 ngt_rng_c1 ngt_rng_c2 ngt_rng_c3 ngt_rng_c4 ngt_rng_c5 ngt_rng_cra ngt_ka1 ngt_kr3 ngt_ka5 ngt_kw6 ngt_kwr7 ngt_kw8 ngt_kwr9 ngt_kw10 ngt_kw11 ngt_kw12 ngt_kw13 ngt_kw14 ngt_kw15 ngt_kw16 ngt_kw17 ngt_kw18 ngt_kw19 ngt_kw20 ngt_kw21 ngt_kw22 ngt_kw23 ngt_kw24 ngt_kw25 ngt_kw26 ngt_kw27 ngt_kw28 ngt_kw29 ngt_kw30 ngt_kw31 ngt_kwr32 ngt_kw33 ngt_kw34 ngt_kw35 ngt_kw36 ngt_kwr37 ngt_kimg38].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = na) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = g1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = g2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = g3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = g4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = g5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = g6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = g7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = g8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = g9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = g10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = g11) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = c1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z53 : bv_unsigned (ev E 53) = c2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z54 : bv_unsigned (ev E 54) = c3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z55 : bv_unsigned (ev E 55) = c4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z56 : bv_unsigned (ev E 56) = c5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z57 : bv_unsigned (ev E 57) = cra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 n + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 n + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 120 [0x44224] AXF_ngt.scr_pngt 0x449dc AXF_ngt.sr_ngt AXF_ngt.kn_ngt 58 _ _ _ E m rom regs AXF_ngt.RES_pngt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ngt.RES_pngt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ngt_mem_pngt m regs CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ngt_mem_pngt. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NGT.
(* [comment removed for export] *)
End AXF_ngtz.

Import ListNotations AX2 AX2S.
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

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

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
  ic_SB : rd m 929848 8 SB ;
  ic_RIB : rd m 929864 8 (SB + 137438953472) ;
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
  scs_denot SEGS m (Ez R (AXF_np0z.VALS_np0 CA ND cnt sz cp SB st)) (snd (fst AXF_np0.RES_pnp0p)).
Proof. LiaFast.lf_pins (fun (SPa RIB HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros cnt sz cp st Hc. cbn [AXF_np0.RES_pnp0p fst snd]. unfold AXF_np0z.VALS_np0. scgo; scd [CA; ND; cnt; sz; cp; SB; st] cnt. Qed.
(* [comment removed for export] *)
#[using="SPa RIB HSPa HND HCA HRI"] Lemma sc_np0r : forall sz st,
  scs_denot SEGS m (Ez R (AXF_np0rz.VALS_np0r CA ND 0 sz SB st)) (snd (fst AXF_np0r.RES_pnp0r)).
Proof. LiaFast.lf_pins (fun (SPa RIB HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros sz st. cbn [AXF_np0r.RES_pnp0r fst snd]. unfold AXF_np0rz.VALS_np0r. scgo; scd [CA; ND; 0; sz; SB; st] 1. Qed.
(* [comment removed for export] *)
#[using="SPa RIB HSPa HND HCA HRI"] Lemma sc_npr : forall mc, 2 <= mc <= 16 ->
  scs_denot SEGS m (Ez R (AXF_nprz.VALS_npr CA ND mc)) (snd (fst AXF_npr.RES_pnpr)).
Proof. LiaFast.lf_pins (fun (SPa RIB HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros mc Hmc. cbn [AXF_npr.RES_pnpr fst snd]. unfold AXF_nprz.VALS_npr. scgo; scd [CA; ND; mc] 1. Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI"] Lemma sc_ng0 : forall n nf, 1 <= n <= 8 -> n <= nf < 2^64 ->
  scs_denot SEGS m (Ez R (AXF_ng0z.VALS_ng0 CA ND n SB RIB nf)) (snd (fst AXF_ng0.RES_png0)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI : LiaFast.U) => LiaFast.u0). intros n nf Hn Hnf. cbn [AXF_ng0.RES_png0 fst snd]. unfold AXF_ng0z.VALS_ng0. scgo; scd [CA; ND; n; SB; RIB; nf] n. Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI HSEP"] Lemma sc_ngt : forall n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, 1 <= n <= 8 ->
  scs_denot SEGS m (Ez R (AXF_ngtz.VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst AXF_ngt.RES_pngt)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI HSEP : LiaFast.U) => LiaFast.u0).
  intros n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra Hn. cbn [AXF_ngt.RES_pngt fst snd]. unfold AXF_ngtz.VALS_ngt.
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
(* [comment removed for export] *)
