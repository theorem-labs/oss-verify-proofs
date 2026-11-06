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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Module AXF_np0.
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
Definition e_ND := EVar 33.
Definition e_cnt := EVar 34.
Definition e_sz := EVar 35.
Definition e_cp := EVar 36.
Definition e_SB := EVar 37.
Definition e_st := EVar 38.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition CHP := EAlu ALU_ADD e_CA (EAlu ALU_ADD (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))) (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_cnt)) (ELit (-4294967296))) (ELit 30))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_np0 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (e_CA)) 12 (e_ND)) 13 (ELit 8)).
Definition kn_np0 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 0) 4 e_cnt;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA CHP 16) 4 e_cp;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_np0 : scripts := SCR [false] [] [].
Definition ss_np0 := SS 0x43ce8 sr_np0 [] kn_np0 39.
Definition RUN_np0 := sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_np0 ss_np0 [].

Definition scr_pnp0p : scripts := SCR [false] [] [].
Definition RES_pnp0p := Eval vm_compute in sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0p ss_np0 [].
Lemma RES_pnp0p_ok : sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0p (SS 0x43ce8 sr_np0 [] kn_np0 39) [] = RES_pnp0p.
Proof. vm_compute. reflexivity. Qed.
End AXF_np0.


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section NP0.
Context {fx : FPState}.

Definition VALS_np0 (CA ND cnt sz cp SB st : Z) : list Z := [CA; ND; cnt; sz; cp; SB; st].

Record np0_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND cnt sz cp SB st : Z) : Prop := {
  np0_R10 : getr regs 10 = wa 923480 ;
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
  np0_kw8 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
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
  exists R, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R (wa 0x43f08) (np0_mem_pnp0p m regs CA ND cnt sz cp SB st) rom) /\
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
  destruct (run_sound SEGS 80 [0x43f08; 0x43f94] AXF_np0.scr_pnp0p 0x43ce8 AXF_np0.sr_np0 AXF_np0.kn_np0 39 _ _ _ E m rom regs AXF_np0.RES_pnp0p_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
