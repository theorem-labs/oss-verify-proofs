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

Module AXF_np0r.
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
Definition e_SB := EVar 36.
Definition e_st := EVar 37.
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_np0r := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (e_CA)) 12 (e_ND)) 13 (ELit 8)).
Definition kn_np0r : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 0) 4 e_cnt;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_np0r : scripts := SCR [false] [] [].
Definition ss_np0r := SS 0x43ce8 sr_np0r [] kn_np0r 38.
Definition RUN_np0r := sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_np0r ss_np0r [].

Definition scr_pnp0r : scripts := SCR [true] [] [].
Definition RES_pnp0r := Eval vm_compute in sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0r ss_np0r [].
Lemma RES_pnp0r_ok : sym_exec SEGS 80 true [0x43f08; 0x43f94] scr_pnp0r (SS 0x43ce8 sr_np0r [] kn_np0r 38) [] = RES_pnp0r.
Proof. vm_compute. reflexivity. Qed.
End AXF_np0r.


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section NP0R.
Context {fx : FPState}.

Definition VALS_np0r (CA ND cnt sz SB st : Z) : list Z := [CA; ND; cnt; sz; SB; st].

Record np0r_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND cnt sz SB st : Z) : Prop := {
  np0r_R10 : getr regs 10 = wa 923480 ;
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
  np0r_kw7 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
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
  exists R, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R (wa 0x43f94) (np0r_mem_pnp0r m regs CA ND cnt sz SB st) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48) /\ getr R 8 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 9 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 12 = wa 923480 /\ getr R 13 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 14 = wa (ND + 31) /\ getr R 15 = wa 65536 /\ getr R 18 = wa 8 /\ getr R 19 = wa CA /\ getr R 20 = wa 923480 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
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
  destruct (run_sound SEGS 80 [0x43f08; 0x43f94] AXF_np0r.scr_pnp0r 0x43ce8 AXF_np0r.sr_np0r AXF_np0r.kn_np0r 38 _ _ _ E m rom regs AXF_np0r.RES_pnp0r_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
