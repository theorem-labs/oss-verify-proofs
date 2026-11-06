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

Module AXF_ng0.
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
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition e_nf := EVar 37.
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition RI := EAlu ALU_ADD e_RIB (EMd M_MUL (ELit 128) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_ng0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 923480)) 11 (EAlu ALU_ADD e_CA (ELit 2560))) 12 (CC)) 13 (EAlu ALU_ADD REC (ELit 16))) 14 (e_n)).
Definition kn_ng0 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA (ELit 0) 923528) 8 e_RIB;
    KWord (SA RI 0) 8 (ELit 0);
    KWr (SA RI 0) (ELit 8);
    KWord (SA RI 16) 8 e_nf;
    KWr (SA RI 16) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_ng0 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition ss_ng0 := SS 0x44474 sr_ng0 [] kn_ng0 38.
Definition RUN_ng0 := sym_exec SEGS 60 true [0x446ac; 0x446c0] scr_ng0 ss_ng0 [].

Definition scr_png0 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition RES_png0 := Eval vm_compute in sym_exec SEGS 60 true [0x446ac; 0x446c0] scr_png0 ss_ng0 [].
Lemma RES_png0_ok : sym_exec SEGS 60 true [0x446ac; 0x446c0] scr_png0 (SS 0x44474 sr_ng0 [] kn_ng0 38) [] = RES_png0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ng0.


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section NG0.
Context {fx : FPState}.

Definition VALS_ng0 (CA ND n SB RIB nf : Z) : list Z := [CA; ND; n; SB; RIB; nf].

Record ng0_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND n SB RIB nf : Z) : Prop := {
  ng0_R10 : getr regs 10 = wa 923480 ;
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
  ng0_kw6 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  ng0_kw7 : rdn SEGS m (wa (0 + 923528)) 8 = Some (word_to_le_bytes 8 (wa RIB)) ;
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
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 279672))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 8 (wa 1152921504606846976))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 16)) (word_to_le_bytes 8 (wa ((-1 * n) + nf))).

#[using="Type"] Theorem ng0_png0 : forall regs m rom CA ND n SB RIB nf, ng0_pre regs m CA ND n SB RIB nf ->
  scs_denot SEGS m (Ez regs (VALS_ng0 CA ND n SB RIB nf)) (snd (fst AXF_ng0.RES_png0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44474) m rom) (mkst R (wa 0x446ac) (ng0_mem_png0 m regs CA ND n SB RIB nf) rom) /\
    getr R 1 = wa 279672 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128) /\ getr R 5 = wa 0 /\ getr R 6 = wa 1152921504606846976 /\ getr R 7 = wa 0 /\ getr R 8 = wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 9 = wa 923480 /\ getr R 10 = wa ((RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 8) /\ getr R 11 = wa ((CA + ((4 * n) + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5))) + 16) /\ getr R 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) /\ getr R 14 = wa n /\ getr R 15 = wa ((-4 * n) + (4 * nf)) /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 19 = wa 2305843009213693952 /\ getr R 20 = wa (((-4 * n) + (SB + ((4 * nf) + (4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5)))) + 3758096384) /\ getr R 21 = wa 1099511627776 /\ getr R 22 = wa 1152921504607895551 /\ getr R 23 = wa 1152921504606846976 /\ getr R 24 = wa 1500 /\ getr R 25 = wa 16140901064495857663 /\ (forall k, In k [3; 4; 18; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
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
  destruct (run_sound SEGS 60 [0x446ac; 0x446c0] AXF_ng0.scr_png0 0x44474 AXF_ng0.sr_ng0 AXF_ng0.kn_ng0 38 _ _ _ E m rom regs AXF_ng0.RES_png0_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
