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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.

Module AXF_nri.
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
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_nri := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_CA)) 11 (REC)) 12 (ELit 929816)) 13 (CC)).
Definition kn_nri : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA REC 4) 4 (ELit 0);
    KWr (SA e_CA 84) (ELit 2488);
    KWr STK (ELit 1024) ].
Definition scr_nri : scripts := SCR [] [] [].
Definition ss_nri := SS 0x442b0 sr_nri [] kn_nri 34.
Definition RUN_nri := sym_exec SEGS 900 true [0x4484c] scr_nri ss_nri [].

Definition scr_pnri : scripts := SCR [] [] [].
Definition RES_pnri := Eval vm_compute in sym_exec SEGS 900 true [0x4484c] scr_pnri ss_nri [].
Lemma RES_pnri_ok : sym_exec SEGS 900 true [0x4484c] scr_pnri (SS 0x442b0 sr_nri [] kn_nri 34) [] = RES_pnri.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_nri.

Module AXF_nriz.
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

Section NRI.
Context {fx : FPState}.

Definition VALS_nri (CA ND : Z) : list Z := [CA; ND].

Record nri_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND : Z) : Prop := {
  nri_R10 : getr regs 10 = wa CA ;
  nri_R11 : getr regs 11 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) ;
  nri_R12 : getr regs 12 = wa 929816 ;
  nri_R13 : getr regs 13 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) ;
  nri_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  nri_rng_CA : 1 <= CA <= 2^47 ;
  nri_rng_ND : 33 <= ND <= 512 ;
  nri_ka1 : CA mod 16 = 0 ;
  nri_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  nri_kw4 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 4)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  nri_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 2488 -> store_ok SEGS m (wa (CA + 84 + d)) k = true
}.


#[using="Type"] Lemma nri_setup : forall regs m CA ND, nri_pre regs m CA ND ->
  regs_ok (Ez regs (VALS_nri CA ND)) AXF_nri.sr_nri regs /\ know_ok SEGS (Ez regs (VALS_nri CA ND)) m AXF_nri.kn_nri.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND P. destruct P as [nri_R10 nri_R11 nri_R12 nri_R13 nri_HSTK nri_rng_CA nri_rng_ND nri_ka1 nri_kr3 nri_kw4 nri_kwr5].
  set (E := Ez regs (VALS_nri CA ND)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_nri.sr_nri.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite nri_R10. reflexivity.
    - rewrite nri_R11, zeval_sound. cbn [zeval edenot AXF_nri.e_CA AXF_nri.e_ND AXF_nri.CC AXF_nri.REC AXF_nri.STK]. rewrite ?Z32, ?Z33, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite nri_R12. reflexivity.
    - rewrite nri_R13, zeval_sound. cbn [zeval edenot AXF_nri.e_CA AXF_nri.e_ND AXF_nri.CC AXF_nri.REC AXF_nri.STK]. rewrite ?Z32, ?Z33, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_nri.kn_nri.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_nri.e_CA AXF_nri.e_ND AXF_nri.CC AXF_nri.REC AXF_nri.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ nri_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ nri_rng_ND eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply nri_kwr5]; assumption).
  all: try (clear - nri_rng_CA nri_rng_ND nri_ka1 nri_kr3 HC; lia).
  all: first [lia].
Qed.


Definition nri_mem_pnri (m : word -> option byte) (regs : bvmap 5 word) (CA ND : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 279220))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (CA + 84)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 88)) (word_to_le_bytes 8 (wa 32))) (wa (CA + 164)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 168)) (word_to_le_bytes 8 (wa 64))) (wa (CA + 244)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 248)) (word_to_le_bytes 8 (wa 96))) (wa (CA + 324)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 328)) (word_to_le_bytes 8 (wa 128))) (wa (CA + 404)) (word_to_le_bytes 4 (wa 12))) (wa (CA + 408)) (word_to_le_bytes 8 (wa 160))) (wa (CA + 484)) (word_to_le_bytes 4 (wa 10))) (wa (CA + 488)) (word_to_le_bytes 8 (wa 192))) (wa (CA + 564)) (word_to_le_bytes 4 (wa 8))) (wa (CA + 568)) (word_to_le_bytes 8 (wa 224))) (wa (CA + 644)) (word_to_le_bytes 4 (wa 8))) (wa (CA + 648)) (word_to_le_bytes 8 (wa 256))) (wa (CA + 724)) (word_to_le_bytes 4 (wa 6))) (wa (CA + 728)) (word_to_le_bytes 8 (wa 288))) (wa (CA + 804)) (word_to_le_bytes 4 (wa 6))) (wa (CA + 808)) (word_to_le_bytes 8 (wa 320))) (wa (CA + 884)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 888)) (word_to_le_bytes 8 (wa 352))) (wa (CA + 964)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 968)) (word_to_le_bytes 8 (wa 384))) (wa (CA + 1044)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1048)) (word_to_le_bytes 8 (wa 416))) (wa (CA + 1124)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1128)) (word_to_le_bytes 8 (wa 448))) (wa (CA + 1204)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1208)) (word_to_le_bytes 8 (wa 480))) (wa (CA + 1284)) (word_to_le_bytes 4 (wa 4))) (wa (CA + 1288)) (word_to_le_bytes 8 (wa 512))) (wa (CA + 1364)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1368)) (word_to_le_bytes 8 (wa 768))) (wa (CA + 1444)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1448)) (word_to_le_bytes 8 (wa 1024))) (wa (CA + 1524)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1528)) (word_to_le_bytes 8 (wa 1536))) (wa (CA + 1604)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1608)) (word_to_le_bytes 8 (wa 2048))) (wa (CA + 1684)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1688)) (word_to_le_bytes 8 (wa 3072))) (wa (CA + 1764)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1768)) (word_to_le_bytes 8 (wa 4096))) (wa (CA + 1844)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1848)) (word_to_le_bytes 8 (wa 6144))) (wa (CA + 1924)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 1928)) (word_to_le_bytes 8 (wa 8192))) (wa (CA + 2004)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2008)) (word_to_le_bytes 8 (wa 12288))) (wa (CA + 2084)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2088)) (word_to_le_bytes 8 (wa 16384))) (wa (CA + 2164)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2168)) (word_to_le_bytes 8 (wa 24576))) (wa (CA + 2244)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2248)) (word_to_le_bytes 8 (wa 32768))) (wa (CA + 2324)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2328)) (word_to_le_bytes 8 (wa 49152))) (wa (CA + 2404)) (word_to_le_bytes 4 (wa 2))) (wa (CA + 2408)) (word_to_le_bytes 8 (wa 65536))) (wa (CA + 2484)) (word_to_le_bytes 4 (wa 16))) (wa (CA + 2488)) (word_to_le_bytes 8 (wa 64)).

#[using="Type"] Theorem nri_pnri : forall regs m rom CA ND, nri_pre regs m CA ND ->
  scs_denot SEGS m (Ez regs (VALS_nri CA ND)) (snd (fst AXF_nri.RES_pnri)) ->
  exists R, msteps SEGS (mkst regs (wa 0x442b0) m rom) (mkst R (wa 0x4484c) (nri_mem_pnri m regs CA ND) rom) /\
    getr R 1 = wa 279220 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32) /\ getr R 5 = wa 16 /\ getr R 6 = wa 17 /\ getr R 7 = wa 512 /\ getr R 8 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 10 = wa CA /\ getr R 11 = wa (CA + 2568) /\ getr R 12 = wa 929816 /\ getr R 13 = wa 1024 /\ getr R 14 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 15 = wa 16 /\ getr R 16 = wa 15 /\ getr R 17 = wa 1024 /\ getr R 28 = wa 64 /\ getr R 29 = wa 16 /\ getr R 30 = wa 0 /\ (forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND P Hsc. destruct (nri_setup regs m CA ND P) as [HR HK].
  set (E := Ez regs (VALS_nri CA ND)) in *. destruct P as [nri_R10 nri_R11 nri_R12 nri_R13 nri_HSTK nri_rng_CA nri_rng_ND nri_ka1 nri_kr3 nri_kw4 nri_kwr5].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 900 [0x4484c] AXF_nri.scr_pnri 0x442b0 AXF_nri.sr_nri AXF_nri.kn_nri 34 _ _ _ E m rom regs AXF_nri.RES_pnri_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nri.RES_pnri fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nri_mem_pnri m regs CA ND) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nri_mem_pnri. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NRI.
(* [comment removed for export] *)
End AXF_nriz.

Module AXF_ng0p.
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
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition RI := EAlu ALU_ADD e_RIB (EMd M_MUL (ELit 128) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_ng0p := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (ELit 929816)) 11 (EAlu ALU_ADD e_CA (ELit 2560))) 12 (CC)) 13 (EAlu ALU_ADD REC (ELit 16))) 14 (e_n)).
Definition kn_ng0p : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KRange e_SB 1 (2^47);
    KAlign e_SB 4096;
    KWord (SA (ELit 0) 929848) 8 e_SB;
    KWord (SA (ELit 0) 929864) 8 e_RIB;
    KWord (SA (ELit 0) 929856) 4 (ELit 4294967295);
    KWord (SA (ELit 0) 929872) 1 (ELit 0);
    KWord (SA RI 0) 8 (ELit 0);
    KWr (SA RI 0) (ELit 8);
    KWord (SA RI 16) 8 (ELit 0);
    KWord (SA RI 32) 8 (ELit 0);
    KWord (SA RI 48) 8 (ELit 0);
    KWord (SA RI 56) 8 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_ng0p : scripts := SCR [true; true; false] [] [].
Definition ss_ng0p := SS 0x44790 sr_ng0p [] kn_ng0p 37.
Definition RUN_ng0p := sym_exec SEGS 200 true [0x7db84] scr_ng0p ss_ng0p [].

Definition scr_png0p : scripts := SCR [true; true; false] [] [].
Definition RES_png0p := Eval vm_compute in sym_exec SEGS 200 true [0x7db84] scr_png0p ss_ng0p [].
Lemma RES_png0p_ok : sym_exec SEGS 200 true [0x7db84] scr_png0p (SS 0x44790 sr_ng0p [] kn_ng0p 37) [] = RES_png0p.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_ng0p.

Module AXF_ng0pz.
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

Section NG0P.
Context {fx : FPState}.

Definition VALS_ng0p (CA ND n SB RIB : Z) : list Z := [CA; ND; n; SB; RIB].

Record ng0p_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND n SB RIB : Z) : Prop := {
  ng0p_R10 : getr regs 10 = wa 929816 ;
  ng0p_R11 : getr regs 11 = wa (CA + 2560) ;
  ng0p_R12 : getr regs 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) ;
  ng0p_R13 : getr regs 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) ;
  ng0p_R14 : getr regs 14 = wa n ;
  ng0p_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  ng0p_rng_CA : 1 <= CA <= 2^47 ;
  ng0p_rng_ND : 33 <= ND <= 512 ;
  ng0p_rng_n : 1 <= n <= 8 ;
  ng0p_rng_SB : 1 <= SB <= 2^47 ;
  ng0p_rng_RIB : 1 <= RIB <= 2^47 ;
  ng0p_ka1 : CA mod 16 = 0 ;
  ng0p_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  ng0p_ka5 : RIB mod 128 = 0 ;
  ng0p_ka7 : SB mod 4096 = 0 ;
  ng0p_kw8 : rdn SEGS m (wa (0 + 929848)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  ng0p_kw9 : rdn SEGS m (wa (0 + 929864)) 8 = Some (word_to_le_bytes 8 (wa RIB)) ;
  ng0p_kw10 : rdn SEGS m (wa (0 + 929856)) 4 = Some (word_to_le_bytes 4 (wa 4294967295)) ;
  ng0p_kw11 : rdn SEGS m (wa (0 + 929872)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  ng0p_kw12 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ng0p_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  ng0p_kw14 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ng0p_kw15 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ng0p_kw16 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 48)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ng0p_kw17 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 56)) 8 = Some (word_to_le_bytes 8 (wa 0))
}.


#[using="Type"] Lemma ng0p_setup : forall regs m CA ND n SB RIB, ng0p_pre regs m CA ND n SB RIB ->
  regs_ok (Ez regs (VALS_ng0p CA ND n SB RIB)) AXF_ng0p.sr_ng0p regs /\ know_ok SEGS (Ez regs (VALS_ng0p CA ND n SB RIB)) m AXF_ng0p.kn_ng0p.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND n SB RIB P. destruct P as [ng0p_R10 ng0p_R11 ng0p_R12 ng0p_R13 ng0p_R14 ng0p_HSTK ng0p_rng_CA ng0p_rng_ND ng0p_rng_n ng0p_rng_SB ng0p_rng_RIB ng0p_ka1 ng0p_kr3 ng0p_ka5 ng0p_ka7 ng0p_kw8 ng0p_kw9 ng0p_kw10 ng0p_kw11 ng0p_kw12 ng0p_kwr13 ng0p_kw14 ng0p_kw15 ng0p_kw16 ng0p_kw17].
  set (E := Ez regs (VALS_ng0p CA ND n SB RIB)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_ng0p.sr_ng0p.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite ng0p_R10. reflexivity.
    - rewrite ng0p_R11, zeval_sound. cbn [zeval edenot AXF_ng0p.e_CA AXF_ng0p.e_ND AXF_ng0p.e_n AXF_ng0p.e_SB AXF_ng0p.e_RIB AXF_ng0p.CC AXF_ng0p.REC AXF_ng0p.RI AXF_ng0p.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ng0p_R12, zeval_sound. cbn [zeval edenot AXF_ng0p.e_CA AXF_ng0p.e_ND AXF_ng0p.e_n AXF_ng0p.e_SB AXF_ng0p.e_RIB AXF_ng0p.CC AXF_ng0p.REC AXF_ng0p.RI AXF_ng0p.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ng0p_R13, zeval_sound. cbn [zeval edenot AXF_ng0p.e_CA AXF_ng0p.e_ND AXF_ng0p.e_n AXF_ng0p.e_SB AXF_ng0p.e_RIB AXF_ng0p.CC AXF_ng0p.REC AXF_ng0p.RI AXF_ng0p.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ng0p_R14. reflexivity. }
  unfold know_ok, AXF_ng0p.kn_ng0p.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ng0p.e_CA AXF_ng0p.e_ND AXF_ng0p.e_n AXF_ng0p.e_SB AXF_ng0p.e_RIB AXF_ng0p.CC AXF_ng0p.REC AXF_ng0p.RI AXF_ng0p.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ ng0p_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ ng0p_rng_ND eq_refl eq_refl), ?(mod64_of_range n _ _ ng0p_rng_n eq_refl eq_refl), ?(mod64_of_range SB _ _ ng0p_rng_SB eq_refl eq_refl), ?(mod64_of_range RIB _ _ ng0p_rng_RIB eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ng0p_kwr13]; assumption).
  all: try (clear - ng0p_rng_CA ng0p_rng_ND ng0p_rng_n ng0p_rng_SB ng0p_rng_RIB ng0p_ka1 ng0p_kr3 ng0p_ka5 ng0p_ka7 HC; lia).
  all: first [lia].
Qed.


Definition ng0p_mem_png0p (m : word -> option byte) (regs : bvmap 5 word) (CA ND n SB RIB : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 280468))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 8 (wa 1152921504606846976))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -136)) (word_to_le_bytes 8 (wa 281360))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -144)) (word_to_le_bytes 8 (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -152)) (word_to_le_bytes 8 (wa 929816))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -160)) (word_to_le_bytes 8 (wa ((RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 8)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -168)) (word_to_le_bytes 8 (wa 2305843009213693952))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -176)) (word_to_le_bytes 8 (wa ((SB + (4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 3758096384)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -184)) (word_to_le_bytes 8 (wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -192)) (word_to_le_bytes 8 (wa n)).

#[using="Type"] Theorem ng0p_png0p : forall regs m rom CA ND n SB RIB, ng0p_pre regs m CA ND n SB RIB ->
  scs_denot SEGS m (Ez regs (VALS_ng0p CA ND n SB RIB)) (snd (fst AXF_ng0p.RES_png0p)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44790) m rom) (mkst R (wa 0x7db84) (ng0p_mem_png0p m regs CA ND n SB RIB) rom) /\
    getr R 1 = wa 281724 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -192) /\ getr R 5 = wa 0 /\ getr R 6 = wa 1152921504606846976 /\ getr R 7 = wa 0 /\ getr R 8 = wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 9 = wa (CA + 2560) /\ getr R 10 = wa 929816 /\ getr R 11 = wa (SB + (4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 12 = wa ((262144 * Z.shiftr (((((32 * Z.shiftr (((ND + 31)) mod 2^64) 5) * n) + -1)) mod 2^64) 18) + 262144) /\ getr R 13 = wa 96426 /\ getr R 14 = wa n /\ getr R 15 = wa 0 /\ getr R 16 = wa 18446744073709551615 /\ getr R 17 = wa 0 /\ getr R 18 = wa (SB + (4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 19 = wa ((262144 * Z.shiftr (((((32 * Z.shiftr (((ND + 31)) mod 2^64) 5) * n) + -1)) mod 2^64) 18) + 262144) /\ getr R 20 = wa (SB + (4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 21 = wa (32 * Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 22 = wa 929816 /\ getr R 23 = wa 1152921504606846976 /\ getr R 24 = wa 1500 /\ getr R 25 = wa 16140901064495857663 /\ (forall k, In k [3; 4; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND n SB RIB P Hsc. destruct (ng0p_setup regs m CA ND n SB RIB P) as [HR HK].
  set (E := Ez regs (VALS_ng0p CA ND n SB RIB)) in *. destruct P as [ng0p_R10 ng0p_R11 ng0p_R12 ng0p_R13 ng0p_R14 ng0p_HSTK ng0p_rng_CA ng0p_rng_ND ng0p_rng_n ng0p_rng_SB ng0p_rng_RIB ng0p_ka1 ng0p_kr3 ng0p_ka5 ng0p_ka7 ng0p_kw8 ng0p_kw9 ng0p_kw10 ng0p_kw11 ng0p_kw12 ng0p_kwr13 ng0p_kw14 ng0p_kw15 ng0p_kw16 ng0p_kw17].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 200 [0x7db84] AXF_ng0p.scr_png0p 0x44790 AXF_ng0p.sr_ng0p AXF_ng0p.kn_ng0p 37 _ _ _ E m rom regs AXF_ng0p.RES_png0p_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ng0p.RES_png0p fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ng0p_mem_png0p m regs CA ND n SB RIB) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ng0p_mem_png0p. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NG0P.
(* [comment removed for export] *)
End AXF_ng0pz.

Module AXF_mf1.
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

Definition e_AD := EVar 32.
Definition e_SZ := EVar 33.
Definition e_CF := EVar 34.
Definition e_RA0 := EVar 35.
Definition e_S0 := EVar 36.
Definition e_S1 := EVar 37.
Definition e_S2 := EVar 38.
Definition e_S3 := EVar 39.
Definition e_S4 := EVar 40.
Definition STK := SA (EVar 2) (-1024).
Definition sr_mf1 := (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 481784)) 8 (e_SZ)) 10 (e_AD)).
Definition kn_mf1 : list kentry :=
  [ KRange e_AD 4096 (2^47);
    KAlign e_AD 4096;
    KRange e_SZ 4096 (2^32);
    KRange e_CF 1 (2^47);
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (EVar 2) 88) 8 e_RA0;
    KWord (SA (EVar 2) 80) 8 e_S0;
    KWord (SA (EVar 2) 72) 8 e_S1;
    KWord (SA (EVar 2) 64) 8 e_S2;
    KWord (SA (EVar 2) 56) 8 e_S3;
    KWord (SA (EVar 2) 48) 8 e_S4;
    KWr (SA (EVar 2) 44) (ELit 4);
    KWord (SA (ELit 0) 910464) 8 e_CF;
    KWord (SA e_CF 144) 8 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_mf1 : scripts := SCR [] [] [].
Definition ss_mf1 := SS 0x73c3c sr_mf1 [] kn_mf1 41.
Definition RUN_mf1 := sym_exec SEGS 80 true [0x75a48] scr_mf1 ss_mf1 [].

Definition scr_pmf1 : scripts := SCR [] [] [].
Definition RES_pmf1 := Eval vm_compute in sym_exec SEGS 80 true [0x75a48] scr_pmf1 ss_mf1 [].
Lemma RES_pmf1_ok : sym_exec SEGS 80 true [0x75a48] scr_pmf1 (SS 0x73c3c sr_mf1 [] kn_mf1 41) [] = RES_pmf1.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_mf1.

Module AXF_mf1z.
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

Section MF1.
Context {fx : FPState}.

Definition VALS_mf1 (AD SZ CF RA0 S0 S1 S2 S3 S4 : Z) : list Z := [AD; SZ; CF; RA0; S0; S1; S2; S3; S4].

Record mf1_pre (regs : bvmap 5 word) (m : word -> option byte) (AD SZ CF RA0 S0 S1 S2 S3 S4 : Z) : Prop := {
  mf1_R1 : getr regs 1 = wa 481784 ;
  mf1_R8 : getr regs 8 = wa SZ ;
  mf1_R10 : getr regs 10 = wa AD ;
  mf1_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  mf1_rng_AD : 4096 <= AD <= 2^47 ;
  mf1_rng_SZ : 4096 <= SZ <= 2^32 ;
  mf1_rng_CF : 1 <= CF <= 2^47 ;
  mf1_rng_RA0 : 0 <= RA0 <= 2^64-1 ;
  mf1_rng_S0 : 0 <= S0 <= 2^64-1 ;
  mf1_rng_S1 : 0 <= S1 <= 2^64-1 ;
  mf1_rng_S2 : 0 <= S2 <= 2^64-1 ;
  mf1_rng_S3 : 0 <= S3 <= 2^64-1 ;
  mf1_rng_S4 : 0 <= S4 <= 2^64-1 ;
  mf1_ka1 : AD mod 4096 = 0 ;
  mf1_kr4 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  mf1_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa RA0)) ;
  mf1_kw6 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa S0)) ;
  mf1_kw7 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa S1)) ;
  mf1_kw8 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64)) 8 = Some (word_to_le_bytes 8 (wa S2)) ;
  mf1_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa S3)) ;
  mf1_kw10 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa S4)) ;
  mf1_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 44 + d)) k = true ;
  mf1_kw12 : rdn SEGS m (wa (0 + 910464)) 8 = Some (word_to_le_bytes 8 (wa CF)) ;
  mf1_kw13 : rdn SEGS m (wa (CF + 144)) 8 = Some (word_to_le_bytes 8 (wa 0))
}.


#[using="Type"] Lemma mf1_setup : forall regs m AD SZ CF RA0 S0 S1 S2 S3 S4, mf1_pre regs m AD SZ CF RA0 S0 S1 S2 S3 S4 ->
  regs_ok (Ez regs (VALS_mf1 AD SZ CF RA0 S0 S1 S2 S3 S4)) AXF_mf1.sr_mf1 regs /\ know_ok SEGS (Ez regs (VALS_mf1 AD SZ CF RA0 S0 S1 S2 S3 S4)) m AXF_mf1.kn_mf1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m AD SZ CF RA0 S0 S1 S2 S3 S4 P. destruct P as [mf1_R1 mf1_R8 mf1_R10 mf1_HSTK mf1_rng_AD mf1_rng_SZ mf1_rng_CF mf1_rng_RA0 mf1_rng_S0 mf1_rng_S1 mf1_rng_S2 mf1_rng_S3 mf1_rng_S4 mf1_ka1 mf1_kr4 mf1_kw5 mf1_kw6 mf1_kw7 mf1_kw8 mf1_kw9 mf1_kw10 mf1_kwr11 mf1_kw12 mf1_kw13].
  set (E := Ez regs (VALS_mf1 AD SZ CF RA0 S0 S1 S2 S3 S4)).
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = CF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = RA0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = S0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = S1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = S2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = S3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = S4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_mf1.sr_mf1.
    apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|].
    - rewrite mf1_R1. reflexivity.
    - rewrite mf1_R8. reflexivity.
    - rewrite mf1_R10. reflexivity. }
  unfold know_ok, AXF_mf1.kn_mf1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mf1.e_AD AXF_mf1.e_SZ AXF_mf1.e_CF AXF_mf1.e_RA0 AXF_mf1.e_S0 AXF_mf1.e_S1 AXF_mf1.e_S2 AXF_mf1.e_S3 AXF_mf1.e_S4 AXF_mf1.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range AD _ _ mf1_rng_AD eq_refl eq_refl), ?(mod64_of_range SZ _ _ mf1_rng_SZ eq_refl eq_refl), ?(mod64_of_range CF _ _ mf1_rng_CF eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mf1_kwr11]; assumption).
  all: try (clear - mf1_rng_AD mf1_rng_SZ mf1_rng_CF mf1_rng_RA0 mf1_rng_S0 mf1_rng_S1 mf1_rng_S2 mf1_rng_S3 mf1_rng_S4 mf1_ka1 mf1_kr4; lia).
  all: first [lia].
Qed.


Definition mf1_mem_pmf1 (m : word -> option byte) (regs : bvmap 5 word) (AD SZ CF RA0 S0 S1 S2 S3 S4 : Z) : word -> option byte :=
  wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 44)) (word_to_le_bytes 4 (wa 18446744072277895850)).

#[using="Type"] Theorem mf1_pmf1 : forall regs m rom AD SZ CF RA0 S0 S1 S2 S3 S4, mf1_pre regs m AD SZ CF RA0 S0 S1 S2 S3 S4 ->
  scs_denot SEGS m (Ez regs (VALS_mf1 AD SZ CF RA0 S0 S1 S2 S3 S4)) (snd (fst AXF_mf1.RES_pmf1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x73c3c) m rom) (mkst R (wa 0x75a48) (mf1_mem_pmf1 m regs AD SZ CF RA0 S0 S1 S2 S3 S4) rom) /\
    getr R 1 = wa RA0 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 96) /\ getr R 8 = wa S0 /\ getr R 9 = wa S1 /\ getr R 10 = wa AD /\ getr R 11 = wa 0 /\ getr R 12 = wa 18446744073709547520 /\ getr R 13 = wa 18446744073709547521 /\ getr R 18 = wa S2 /\ getr R 19 = wa S3 /\ getr R 20 = wa S4 /\ (forall k, In k [3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom AD SZ CF RA0 S0 S1 S2 S3 S4 P Hsc. destruct (mf1_setup regs m AD SZ CF RA0 S0 S1 S2 S3 S4 P) as [HR HK].
  set (E := Ez regs (VALS_mf1 AD SZ CF RA0 S0 S1 S2 S3 S4)) in *. destruct P as [mf1_R1 mf1_R8 mf1_R10 mf1_HSTK mf1_rng_AD mf1_rng_SZ mf1_rng_CF mf1_rng_RA0 mf1_rng_S0 mf1_rng_S1 mf1_rng_S2 mf1_rng_S3 mf1_rng_S4 mf1_ka1 mf1_kr4 mf1_kw5 mf1_kw6 mf1_kw7 mf1_kw8 mf1_kw9 mf1_kw10 mf1_kwr11 mf1_kw12 mf1_kw13].
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = CF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = RA0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = S0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = S1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = S2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = S3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = S4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 80 [0x75a48] AXF_mf1.scr_pmf1 0x73c3c AXF_mf1.sr_mf1 AXF_mf1.kn_mf1 41 _ _ _ E m rom regs AXF_mf1.RES_pmf1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mf1.RES_pmf1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mf1_mem_pmf1 m regs AD SZ CF RA0 S0 S1 S2 S3 S4) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mf1_mem_pmf1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End MF1.
(* [comment removed for export] *)
End AXF_mf1z.

Module AXF_pb2.
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
Definition e_RI := EVar 33.
Definition e_RB := EVar 34.
Definition e_SZC := EVar 35.
Definition e_TP := EVar 36.
Definition e_K := EVar 37.
Definition e_TSDA := EVar 38.
Definition e_PT := EVar 39.
Definition e_T := EVar 40.
Definition e_mm1 := EVar 41.
Definition e_mm2 := EVar 42.
Definition e_st2 := EVar 43.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pb2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 4 (e_TP)) 8 (e_RI)) 9 (EAlu ALU_ADD e_CA (ELit 2560))) 18 (e_RB)) 19 (ELit 262144)) 20 (e_RB)) 21 (e_SZC)) 22 (ELit 929816)).
Definition kn_pb2 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_RI 1 (2^47);
    KAlign e_RI 128;
    KRange e_RB 4096 (2^47);
    KAlign e_RB 4096;
    KRange e_SZC 64 512;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 941792) 1 (ELit 1);
    KWord (SA (ELit 0) 941796) 4 e_K;
    KWord (SA e_TP (-88)) 8 e_TSDA;
    KWord (SA (EAlu ALU_ADD e_TSDA (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_K)) (ELit 29))) 0) 8 e_PT;
    KWord (SA e_PT 152) 8 e_T;
    KWord (SA e_T 2872) 8 e_mm1;
    KWr (SA e_T 2872) (ELit 8);
    KWord (SA e_T 2880) 8 e_mm2;
    KWr (SA e_T 2880) (ELit 8);
    KWord (SA e_CA 2584) 8 e_st2;
    KWr (SA e_CA 2584) (ELit 8);
    KWord (SA e_RI 16) 8 (ELit 0);
    KWord (SA e_RI 24) 8 (ELit 0);
    KWord (SA e_RI 32) 8 (ELit 0);
    KWord (SA e_RI 48) 8 (ELit 0);
    KWr (SA e_RI 48) (ELit 8);
    KWord (SA (ELit 0) 929872) 1 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_pb2 : scripts := SCR [false; false] [] [].
Definition ss_pb2 := SS 0x44c98 sr_pb2 [] kn_pb2 44.
Definition RUN_pb2 := sym_exec SEGS 160 true [0x7db84] scr_pb2 ss_pb2 [].

Definition scr_ppb2 : scripts := SCR [false; false] [] [].
Definition RES_ppb2 := Eval vm_compute in sym_exec SEGS 160 true [0x7db84] scr_ppb2 ss_pb2 [].
Lemma RES_ppb2_ok : sym_exec SEGS 160 true [0x7db84] scr_ppb2 (SS 0x44c98 sr_pb2 [] kn_pb2 44) [] = RES_ppb2.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pb2.

Module AXF_pb2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section PB2.
Context {fx : FPState}.

Definition VALS_pb2 (CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 : Z) : list Z := [CA; RI; RB; SZC; TP; K; TSDA; PT; T; mm1; mm2; st2].

Record pb2_pre (regs : bvmap 5 word) (m : word -> option byte) (CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 : Z) : Prop := {
  pb2_R4 : getr regs 4 = wa TP ;
  pb2_R8 : getr regs 8 = wa RI ;
  pb2_R9 : getr regs 9 = wa (CA + 2560) ;
  pb2_R18 : getr regs 18 = wa RB ;
  pb2_R19 : getr regs 19 = wa 262144 ;
  pb2_R20 : getr regs 20 = wa RB ;
  pb2_R21 : getr regs 21 = wa SZC ;
  pb2_R22 : getr regs 22 = wa 929816 ;
  pb2_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pb2_rng_CA : 1 <= CA <= 2^47 ;
  pb2_rng_RI : 1 <= RI <= 2^47 ;
  pb2_rng_RB : 4096 <= RB <= 2^47 ;
  pb2_rng_SZC : 64 <= SZC <= 512 ;
  pb2_rng_TP : 4096 <= TP <= 2^47 ;
  pb2_rng_K : 0 <= K <= 1023 ;
  pb2_rng_TSDA : 1 <= TSDA <= 2^47 ;
  pb2_rng_PT : 1 <= PT <= 2^47 ;
  pb2_rng_T : 1 <= T <= 2^47 ;
  pb2_rng_mm1 : 0 <= mm1 <= 2^64-1 ;
  pb2_rng_mm2 : 0 <= mm2 <= 2^64-1 ;
  pb2_rng_st2 : 0 <= st2 <= 2^64-1 ;
  pb2_ka1 : CA mod 16 = 0 ;
  pb2_ka3 : RI mod 128 = 0 ;
  pb2_ka5 : RB mod 4096 = 0 ;
  pb2_kr7 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pb2_kw8 : rdn SEGS m (wa (0 + 941792)) 1 = Some (word_to_le_bytes 1 (wa 1)) ;
  pb2_kw9 : rdn SEGS m (wa (0 + 941796)) 4 = Some (word_to_le_bytes 4 (wa K)) ;
  pb2_kw10 : rdn SEGS m (wa (TP + -88)) 8 = Some (word_to_le_bytes 8 (wa TSDA)) ;
  pb2_kw11 : rdn SEGS m (wa (TSDA + Z.shiftr (((4294967296 * ext_Z true 0 4 K)) mod 2^64) 29 + 0)) 8 = Some (word_to_le_bytes 8 (wa PT)) ;
  pb2_kw12 : rdn SEGS m (wa (PT + 152)) 8 = Some (word_to_le_bytes 8 (wa T)) ;
  pb2_kw13 : rdn SEGS m (wa (T + 2872)) 8 = Some (word_to_le_bytes 8 (wa mm1)) ;
  pb2_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2872 + d)) k = true ;
  pb2_kw15 : rdn SEGS m (wa (T + 2880)) 8 = Some (word_to_le_bytes 8 (wa mm2)) ;
  pb2_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2880 + d)) k = true ;
  pb2_kw17 : rdn SEGS m (wa (CA + 2584)) 8 = Some (word_to_le_bytes 8 (wa st2)) ;
  pb2_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2584 + d)) k = true ;
  pb2_kw19 : rdn SEGS m (wa (RI + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pb2_kw20 : rdn SEGS m (wa (RI + 24)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pb2_kw21 : rdn SEGS m (wa (RI + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pb2_kw22 : rdn SEGS m (wa (RI + 48)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pb2_kwr23 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 48 + d)) k = true ;
  pb2_kw24 : rdn SEGS m (wa (0 + 929872)) 1 = Some (word_to_le_bytes 1 (wa 0))
}.


#[using="Type"] Lemma pb2_setup : forall regs m CA RI RB SZC TP K TSDA PT T mm1 mm2 st2, pb2_pre regs m CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 ->
  regs_ok (Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) AXF_pb2.sr_pb2 regs /\ know_ok SEGS (Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) m AXF_pb2.kn_pb2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 P. destruct P as [pb2_R4 pb2_R8 pb2_R9 pb2_R18 pb2_R19 pb2_R20 pb2_R21 pb2_R22 pb2_HSTK pb2_rng_CA pb2_rng_RI pb2_rng_RB pb2_rng_SZC pb2_rng_TP pb2_rng_K pb2_rng_TSDA pb2_rng_PT pb2_rng_T pb2_rng_mm1 pb2_rng_mm2 pb2_rng_st2 pb2_ka1 pb2_ka3 pb2_ka5 pb2_kr7 pb2_kw8 pb2_kw9 pb2_kw10 pb2_kw11 pb2_kw12 pb2_kw13 pb2_kwr14 pb2_kw15 pb2_kwr16 pb2_kw17 pb2_kwr18 pb2_kw19 pb2_kw20 pb2_kw21 pb2_kw22 pb2_kwr23 pb2_kw24].
  set (E := Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SZC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = st2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  split.
  { unfold AXF_pb2.sr_pb2.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 4); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite pb2_R4. reflexivity.
    - rewrite pb2_R8. reflexivity.
    - rewrite pb2_R9, zeval_sound. cbn [zeval edenot AXF_pb2.e_CA AXF_pb2.e_RI AXF_pb2.e_RB AXF_pb2.e_SZC AXF_pb2.e_TP AXF_pb2.e_K AXF_pb2.e_TSDA AXF_pb2.e_PT AXF_pb2.e_T AXF_pb2.e_mm1 AXF_pb2.e_mm2 AXF_pb2.e_st2 AXF_pb2.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite pb2_R18. reflexivity.
    - rewrite pb2_R19. reflexivity.
    - rewrite pb2_R20. reflexivity.
    - rewrite pb2_R21. reflexivity.
    - rewrite pb2_R22. reflexivity. }
  unfold know_ok, AXF_pb2.kn_pb2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pb2.e_CA AXF_pb2.e_RI AXF_pb2.e_RB AXF_pb2.e_SZC AXF_pb2.e_TP AXF_pb2.e_K AXF_pb2.e_TSDA AXF_pb2.e_PT AXF_pb2.e_T AXF_pb2.e_mm1 AXF_pb2.e_mm2 AXF_pb2.e_st2 AXF_pb2.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ pb2_rng_CA eq_refl eq_refl), ?(mod64_of_range RI _ _ pb2_rng_RI eq_refl eq_refl), ?(mod64_of_range RB _ _ pb2_rng_RB eq_refl eq_refl), ?(mod64_of_range SZC _ _ pb2_rng_SZC eq_refl eq_refl), ?(mod64_of_range TP _ _ pb2_rng_TP eq_refl eq_refl), ?(mod64_of_range K _ _ pb2_rng_K eq_refl eq_refl), ?(mod64_of_range TSDA _ _ pb2_rng_TSDA eq_refl eq_refl), ?(mod64_of_range PT _ _ pb2_rng_PT eq_refl eq_refl), ?(mod64_of_range T _ _ pb2_rng_T eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pb2_kwr14 | apply pb2_kwr16 | apply pb2_kwr18 | apply pb2_kwr23]; assumption).
  all: try (clear - pb2_rng_CA pb2_rng_RI pb2_rng_RB pb2_rng_SZC pb2_rng_TP pb2_rng_K pb2_rng_TSDA pb2_rng_PT pb2_rng_T pb2_rng_mm1 pb2_rng_mm2 pb2_rng_st2 pb2_ka1 pb2_ka3 pb2_ka5 pb2_kr7 HKO; lia).
  all: first [lia].
Qed.


Definition pb2_mem_ppb2 (m : word -> option byte) (regs : bvmap 5 word) (CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 281756))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa 436880))) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))) (wa (CA + 2584)) (word_to_le_bytes 8 (wa (st2 + 262144)))) (wa (RI + 48)) (word_to_le_bytes 8 (wa 262144))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 281840))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa RI))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (edenot (Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) (EMd M_DIVU (ELit 262144) (EVar 35))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa RB))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (edenot (Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) (EMd M_DIVU (ELit 262144) (EVar 35)))))).

#[using="Type"] Theorem pb2_ppb2 : forall regs m rom CA RI RB SZC TP K TSDA PT T mm1 mm2 st2, pb2_pre regs m CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 ->
  scs_denot SEGS m (Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) (snd (fst AXF_pb2.RES_ppb2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44c98) m rom) (mkst R (wa 0x7db84) (pb2_mem_ppb2 m regs CA RI RB SZC TP K TSDA PT T mm1 mm2 st2) rom) /\
    getr R 1 = wa 272576 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48) /\ getr R 4 = wa TP /\ getr R 8 = wa 262144 /\ getr R 9 = wa (RB + 3758096384) /\ getr R 10 = wa 929816 /\ getr R 11 = wa (RB + 3758096384) /\ getr R 12 = wa 262144 /\ getr R 13 = wa 104102 /\ getr R 14 = wa 0 /\ getr R 15 = wa 3758096384 /\ getr R 18 = wa 262144 /\ getr R 19 = wa RI /\ getr R 20 = wa 262144 /\ getr R 21 = wa SZC /\ getr R 22 = wa 929816 /\ (forall k, In k [3; 5; 6; 7; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 P Hsc. destruct (pb2_setup regs m CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 P) as [HR HK].
  set (E := Ez regs (VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) in *. destruct P as [pb2_R4 pb2_R8 pb2_R9 pb2_R18 pb2_R19 pb2_R20 pb2_R21 pb2_R22 pb2_HSTK pb2_rng_CA pb2_rng_RI pb2_rng_RB pb2_rng_SZC pb2_rng_TP pb2_rng_K pb2_rng_TSDA pb2_rng_PT pb2_rng_T pb2_rng_mm1 pb2_rng_mm2 pb2_rng_st2 pb2_ka1 pb2_ka3 pb2_ka5 pb2_kr7 pb2_kw8 pb2_kw9 pb2_kw10 pb2_kw11 pb2_kw12 pb2_kw13 pb2_kwr14 pb2_kw15 pb2_kwr16 pb2_kw17 pb2_kwr18 pb2_kw19 pb2_kw20 pb2_kw21 pb2_kw22 pb2_kwr23 pb2_kw24].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SZC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = st2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  destruct (run_sound SEGS 160 [0x7db84] AXF_pb2.scr_ppb2 0x44c98 AXF_pb2.sr_pb2 AXF_pb2.kn_pb2 44 _ _ _ E m rom regs AXF_pb2.RES_ppb2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pb2.RES_ppb2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pb2_mem_ppb2 m regs CA RI RB SZC TP K TSDA PT T mm1 mm2 st2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pb2_mem_ppb2. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PB2.
(* [comment removed for export] *)
End AXF_pb2z.

Module AXF_pc1b.
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

Definition e_RI := EVar 32.
Definition e_RB := EVar 33.
Definition e_SZC := EVar 34.
Definition e_NEW := EVar 35.
Definition e_TP := EVar 36.
Definition e_K := EVar 37.
Definition e_TSDA := EVar 38.
Definition e_PT := EVar 39.
Definition e_T := EVar 40.
Definition e_mm1 := EVar 41.
Definition e_mm2 := EVar 42.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pc1b := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 4 (e_TP)) 8 (ELit 262144)) 9 (EAlu ALU_ADD e_RB (ELit 3758096384))) 18 (ELit 262144)) 19 (e_RI)) 20 (ELit 262144)) 21 (e_SZC)) 22 (ELit 929816)).
Definition kn_pc1b : list kentry :=
  [ KRange e_RI 1 (2^47);
    KAlign e_RI 128;
    KRange e_RB 4096 (2^47);
    KAlign e_RB 4096;
    KRange e_SZC 64 512;
    KRange e_NEW 512 4096;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 941792) 1 (ELit 1);
    KWord (SA (ELit 0) 941796) 4 e_K;
    KWord (SA e_TP (-88)) 8 e_TSDA;
    KWord (SA (EAlu ALU_ADD e_TSDA (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_K)) (ELit 29))) 0) 8 e_PT;
    KWord (SA e_PT 152) 8 e_T;
    KWord (SA e_T 2872) 8 e_mm1;
    KWr (SA e_T 2872) (ELit 8);
    KWord (SA e_T 2880) 8 e_mm2;
    KWr (SA e_T 2880) (ELit 8);
    KWr (SA e_RI 24) (ELit 8);
    KWord (SA e_RI 32) 8 (ELit 0);
    KWord (SA (EVar 2) 40) 8 (ELit 281840);
    KWord (SA (EVar 2) 32) 8 e_RI;
    KWord (SA (EVar 2) 24) 8 e_NEW;
    KWord (SA (EVar 2) 16) 8 e_RB;
    KWord (SA (EVar 2) 8) 8 e_NEW;
    KWr STK (ELit 1024) ].
Definition scr_pc1b : scripts := SCR [false; false] [] [].
Definition ss_pc1b := SS 0x428dc sr_pc1b [] kn_pc1b 43.
Definition RUN_pc1b := sym_exec SEGS 120 true [0x44d18] scr_pc1b ss_pc1b [].

Definition scr_ppc1b : scripts := SCR [false; false] [] [].
Definition RES_ppc1b := Eval vm_compute in sym_exec SEGS 120 true [0x44d18] scr_ppc1b ss_pc1b [].
Lemma RES_ppc1b_ok : sym_exec SEGS 120 true [0x44d18] scr_ppc1b (SS 0x428dc sr_pc1b [] kn_pc1b 43) [] = RES_ppc1b.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pc1b.

Module AXF_pc1bz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section PC1B.
Context {fx : FPState}.

Definition VALS_pc1b (RI RB SZC NEW TP K TSDA PT T mm1 mm2 : Z) : list Z := [RI; RB; SZC; NEW; TP; K; TSDA; PT; T; mm1; mm2].

Record pc1b_pre (regs : bvmap 5 word) (m : word -> option byte) (RI RB SZC NEW TP K TSDA PT T mm1 mm2 : Z) : Prop := {
  pc1b_R4 : getr regs 4 = wa TP ;
  pc1b_R8 : getr regs 8 = wa 262144 ;
  pc1b_R9 : getr regs 9 = wa (RB + 3758096384) ;
  pc1b_R18 : getr regs 18 = wa 262144 ;
  pc1b_R19 : getr regs 19 = wa RI ;
  pc1b_R20 : getr regs 20 = wa 262144 ;
  pc1b_R21 : getr regs 21 = wa SZC ;
  pc1b_R22 : getr regs 22 = wa 929816 ;
  pc1b_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pc1b_rng_RI : 1 <= RI <= 2^47 ;
  pc1b_rng_RB : 4096 <= RB <= 2^47 ;
  pc1b_rng_SZC : 64 <= SZC <= 512 ;
  pc1b_rng_NEW : 512 <= NEW <= 4096 ;
  pc1b_rng_TP : 4096 <= TP <= 2^47 ;
  pc1b_rng_K : 0 <= K <= 1023 ;
  pc1b_rng_TSDA : 1 <= TSDA <= 2^47 ;
  pc1b_rng_PT : 1 <= PT <= 2^47 ;
  pc1b_rng_T : 1 <= T <= 2^47 ;
  pc1b_rng_mm1 : 0 <= mm1 <= 2^64-1 ;
  pc1b_rng_mm2 : 0 <= mm2 <= 2^64-1 ;
  pc1b_ka1 : RI mod 128 = 0 ;
  pc1b_ka3 : RB mod 4096 = 0 ;
  pc1b_kr6 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pc1b_kw7 : rdn SEGS m (wa (0 + 941792)) 1 = Some (word_to_le_bytes 1 (wa 1)) ;
  pc1b_kw8 : rdn SEGS m (wa (0 + 941796)) 4 = Some (word_to_le_bytes 4 (wa K)) ;
  pc1b_kw9 : rdn SEGS m (wa (TP + -88)) 8 = Some (word_to_le_bytes 8 (wa TSDA)) ;
  pc1b_kw10 : rdn SEGS m (wa (TSDA + Z.shiftr (((4294967296 * ext_Z true 0 4 K)) mod 2^64) 29 + 0)) 8 = Some (word_to_le_bytes 8 (wa PT)) ;
  pc1b_kw11 : rdn SEGS m (wa (PT + 152)) 8 = Some (word_to_le_bytes 8 (wa T)) ;
  pc1b_kw12 : rdn SEGS m (wa (T + 2872)) 8 = Some (word_to_le_bytes 8 (wa mm1)) ;
  pc1b_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2872 + d)) k = true ;
  pc1b_kw14 : rdn SEGS m (wa (T + 2880)) 8 = Some (word_to_le_bytes 8 (wa mm2)) ;
  pc1b_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (T + 2880 + d)) k = true ;
  pc1b_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 24 + d)) k = true ;
  pc1b_kw17 : rdn SEGS m (wa (RI + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc1b_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa 281840)) ;
  pc1b_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa RI)) ;
  pc1b_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa NEW)) ;
  pc1b_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa RB)) ;
  pc1b_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa NEW))
}.


#[using="Type"] Lemma pc1b_setup : forall regs m RI RB SZC NEW TP K TSDA PT T mm1 mm2, pc1b_pre regs m RI RB SZC NEW TP K TSDA PT T mm1 mm2 ->
  regs_ok (Ez regs (VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)) AXF_pc1b.sr_pc1b regs /\ know_ok SEGS (Ez regs (VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)) m AXF_pc1b.kn_pc1b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m RI RB SZC NEW TP K TSDA PT T mm1 mm2 P. destruct P as [pc1b_R4 pc1b_R8 pc1b_R9 pc1b_R18 pc1b_R19 pc1b_R20 pc1b_R21 pc1b_R22 pc1b_HSTK pc1b_rng_RI pc1b_rng_RB pc1b_rng_SZC pc1b_rng_NEW pc1b_rng_TP pc1b_rng_K pc1b_rng_TSDA pc1b_rng_PT pc1b_rng_T pc1b_rng_mm1 pc1b_rng_mm2 pc1b_ka1 pc1b_ka3 pc1b_kr6 pc1b_kw7 pc1b_kw8 pc1b_kw9 pc1b_kw10 pc1b_kw11 pc1b_kw12 pc1b_kwr13 pc1b_kw14 pc1b_kwr15 pc1b_kwr16 pc1b_kw17 pc1b_kw18 pc1b_kw19 pc1b_kw20 pc1b_kw21 pc1b_kw22].
  set (E := Ez regs (VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)).
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = SZC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  split.
  { unfold AXF_pc1b.sr_pc1b.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 4); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite pc1b_R4. reflexivity.
    - rewrite pc1b_R8. reflexivity.
    - rewrite pc1b_R9, zeval_sound. cbn [zeval edenot AXF_pc1b.e_RI AXF_pc1b.e_RB AXF_pc1b.e_SZC AXF_pc1b.e_NEW AXF_pc1b.e_TP AXF_pc1b.e_K AXF_pc1b.e_TSDA AXF_pc1b.e_PT AXF_pc1b.e_T AXF_pc1b.e_mm1 AXF_pc1b.e_mm2 AXF_pc1b.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite pc1b_R18. reflexivity.
    - rewrite pc1b_R19. reflexivity.
    - rewrite pc1b_R20. reflexivity.
    - rewrite pc1b_R21. reflexivity.
    - rewrite pc1b_R22. reflexivity. }
  unfold know_ok, AXF_pc1b.kn_pc1b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pc1b.e_RI AXF_pc1b.e_RB AXF_pc1b.e_SZC AXF_pc1b.e_NEW AXF_pc1b.e_TP AXF_pc1b.e_K AXF_pc1b.e_TSDA AXF_pc1b.e_PT AXF_pc1b.e_T AXF_pc1b.e_mm1 AXF_pc1b.e_mm2 AXF_pc1b.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range RI _ _ pc1b_rng_RI eq_refl eq_refl), ?(mod64_of_range RB _ _ pc1b_rng_RB eq_refl eq_refl), ?(mod64_of_range SZC _ _ pc1b_rng_SZC eq_refl eq_refl), ?(mod64_of_range NEW _ _ pc1b_rng_NEW eq_refl eq_refl), ?(mod64_of_range TP _ _ pc1b_rng_TP eq_refl eq_refl), ?(mod64_of_range K _ _ pc1b_rng_K eq_refl eq_refl), ?(mod64_of_range TSDA _ _ pc1b_rng_TSDA eq_refl eq_refl), ?(mod64_of_range PT _ _ pc1b_rng_PT eq_refl eq_refl), ?(mod64_of_range T _ _ pc1b_rng_T eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pc1b_kwr13 | apply pc1b_kwr15 | apply pc1b_kwr16]; assumption).
  all: try (clear - pc1b_rng_RI pc1b_rng_RB pc1b_rng_SZC pc1b_rng_NEW pc1b_rng_TP pc1b_rng_K pc1b_rng_TSDA pc1b_rng_PT pc1b_rng_T pc1b_rng_mm1 pc1b_rng_mm2 pc1b_ka1 pc1b_ka3 pc1b_kr6 HKO; lia).
  all: first [lia].
Qed.


Definition pc1b_mem_ppc1b (m : word -> option byte) (regs : bvmap 5 word) (RI RB SZC NEW TP K TSDA PT T mm1 mm2 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 272608))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa 436880))) (wa (T + 2872)) (word_to_le_bytes 8 (wa (mm1 + 1)))) (wa (T + 2880)) (word_to_le_bytes 8 (wa (mm2 + 262144)))) (wa (RI + 24)) (word_to_le_bytes 8 (wa 262144)).

#[using="Type"] Theorem pc1b_ppc1b : forall regs m rom RI RB SZC NEW TP K TSDA PT T mm1 mm2, pc1b_pre regs m RI RB SZC NEW TP K TSDA PT T mm1 mm2 ->
  scs_denot SEGS m (Ez regs (VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)) (snd (fst AXF_pc1b.RES_ppc1b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x428dc) m rom) (mkst R (wa 0x44d18) (pc1b_mem_ppc1b m regs RI RB SZC NEW TP K TSDA PT T mm1 mm2) rom) /\
    getr R 1 = wa 281840 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48) /\ getr R 4 = wa TP /\ getr R 8 = wa RI /\ getr R 9 = wa (4 * NEW) /\ getr R 10 = wa 0 /\ getr R 11 = wa ((RB + (4 * NEW)) + 3758096384) /\ getr R 12 = wa 0 /\ getr R 13 = wa 0 /\ getr R 18 = wa RB /\ getr R 19 = wa NEW /\ getr R 20 = wa 262144 /\ getr R 21 = wa SZC /\ getr R 22 = wa 929816 /\ (forall k, In k [3; 5; 6; 7; 14; 15; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom RI RB SZC NEW TP K TSDA PT T mm1 mm2 P Hsc. destruct (pc1b_setup regs m RI RB SZC NEW TP K TSDA PT T mm1 mm2 P) as [HR HK].
  set (E := Ez regs (VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)) in *. destruct P as [pc1b_R4 pc1b_R8 pc1b_R9 pc1b_R18 pc1b_R19 pc1b_R20 pc1b_R21 pc1b_R22 pc1b_HSTK pc1b_rng_RI pc1b_rng_RB pc1b_rng_SZC pc1b_rng_NEW pc1b_rng_TP pc1b_rng_K pc1b_rng_TSDA pc1b_rng_PT pc1b_rng_T pc1b_rng_mm1 pc1b_rng_mm2 pc1b_ka1 pc1b_ka3 pc1b_kr6 pc1b_kw7 pc1b_kw8 pc1b_kw9 pc1b_kw10 pc1b_kw11 pc1b_kw12 pc1b_kwr13 pc1b_kw14 pc1b_kwr15 pc1b_kwr16 pc1b_kw17 pc1b_kw18 pc1b_kw19 pc1b_kw20 pc1b_kw21 pc1b_kw22].
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = RB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = SZC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = TP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = K) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = TSDA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PT) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = T) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = mm1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = mm2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HKO : Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K) by (rewrite ext_Z_lo32_small by lia; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^29) with 536870912; replace (4294967296 * K) with ((8 * K) * 536870912) by ring; apply Z.div_mul; lia).
  destruct (run_sound SEGS 120 [0x44d18] AXF_pc1b.scr_ppc1b 0x428dc AXF_pc1b.sr_pc1b AXF_pc1b.kn_pc1b 43 _ _ _ E m rom regs AXF_pc1b.RES_ppc1b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pc1b.RES_ppc1b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pc1b_mem_ppc1b m regs RI RB SZC NEW TP K TSDA PT T mm1 mm2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pc1b_mem_ppc1b. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End PC1B.
(* [comment removed for export] *)
End AXF_pc1bz.

Module AXF_pc2.
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

Definition e_RI := EVar 32.
Definition e_SZC := EVar 33.
Definition e_NEW := EVar 34.
Definition e_FA := EVar 35.
Definition e_REC16 := EVar 36.
Definition e_n := EVar 37.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pc2 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_RI)) 10 (e_NEW)) 19 (e_NEW)) 21 (e_SZC)).
Definition kn_pc2 : list kentry :=
  [ KRange e_RI 1 (2^47);
    KAlign e_RI 128;
    KRange e_SZC 64 512;
    KRange e_NEW 512 4096;
    KRange e_FA 4096 (2^47);
    KRange e_REC16 1 (2^47);
    KRange e_n 1 8;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA e_RI 16) 8 (ELit 0);
    KWr (SA e_RI 16) (ELit 8);
    KWord (SA e_RI 32) 8 (ELit 0);
    KWr (SA e_RI 32) (ELit 8);
    KWord (SA e_RI 48) 8 (ELit 262144);
    KWord (SA e_RI 40) 8 (ELit 0);
    KWord (SA e_RI 56) 8 (ELit 0);
    KWr (SA e_RI 68) (ELit 1);
    KWord (SA (EVar 2) 56) 8 (ELit 281360);
    KWord (SA (EVar 2) 48) 8 e_RI;
    KWord (SA (EVar 2) 40) 8 (ELit 929816);
    KWord (SA (EVar 2) 32) 8 (EAlu ALU_ADD e_RI (ELit 8));
    KWord (SA (EVar 2) 24) 8 (ELit 2305843009213693952);
    KWord (SA (EVar 2) 16) 8 e_FA;
    KWord (SA (EVar 2) 8) 8 e_REC16;
    KWord (SA (EVar 2) 0) 8 e_n;
    KWr STK (ELit 1024) ].
Definition scr_pc2 : scripts := SCR [false] [] [].
Definition ss_pc2 := SS 0x44d38 sr_pc2 [] kn_pc2 38.
Definition RUN_pc2 := sym_exec SEGS 80 true [0x449c8] scr_pc2 ss_pc2 [].

Definition scr_ppc2 : scripts := SCR [false] [] [].
Definition RES_ppc2 := Eval vm_compute in sym_exec SEGS 80 true [0x449c8] scr_ppc2 ss_pc2 [].
Lemma RES_ppc2_ok : sym_exec SEGS 80 true [0x449c8] scr_ppc2 (SS 0x44d38 sr_pc2 [] kn_pc2 38) [] = RES_ppc2.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pc2.

Module AXF_pc2z.
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

Section PC2.
Context {fx : FPState}.

Definition VALS_pc2 (RI SZC NEW FA REC16 n : Z) : list Z := [RI; SZC; NEW; FA; REC16; n].

Record pc2_pre (regs : bvmap 5 word) (m : word -> option byte) (RI SZC NEW FA REC16 n : Z) : Prop := {
  pc2_R8 : getr regs 8 = wa RI ;
  pc2_R10 : getr regs 10 = wa NEW ;
  pc2_R19 : getr regs 19 = wa NEW ;
  pc2_R21 : getr regs 21 = wa SZC ;
  pc2_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pc2_rng_RI : 1 <= RI <= 2^47 ;
  pc2_rng_SZC : 64 <= SZC <= 512 ;
  pc2_rng_NEW : 512 <= NEW <= 4096 ;
  pc2_rng_FA : 4096 <= FA <= 2^47 ;
  pc2_rng_REC16 : 1 <= REC16 <= 2^47 ;
  pc2_rng_n : 1 <= n <= 8 ;
  pc2_ka1 : RI mod 128 = 0 ;
  pc2_kr7 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pc2_kw8 : rdn SEGS m (wa (RI + 16)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc2_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 16 + d)) k = true ;
  pc2_kw10 : rdn SEGS m (wa (RI + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc2_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RI + 32 + d)) k = true ;
  pc2_kw12 : rdn SEGS m (wa (RI + 48)) 8 = Some (word_to_le_bytes 8 (wa 262144)) ;
  pc2_kw13 : rdn SEGS m (wa (RI + 40)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc2_kw14 : rdn SEGS m (wa (RI + 56)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  pc2_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (RI + 68 + d)) k = true ;
  pc2_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa 281360)) ;
  pc2_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa RI)) ;
  pc2_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa 929816)) ;
  pc2_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa (RI + 8))) ;
  pc2_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa 2305843009213693952)) ;
  pc2_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa FA)) ;
  pc2_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa REC16)) ;
  pc2_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa n))
}.


#[using="Type"] Lemma pc2_setup : forall regs m RI SZC NEW FA REC16 n, pc2_pre regs m RI SZC NEW FA REC16 n ->
  regs_ok (Ez regs (VALS_pc2 RI SZC NEW FA REC16 n)) AXF_pc2.sr_pc2 regs /\ know_ok SEGS (Ez regs (VALS_pc2 RI SZC NEW FA REC16 n)) m AXF_pc2.kn_pc2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m RI SZC NEW FA REC16 n P. destruct P as [pc2_R8 pc2_R10 pc2_R19 pc2_R21 pc2_HSTK pc2_rng_RI pc2_rng_SZC pc2_rng_NEW pc2_rng_FA pc2_rng_REC16 pc2_rng_n pc2_ka1 pc2_kr7 pc2_kw8 pc2_kwr9 pc2_kw10 pc2_kwr11 pc2_kw12 pc2_kw13 pc2_kw14 pc2_kwr15 pc2_kw16 pc2_kw17 pc2_kw18 pc2_kw19 pc2_kw20 pc2_kw21 pc2_kw22 pc2_kw23].
  set (E := Ez regs (VALS_pc2 RI SZC NEW FA REC16 n)).
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = FA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = REC16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_pc2.sr_pc2.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite pc2_R8. reflexivity.
    - rewrite pc2_R10. reflexivity.
    - rewrite pc2_R19. reflexivity.
    - rewrite pc2_R21. reflexivity. }
  unfold know_ok, AXF_pc2.kn_pc2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pc2.e_RI AXF_pc2.e_SZC AXF_pc2.e_NEW AXF_pc2.e_FA AXF_pc2.e_REC16 AXF_pc2.e_n AXF_pc2.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range RI _ _ pc2_rng_RI eq_refl eq_refl), ?(mod64_of_range SZC _ _ pc2_rng_SZC eq_refl eq_refl), ?(mod64_of_range NEW _ _ pc2_rng_NEW eq_refl eq_refl), ?(mod64_of_range FA _ _ pc2_rng_FA eq_refl eq_refl), ?(mod64_of_range REC16 _ _ pc2_rng_REC16 eq_refl eq_refl), ?(mod64_of_range n _ _ pc2_rng_n eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pc2_kwr9 | apply pc2_kwr11 | apply pc2_kwr15]; assumption).
  all: try (clear - pc2_rng_RI pc2_rng_SZC pc2_rng_NEW pc2_rng_FA pc2_rng_REC16 pc2_rng_n pc2_ka1 pc2_kr7; lia).
  all: first [lia].
Qed.


Definition pc2_mem_ppc2 (m : word -> option byte) (regs : bvmap 5 word) (RI SZC NEW FA REC16 n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (RI + 16)) (word_to_le_bytes 8 (wa NEW))) (wa (RI + 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + (NEW * SZC))))) (wa (RI + 68)) (word_to_le_bytes 1 (wa 0))) (wa (RI + 16)) (word_to_le_bytes 8 (wa (NEW + (-1 * n)))).

#[using="Type"] Theorem pc2_ppc2 : forall regs m rom RI SZC NEW FA REC16 n, pc2_pre regs m RI SZC NEW FA REC16 n ->
  scs_denot SEGS m (Ez regs (VALS_pc2 RI SZC NEW FA REC16 n)) (snd (fst AXF_pc2.RES_ppc2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44d38) m rom) (mkst R (wa 0x449c8) (pc2_mem_ppc2 m regs RI SZC NEW FA REC16 n) rom) /\
    getr R 1 = wa 281360 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64) /\ getr R 8 = wa RI /\ getr R 9 = wa 929816 /\ getr R 10 = wa (RI + 8) /\ getr R 11 = wa (REC16 + (4 * n)) /\ getr R 13 = wa REC16 /\ getr R 14 = wa n /\ getr R 15 = wa ((4 * NEW) + (-4 * n)) /\ getr R 18 = wa (RI + 8) /\ getr R 19 = wa 2305843009213693952 /\ getr R 20 = wa ((4 * NEW) + (FA + (-4 * n))) /\ getr R 21 = wa REC16 /\ getr R 22 = wa n /\ (forall k, In k [3; 4; 5; 6; 7; 12; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom RI SZC NEW FA REC16 n P Hsc. destruct (pc2_setup regs m RI SZC NEW FA REC16 n P) as [HR HK].
  set (E := Ez regs (VALS_pc2 RI SZC NEW FA REC16 n)) in *. destruct P as [pc2_R8 pc2_R10 pc2_R19 pc2_R21 pc2_HSTK pc2_rng_RI pc2_rng_SZC pc2_rng_NEW pc2_rng_FA pc2_rng_REC16 pc2_rng_n pc2_ka1 pc2_kr7 pc2_kw8 pc2_kwr9 pc2_kw10 pc2_kwr11 pc2_kw12 pc2_kw13 pc2_kw14 pc2_kwr15 pc2_kw16 pc2_kw17 pc2_kw18 pc2_kw19 pc2_kw20 pc2_kw21 pc2_kw22 pc2_kw23].
  assert (Z32 : bv_unsigned (ev E 32) = RI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = NEW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = FA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = REC16) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 80 [0x449c8] AXF_pc2.scr_ppc2 0x44d38 AXF_pc2.sr_pc2 AXF_pc2.kn_pc2 38 _ _ _ E m rom regs AXF_pc2.RES_ppc2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pc2.RES_ppc2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pc2_mem_ppc2 m regs RI SZC NEW FA REC16 n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pc2_mem_ppc2. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PC2.
(* [comment removed for export] *)
End AXF_pc2z.

Module AXG_nfsc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits.AxScChk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac zat R := repeat match goal with |- context [bv_unsigned (ev (Ez R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia
              end end.
(* [comment removed for export] *)
Lemma hko : forall K, 0 <= K <= 1023 -> Z.shiftr ((4294967296 * ext_Z true 0 4 K) mod 2^64) 29 = 8 * K.
Proof.
  intros K H. rewrite ext_Z_lo32_small by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^29) with 536870912.
  replace (4294967296 * K) with ((8 * K) * 536870912) by ring. apply Z.div_mul. lia.
Qed.
Lemma shr18 : forall x, 0 <= x < 2^18 -> Z.shiftr x 18 = 0.
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Definition B47 : iv := (4194304, 2^47).
(* [comment removed for export] *)
Ltac fact_go R HSPa HX HH :=
  try unfold rf_ok; try unfold df_ok; try unfold B47; cbn [fst snd zeval edenot]; zat R; rewrite ?HSPa, ?HX; zlh HH.
Ltac facts_go R HSPa HX HH := repeat (first [apply Forall_nil | apply Forall_cons; [fact_go R HSPa HX HH|]]).
(* [comment removed for export] *)
Ltac sc_refl rf df R HSPa HX HH :=
  apply (scs_chk_sound rf df); [ facts_go R HSPa HX HH | facts_go R HSPa HX HH | vm_compute; reflexivity ].

Section SCF.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).

(* [comment removed for export] *)
#[using="Type"] Lemma sc_nri : forall SPa CA ND, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  33 <= ND <= 512 /\ 4194304 <= CA /\ CA + 4096 + 256 <= SPa /\ SPa <= 2^47 ->
  scs_denot SEGS m (Ez R (AXF_nriz.VALS_nri CA ND)) (snd (fst AXF_nri.RES_pnri)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa CA ND HSPa HH. unfold AXF_nriz.VALS_nri.
  sc_refl [(EVar 2, B47); (EVar 32, B47); (EVar 33, (33, 512))] [(EVar 2, EVar 32, 4352)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma sc_ng0p : forall SPa CA ND n SB RIB, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  33 <= ND <= 512 /\ 1 <= n <= 8 /\ 4194304 <= CA /\ CA + 4096 + 512 <= SPa /\ SPa <= 2^47 /\ 4194304 <= SB /\ RIB = SB + 137438953472 /\
  SB + 137438953472 + 4096 + 512 <= SPa /\ (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) ->
  scs_denot SEGS m (Ez R (AXF_ng0pz.VALS_ng0p CA ND n SB RIB)) (snd (fst AXF_ng0p.RES_png0p)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa CA ND n SB RIB HSPa HH. unfold AXF_ng0pz.VALS_ng0p.
  assert (HD : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by tauto.
  destruct HD as [HD|HD]; assert (HH2 := conj HD HH); clear HH HD.
  - sc_refl [(EVar 2, B47); (EVar 32, B47); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH2.
  - sc_refl [(EVar 2, B47); (EVar 32, B47); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 32, EVar 35, 137438957568); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH2.
Qed.
End SCF.

Section SCM.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
(* [comment removed for export] *)
#[using="Type"] Lemma sc_mf0 : forall SPa AD SZ NM CF, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  2^46 <= SPa <= 2^47 /\ 4096 <= CF /\ CF + 4096 <= 2^30 ->
  scs_denot SEGS m (Ez R (AXF_mf0z.VALS_mf0 AD SZ NM CF)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXF_mf0z.AXF_mf0.RES_pmf0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa AD SZ NM CF HSPa HH. unfold AXF_mf0z.VALS_mf0.
  sc_refl [(EVar 2, (2^46, 2^47)); (EVar 35, (4096, 2^30 - 4096))] (@nil dfact) R HSPa HSPa HH.
Qed.
#[using="Type"] Lemma sc_mf1 : forall SPa AD SZ CF RA0 S0 S1 S2 S3 S4, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  2^46 <= SPa <= 2^47 /\ 4096 <= CF /\ CF + 4096 <= 2^30 ->
  scs_denot SEGS m (Ez R (AXF_mf1z.VALS_mf1 AD SZ CF RA0 S0 S1 S2 S3 S4)) (snd (fst AXF_mf1.RES_pmf1)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa AD SZ CF RA0 S0 S1 S2 S3 S4 HSPa HH. unfold AXF_mf1z.VALS_mf1.
  sc_refl [(EVar 2, (2^46, 2^47)); (EVar 34, (4096, 2^30 - 4096))] (@nil dfact) R HSPa HSPa HH.
Qed.
End SCM.

Section SCP.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
(* [comment removed for export] *)
Definition objs_ok (SPa T RI TP TSDA PT : Z) : Prop :=
  2^46 <= SPa <= 2^47 /\ 4194304 <= T /\ T + 4096 <= SPa - 256 /\ 4194304 <= RI /\ RI + 128 <= SPa - 256 /\ (RI + 128 <= T \/ T + 4096 <= RI) /\
  4096 <= TP /\ TP <= SPa - 256 /\ 1 <= TSDA /\ TSDA + 8192 <= SPa - 256 /\ 1 <= PT /\ PT + 160 <= SPa - 256.
#[using="Type"] Lemma sc_pb2 : forall SPa CA RI RB SZC TP K TSDA PT T mm1 mm2 st2, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  objs_ok SPa T RI TP TSDA PT -> CA = T + 208 -> 0 <= K <= 1023 ->
  scs_denot SEGS m (Ez R (AXF_pb2z.VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) (snd (fst AXF_pb2.RES_ppb2)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 HSPa HO HCA HK. unfold objs_ok in HO. unfold AXF_pb2z.VALS_pb2.
  assert (HD : RI + 128 <= T \/ T + 4096 <= RI) by tauto.
  destruct HD as [HD|HD]; assert (HH := conj HD (conj HK (conj HCA HO))); clear HO HCA HK HD.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 33, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, B47)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
             (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 40, EVar 33, 128); (EVar 32, EVar 33, 336)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 33, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, B47)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
             (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 33, EVar 40, 4096); (EVar 33, EVar 32, 3888)] R HSPa HSPa HH.
Qed.
#[using="Type"] Lemma sc_pc1b : forall SPa RI RB SZC NEW TP K TSDA PT T mm1 mm2, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  objs_ok SPa T RI TP TSDA PT -> 0 <= K <= 1023 ->
  scs_denot SEGS m (Ez R (AXF_pc1bz.VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)) (snd (fst AXF_pc1b.RES_ppc1b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa RI RB SZC NEW TP K TSDA PT T mm1 mm2 HSPa HO HK. unfold objs_ok in HO. unfold AXF_pc1bz.VALS_pc1b.
  assert (HD : RI + 128 <= T \/ T + 4096 <= RI) by tauto.
  destruct HD as [HD|HD]; assert (HH := conj HD (conj HK HO)); clear HO HK HD.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, B47)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 40, EVar 32, 128)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, B47)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 32, EVar 40, 4096)] R HSPa HSPa HH.
Qed.
#[using="Type"] Lemma sc_pc2 : forall SPa RI SZC NEW FA REC16 n, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa -> bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 13))) = 0 ->
  2^46 <= SPa <= 2^47 /\ 4194304 <= RI /\ RI + 128 <= SPa - 256 /\ NEW * SZC <= 262144 /\ 64 <= SZC <= 512 /\ 512 <= NEW <= 4096 ->
  scs_denot SEGS m (Ez R (AXF_pc2z.VALS_pc2 RI SZC NEW FA REC16 n)) (snd (fst AXF_pc2.RES_ppc2)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa RI SZC NEW FA REC16 n HSPa HX HH. unfold AXF_pc2z.VALS_pc2.
  sc_refl [(EVar 2, (2^46, 2^47)); (EVar 13, (0,0)); (EVar 32, B47); (EVar 33, (64, 512)); (EVar 34, (512, 4096));
           (EMd M_MUL (EVar 34) (EVar 33), (0, 262144)); (EMd M_MUL (EVar 33) (EVar 34), (0, 262144))]
          [(EVar 2, EVar 32, 384)] R HSPa HX HH.
Qed.
End SCP.
(* [comment removed for export] *)
End AXG_nfsc.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfsc.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.

Module AXG_nfscp.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits.AxScChk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac zat R := repeat match goal with |- context [bv_unsigned (ev (Ez R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia
              end end.
Ltac fact_go R HSPa HX HH :=
  try unfold rf_ok; try unfold df_ok; try unfold LOW; try unfold HIGH; try unfold B47; cbn [fst snd zeval edenot]; zat R; rewrite ?HSPa, ?HX; zlh HH.
Ltac facts_go R HSPa HX HH := repeat (first [apply Forall_nil | apply Forall_cons; [fact_go R HSPa HX HH|]]).
Ltac sc_refl rf df R HSPa HX HH :=
  apply (scs_chk_sound rf df); [ facts_go R HSPa HX HH | facts_go R HSPa HX HH | vm_compute; reflexivity ].
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_place (T : Z) : Prop := (4096 <= T /\ T + 4096 <= 65536) \/ 6537216 <= T.
Definition TLOW : iv := (4096, 61440).
Definition THIGH : iv := (6537216, 2^47).
Ltac fact_go R HSPa HX HH ::=
  try unfold rf_ok; try unfold df_ok; try unfold LOW; try unfold HIGH; try unfold TLOW; try unfold THIGH; try unfold B47; cbn [fst snd zeval edenot]; zat R; rewrite ?HSPa, ?HX; zlh HH.

Section SCF.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).

(* [comment removed for export] *)
#[using="Type"] Lemma sc_nri_p : forall SPa CA ND, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  33 <= ND <= 512 /\ ca_place CA /\ CA + 4096 + 256 <= SPa /\ 2^46 <= SPa <= 2^47 ->
  scs_denot SEGS m (Ez R (AXF_nriz.VALS_nri CA ND)) (snd (fst AXF_nri.RES_pnri)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa CA ND HSPa HH0. unfold AXF_nriz.VALS_nri. destruct HH0 as (H1 & HP & H2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj H1 H2)).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512))] [(EVar 2, EVar 32, 4352)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512))] [(EVar 2, EVar 32, 4352)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma sc_ng0p_p : forall SPa CA ND n SB RIB, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  33 <= ND <= 512 /\ 1 <= n <= 8 /\ ca_place CA /\ CA + 4096 + 512 <= SPa /\ 2^46 <= SPa <= 2^47 /\ 4194304 <= SB /\ RIB = SB + 137438953472 /\
  SB + 137438953472 + 4096 + 512 <= SPa /\ (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) ->
  scs_denot SEGS m (Ez R (AXF_ng0pz.VALS_ng0p CA ND n SB RIB)) (snd (fst AXF_ng0p.RES_png0p)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa CA ND n SB RIB HSPa HH0. unfold AXF_ng0pz.VALS_ng0p.
  destruct HH0 as (H1 & H2 & HP & H3 & H4 & H5 & H6 & H7 & HD). unfold ca_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 H7))))))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
            [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
             (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HD (conj HP (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 H7)))))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
              [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
               (EVar 35, EVar 32, 2592); (EVar 36, EVar 32, 137438956064)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 35, B47); (EVar 36, B47)]
              [(EVar 2, EVar 32, 4608); (EVar 36, EVar 35, 137438953472); (EVar 35, EVar 36, -137438953472); (EVar 2, EVar 36, 4608);
               (EVar 32, EVar 35, 137438957568); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
End SCF.

Section SCP.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
(* [comment removed for export] *)
Definition objs_ok_p (SPa T RI TP TSDA PT : Z) : Prop :=
  2^46 <= SPa <= 2^47 /\ t_place T /\ T + 4096 <= SPa - 256 /\ 4194304 <= RI /\ RI + 128 <= SPa - 256 /\ (RI + 128 <= T \/ T + 4096 <= RI) /\
  4096 <= TP /\ TP <= SPa - 256 /\ 1 <= TSDA /\ TSDA + 8192 <= SPa - 256 /\ 1 <= PT /\ PT + 160 <= SPa - 256.
#[using="Type"] Lemma sc_pb2_p : forall SPa CA RI RB SZC TP K TSDA PT T mm1 mm2 st2, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  objs_ok_p SPa T RI TP TSDA PT -> CA = T + 208 -> 0 <= K <= 1023 ->
  scs_denot SEGS m (Ez R (AXF_pb2z.VALS_pb2 CA RI RB SZC TP K TSDA PT T mm1 mm2 st2)) (snd (fst AXF_pb2.RES_ppb2)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa CA RI RB SZC TP K TSDA PT T mm1 mm2 st2 HSPa HO HCA HK. unfold objs_ok_p in HO. unfold AXF_pb2z.VALS_pb2.
  destruct HO as (O1 & HP & O2 & O3 & O4 & HD & O5). unfold t_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj HK (conj HCA (conj O1 (conj O2 (conj O3 (conj O4 O5))))))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, TLOW)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
             (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 33, EVar 40, 4096); (EVar 33, EVar 32, 3888)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HD (conj HP (conj HK (conj HCA (conj O1 (conj O2 (conj O3 (conj O4 O5)))))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
              [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
               (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 40, EVar 33, 128); (EVar 32, EVar 33, 336)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
              [(EVar 2, EVar 40, 4352); (EVar 2, EVar 33, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416);
               (EVar 32, EVar 40, 208); (EVar 40, EVar 32, -208); (EVar 2, EVar 32, 4144); (EVar 33, EVar 40, 4096); (EVar 33, EVar 32, 3888)] R HSPa HSPa HH.
Qed.
#[using="Type"] Lemma sc_pc1b_p : forall SPa RI RB SZC NEW TP K TSDA PT T mm1 mm2, bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa ->
  objs_ok_p SPa T RI TP TSDA PT -> 0 <= K <= 1023 ->
  scs_denot SEGS m (Ez R (AXF_pc1bz.VALS_pc1b RI RB SZC NEW TP K TSDA PT T mm1 mm2)) (snd (fst AXF_pc1b.RES_ppc1b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros SPa RI RB SZC NEW TP K TSDA PT T mm1 mm2 HSPa HO HK. unfold objs_ok_p in HO. unfold AXF_pc1bz.VALS_pc1b.
  destruct HO as (O1 & HP & O2 & O3 & O4 & HD & O5). unfold t_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj HK (conj O1 (conj O2 (conj O3 (conj O4 O5)))))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, TLOW)]
            [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 32, EVar 40, 4096)] R HSPa HSPa HH.
  - destruct HD as [HD|HD]; assert (HH := conj HD (conj HP (conj HK (conj O1 (conj O2 (conj O3 (conj O4 O5))))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
              [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 40, EVar 32, 128)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, B47); (EVar 36, (4096, 2^47)); (EVar 37, (0,1023)); (EVar 38, (1, 2^47)); (EVar 39, (1, 2^47)); (EVar 40, THIGH)]
              [(EVar 2, EVar 40, 4352); (EVar 2, EVar 32, 384); (EVar 2, EVar 36, 256); (EVar 2, EVar 38, 8448); (EVar 2, EVar 39, 416); (EVar 32, EVar 40, 4096)] R HSPa HSPa HH.
Qed.
End SCP.
(* [comment removed for export] *)
End AXG_nfscp.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.

Module AXF_nri2.
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
Definition sr_nri2 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (REC)) 10 (e_CA)) 12 (ELit 929816)) 14 (CC)).
Definition kn_nri2 : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KWord (SA REC 4) 4 e_mc ].
Definition scr_nri2 : scripts := SCR [] [] [].
Definition ss_nri2 := SS 0x4484c sr_nri2 [] kn_nri2 35.
Definition RUN_nri2 := sym_exec SEGS 40 true [0x44790] scr_nri2 ss_nri2 [].

Definition scr_pnri2 : scripts := SCR [] [] [].
Definition RES_pnri2 := Eval vm_compute in sym_exec SEGS 40 true [0x44790] scr_pnri2 ss_nri2 [].
Lemma RES_pnri2_ok : sym_exec SEGS 40 true [0x44790] scr_pnri2 (SS 0x4484c sr_nri2 [] kn_nri2 35) [] = RES_pnri2.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_nri2.


Module AXF_nri2z.
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

Section NRI2.
Context {fx : FPState}.

Definition VALS_nri2 (CA ND mc : Z) : list Z := [CA; ND; mc].

Record nri2_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND mc : Z) : Prop := {
  nri2_R8 : getr regs 8 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) ;
  nri2_R10 : getr regs 10 = wa CA ;
  nri2_R12 : getr regs 12 = wa 929816 ;
  nri2_R14 : getr regs 14 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) ;
  nri2_rng_CA : 1 <= CA <= 2^47 ;
  nri2_rng_ND : 33 <= ND <= 512 ;
  nri2_rng_mc : 2 <= mc <= 16 ;
  nri2_ka1 : CA mod 16 = 0 ;
  nri2_kw3 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 4)) 4 = Some (word_to_le_bytes 4 (wa mc))
}.


#[using="Type"] Lemma nri2_setup : forall regs m CA ND mc, nri2_pre regs m CA ND mc ->
  regs_ok (Ez regs (VALS_nri2 CA ND mc)) AXF_nri2.sr_nri2 regs /\ know_ok SEGS (Ez regs (VALS_nri2 CA ND mc)) m AXF_nri2.kn_nri2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND mc P. destruct P as [nri2_R8 nri2_R10 nri2_R12 nri2_R14 nri2_rng_CA nri2_rng_ND nri2_rng_mc nri2_ka1 nri2_kw3].
  set (E := Ez regs (VALS_nri2 CA ND mc)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_nri2.sr_nri2.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite nri2_R8, zeval_sound. cbn [zeval edenot AXF_nri2.e_CA AXF_nri2.e_ND AXF_nri2.e_mc AXF_nri2.CC AXF_nri2.REC]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite nri2_R10. reflexivity.
    - rewrite nri2_R12. reflexivity.
    - rewrite nri2_R14, zeval_sound. cbn [zeval edenot AXF_nri2.e_CA AXF_nri2.e_ND AXF_nri2.e_mc AXF_nri2.CC AXF_nri2.REC]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_nri2.kn_nri2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_nri2.e_CA AXF_nri2.e_ND AXF_nri2.e_mc AXF_nri2.CC AXF_nri2.REC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ nri2_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ nri2_rng_ND eq_refl eq_refl), ?(mod64_of_range mc _ _ nri2_rng_mc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nri2_rng_CA nri2_rng_ND nri2_rng_mc nri2_ka1 HC; lia).
  all: first [lia].
Qed.


Definition nri2_mem_pnri2 (m : word -> option byte) (regs : bvmap 5 word) (CA ND mc : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nri2_pnri2 : forall regs m rom CA ND mc, nri2_pre regs m CA ND mc ->
  scs_denot SEGS m (Ez regs (VALS_nri2 CA ND mc)) (snd (fst AXF_nri2.RES_pnri2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x4484c) m rom) (mkst R (wa 0x44790) (nri2_mem_pnri2 m regs CA ND mc) rom) /\
    getr R 8 = wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) /\ getr R 9 = wa (bv_unsigned (edenot (Ez regs (VALS_nri2 CA ND mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ getr R 10 = wa 929816 /\ getr R 11 = wa (CA + 2560) /\ getr R 12 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 13 = wa ((CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)) + 16) /\ getr R 14 = wa (bv_unsigned (edenot (Ez regs (VALS_nri2 CA ND mc)) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1)))) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND mc P Hsc. destruct (nri2_setup regs m CA ND mc P) as [HR HK].
  set (E := Ez regs (VALS_nri2 CA ND mc)) in *. destruct P as [nri2_R8 nri2_R10 nri2_R12 nri2_R14 nri2_rng_CA nri2_rng_ND nri2_rng_mc nri2_ka1 nri2_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 40 [0x44790] AXF_nri2.scr_pnri2 0x4484c AXF_nri2.sr_nri2 AXF_nri2.kn_nri2 35 _ _ _ E m rom regs AXF_nri2.RES_pnri2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nri2.RES_pnri2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nri2_mem_pnri2 m regs CA ND mc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nri2_mem_pnri2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    split; [first [zpost_reg HR' | (rewrite wa_u; srg HR'; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NRI2.
(* [comment removed for export] *)
End AXF_nri2z.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXF_mf0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)
Ltac lenq' := rewrite ?length_N_to_le_bytes; try change (Z.of_nat 4) with 4 in *; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 1) with 1 in *.
Lemma sub_add_lit : forall S a b, S - a + b = S + (b - a).
Proof. intros. ring. Qed.
Lemma u_rng' : forall w : word, 0 <= bv_unsigned w <= 2^64 - 1.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2^64) in H. lia. Qed.

(* [comment removed for export] *)
Definition L1a (c CA v1 v8 v9 v18 v19 v20 : Z) : list (Z * nat * Z) := [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220); (-48, 8%nat, v20); (-40, 8%nat, v19); (-32, 8%nat, v18); (-24, 8%nat, v9); (-16, 8%nat, v8); (-8, 8%nat, v1)].
Definition L2a (c CA n g21 g22 g23 g24 g25 g26 g27 : Z) : list (Z * nat * Z) := [(-184, 8%nat, g27); (-176, 8%nat, g26); (-168, 8%nat, g25); (-160, 8%nat, g24); (-152, 8%nat, g23); (-144, 8%nat, g22); (-136, 8%nat, g21); (-128, 8%nat, 929816); (-120, 8%nat, CA); (-112, 8%nat, 8); (-104, 8%nat, n); (-96, 8%nat, CA + 80 * c); (-88, 8%nat, 280468)].
Definition L3a (c CA n RI RB FA : Z) : list (Z * nat * Z) := [(-456, 8%nat, 32 * c); (-448, 8%nat, 1532192); (-440, 8%nat, 96426); (-432, 8%nat, RB); (-424, 8%nat, 1); (-416, 8%nat, 262144); (-408, 8%nat, 481756); (-400, 4%nat, 50); (-352, 8%nat, RB); (-344, 8%nat, 262144); (-336, 8%nat, RB); (-328, 8%nat, RB); (-320, 8%nat, 262144); (-312, 8%nat, 514992); (-304, 8%nat, RB); (-296, 8%nat, CA + 2560); (-288, 8%nat, RI); (-280, 8%nat, 281724); (-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, FA); (-248, 8%nat, 2305843009213693952); (-240, 8%nat, RI + 8); (-232, 8%nat, 929816); (-224, 8%nat, RI); (-216, 8%nat, 281360)].
Definition mAc (m : word -> option byte) (SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 : Z) : word -> option byte :=
  wchainS (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))
                  (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (L3a c CA n RI RB FA).

Lemma mc_tbl_rng : forall c, 2 <= c <= 16 -> 4 <= mc_tbl c <= 16 /\ mc_tbl c mod 2 = 0.
Proof.
  intros c H. assert (Hcs : c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16) by lia.
  repeat (destruct Hcs as [Hcs|Hcs]; [subst c; cbn; lia|]). subst c. cbn. lia.
Qed.
Lemma shr18' : forall x, 0 <= x < 2^18 -> Z.shiftr x 18 = 0.
Proof. intros x H. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Section SA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP sz0 st : Z).
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 929816.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hszst : 0 <= sz0 < 2^64 /\ 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 0.
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 sz0.
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis ISB : rd m 929848 8 SB.
Hypothesis IRIB : rd m 929864 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 929856 4 4294967295.
Hypothesis Iprem : rd m 929872 1 0.
Hypothesis Imu : rd m (SB + 137438953472 + 128 * c) 8 0.
Hypothesis Inf0 : rd m (SB + 137438953472 + 128 * c + 16) 8 0.
Hypothesis Iau : rd m (SB + 137438953472 + 128 * c + 32) 8 0.
Hypothesis Imapu : rd m (SB + 137438953472 + 128 * c + 48) 8 0.
Hypothesis Imeta : rd m (SB + 137438953472 + 128 * c + 56) 8 0.
Hypothesis Iwri : wr m (SB + 137438953472 + 128 * c) 128.
Hypothesis Igot : rd m 910448 8 1532192.
Hypothesis Ipsz : rd m 1532192 8 4096.
Hypothesis Icf : rd m 910464 8 1540520.
Hypothesis Idpm : rd m 1540780 1 0.

#[using="ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hszst Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem Imu Inf0 Iau Imapu Imeta Iwri Igot Ipsz Icf Idpm"] Lemma segA : exists R mA, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x73c38) mA rom) /\
  getr R (Z_to_bv 5 (Z.of_nat 1)) = wa 481784 /\ getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = wa (SB + 4294967296 * c) /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa 262144 /\ getr R (Z_to_bv 5 (Z.of_nat 12)) = wa 3 /\ getr R (Z_to_bv 5 (Z.of_nat 13)) = wa 50 /\
  getr R (Z_to_bv 5 (Z.of_nat 14)) = wa 18446744073709551615 /\ getr R (Z_to_bv 5 (Z.of_nat 15)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 17)) = wa 222 /\ getr R (Z_to_bv 5 (Z.of_nat 21)) = wa (32 * c) /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
  (forall k, In k [3; 4]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  mA = mAc m SP CA c (mc_tbl c / 2) (SB + 137438953472 + 128 * c) (SB + 4294967296 * c) (SB + 4294967296 * c + 3758096384)
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
         (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))).
Proof. LiaFast.lf_pins (fun (ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hszst Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem Imu Inf0 Iau Imapu Imeta Iwri Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  assert (HC5 : Z.shiftr ((ND + 31) mod 2^64) 5 = c) by (rewrite Hc; apply c_of_nd; exact HND).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 33 <= ND <= 512 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ 0 <= sz0 < 2^64 /\ 0 <= st < 2^64) by (clear - HCA HSB HSP Hcr5 HND HSEP Hszst; lia).
  clear HCA HSB HSP Hcr5 HSEP Hszst.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_pre regs m CA ND 0 sz0 SB st).
  { constructor; [exact H10 | exact H11 | exact H12 | exact H13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPa; (zlh HZ) | | | | | | ].
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [(zlh HZ) | exact HSTK].
    - rewrite HC5, Z.add_0_r. exact Icnt.
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. replace (CA + 80 * c + d) with (CA + (80 * c + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia.
    - rewrite HC5. exact Isz.
    - exact ISB.
    - exact Ist.
    - intros d k Hd Hk. replace (CA + 2576 + d) with (CA + (2576 + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_pnp0r regs m rom CA ND 0 sz0 SB st P0 (sc_np0r_p regs m SP CA ND SB HSPa ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) sz0 st))
    as (R1 & Hms1 & B2 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B18 & B19 & B20 & KK1).
  clear P0 B14 B15.
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_mem_pnp0r m regs CA ND 0 sz0 SB st) in *.
  assert (EM1 : m1 = wchainS m SP [(-48, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))); (-40, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))));
                                     (-32, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))); (-24, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))));
                                     (-16, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))); (-8, 8%nat, bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))]).
  { unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.np0r_mem_pnp0r. rewrite HSPa. reflexivity. }
  clearbody m1.
  assert (G1 : mem_grows m m1) by (rewrite EM1; apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. rewrite EM1. apply (wchainS_frame_in _ m SP (-48) 0); [(zlh HZ) | (zlh HZ) | vm_compute; reflexivity | vm_compute; reflexivity | exact Hx | rewrite Z.add_0_r; exact H]. }
  regzH B2. regzH B8. regzH B9. regzH B18. regzH B19. regzH B20.
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rewrite B2, HSPa, u_wa_small by (zlh HZ); ring).
  (* [comment removed for export] *)
  assert (P1 : AXF_nriz.nri_pre R1 m1 CA ND).
  { constructor; [exact B10 | exact B11 | exact B12 | exact B13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP1; (zlh HZ) | | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2, HSPa; f_equal; ring).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite HC5. apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m1 _ G1). replace (CA + 84 + d) with (CA + (84 + d)) by ring. apply Iwc; clear - HZ Hd Hk; lia. }
  destruct (AXF_nriz.nri_pnri R1 m1 rom CA ND P1 (sc_nri_p R1 m1 (SP - 48) CA ND HSP1 ltac:(unfold ca_place; (zlh HZ))))
    as (R2 & Hms2 & C1 & C2 & C5 & C6 & C7 & C8 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C28 & C29 & C30 & KK2).
  clear P1 C5 C6 C7 C15 C16 C17 C28 C29 C30.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms. clear Hms1 Hms2.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = c) by (rewrite B8, HC5, u_wa_small by (zlh HZ); reflexivity).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA + 80 * c) by (rewrite B9, HC5, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := AXF_nriz.nri_mem_pnri m1 R1 CA ND) in *.
  assert (EM2 : m2 = ic_mem (wchainS m1 SP [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]) CA).
  { unfold m2, AXF_nriz.nri_mem_pnri, ic_mem. rewrite HSP1, V18, V19, ?sub_add_lit. reflexivity. }
  clearbody m2.
  set (n := mc_tbl c / 2).
  destruct (mc_tbl_rng c ltac:((zlh HZ))) as [Hmc1 Hmc2].
  assert (Hn : 2 <= n <= 8 /\ mc_tbl c = 2 * n) by (unfold n; pose proof (Z.div_mod (mc_tbl c) 2 ltac:(lia)); lia).
  (* [comment removed for export] *)
  destruct (ic_rd (wchainS m1 SP [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]) CA c ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ))) as [Rmc Rsz].
  rewrite <- EM2 in Rmc, Rsz.
  assert (P2 : AXF_nri2z.nri2_pre R2 m2 CA ND (mc_tbl c)).
  { constructor; [exact C8 | exact C10 | exact C12 | exact C14 | (zlh HZ) | (zlh HZ) | (zlh Hmc1) | (zlh HZ) | rewrite HC5; exact Rmc]. }
  destruct (AXF_nri2z.nri2_pnri2 R2 m2 rom CA ND (mc_tbl c) P2 ltac:(cbn [AXF_nri2.RES_pnri2 fst snd]; constructor))
    as (R3 & Hms3 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & KK3).
  clear P2.
  assert (Em3 : AXF_nri2z.nri2_mem_pnri2 m2 R2 CA ND (mc_tbl c) = m2) by reflexivity. rewrite Em3 in Hms3. clear Em3.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms3) as Hms'. clear Hms Hms3. rename Hms' into Hms.
  assert (Vn : bv_unsigned (edenot (Ez R2 (AXF_nri2z.VALS_nri2 CA ND (mc_tbl c))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = n).
  { rewrite (srlw1 0 0 0 0 R2 (AXF_nri2z.VALS_nri2 CA ND (mc_tbl c)) (mc_tbl c) eq_refl ltac:(lia)). reflexivity. }
  rewrite Vn in D9, D14.
  regzH C2.
  assert (HSP3 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80).
  { rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1, u_wa_small by (zlh HZ); ring. }
  assert (G2 : mem_grows m m2).
  { rewrite EM2. set (L := [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)]).
    exact (mem_grows_trans m m1 (ic_mem (wchainS m1 SP L) CA) G1 (mem_grows_trans m1 (wchainS m1 SP L) (ic_mem (wchainS m1 SP L) CA) (wchainS_grows L m1 SP) (ic_grows (wchainS m1 SP L) CA))). }
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 4096) -> m2 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2. rewrite EM2, ic_frame by (clear - HZ Hx Q2; lia).
    rewrite (wchainS_frame_in [(-72, 8%nat, CA + 80 * c); (-64, 8%nat, c); (-56, 8%nat, 279220)] m1 SP (-72) (-48)); [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia]. apply F1; clear - HZ Hx Q1; lia. }
  (* [comment removed for export] *)
  assert (P3 : AXF_ng0pz.ng0p_pre R3 m2 CA ND n SB (SB + 137438953472)).
  { constructor; [exact D10 | exact D11 | exact D12 | exact D13 | exact D14
                 | (replace (getr R3 2) with (wa (SP - 80)) by (regzG; rewrite (KK3 2%nat ltac:(cbn; memb')), C2, HSP1; f_equal; ring);
                    apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh Hn) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                 | rewrite HSP3; (zlh HZ) | (zlh HZ) | (zlh HZ) | | | | | | | | | | ].
    all: try rewrite HC5, ?Z.add_0_r.
    all: first [ (apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | assumption])
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k m m2 _ G2); apply Iwri; clear - HZ Hd Hk; lia) ]. }
  destruct (AXF_ng0pz.ng0p_png0p R3 m2 rom CA ND n SB (SB + 137438953472) P3
              (sc_ng0p_p R3 m2 (SP - 80) CA ND n SB (SB + 137438953472) HSP3 ltac:(unfold ca_place; clear - HZ Hn; lia)))
    as (R4 & Hms4 & E1 & E2 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & KK4).
  clear P3 E5 E6 E7 E10 E14 E15 E16 E17 E23 E24 E25.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms4) as Hms'. clear Hms Hms4. rename Hms' into Hms.
  regzH D8. regzH D9.
  assert (V38 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite D8, HC5, u_wa_small by (zlh HZ); reflexivity).
  assert (V39 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 9))) = n) by (rewrite D9, u_wa_small by (zlh Hn); reflexivity).
  assert (V318 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) = 8) by (rewrite (KK3 18%nat ltac:(cbn; memb')), (KK2 18%nat ltac:(cbn; memb')), B18, u_wa_small by (zlh HZ); reflexivity).
  assert (V319 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) = CA) by (rewrite (KK3 19%nat ltac:(cbn; memb')), (KK2 19%nat ltac:(cbn; memb')), B19, u_wa_small by (zlh HZ); reflexivity).
  assert (V320 : bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) = 929816) by (rewrite (KK3 20%nat ltac:(cbn; memb')), (KK2 20%nat ltac:(cbn; memb')), B20, u_wa_small by (zlh HZ); reflexivity).
  assert (W21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = getr regs (Z_to_bv 5 (Z.of_nat 21))) by (rewrite (KK3 21%nat ltac:(cbn; memb')), (KK2 21%nat ltac:(cbn; memb')), (KK1 21%nat ltac:(cbn; memb')); reflexivity).
  assert (W22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK3 22%nat ltac:(cbn; memb')), (KK2 22%nat ltac:(cbn; memb')), (KK1 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R3 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK3 23%nat ltac:(cbn; memb')), (KK2 23%nat ltac:(cbn; memb')), (KK1 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R3 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK3 24%nat ltac:(cbn; memb')), (KK2 24%nat ltac:(cbn; memb')), (KK1 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R3 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK3 25%nat ltac:(cbn; memb')), (KK2 25%nat ltac:(cbn; memb')), (KK1 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R3 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK3 26%nat ltac:(cbn; memb')), (KK2 26%nat ltac:(cbn; memb')), (KK1 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R3 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK3 27%nat ltac:(cbn; memb')), (KK2 27%nat ltac:(cbn; memb')), (KK1 27%nat ltac:(cbn; memb')); reflexivity).
  set (m3 := AXF_ng0pz.ng0p_mem_png0p m2 R3 CA ND n SB (SB + 137438953472)) in *.
  assert (EM3 : m3 = wchainS (wbytes (wchainS m2 SP (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))))
                               (wa (SB + 137438953472 + 128 * c)) (word_to_le_bytes 8 (wa 1152921504606846976)))
                             SP [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 929816); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 281360)]).
  { unfold m3, AXF_ng0pz.ng0p_mem_png0p, L2a. rewrite HSP3, V38, V39, V318, V319, V320, W21, W22, W23, W24, W25, W26, W27, HC5, ?sub_add_lit, ?Z.add_0_r. reflexivity. }
  clearbody m3.
  assert (G3 : mem_grows m m3).
  { rewrite EM3. exact (mem_grows_trans _ _ _ G2 (mem_grows_trans _ _ _ (wchainS_grows (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP)
                          (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wchainS_grows _ _ SP)))). }
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 4096) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 8) ->
                  m3 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3. rewrite EM3.
    rewrite (wchainS_frame_in [(-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, SB + 4294967296 * c + 3758096384); (-248, 8%nat, 2305843009213693952);
                                 (-240, 8%nat, SB + 137438953472 + 128 * c + 8); (-232, 8%nat, 929816); (-224, 8%nat, SB + 137438953472 + 128 * c); (-216, 8%nat, 281360)] _ SP (-272) (-208));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    rewrite wb_other by first [exact Hx | (lenq'; clear - HZ Hn; lia) | (lenq'; clear - HZ Hn Q3; lia)].
    rewrite (wchainS_frame_in (L2a c CA n (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) m2 SP (-184) (-80));
      [| clear - HZ; lia | clear - HZ; lia | reflexivity | reflexivity | clear - Hx; lia | clear - HZ Q1; lia].
    apply F12; assumption. }
  (* [comment removed for export] *)
  regzH E2. regzH E8. regzH E9. regzH E11. regzH E12. regzH E13. regzH E18. regzH E19. regzH E20. regzH E21. regzH E22. regzH E1.
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 272) by (rewrite E2, HSP3, u_wa_small by (zlh HZ); ring).
  assert (Esz : 262144 * Z.shiftr ((32 * Z.shiftr ((ND + 31) mod 2^64) 5 * n + -1) mod 2^64) 18 + 262144 = 262144).
  { rewrite HC5. assert (64 <= 32 * c * n <= 4096) by (clear - HZ Hn; nia). rewrite Z.mod_small by lia. rewrite shr18' by lia. ring. }
  rewrite Esz in E12, E19.
  assert (P4 : AXF_mf0z.mf0_pre R4 m3 (SB + 4294967296 * c) 262144 96426 1540520).
  { constructor; [regzG; rewrite E11, HC5; reflexivity | regzG; exact E12 | regzG; exact E13
                 | (replace (getr R4 2) with (wa (SP - 272)) by (regzG; rewrite E2, HSP3; f_equal; ring);
                    apply (stk_ok_move m3 SP (SP - 272) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m3 (wa SP) 2048 G3 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)])
                 | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP4; (zlh HZ) | | | | ].
    all: apply (rd_frame m m3); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F13; clear - HZ Hx; lia | assumption]. }
  destruct (AXF_mf0z.mf0_pmf0 R4 m3 rom (SB + 4294967296 * c) 262144 96426 1540520 P4
              (sc_mf0 R4 m3 (SP - 272) (SB + 4294967296 * c) 262144 96426 1540520 HSP4 ltac:((zlh HZ))))
    as (R5 & Hms5 & F1' & F2' & F8 & F9 & F10 & F11 & F12' & F13' & F14 & F15 & F17 & F18 & F19 & F20 & KK5).
  clear P4.
  pose proof (msteps_trans SEGS _ _ _ Hms Hms5) as Hms'. clear Hms Hms5. rename Hms' into Hms.
  assert (EM4 : AXF_mf0z.mf0_mem_pmf0 m3 R4 (SB + 4294967296 * c) 262144 96426 1540520 =
                wchainS m3 SP [(-456, 8%nat, 32 * c); (-448, 8%nat, 1532192); (-440, 8%nat, 96426); (-432, 8%nat, SB + 4294967296 * c); (-424, 8%nat, 1);
                               (-416, 8%nat, 262144); (-408, 8%nat, 481756); (-400, 4%nat, 50); (-352, 8%nat, SB + 4294967296 * c); (-344, 8%nat, 262144);
                               (-336, 8%nat, SB + 4294967296 * c); (-328, 8%nat, SB + 4294967296 * c); (-320, 8%nat, 262144); (-312, 8%nat, 514992);
                               (-304, 8%nat, SB + 4294967296 * c); (-296, 8%nat, CA + 2560); (-288, 8%nat, SB + 137438953472 + 128 * c); (-280, 8%nat, 281724)]).
  { unfold AXF_mf0z.mf0_mem_pmf0. rewrite HSP4, E1, E8, E9, E18, E19, E20, E21, HC5, ?u_wa_small by (zlh HZ). rewrite ?sub_add_lit. reflexivity. }
  rewrite EM4 in Hms. clear EM4.
  eexists R5, _. split; [exact Hms|].
  split; [regzH F1'; exact F1'|]. split; [regzH F2'; rewrite F2', HSP4; f_equal; ring|].
  split; [regzH F8; exact F8|]. split; [regzH F10; exact F10|]. split; [regzH F11; exact F11|]. split; [regzH F12'; exact F12'|].
  split; [regzH F13'; exact F13'|]. split; [regzH F14; exact F14|]. split; [regzH F15; exact F15|]. split; [regzH F17; exact F17|].
  split; [rewrite (KK5 21%nat ltac:(cbn; memb')), E21, HC5; reflexivity|].
  split; [rewrite (KK5 22%nat ltac:(cbn; memb')); exact E22|].
  split; [intros k Hk; cbn in Hk; destruct Hk as [<-|[<-|[]]]; lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK3 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK1 k ltac:(cbn; memb')); reflexivity end|].
  rewrite EM3, EM2, EM1. unfold mAc, L3a. rewrite <- wchainS_app. unfold L1a. rewrite <- wchainS_app. reflexivity.
Qed.
End SA.
(* [comment removed for export] *)
