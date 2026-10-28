(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.GcFlush06.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0SumsMemset_code_b Ba0SumsMemset_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r60dd4_61420_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatPoisonRun_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma art_poison_hi0_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1366c8 0xc000 -> apart (sp - 64) 64 0x1d1768 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x7ab38 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0x129d04)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0x129d04 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_7a720 D_7a720.
  zsd F_7a724 D_7a724 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_7a728 D_7a728 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7a72c D_7a72c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7a730 D_7a730 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7a734 D_7a734 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_7a738 D_7a738 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_7a73c D_7a73c (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (L1 : art_layout Mf) by (unfold Mf; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
  assert (Cra : cellA Mf (sp - 8) 8 (U raw)) by (unfold Mf; do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs0 : cellA Mf (sp - 16) 8 (U (getr regs 8))) by (unfold Mf; do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs1 : cellA Mf (sp - 24) 8 (U (getr regs 9))) by (unfold Mf; do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs2 : cellA Mf (sp - 32) 8 (U (getr regs 18))) by (unfold Mf; do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs3 : cellA Mf (sp - 40) 8 (U (getr regs 19))) by (unfold Mf; do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs4 : cellA Mf (sp - 48) 8 (U (getr regs 20))) by (unfold Mf; do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs5 : cellA Mf (sp - 56) 8 (U (getr regs 21))) by (unfold Mf; apply cell_Wn_hit; lia).
  destruct L1 as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hp8' : p / 8 * 8 = p) by lia. assert (Hn8' : n / 8 * 8 = n) by lia.
  destruct (Z.eq_dec v 0) as [V0|V1].
  (* [comment removed for export] *)
  - zbtk F_7a740 D_7a740.
    stepn F_7a754 D_7a754. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a758 D_7a758.
  zstep F_7a75c D_7a75c.
  zld F_7a760 D_7a760 0x1374c0 G48.
  zld F_7a764 D_7a764 0x13fc38 Csb. unfold SB in *.
  zstep F_7a768 D_7a768. zstep F_7a76c D_7a76c. zstep F_7a770 D_7a770.
  zstep F_7a774 D_7a774.
  zbft F_7a778 D_7a778.
  zstep F_7a77c D_7a77c. zld F_7a780 D_7a780 0x1374c8 G50.
  zstep F_7a784 D_7a784. zld F_7a788 D_7a788 0x1374d0 G58.
  zld F_7a78c D_7a78c 0x140928 Cmb. zld F_7a790 D_7a790 0x140930 Cme.
  zstep F_7a794 D_7a794.
  zbtk F_7a798 D_7a798.
  zstep F_7a7a0 D_7a7a0. zld F_7a7a4 D_7a7a4 0x1374d8 G60. zld F_7a7a8 D_7a7a8 0x140920 Che.
  zstep F_7a7ac D_7a7ac.
  zstep F_7a7b0 D_7a7b0.
  zbft F_7a7b4 D_7a7b4.
  zbtk F_7a7b8 D_7a7b8.
  zld F_7a880 D_7a880 0x140920 Che.
  zstep F_7a884 D_7a884.
  zstep F_7a888 D_7a888.
  zbft F_7a88c D_7a88c.
  zbtk F_7a890 D_7a890.
  stepn F_7a950 D_7a950. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a954 D_7a954.
  zstep F_7a958 D_7a958. zstep F_7a95c D_7a95c.
  zbft F_7a960 D_7a960.
  zstep F_7a964 D_7a964. zld F_7a968 D_7a968 0x1374c8 G50.
  zstep F_7a96c D_7a96c. zld F_7a970 D_7a970 0x1374d0 G58.
  zld F_7a974 D_7a974 0x140928 Cmb. zld F_7a978 D_7a978 0x140930 Cme.
  zstep F_7a97c D_7a97c.
  zbtk F_7a980 D_7a980.
  zstep F_7a988 D_7a988. zld F_7a98c D_7a98c 0x1374d8 G60. zld F_7a990 D_7a990 0x140920 Che.
  zstep F_7a994 D_7a994.
  zstep F_7a998 D_7a998.
  zbft F_7a99c D_7a99c.
  zbft F_7a9a0 D_7a9a0.
  zstep F_7a9a4 D_7a9a4. zld F_7a9a8 D_7a9a8 0x1374e0 G68. zld F_7a9ac D_7a9ac 0x1394d0 Crm.
  zbft F_7a9b0 D_7a9b0.
  stepn F_7a9b4 D_7a9b4. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7a9b8 D_7a9b8. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7a9bc D_7a9bc. zstep F_7a9c0 D_7a9c0. zstep F_7a9c4 D_7a9c4.
    zbft F_7a9c8 D_7a9c8.
    zstep F_7a9cc D_7a9cc. zld F_7a9d0 D_7a9d0 0x1374b0 G38. zld F_7a9d4 D_7a9d4 (0x1d1768 + 120) Cth.
    zbtk F_7a9d8 D_7a9d8.
    zstep F_7aa88 D_7aa88. stepn F_7aa8c D_7aa8c.
  zstep F_7aa98 D_7aa98.
  zld F_7aa9c D_7aa9c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa0 D_7aaa0 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa4 D_7aaa4 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa8 D_7aaa8 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaac D_7aaac (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab0 D_7aab0 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab4 D_7aab4 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7aab8 D_7aab8.
  stepjr F_7aabc D_7aabc (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.
  (* [comment removed for export] *)
  - zbft F_7a740 D_7a740.
    zstep F_7a744 D_7a744.
    zlb F_7a748 D_7a748 0x13f49c Ccp.
    stepfence F_7a74c D_7a74c.
    zbft F_7a750 D_7a750.
    stepn F_7a754 D_7a754. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a758 D_7a758.
  zstep F_7a75c D_7a75c.
  zld F_7a760 D_7a760 0x1374c0 G48.
  zld F_7a764 D_7a764 0x13fc38 Csb. unfold SB in *.
  zstep F_7a768 D_7a768. zstep F_7a76c D_7a76c. zstep F_7a770 D_7a770.
  zstep F_7a774 D_7a774.
  zbft F_7a778 D_7a778.
  zstep F_7a77c D_7a77c. zld F_7a780 D_7a780 0x1374c8 G50.
  zstep F_7a784 D_7a784. zld F_7a788 D_7a788 0x1374d0 G58.
  zld F_7a78c D_7a78c 0x140928 Cmb. zld F_7a790 D_7a790 0x140930 Cme.
  zstep F_7a794 D_7a794.
  zbtk F_7a798 D_7a798.
  zstep F_7a7a0 D_7a7a0. zld F_7a7a4 D_7a7a4 0x1374d8 G60. zld F_7a7a8 D_7a7a8 0x140920 Che.
  zstep F_7a7ac D_7a7ac.
  zstep F_7a7b0 D_7a7b0.
  zbft F_7a7b4 D_7a7b4.
  zbtk F_7a7b8 D_7a7b8.
  zld F_7a880 D_7a880 0x140920 Che.
  zstep F_7a884 D_7a884.
  zstep F_7a888 D_7a888.
  zbft F_7a88c D_7a88c.
  zbtk F_7a890 D_7a890.
  stepn F_7a950 D_7a950. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a954 D_7a954.
  zstep F_7a958 D_7a958. zstep F_7a95c D_7a95c.
  zbft F_7a960 D_7a960.
  zstep F_7a964 D_7a964. zld F_7a968 D_7a968 0x1374c8 G50.
  zstep F_7a96c D_7a96c. zld F_7a970 D_7a970 0x1374d0 G58.
  zld F_7a974 D_7a974 0x140928 Cmb. zld F_7a978 D_7a978 0x140930 Cme.
  zstep F_7a97c D_7a97c.
  zbtk F_7a980 D_7a980.
  zstep F_7a988 D_7a988. zld F_7a98c D_7a98c 0x1374d8 G60. zld F_7a990 D_7a990 0x140920 Che.
  zstep F_7a994 D_7a994.
  zstep F_7a998 D_7a998.
  zbft F_7a99c D_7a99c.
  zbft F_7a9a0 D_7a9a0.
  zstep F_7a9a4 D_7a9a4. zld F_7a9a8 D_7a9a8 0x1374e0 G68. zld F_7a9ac D_7a9ac 0x1394d0 Crm.
  zbft F_7a9b0 D_7a9b0.
  stepn F_7a9b4 D_7a9b4. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7a9b8 D_7a9b8. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7a9bc D_7a9bc. zstep F_7a9c0 D_7a9c0. zstep F_7a9c4 D_7a9c4.
    zbtk F_7a9c8 D_7a9c8.
    zstep F_7aa88 D_7aa88. stepn F_7aa8c D_7aa8c.
  zstep F_7aa98 D_7aa98.
  zld F_7aa9c D_7aa9c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa0 D_7aaa0 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa4 D_7aaa4 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa8 D_7aaa8 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaac D_7aaac (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab0 D_7aab0 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab4 D_7aab4 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7aab8 D_7aab8.
  stepjr F_7aabc D_7aabc (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

#[using="Type"] Theorem art_poison_hi0_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1366c8 0xc000 -> apart (sp - 64) 64 0x1d1768 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7ab38 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr Wsh.
  pose proof (art_poison_hi0_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0x129d04 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  zsplit;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma art_poison_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1366c8 0xc000 -> apart (sp - 64) 64 0x1d1768 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x7ab38 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 raw) 2 (Z_to_bv 64 sp)) 6 (Z_to_bv 64 0x129d04)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8)))
             13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 (SB - 1))) 15 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
       (0x129d04 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  zstep F_7a720 D_7a720.
  zsd F_7a724 D_7a724 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_7a728 D_7a728 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7a72c D_7a72c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7a730 D_7a730 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7a734 D_7a734 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_7a738 D_7a738 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_7a73c D_7a73c (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (L1 : art_layout Mf) by (unfold Mf; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
  assert (Cra : cellA Mf (sp - 8) 8 (U raw)) by (unfold Mf; do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs0 : cellA Mf (sp - 16) 8 (U (getr regs 8))) by (unfold Mf; do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs1 : cellA Mf (sp - 24) 8 (U (getr regs 9))) by (unfold Mf; do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs2 : cellA Mf (sp - 32) 8 (U (getr regs 18))) by (unfold Mf; do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs3 : cellA Mf (sp - 40) 8 (U (getr regs 19))) by (unfold Mf; do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs4 : cellA Mf (sp - 48) 8 (U (getr regs 20))) by (unfold Mf; do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs5 : cellA Mf (sp - 56) 8 (U (getr regs 21))) by (unfold Mf; apply cell_Wn_hit; lia).
  destruct L1 as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hp8' : p / 8 * 8 = p) by lia. assert (Hn8' : n / 8 * 8 = n) by lia.
  destruct (Z.eq_dec v 0) as [V0|V1].
  - zbtk F_7a740 D_7a740.
    stepn F_7a754 D_7a754. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a758 D_7a758.
  zstep F_7a75c D_7a75c.
  zld F_7a760 D_7a760 0x1374c0 G48.
  zld F_7a764 D_7a764 0x13fc38 Csb. unfold SB in *.
  zstep F_7a768 D_7a768. zstep F_7a76c D_7a76c. zstep F_7a770 D_7a770.
  zstep F_7a774 D_7a774.
  zbtk F_7a778 D_7a778.
  stepn F_7a950 D_7a950. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a954 D_7a954.
  zstep F_7a958 D_7a958. zstep F_7a95c D_7a95c.
  zbtk F_7a960 D_7a960.
  zstep F_7a9a4 D_7a9a4. zld F_7a9a8 D_7a9a8 0x1374e0 G68. zld F_7a9ac D_7a9ac 0x1394d0 Crm.
  zbft F_7a9b0 D_7a9b0.
  stepn F_7a9b4 D_7a9b4. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7a9b8 D_7a9b8. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7a9bc D_7a9bc. zstep F_7a9c0 D_7a9c0. zstep F_7a9c4 D_7a9c4.
    zbft F_7a9c8 D_7a9c8.
    zstep F_7a9cc D_7a9cc. zld F_7a9d0 D_7a9d0 0x1374b0 G38. zld F_7a9d4 D_7a9d4 (0x1d1768 + 120) Cth.
    zbtk F_7a9d8 D_7a9d8.
    zstep F_7aa88 D_7aa88. stepn F_7aa8c D_7aa8c.
  zstep F_7aa98 D_7aa98.
  zld F_7aa9c D_7aa9c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa0 D_7aaa0 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa4 D_7aaa4 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa8 D_7aaa8 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaac D_7aaac (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab0 D_7aab0 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab4 D_7aab4 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7aab8 D_7aab8.
  stepjr F_7aabc D_7aabc (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. subst v. zret.
  - zbft F_7a740 D_7a740.
    zstep F_7a744 D_7a744.
    zlb F_7a748 D_7a748 0x13f49c Ccp.
    stepfence F_7a74c D_7a74c.
    zbft F_7a750 D_7a750.
    stepn F_7a754 D_7a754. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a758 D_7a758.
  zstep F_7a75c D_7a75c.
  zld F_7a760 D_7a760 0x1374c0 G48.
  zld F_7a764 D_7a764 0x13fc38 Csb. unfold SB in *.
  zstep F_7a768 D_7a768. zstep F_7a76c D_7a76c. zstep F_7a770 D_7a770.
  zstep F_7a774 D_7a774.
  zbtk F_7a778 D_7a778.
  stepn F_7a950 D_7a950. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7a954 D_7a954.
  zstep F_7a958 D_7a958. zstep F_7a95c D_7a95c.
  zbtk F_7a960 D_7a960.
  zstep F_7a9a4 D_7a9a4. zld F_7a9a8 D_7a9a8 0x1374e0 G68. zld F_7a9ac D_7a9ac 0x1394d0 Crm.
  zbft F_7a9b0 D_7a9b0.
  stepn F_7a9b4 D_7a9b4. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7a9b8 D_7a9b8. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7a9bc D_7a9bc. zstep F_7a9c0 D_7a9c0. zstep F_7a9c4 D_7a9c4.
    zbtk F_7a9c8 D_7a9c8.
    zstep F_7aa88 D_7aa88. stepn F_7aa8c D_7aa8c.
  zstep F_7aa98 D_7aa98.
  zld F_7aa9c D_7aa9c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa0 D_7aaa0 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa4 D_7aaa4 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaa8 D_7aaa8 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7aaac D_7aaac (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab0 D_7aab0 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7aab4 D_7aab4 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7aab8 D_7aab8.
  stepjr F_7aabc D_7aabc (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. zret.
Qed.

#[using="Type"] Theorem art_poison_lo_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1366c8 0xc000 -> apart (sp - 64) 64 0x1d1768 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7ab38 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
  pose proof (art_poison_lo_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0x129d04 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  zsplit;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_poison_lo_ok (p n : Z) : Prop := 8 <= p /\ p + 8 <= SB /\ p + n <= SB.
Definition art_poison_hi_ok (p n : Z) : Prop := kHighMemBeg <= p /\ kHighMemBeg + 8 <= p + n /\ p <= kHighMemEnd /\ p + n <= kHighMemEnd + 1.

#[using="Type"] Theorem art_poison_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1366c8 0xc000 -> apart (sp - 64) 64 0x1d1768 256 ->
  art_layout M ->
  (art_poison_lo_ok p n \/ art_poison_hi_ok p n) -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7ab38 : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L [Hl|Hh] Hp8 Hn8 Hn Hv Hthr Wsh.
  - destruct Hl as (Ha & Hb & Hc). exact (art_poison_lo_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hb Hc Hp8 Hn8 Hn Hv Hthr Wsh).
  - destruct Hh as (Ha & Hb & Hc & Hd). exact (art_poison_hi0_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hd Hp8 Hn8 Hn Hb Hc Hv Hthr Wsh).
Qed.
End FPX.
