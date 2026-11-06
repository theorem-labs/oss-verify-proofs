(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmit.v, with its module paths and module names changed; 873 of its 913 lines of code are new or changed and 619 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxC1AddDefs.v; 85 of its 150 lines of code are new or changed and 848 lines of the source are left out. *)
(* Segment 5 of case 1's add piece (fuzz_boxreg.c:310-361): from the cut CA_P CA_PR4 (0x8087c, after the second
   reac_boxreg_find) through `bne a0, s3` and the second reac_boxreg_add (0x8088c) to the cut CA_P CA_PR5
   (0x80890). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC81 YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregFind ReacBoxregAdd LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat BoxLxC1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1
reac_boxreg_add_c reac_boxreg_find_c lowest_free_c reac_boxreg_add_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxC1AddDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

Let cb5_RUN := paj_run B LAWS.
Let cb5_BR := paj_branch (PI := PI).

(* 0x8087c .. 0x80890: find-again returned z (= s3), so `bne a0, s3` falls through; then
   reac_boxreg_add (r, mac, nch) again. Box z holds M already (c1_add_pos), so the second add returns z and leaves
   the registry as it is (c1_add_again). *)
Lemma ca_s5 : forall i, gb_from B MT POST (CA_P B MT CA_PR5 false i) -> gb_from B MT POST (CA_P B MT CA_PR4 false i).
Proof.
  intros i HN cx fp k acc ly3 S3 W3 ms md HB HJ HFR HMO HC.
  destruct HC as (r & bs & bs' & pos & M & nch & lf & want & known & z & HCO & HCOM & HREG & Hfnd & Hadd & Hz0 &
    R10 & R19 & R21 & R23).
  cbn iota in R10.
  pose proof HCOM as (HBASE & HMAC & Hnch & S58 & S30 & Hlf & HW & Hwant & R22 & R26 & R25).
  pose proof HBASE as (Hi & Hk & Hacc & HBL & HIb & HMEM & HSR & HCU & H68 & H48 & R20).
  pose proof HMEM as (HSV & HSH & HFL & HIN & HFRS & HPV).
  pose proof HJ as (HAR3 & _).
  pose proof HMAC as (HLM & _).
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  destruct (c1_after_add bs M nch z bs' HIb HLM Hadd) as (HIb' & Hfab & _ & Hzr).
  destruct (LLVMFuzzerTestOneInput_case1.c1_add_pos bs M nch z bs' HIb HLM Hadd Hz0)
    as (HMnz & Hok & _ & _ & Hheld & _).
  destruct (ca_seat B MT LAWS cx fp k ly3 S3 W3 ms md CA_PR4 r (Boxreg.bx_fabric bs) nch (lf mod 2 ^ 64)
    HB HJ HFR HCO R20 Hrin HFRS HSR S58 S30) as (HS & HEI & SHOK).
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 10 10%bv z eq_refl R10) as F10.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 19 19%bv z eq_refl R19) as F19.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 20 20%bv r eq_refl R20) as F20.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 21 21%bv _ eq_refl R21) as F21.
  pose proof (ca_Fx (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 1 ltac:(unfold A_TEXT; lia)) as F33.
  cbn [nth ca_ext Nat.add] in F33; unfold w64 in F33.
  remember (ca_E (ms_regs ms) cx fp r nch (lf mod 2 ^ 64)) as E eqn:HE.
  assert (HM : forall x, ms_mem ms x = ms_mem ms x) by reflexivity.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
  (* 0x8087c: bne a0, s3, 0x80f60 (__asan_handle_no_return + abort): a0 = s3 = z, so not taken. *)
  psrr_branch_tok cb5_RUN cb5_BR HS SHOK ca_Bspan.
  { ca_bf. lia. }
  clear Hc.
  (* 0x80880 .. 0x8088c: a0 := s4 (r), a1 := s5 (mac), a2 := nch (slot 0x58), jal reac_boxreg_add. *)
  paj_run_tok cb5_RUN HS HJ SHOK ca_Bspan; [ca_awr|]. ca_upd HM.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msC end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  pose proof (ca_kept_st _ _ _ _ _ _ _ _ _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 25%bv; 26%bv]
    ltac:(rewrite <- HE; exact HS) ltac:(vm_compute; reflexivity)) as HKR.
  assert (HKg : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msC)) by (apply gb_keep_pointwise; exact HM).
  assert (HKg0 : gb_keep cx fp W3 [] (ms_mem ms) (ms_mem msC)) by (apply gb_keep_pointwise; exact HM).
  pose proof HCO as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
  apply (ca_add_at B MT LAWS TADD cx fp k ly3 S3 W3 msC _ r bs' M nch 2372 (POST cx) HB HJ HFR HBL).
  - rewrite (HKR 2%bv ltac:(cbn; tauto)); exact G2.
  - rewrite (HKR 3%bv ltac:(cbn; tauto)); exact G3.
  - rewrite (HKR 4%bv ltac:(cbn; tauto)); exact G4.
  - rewrite (HKR 8%bv ltac:(cbn; tauto)); exact G8.
  - exact Q1.
  - lia.
  - reflexivity.
  - rewrite Q10, F20; reflexivity.
  - rewrite Q11, F21; reflexivity.
  - rewrite Q12, F33; reflexivity.
  - lia.
  - exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms msC r bs' HKg (or_introl eq_refl) HREG).
  - exact HIb'.
  - exact (gb_gsaved_keep B MT cx fp W3 HB [(r, REG_SIZE)] ms msC HKg HSV).
  - exact (gb_gshadow_keep cx fp W3 [(r, REG_SIZE)] ms msC GSH_it HKg ltac:(vm_compute; discriminate) HSH).
  - exact (c1mac_keep cx fp W3 [(r, REG_SIZE)] ms msC M HKg HMAC).
  - (* back at 0x80890 *)
    intros regs2 mem2 md2 z2 bs2 HJ2 HP2 HK2 Ha0 Hadd2 HREG2.
    destruct (LLVMFuzzerTestOneInput_case1.c1_add_again bs' M nch z z2 bs2 HMnz
      ltac:(rewrite Hfab; exact Hok) Hheld Hadd2) as (-> & ->).
    assert (HKall : gb_keep cx fp W3 [] (ms_mem ms) mem2) by exact (gb_keep_trans cx fp W3 _ _ _ _ HKg0 HK2).
    eapply HN; [exact HB | exact HJ2 | exact HFR | exact HMO |].
    exists r, bs, bs', pos, M, nch, lf, want, known, z.
    split; [exact (ca_core_at cx fp CA_PR4 CA_PR5 ms regs2 mem2 HCO
              (fun q Hq => ca_presq _ regs2 q _ HP2 ltac:(cbn [In] in Hq; repeat destruct Hq as [<- | Hq]; try ca_cs; destruct Hq)
                 (HKR q ltac:(cbn [In] in Hq |- *; tauto))))|].
    split;
    [ eapply (ca_com_keep B MT i cx fp k acc ly3 S3 W3 [] ms (mkst regs2 (Z_to_bv 64 (BASE + 2372)) mem2 (seg_rom SEGS))
        r bs pos M nch lf want HB HKall);
      [ cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
        rewrite (HKR 20%bv ltac:(cbn; tauto)); exact R20
      | cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
        rewrite (HKR 22%bv ltac:(cbn; tauto)); exact R22
      | cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
        rewrite (HKR 26%bv ltac:(cbn; tauto)); exact R26
      | cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
        rewrite (HKR 25%bv ltac:(cbn; tauto)); exact R25
      | exact HCOM ]
    | ].
    split; [exact HREG2|].
    split; [exact Hfnd|]. split; [exact Hadd|]. split; [exact Hz0|].
    cbn [ms_regs mkst].
    split; [exact Ha0|].
    split; [apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |]; rewrite (HKR 19%bv ltac:(cbn; tauto)); exact R19|].
    split; [apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |]; rewrite (HKR 21%bv ltac:(cbn; tauto)); exact R21|].
    apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |]; rewrite (HKR 23%bv ltac:(cbn; tauto)); exact R23.
Qed.

End c.
End b.
End a.
