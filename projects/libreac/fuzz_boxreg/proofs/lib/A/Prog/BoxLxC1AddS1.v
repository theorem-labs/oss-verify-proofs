(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmit.v, with its module paths and module names changed; 873 of its 913 lines of code are new or changed and 619 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxC1AddDefs.v; 75 of its 140 lines of code are new or changed and 848 lines of the source are left out. *)
(* Segment 1 of case 1's add piece (0x807e8 .. 0x80ab4, fuzz_boxreg.c:310-361): from the cut C1_call at 0x807e8
   (PC1_call, lib/A/Prog/BoxLxC1Defs.v) to the cut CA_R1 at 0x807f8 (CA_PR1, find returned `known` in a0).
     807e8: mv a0, s4        807ec: ld s3, 0x70(s1)        807f0: mv a1, s3
     807f4: jal reac_boxreg_find (0x816a0)
   No branch. The engine walks to the call (s3 := mac from the slot 0x70 that gslots_fr names); the call goes
   through ca_find_at (TFIND). find reads only: the registry block r is kept as well (gb_keep with [(r, REG_SIZE)]). *)
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

Let cb1_RUN := paj_run B LAWS.

Lemma ca_s1 : forall i, gb_from B MT POST (CA_R1 B MT i) -> gb_from B MT POST (C1_call B MT i).
Proof.
  intros i HN cx fp k acc ly3 S3 W3 ms md HB HJ HFR HMO HC.
  destruct HC as (r & bs & pos & M & nch & lf & want & v & w5 & HCO & HBASE & HREG & HMAC & Hnch & S58 & S30 &
    Hlf & HW & Hwant & R22 & R26 & R25 & Hv & Hvr & R27 & Hw5r & R21 & Hw5).
  assert (HCOM : ca_com B MT i cx fp k acc ly3 S3 W3 ms r bs pos M nch lf want)
    by (repeat (split; [assumption|]); assumption).
  pose proof HBASE as (Hi & Hk & Hacc & HBL & HIb & HMEM & HSR & HCU & H68 & H48 & R20).
  pose proof HMEM as (HSV & HSH & HFL & HIN & HFRS & HPV).
  pose proof HIb as ((_ & HB1 & _) & _).
  pose proof HJ as (HAR3 & _).
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  destruct (ca_seat B MT LAWS cx fp k ly3 S3 W3 ms md PC1_call r (Boxreg.bx_fabric bs) nch (lf mod 2 ^ 64)
    HB HJ HFR HCO R20 Hrin HFRS HSR S58 S30) as (HS & HEI & SHOK).
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 20 20%bv r eq_refl R20) as F20.
  pose proof (ca_Fx (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 0 ltac:(unfold A_TEXT; lia)) as F32.
  cbn [nth ca_ext Nat.add] in F32; unfold w64 in F32.
  remember (ca_E (ms_regs ms) cx fp r nch (lf mod 2 ^ 64)) as E eqn:HE.
  assert (HM : forall x, ms_mem ms x = ms_mem ms x) by reflexivity.
  (* 0x807e8 .. 0x807f4: the engine stops at the call, a0 = s4 = r, s3 = a1 = mac (slot 0x70), ra = 0x807f8. *)
  paj_run_tok cb1_RUN HS HJ SHOK ca_Bspan; [ca_awr|]. ca_upd HM.

  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msC) |- _ =>
    pmkst HS;
    prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (19%bv : bv 5) Q19;
    pose proof (ca_kept_st _ _ _ _ _ _ _ _ _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv; 20%bv; 21%bv; 22%bv; 25%bv; 26%bv; 27%bv]
      ltac:(rewrite <- HE; exact HS) ltac:(vm_compute; reflexivity)) as HKR;
    assert (HKr : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msC)) by (apply gb_keep_pointwise; exact HM)
  end.
  pose proof HCO as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).

  (* 0x807f4: jal reac_boxreg_find (r, mac), returning to 0x807f8 (offset 2220, CA_PR1). *)
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msC) |- _ =>
    apply (ca_find_at B MT LAWS TFIND cx fp k ly3 S3 W3 msC _ r bs M 2220 (POST cx) HB HJ HFR HBL);
    [ rewrite (HKR 2%bv ltac:(cbn; tauto)); exact G2
    | rewrite (HKR 3%bv ltac:(cbn; tauto)); exact G3
    | rewrite (HKR 4%bv ltac:(cbn; tauto)); exact G4
    | rewrite (HKR 8%bv ltac:(cbn; tauto)); exact G8
    | exact Q1 | lia | reflexivity
    | rewrite Q10, F20; reflexivity
    | rewrite Q11, F32; reflexivity
    | exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms msC r bs HKr (or_introl eq_refl) HREG)
    | exact HB1
    | exact (gb_gsaved_keep B MT cx fp W3 HB [(r, REG_SIZE)] ms msC HKr HSV)
    | exact (gb_gshadow_keep cx fp W3 [(r, REG_SIZE)] ms msC GSH_it HKr ltac:(vm_compute; discriminate) HSH)
    | exact (c1mac_keep cx fp W3 [(r, REG_SIZE)] ms msC M HKr HMAC)
    | ]
  end.

  (* After the call: CA_R1 at 0x807f8. *)
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msC) |- _ =>
    intros regs2 mem2 md2 known HJ2 HP2 HK2 Ha0 Hfnd;
    assert (HKall : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) mem2) by exact (gb_keep_trans cx fp W3 _ _ _ _ HKr HK2);
    eapply HN; [exact HB | exact HJ2 | exact HFR | exact HMO |];
    exists r, bs, pos, M, nch, lf, want, v, w5, known;
    split; [exact (ca_core_at cx fp PC1_call CA_PR1 ms regs2 mem2 HCO
              (fun q Hq => ca_presq _ regs2 q _ HP2 ltac:(cbn [In] in Hq; repeat destruct Hq as [<- | Hq]; try ca_cs; destruct Hq)
                 (HKR q ltac:(cbn [In] in Hq |- *; tauto))))|];
    split;
    [ eapply (ca_com_keep B MT i cx fp k acc ly3 S3 W3 [(r, REG_SIZE)] ms (mkst regs2 (Z_to_bv 64 (BASE + 2220)) mem2 (seg_rom SEGS))
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
    | ];
    split; [exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms (mkst regs2 (Z_to_bv 64 (BASE + 2220)) mem2 (seg_rom SEGS))
                     r bs HKall (or_introl eq_refl) HREG)|];
    split; [exact Hv|]; split; [exact Hvr|];
    split; [cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
            rewrite (HKR 27%bv ltac:(cbn; tauto)); exact R27|];
    split; [exact Hw5r|];
    split; [cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
            rewrite (HKR 21%bv ltac:(cbn; tauto)); exact R21|];
    split; [exact Hw5|]; split; [exact Hfnd|];
    split; [cbn [ms_regs mkst]; exact Ha0|];
    cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |]; rewrite Q19, F32; reflexivity
  end.
Qed.

End c.
End b.
End a.
