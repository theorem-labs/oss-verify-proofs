(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmit.v, with its module paths and module names changed; 873 of its 913 lines of code are new or changed and 619 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxC1AddDefs.v; 159 of its 230 lines of code are new or changed and 842 lines of the source are left out. *)
(* The walk of case 1 of fuzz_boxreg's LLVMFuzzerTestOneInput on the ASan build, segment s3 of the add piece
   0x807e8 .. 0x80ab4 (fuzz_boxreg.c:310-361); the cuts, the seat and the call lemmas are BoxLxC1AddDefs.v's.
     s3  CA_R2 (0x8080c, after reac_boxreg_add) .. the checks 0x80810 .. 0x80864, then bcmp (r->box[idx].mac, mac, 6)
         at 0x80868 .. CA_P CA_PR3 true (0x8086c); or, for idx = -1, 0x808c8 .. 0x808d4 and the join GI_K (0x80ab4).
   Every branch into the abort block 0x80f60 is refuted by Pau's address-free lemmas of
   lib/Prog/LLVMFuzzerTestOneInput_case1.v; the shadow test of r->n (0x8083c) is decided by a region holding its
   shadow byte 0. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxC1AddDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1
reac_boxreg_add_c reac_boxreg_find_c lowest_free_c reac_boxreg_add_inv.
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

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).



Lemma ca_s3 : forall i, gb_from B MT POST (CA_P B MT CA_PR3 true i) -> gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (CA_R2 B MT i).
Proof.
  intros i HN HKK cx fp k acc ly3 S3 W3 ms md HB HJ HFR HMO HC.
  destruct HC as (r & bs & bs' & pos & M & nch & lf & want & v & w5 & known & z & HCO & HCOM & HREG & Hv & Hvr & R27 &
    Hw5r & R21 & Hw5 & Hfnd & Hadd & R10 & R23).
  pose proof HCOM as (HBASE & HMAC & Hnch & S58 & S30 & Hlf & HW & Hwant & R22 & R26 & R25).
  pose proof HBASE as (Hi & Hk & Hacc & HBL & HIb & HMEM & HSR & HCU & H68 & H48 & R20).
  pose proof HMEM as (HSV & HSH & HFL & HIN & HFRS & HPV).
  pose proof HJ as (HAR3 & _).
  pose proof HMAC as (HLM & _).
  pose proof HREG as (_ & HL' & Hbytes').
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  destruct (c1_after_add bs M nch z bs' HIb HLM Hadd) as (HIb' & Hfab & Hkept & Hzr).
  destruct (LLVMFuzzerTestOneInput_case1.c1_add_want bs M nch lf want z bs' HIb HLM HW Hadd) as (Ezw & Hnew).
  subst want.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HIb) as Hn.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs' HIb') as Hn'.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_find_range bs M known Hfnd Hn) as Hkr.
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size REG_SIZE) with 288 in Hrceil, Hria.
  pose proof (ca_sh280 B LAWS ly3 S3 W3 (ms_mem ms) md r HAR3 Hrin) as Hsh280.
  assert (Hshb : 0 <= shadow_of_addr SHADOW_OFF (r + 280) < 2 ^ 64 - 1).
  { unfold shadow_of_addr, SHADOW_OFF.
    assert (0 <= (r + 280) / 8) by (apply Z.div_pos; lia).
    assert ((r + 280) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }

  assert (Hshr : shadow_of_addr SHADOW_OFF (r + 280) + 1 <= r \/ r + 288 <= shadow_of_addr SHADOW_OFF (r + 280)).
  { unfold shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hria.
    assert (0 <= (r + 280) / 8) by (apply Z.div_pos; lia).
    assert ((r + 280) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    assert ((r + 280) / 8 <= (r + 280) / 8) by lia. lia. }
  assert (Hshs : shadow_of_addr SHADOW_OFF (r + 280) + 1 <= c_sp1 cx).
  { unfold shadow_of_addr, SHADOW_OFF.
    assert ((r + 280) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct (ca_seat B MT LAWS cx fp k ly3 S3 W3 ms md CA_PR2 r (Boxreg.bx_fabric bs) nch (lf mod 2 ^ 64)
    HB HJ HFR HCO R20 Hrin HFRS HSR S58 S30) as (HS & HEI & SHOK).
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 9 9%bv _ eq_refl (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HCO))))))))) ) as F9.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 20 20%bv r eq_refl R20) as F20.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 21 21%bv w5 eq_refl R21) as F21.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 23 23%bv known eq_refl R23) as F23.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 26 26%bv _ eq_refl R26) as F26.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 27 27%bv v eq_refl R27) as F27.
  pose proof (ca_Fx (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 0 ltac:(unfold A_TEXT; lia)) as F32. cbn [nth ca_ext Nat.add] in F32; unfold w64 in F32.
  pose proof (ca_Fx (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 3 ltac:(unfold A_TEXT; lia)) as F35. cbn [nth ca_ext Nat.add] in F35; unfold w64 in F35.
  remember (ca_E (ms_regs ms) cx fp r nch (lf mod 2 ^ 64)) as E eqn:HE.
  assert (HM : forall x, ms_mem ms x = ms_mem ms x) by reflexivity.

  assert (Hzc : z = -1 \/ z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4) by lia.
  destruct Hzc as [-> | Hzc].
  { (* idx = -1: the checks 0x80810 .. 0x8082c, then 0x808c8 .. 0x808d4 and the join *)
    pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) (-1) HS R10 eq_refl) as HS1.
    pose proof (st_ok_pi_pin_reg' E _ _ (22%bv : bv 5) (-1) HS1 R22 eq_refl) as HS2.
    clear HS HS1. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]. ca_upd HM.
    psrr_branch_tok RUN BR HS SHOK ca_Bspan; ca_bfact Hc.
    all: paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM.
    all: psrr_branch_tok RUN BR HS SHOK ca_Bspan;
      [ clear Hc0; paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM;
        psrr_branch_tok RUN BR HS SHOK ca_Bspan;
        [ ca_bf; paj_run_to_tok RUNTO HS HJ SHOK ca_Bspan GP_K; [ca_awr|]; ca_upd HM
        | ca_bf; exfalso; lia ]
      | rewrite (ca_cond_or E w5 known F21 Hw5r F23 ltac:(lia)) in Hc0; ca_zbool; (exfalso; match goal with Hb : Z.land _ 1 = 0, Hk0 : 0 <= ?kn |- _ => pose proof (LLVMFuzzerTestOneInput_case1.c1_known bs M nch kn _ bs' Hfnd Hk0 (proj1 Hw5 Hb) Hadd) end; lia) ].
    all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msF) |- _ =>
    pose proof (ca_kept_pi _ _ _ _ _ _ _ _ _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv; 20%bv; 25%bv; 26%bv]
      ltac:(rewrite <- HE; exact HS) ltac:(vm_compute; reflexivity)) as HKR;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22;
    pmkst HS;
    assert (HKg : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msF)) by (apply gb_keep_pointwise; exact HM);
    eapply HKK; [exact HB | exact HJ | exact HFR | exact HMO |];
    eapply (ca_land B MT MTL i cx fp k acc ly3 S3 W3 _ _ r bs bs' pos M nch lf);
    [ exact (ca_core_at cx fp CA_PR2 GP_K ms _ _ HCO (fun q Hq => HKR q ltac:(cbn [In] in Hq |- *; tauto)))
    | eapply (ca_com_keep B MT i cx fp k acc ly3 S3 W3 [(r, REG_SIZE)] ms
        (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 2920)) (ms_mem msF) (seg_rom SEGS)) r bs pos M nch lf _ HB HKg);
      [ cbn [ms_regs mkst]; rewrite (HKR 20%bv ltac:(cbn; tauto)); exact R20
      | cbn [ms_regs mkst]; rewrite Q22; reflexivity
      | cbn [ms_regs mkst]; rewrite (HKR 26%bv ltac:(cbn; tauto)); exact R26
      | cbn [ms_regs mkst]; rewrite (HKR 25%bv ltac:(cbn; tauto)); exact R25
      | exact HCOM ]
    | exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms
        (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 2920)) (ms_mem msF) (seg_rom SEGS)) r bs' HKg (or_introl eq_refl) HREG)
    | cbn [ms_regs mkst]; rewrite Q21; reflexivity
    | exact Hadd ] end. }
  (* idx >= 0 *)
  assert (Hz0 : 0 <= z) by lia.
  destruct (LLVMFuzzerTestOneInput_case1.c1_add_pos bs M nch z bs' HIb HLM Hadd Hz0) as (HMnz & Hok & Hfab' & Hn5 & Hheld & Hcase).
  pose proof Hheld as (Hzlt & Hmac & _).
  assert (Hnc : Boxreg.bx_n bs' = 1 \/ Boxreg.bx_n bs' = 2 \/ Boxreg.bx_n bs' = 3 \/ Boxreg.bx_n bs' = 4 \/ Boxreg.bx_n bs' = 5) by lia.
  destruct Hzc as [-> | [-> | [-> | [-> | ->]]]]; destruct Hnc as [En | [En | [En | [En | En]]]]; try lia.
  all: let nn := lazymatch type of En with _ = ?x => x end in let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) zz HS R10 eq_refl) as HS1;
    pose proof (st_ok_pi_pin_reg' E _ _ (22%bv : bv 5) zz HS1 R22 eq_refl) as HS2;
    clear HS HS1; rename HS2 into HS;
    pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SLit nn))]) HS
      ltac:(vm_compute; reflexivity)
      (ca_rfield_ok E (w_H W3) (ms_mem ms) r bs' 280 (SLit nn) F20 ltac:(lia) ltac:(lia) HL' Hbytes' ltac:(lia) ltac:(lia)
         ltac:(change (Boxreg.rd4 bs' 280) with (Boxreg.bx_n bs'); lia)
         ltac:(change (Boxreg.rd4 bs' 280) with (Boxreg.bx_n bs'); rewrite En; reflexivity))
      ltac:(ca_dj)) as HS1;
    clear HS; rename HS1 into HS;
    pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS
      ltac:(vm_compute; reflexivity) (ca_shbyte_ok E (w_H W3) (ms_mem ms) _ F35 Hshb Hsh280) ltac:(ca_dj)) as HS1;
    clear HS; rename HS1 into HS.
  all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ => let v := eval vm_compute in ss in change ss with v in HS end.
  all: paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM.
  all: psrr_branch_tok RUN BR HS SHOK ca_Bspan;
    [ ca_bfact Hc;
      paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM;
      psrr_branch_tok RUN BR HS SHOK ca_Bspan;
      [ clear Hc0; paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM
      | rewrite (ca_cond_or E w5 known F21 Hw5r F23 ltac:(lia)) in Hc0; ca_zbool;
        paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM;
        psrr_branch_tok RUN BR HS SHOK ca_Bspan;
        [ ca_bf; (exfalso; match goal with Hb : Z.land _ 1 = 0, Hk0 : 0 <= ?kn |- _ => pose proof (LLVMFuzzerTestOneInput_case1.c1_known bs M nch kn _ bs' Hfnd Hk0 (proj1 Hw5 Hb) Hadd) end; lia)
        | ca_bf; paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM ] ]
    | ca_bfact Hc; exfalso; rewrite (proj1 Hv Hc) in Hadd;
      apply LLVMFuzzerTestOneInput_case1.c1_add_zero in Hadd; lia ].
  all: lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msC) |- _ =>
    pmkst HS;
    prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
    prreg HS (19%bv : bv 5) Q19; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22;
    pose proof (ca_kept_st _ _ _ _ _ _ _ _ _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv; 20%bv; 23%bv; 25%bv; 26%bv]
      ltac:(rewrite <- HE; exact HS) ltac:(vm_compute; reflexivity)) as HKR;
    assert (HKg : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msC)) by (apply gb_keep_pointwise; exact HM);
    pose proof HCO as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24));
    lazymatch type of Q19 with _ = Z_to_bv 64 ?zz =>
    apply (ca_bcmp_at B MT LAWS ABCMP cx fp k ly3 S3 W3 msC _ r bs' M zz 2336 (POST cx) HB HJ HFR HBL);
    [ rewrite (HKR 2%bv ltac:(cbn; tauto)); exact G2
    | rewrite (HKR 3%bv ltac:(cbn; tauto)); exact G3
    | rewrite (HKR 4%bv ltac:(cbn; tauto)); exact G4
    | exact Q1 | lia | reflexivity
    | rewrite Q10, F20; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; try lia
    | rewrite Q11, F32; reflexivity
    | exact Q12 | lia
    | exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms msC r bs' HKg (or_introl eq_refl) HREG)
    | exact Hmac
    | exact (gb_gshadow_keep cx fp W3 [(r, REG_SIZE)] ms msC GSH_it HKg ltac:(vm_compute; discriminate) HSH)
    | exact (c1mac_keep cx fp W3 [(r, REG_SIZE)] ms msC M HKg HMAC)
    | intros regs2 mem2 md2 HJ2 HP2 HK2 Ha0;
      assert (HKall : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) mem2) by exact (gb_keep_trans cx fp W3 _ _ _ _ HKg HK2);
      eapply HN; [exact HB | exact HJ2 | exact HFR | exact HMO |];
      exists r, bs, bs', pos, M, nch, lf, zz, known, zz;
      split; [exact (ca_core_at cx fp CA_PR2 CA_PR3 ms regs2 mem2 HCO
                (fun q Hq => ca_presq _ regs2 q _ HP2 ltac:(cbn [In] in Hq; repeat destruct Hq as [<- | Hq]; try ca_cs; destruct Hq)
                   (HKR q ltac:(cbn [In] in Hq |- *; tauto))))|];
      split;
      [ eapply (ca_com_keep B MT i cx fp k acc ly3 S3 W3 [(r, REG_SIZE)] ms (mkst regs2 (Z_to_bv 64 (BASE + 2336)) mem2 (seg_rom SEGS))
          r bs pos M nch lf _ HB HKall);
        [ cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
          rewrite (HKR 20%bv ltac:(cbn; tauto)); exact R20
        | cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |]; rewrite Q22; reflexivity
        | cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
          rewrite (HKR 26%bv ltac:(cbn; tauto)); exact R26
        | cbn [ms_regs mkst]; apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |];
          rewrite (HKR 25%bv ltac:(cbn; tauto)); exact R25
        | exact HCOM ]
      | ];
      split; [exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms (mkst regs2 (Z_to_bv 64 (BASE + 2336)) mem2 (seg_rom SEGS))
                r bs' HKall (or_introl eq_refl) HREG)|];
      split; [exact Hfnd|]; split; [exact Hadd|]; split; [lia|];
      split; [cbn [ms_regs mkst]; exact Ha0|];
      cbn [ms_regs mkst];
      split; [apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs | rewrite Q19; reflexivity]|];
      split; [apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs | rewrite Q21, F32; reflexivity]|];
      apply (ca_presq (ms_regs msC) regs2); [exact HP2 | ca_cs |]; rewrite (HKR 23%bv ltac:(cbn; tauto)); exact R23 ]
    end end.
Qed.

End c.
End b.
End a.
