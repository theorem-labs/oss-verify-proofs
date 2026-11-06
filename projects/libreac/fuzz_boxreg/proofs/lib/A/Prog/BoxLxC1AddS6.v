(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmit.v, with its module paths and module names changed; 873 of its 913 lines of code are new or changed and 619 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxC1AddDefs.v; 170 of its 241 lines of code are new or changed and 842 lines of the source are left out. *)
(* Segment 6 of case 1's add piece: 0x80890 (CA_PR5) .. 0x80ab4 (GP_K), the checks of the new row's base and
   pinned against the lowest free base and 0, and the join. Split off a Theorem Labs lane's BoxLxC1Add.v (its script comment
   at a working branch b83af11e4b5) so that each segment of the piece builds on its own; the two
   field regions of the registry are stated over the memory the walk has reached, and each premise of
   st_ok_pi_add_region is a named hypothesis, which is what makes this segment build in seconds instead of hours
   (one `pose proof` with placeholders and inline `ltac:` arguments left the unifier working on
   `mrestrict _ (ms_mem ms)` against `mrestrict _ (ms_mem ms1)`). *)
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

(* ca_dj, also through `add_cond` (a state after a branch). *)
Ltac ca_dj2 := cbn [ss_mem ca_ss add_cond YP09.all_disjoint]; unfold extent_disjoint, ca_spill;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
  repeat match goal with |- context [bv_unsigned (ew ?Ex ?n)] =>
    match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite F end end;
  rewrite ?unsigned_lit_small by lia; repeat split; try exact I; lia.



Lemma ca_s6 : forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (CA_P B MT CA_PR5 false i).
Proof.
  intros i HKK cx fp k acc ly3 S3 W3 ms md HB HJ HFR HMO HC.
  destruct HC as (r & bs & bs' & pos & M & nch & lf & want & known & z & HCO & HCOM & HREG & Hfnd & Hadd & Hz0 &
    R10 & R19 & R21 & R23).
  cbn iota in R10.
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
  destruct (LLVMFuzzerTestOneInput_case1.c1_add_pos bs M nch z bs' HIb HLM Hadd Hz0) as (HMnz & Hok & Hfab' & Hn5 & Hheld & Hcase).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HIb) as Hn.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_find_range bs M known Hfnd Hn) as Hkr.
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size REG_SIZE) with 288 in Hrceil, Hria.
  destruct (ca_seat B MT LAWS cx fp k ly3 S3 W3 ms md CA_PR5 r (Boxreg.bx_fabric bs) nch (lf mod 2 ^ 64)
    HB HJ HFR HCO R20 Hrin HFRS HSR S58 S30) as (HS & HEI & SHOK).
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 9 9%bv _ eq_refl (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HCO))))))))) ) as F9.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 20 20%bv r eq_refl R20) as F20.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 23 23%bv known eq_refl R23) as F23.
  pose proof (ca_Fr (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 26 26%bv _ eq_refl R26) as F26.
  pose proof (ca_Fx (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 1 ltac:(unfold A_TEXT; lia)) as F33.
  cbn [nth ca_ext Nat.add] in F33; unfold w64 in F33.
  pose proof (ca_Fx (ms_regs ms) cx fp r nch (lf mod 2 ^ 64) 2 ltac:(unfold A_TEXT; lia)) as F34.
  cbn [nth ca_ext Nat.add] in F34; unfold w64 in F34.
  remember (ca_E (ms_regs ms) cx fp r nch (lf mod 2 ^ 64)) as E eqn:HE.
  assert (HM : forall x, ms_mem ms x = ms_mem ms x) by reflexivity.
  pose proof Hheld as (Hzlt & Hmac & _).
  assert (Hzc : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4) by lia.
  assert (Hkc : known = -1 \/ known = z).
  { destruct (Z.ltb_spec known 0) as [Hk0 | Hk0]; [left; lia | right].
    symmetry. exact (LLVMFuzzerTestOneInput_case1.c1_known bs M nch known z bs' Hfnd Hk0 Hok Hadd). }

  destruct Hzc as [-> | [-> | [-> | [-> | ->]]]]; destruct Hkc as [-> | ->].
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    let kk := lazymatch type of R23 with _ = w64 ?x => x end in
    pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) zz HS R10 eq_refl) as HS1;
    pose proof (st_ok_pi_pin_reg' E _ _ (19%bv : bv 5) zz HS1 R19 eq_refl) as HS2;
    pose proof (st_ok_pi_pin_reg' E _ _ (22%bv : bv 5) zz HS2 R22 eq_refl) as HS3;
    pose proof (st_ok_pi_pin_reg' E _ _ (23%bv : bv 5) kk HS3 R23 eq_refl) as HS4;
    clear HS HS1 HS2 HS3; rename HS4 into HS.
  (* known = -1: 0x80898 .. 0x808c4, the row's nch against slot 0x58 *)
  all: lazymatch type of R23 with _ = w64 (-1) =>
    let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    assert (Hnch' : Boxreg.bx_nch bs' zz = nch)
      by (destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso | exact Hk'];
          pose proof (LLVMFuzzerTestOneInput_case1.c1_find_none bs M (-1) Hfnd ltac:(lia) HMnz) as NH;
          destruct Hh as (Hi0 & Mi & _); exact (NH zz Hi0 Mi));
    pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 20%nat) (56 * zz + 12) (56 * zz + 12 + 4) 0 0
      [YP09.mkChunk (56 * zz + 12) (CVal 4 (SOff 33 0))]) HS
      ltac:(vm_compute; reflexivity)
      (ca_rfield_ok E (w_H W3) (ms_mem ms) r bs' (56 * zz + 12) (SOff 33 0) F20 ltac:(lia) ltac:(lia) HL' Hbytes' ltac:(lia) ltac:(lia)
         ltac:(change (Boxreg.rd4 bs' (56 * zz + 12)) with (Boxreg.bx_nch bs' zz); lia)
         ltac:(change (Boxreg.rd4 bs' (56 * zz + 12)) with (Boxreg.bx_nch bs' zz); rewrite Hnch';
               exact (LowestFreeBase.lfb_den_atom E 33 nch F33)))
      ltac:(ca_dj2)) as HS1;
    clear HS; rename HS1 into HS
  | _ => idtac end.
  all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ => let v := eval vm_compute in ss in change ss with v in HS end.
  all: paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM.
  all: lazymatch type of R23 with _ = w64 (-1) =>
    psrr_branch_tok RUN BR HS SHOK ca_Bspan;
      [ exfalso; rewrite (ca_br_sext_self E 33 nch F33 ltac:(lia)) in Hc; discriminate | clear Hc ];
    paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM
  | _ => idtac end.
  (* 0x808d4: bne s6, s10 *)
  all: psrr_branch_tok RUN BR HS SHOK ca_Bspan; ca_bf.
  (* idx <> n_before: the join *)
  1, 3, 5, 7, 9, 11, 13, 15, 17, 19: paj_run_to_tok RUNTO HS HJ SHOK ca_Bspan GP_K; [ca_awr|]; ca_upd HM; lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msF) |- _ =>
    pose proof (ca_kept_pi _ _ _ _ _ _ _ _ _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv; 20%bv; 25%bv]
      ltac:(rewrite <- HE; exact HS) ltac:(vm_compute; reflexivity)) as HKR;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (26%bv : bv 5) Q26;
    pmkst HS;
    assert (HKg : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msF)) by (apply gb_keep_pointwise; exact HM);
    eapply HKK; [exact HB | exact HJ | exact HFR | exact HMO |];
    eapply (ca_land B MT MTL i cx fp k acc ly3 S3 W3 _ _ r bs bs' pos M nch lf);
    [ exact (ca_core_at cx fp CA_PR5 GP_K ms _ _ HCO (fun q Hq => HKR q ltac:(cbn [In] in Hq |- *; tauto)))
    | eapply (ca_com_keep B MT i cx fp k acc ly3 S3 W3 [(r, REG_SIZE)] ms
        (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 2920)) (ms_mem msF) (seg_rom SEGS)) r bs pos M nch lf _ HB HKg);
      [ cbn [ms_regs mkst]; rewrite (HKR 20%bv ltac:(cbn; tauto)); exact R20
      | cbn [ms_regs mkst]; rewrite Q22; reflexivity
      | cbn [ms_regs mkst]; rewrite Q26; first [ rewrite F26; reflexivity | unfold w64; f_equal; lia ]
      | cbn [ms_regs mkst]; rewrite (HKR 25%bv ltac:(cbn; tauto)); exact R25
      | exact HCOM ]
    | exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms
        (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 2920)) (ms_mem msF) (seg_rom SEGS)) r bs' HKg (or_introl eq_refl) HREG)
    | cbn [ms_regs mkst]; rewrite Q21; reflexivity
    | exact Hadd ] end.

  (* idx = n_before: 0x808d8 .. 0x80924, the new row's base against slot 0x30 and its pinned flag *)
  all: destruct (Hnew ltac:(lia)) as (Hbase & Hpin).
  all: assert (F34' : ew E 34 = Z_to_bv 64 lf).
  all: try (rewrite F34; rewrite Z.mod_small; [reflexivity|];
    let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    destruct HIb' as ((_ & _ & HB2 & HB3 & _) & _); pose proof (Boxreg.B3_bounds bs' zz HB2 HB3 ltac:(lia)); lia).
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    assert (Hbr : 0 <= Boxreg.bx_base bs' zz <= 38)
      by (destruct HIb' as ((_ & _ & HB2 & HB3 & _) & _); pose proof (Boxreg.B3_bounds bs' zz HB2 HB3 ltac:(lia)); lia).
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msX) |- _ =>
      prreg HS (26%bv : bv 5) Q26;
      pose proof (st_ok_pi_pin_reg' E _ _ (26%bv : bv 5) zz HS ltac:(cbn [restrict ms_regs]; rewrite Q26, F26; f_equal; lia) eq_refl) as HS1 end;
    clear HS; rename HS1 into HS.
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    assert (RB : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 20%nat) (56 * zz + 8) (56 * zz + 8 + 4) 0 0
      [YP09.mkChunk (56 * zz + 8) (CVal 4 (SOff 34 0))]))
    by (apply (ca_rfield_ok E (w_H W3) (ms_mem ms) r bs' (56 * zz + 8) (SOff 34 0) F20); try lia; try exact HL'; try exact Hbytes';
        [ change (Boxreg.rd4 bs' (56 * zz + 8)) with (Boxreg.bx_base bs' zz); lia
        | change (Boxreg.rd4 bs' (56 * zz + 8)) with (Boxreg.bx_base bs' zz); rewrite Hbase;
          exact (LowestFreeBase.lfb_den_atom E 34 lf F34') ]).
  all: lazymatch goal with HSq : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ =>
    assert (Hmemx : ms_mem msX = ms_mem ms)
      by (apply FunctionalExtensionality.functional_extensionality; exact HM) end.
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    lazymatch goal with HSq : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ =>
    assert (RB2 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem msX)) (YP09.mkRegion (Some 20%nat) (56 * zz + 8) (56 * zz + 8 + 4) 0 0
      [YP09.mkChunk (56 * zz + 8) (CVal 4 (SOff 34 0))])) by (rewrite Hmemx; exact RB) end.
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    assert (WFB : YP09.region_wf (YP09.mkRegion (Some 20%nat) (56 * zz + 8) (56 * zz + 8 + 4) 0 0
      [YP09.mkChunk (56 * zz + 8) (CVal 4 (SOff 34 0))]) = true) by (vm_compute; reflexivity).
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    lazymatch goal with HSq : st_ok_pi _ _ _ ?ssx _ |- _ =>
    assert (DJB : YP09.all_disjoint E (YP09.mkRegion (Some 20%nat) (56 * zz + 8) (56 * zz + 8 + 4) 0 0
      [YP09.mkChunk (56 * zz + 8) (CVal 4 (SOff 34 0))]) (ss_mem ssx)) by ca_dj2 end.
  all: lazymatch goal with HSq : st_ok_pi _ _ _ ?ssx _ |- _ =>
    pose proof (st_ok_pi_add_region E ssx _ _ HSq WFB RB2 DJB) as HS1 end;
    clear HS; rename HS1 into HS.

  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    lazymatch goal with HSq : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ =>
    assert (RP2 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem msX)) (YP09.mkRegion (Some 20%nat) (56 * zz + 20) (56 * zz + 20 + 4) 0 0
      [YP09.mkChunk (56 * zz + 20) (CVal 4 (SLit 0))]))
    by (rewrite Hmemx; apply (ca_rfield_ok E (w_H W3) (ms_mem ms) r bs' (56 * zz + 20) (SLit 0) F20); try lia; try exact HL'; try exact Hbytes';
        [ change (Boxreg.rd4 bs' (56 * zz + 20)) with (Boxreg.bx_pinned bs' zz); lia
        | change (Boxreg.rd4 bs' (56 * zz + 20)) with (Boxreg.bx_pinned bs' zz); rewrite Hpin; reflexivity ]) end.
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    assert (WFP : YP09.region_wf (YP09.mkRegion (Some 20%nat) (56 * zz + 20) (56 * zz + 20 + 4) 0 0
      [YP09.mkChunk (56 * zz + 20) (CVal 4 (SLit 0))]) = true) by (vm_compute; reflexivity).
  all: let zz := lazymatch type of R10 with _ = w64 ?x => x end in
    lazymatch goal with HSq : st_ok_pi _ _ _ ?ssx _ |- _ =>
    assert (DJP : YP09.all_disjoint E (YP09.mkRegion (Some 20%nat) (56 * zz + 20) (56 * zz + 20 + 4) 0 0
      [YP09.mkChunk (56 * zz + 20) (CVal 4 (SLit 0))]) (ss_mem ssx)) by ca_dj2 end.
  all: lazymatch goal with HSq : st_ok_pi _ _ _ ?ssx _ |- _ =>
    pose proof (st_ok_pi_add_region E ssx _ _ HSq WFP RP2 DJP) as HS1 end;
    clear HS; rename HS1 into HS.
  all: paj_run_tok RUN HS HJ SHOK ca_Bspan; [ca_awr|]; ca_upd HM.
  all: try rename Hc into Hc_old.
  all: try rename Q26 into Q26a.
    all: psrr_branch_tok RUN BR HS SHOK ca_Bspan;
    [ exfalso; rewrite (ca_br_sext_self E 34 lf F34' ltac:(lia)) in Hc; discriminate | clear Hc ].
  all: paj_run_to_tok RUNTO HS HJ SHOK ca_Bspan GP_K; [ca_awr|]; ca_upd HM; lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msF) |- _ =>
    pose proof (ca_kept_pi _ _ _ _ _ _ _ _ _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv; 20%bv; 25%bv]
      ltac:(rewrite <- HE; exact HS) ltac:(vm_compute; reflexivity)) as HKR;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (26%bv : bv 5) Q26;
    pmkst HS;
    assert (HKg : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msF)) by (apply gb_keep_pointwise; exact HM);
    eapply HKK; [exact HB | exact HJ | exact HFR | exact HMO |];
    eapply (ca_land B MT MTL i cx fp k acc ly3 S3 W3 _ _ r bs bs' pos M nch lf);
    [ exact (ca_core_at cx fp CA_PR5 GP_K ms _ _ HCO (fun q Hq => HKR q ltac:(cbn [In] in Hq |- *; tauto)))
    | eapply (ca_com_keep B MT i cx fp k acc ly3 S3 W3 [(r, REG_SIZE)] ms
        (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 2920)) (ms_mem msF) (seg_rom SEGS)) r bs pos M nch lf _ HB HKg);
      [ cbn [ms_regs mkst]; rewrite (HKR 20%bv ltac:(cbn; tauto)); exact R20
      | cbn [ms_regs mkst]; rewrite Q22; reflexivity
      | cbn [ms_regs mkst]; rewrite Q26; first [ rewrite F26; reflexivity | unfold w64; f_equal; lia ]
      | cbn [ms_regs mkst]; rewrite (HKR 25%bv ltac:(cbn; tauto)); exact R25
      | exact HCOM ]
    | exact (gb_greg_keep B cx fp W3 ly3 S3 [(r, REG_SIZE)] ms
        (mkst (ms_regs msF) (Z_to_bv 64 (BASE + 2920)) (ms_mem msF) (seg_rom SEGS)) r bs' HKg (or_introl eq_refl) HREG)
    | cbn [ms_regs mkst]; rewrite Q21; reflexivity
    | exact Hadd ] end.
Qed.


End c.
End b.
End a.
