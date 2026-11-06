(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.GcFlush17.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import muslA.Bo0SumsMemset_code muslA.Bo0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_611e4_61830.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BrtPoison BrtPoisonRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma art_poison_hi0_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x170268 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x611f8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0xcc740)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0xcc740 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_611f8 D_611f8.
  zsd F_611fc D_611fc (sp - 8) (U raw) ltac:(rewok W).
  zsd F_61200 D_61200 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_61204 D_61204 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_61208 D_61208 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_6120c D_6120c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_61210 D_61210 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_61214 D_61214 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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
  - zbtk F_61218 D_61218.
    stepn F_6122c D_6122c. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_61230 D_61230.
  zstep F_61234 D_61234.
  zld F_61238 D_61238 0xd64c8 G48.
  zld F_6123c D_6123c 0xde738 Csb. unfold SB in *.
  zstep F_61240 D_61240. zstep F_61244 D_61244. zstep F_61248 D_61248.
  zstep F_6124c D_6124c.
  zbft F_61250 D_61250.
  zstep F_61254 D_61254. zld F_61258 D_61258 0xd64d0 G50.
  zstep F_6125c D_6125c. zld F_61260 D_61260 0xd64d8 G58.
  zld F_61264 D_61264 0xdf428 Cmb. zld F_61268 D_61268 0xdf430 Cme.
  zstep F_6126c D_6126c.
  zbtk F_61270 D_61270.
  zstep F_61278 D_61278. zld F_6127c D_6127c 0xd64e0 G60. zld F_61280 D_61280 0xdf420 Che.
  zstep F_61284 D_61284.
  zstep F_61288 D_61288.
  zbft F_6128c D_6128c.
  zbtk F_61290 D_61290.
  zld F_61358 D_61358 0xdf420 Che.
  zstep F_6135c D_6135c.
  zstep F_61360 D_61360.
  zbft F_61364 D_61364.
  zbtk F_61368 D_61368.
  stepn F_61428 D_61428. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_6142c D_6142c.
  zstep F_61430 D_61430. zstep F_61434 D_61434.
  zbft F_61438 D_61438.
  zstep F_6143c D_6143c. zld F_61440 D_61440 0xd64d0 G50.
  zstep F_61444 D_61444. zld F_61448 D_61448 0xd64d8 G58.
  zld F_6144c D_6144c 0xdf428 Cmb. zld F_61450 D_61450 0xdf430 Cme.
  zstep F_61454 D_61454.
  zbtk F_61458 D_61458.
  zstep F_61460 D_61460. zld F_61464 D_61464 0xd64e0 G60. zld F_61468 D_61468 0xdf420 Che.
  zstep F_6146c D_6146c.
  zstep F_61470 D_61470.
  zbft F_61474 D_61474.
  zbft F_61478 D_61478.
  zstep F_6147c D_6147c. zld F_61480 D_61480 0xd64e8 G68. zld F_61484 D_61484 0xd8428 Crm.
  zbft F_61488 D_61488.
  stepn F_6148c D_6148c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61490 D_61490. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61494 D_61494. zstep F_61498 D_61498. zstep F_6149c D_6149c.
    zbft F_614a0 D_614a0.
    zstep F_614a4 D_614a4. zld F_614a8 D_614a8 0xd64b8 G38. zld F_614ac D_614ac (0x170268 + 120) Cth.
    zbtk F_614b0 D_614b0.
    zstep F_61560 D_61560. stepn F_61564 D_61564.
  zstep F_61570 D_61570.
  zld F_61574 D_61574 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_61578 D_61578 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_6157c D_6157c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61580 D_61580 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61584 D_61584 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61588 D_61588 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6158c D_6158c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61590 D_61590.
  stepjr F_61594 D_61594 (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.
  (* [comment removed for export] *)
  - zbft F_61218 D_61218.
    zstep F_6121c D_6121c.
    zlb F_61220 D_61220 0xddf9c Ccp.
    stepfence F_61224 D_61224.
    zbft F_61228 D_61228.
    stepn F_6122c D_6122c. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_61230 D_61230.
  zstep F_61234 D_61234.
  zld F_61238 D_61238 0xd64c8 G48.
  zld F_6123c D_6123c 0xde738 Csb. unfold SB in *.
  zstep F_61240 D_61240. zstep F_61244 D_61244. zstep F_61248 D_61248.
  zstep F_6124c D_6124c.
  zbft F_61250 D_61250.
  zstep F_61254 D_61254. zld F_61258 D_61258 0xd64d0 G50.
  zstep F_6125c D_6125c. zld F_61260 D_61260 0xd64d8 G58.
  zld F_61264 D_61264 0xdf428 Cmb. zld F_61268 D_61268 0xdf430 Cme.
  zstep F_6126c D_6126c.
  zbtk F_61270 D_61270.
  zstep F_61278 D_61278. zld F_6127c D_6127c 0xd64e0 G60. zld F_61280 D_61280 0xdf420 Che.
  zstep F_61284 D_61284.
  zstep F_61288 D_61288.
  zbft F_6128c D_6128c.
  zbtk F_61290 D_61290.
  zld F_61358 D_61358 0xdf420 Che.
  zstep F_6135c D_6135c.
  zstep F_61360 D_61360.
  zbft F_61364 D_61364.
  zbtk F_61368 D_61368.
  stepn F_61428 D_61428. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_6142c D_6142c.
  zstep F_61430 D_61430. zstep F_61434 D_61434.
  zbft F_61438 D_61438.
  zstep F_6143c D_6143c. zld F_61440 D_61440 0xd64d0 G50.
  zstep F_61444 D_61444. zld F_61448 D_61448 0xd64d8 G58.
  zld F_6144c D_6144c 0xdf428 Cmb. zld F_61450 D_61450 0xdf430 Cme.
  zstep F_61454 D_61454.
  zbtk F_61458 D_61458.
  zstep F_61460 D_61460. zld F_61464 D_61464 0xd64e0 G60. zld F_61468 D_61468 0xdf420 Che.
  zstep F_6146c D_6146c.
  zstep F_61470 D_61470.
  zbft F_61474 D_61474.
  zbft F_61478 D_61478.
  zstep F_6147c D_6147c. zld F_61480 D_61480 0xd64e8 G68. zld F_61484 D_61484 0xd8428 Crm.
  zbft F_61488 D_61488.
  stepn F_6148c D_6148c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61490 D_61490. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61494 D_61494. zstep F_61498 D_61498. zstep F_6149c D_6149c.
    zbtk F_614a0 D_614a0.
    zstep F_61560 D_61560. stepn F_61564 D_61564.
  zstep F_61570 D_61570.
  zld F_61574 D_61574 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_61578 D_61578 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_6157c D_6157c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61580 D_61580 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61584 D_61584 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61588 D_61588 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6158c D_6158c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61590 D_61590.
  stepjr F_61594 D_61594 (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

Theorem art_poison_hi0_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x170268 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x611f8 : word) M rom)
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
    replace (Z_to_bv 64 ms_base) with (0xcc740 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma art_poison_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x170268 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x611f8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 raw) 2 (Z_to_bv 64 sp)) 6 (Z_to_bv 64 0xcc740)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8)))
             13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 (SB - 1))) 15 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
       (0xcc740 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  zstep F_611f8 D_611f8.
  zsd F_611fc D_611fc (sp - 8) (U raw) ltac:(rewok W).
  zsd F_61200 D_61200 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_61204 D_61204 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_61208 D_61208 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_6120c D_6120c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_61210 D_61210 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_61214 D_61214 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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
  - zbtk F_61218 D_61218.
    stepn F_6122c D_6122c. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_61230 D_61230.
  zstep F_61234 D_61234.
  zld F_61238 D_61238 0xd64c8 G48.
  zld F_6123c D_6123c 0xde738 Csb. unfold SB in *.
  zstep F_61240 D_61240. zstep F_61244 D_61244. zstep F_61248 D_61248.
  zstep F_6124c D_6124c.
  zbtk F_61250 D_61250.
  stepn F_61428 D_61428. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_6142c D_6142c.
  zstep F_61430 D_61430. zstep F_61434 D_61434.
  zbtk F_61438 D_61438.
  zstep F_6147c D_6147c. zld F_61480 D_61480 0xd64e8 G68. zld F_61484 D_61484 0xd8428 Crm.
  zbft F_61488 D_61488.
  stepn F_6148c D_6148c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61490 D_61490. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61494 D_61494. zstep F_61498 D_61498. zstep F_6149c D_6149c.
    zbft F_614a0 D_614a0.
    zstep F_614a4 D_614a4. zld F_614a8 D_614a8 0xd64b8 G38. zld F_614ac D_614ac (0x170268 + 120) Cth.
    zbtk F_614b0 D_614b0.
    zstep F_61560 D_61560. stepn F_61564 D_61564.
  zstep F_61570 D_61570.
  zld F_61574 D_61574 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_61578 D_61578 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_6157c D_6157c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61580 D_61580 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61584 D_61584 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61588 D_61588 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6158c D_6158c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61590 D_61590.
  stepjr F_61594 D_61594 (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. subst v. zret.
  - zbft F_61218 D_61218.
    zstep F_6121c D_6121c.
    zlb F_61220 D_61220 0xddf9c Ccp.
    stepfence F_61224 D_61224.
    zbft F_61228 D_61228.
    stepn F_6122c D_6122c. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_61230 D_61230.
  zstep F_61234 D_61234.
  zld F_61238 D_61238 0xd64c8 G48.
  zld F_6123c D_6123c 0xde738 Csb. unfold SB in *.
  zstep F_61240 D_61240. zstep F_61244 D_61244. zstep F_61248 D_61248.
  zstep F_6124c D_6124c.
  zbtk F_61250 D_61250.
  stepn F_61428 D_61428. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_6142c D_6142c.
  zstep F_61430 D_61430. zstep F_61434 D_61434.
  zbtk F_61438 D_61438.
  zstep F_6147c D_6147c. zld F_61480 D_61480 0xd64e8 G68. zld F_61484 D_61484 0xd8428 Crm.
  zbft F_61488 D_61488.
  stepn F_6148c D_6148c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_61490 D_61490. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_61494 D_61494. zstep F_61498 D_61498. zstep F_6149c D_6149c.
    zbtk F_614a0 D_614a0.
    zstep F_61560 D_61560. stepn F_61564 D_61564.
  zstep F_61570 D_61570.
  zld F_61574 D_61574 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_61578 D_61578 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_6157c D_6157c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_61580 D_61580 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_61584 D_61584 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_61588 D_61588 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_6158c D_6158c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_61590 D_61590.
  stepjr F_61594 D_61594 (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. zret.
Qed.

Theorem art_poison_lo_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x170268 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x611f8 : word) M rom)
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
    replace (Z_to_bv 64 ms_base) with (0xcc740 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_poison_lo_ok (p n : Z) : Prop := 8 <= p /\ p + 8 <= SB /\ p + n <= SB.
Definition art_poison_hi_ok (p n : Z) : Prop := kHighMemBeg <= p /\ kHighMemBeg + 8 <= p + n /\ p <= kHighMemEnd /\ p + n <= kHighMemEnd + 1.

Theorem art_poison_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0xd5000 0xc000 -> apart (sp - 64) 64 0x170268 256 ->
  art_layout M ->
  (art_poison_lo_ok p n \/ art_poison_hi_ok p n) -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x611f8 : word) M rom)
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
