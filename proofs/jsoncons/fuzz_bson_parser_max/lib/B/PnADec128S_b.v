(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128P1_b PnADec128E_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADS.
Import L5A. Import L5CA. Import L5SAR. Import PNADK. Import PNADE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Lemma u8_eqaddr (M : mem) a b v : L5.u8_at RSEGS M a v -> a = b -> L5.u8_at RSEGS M b v.
Proof. intros H <-. exact H. Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Definition at_b2 : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    dsg L ar HI E (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac -> rgd E Rc ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb3fcc Mc modelc) (vK E).
Definition at_signj : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) (sigma : Z),
    dst L ar HI E Mc modelc LKc Ac -> L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) (vF E + 32) 144 -> 0 <= sigma <= 1 ->
    PNADD.stJ (vR E) (vsp E) (vF E) (vfirst E) sigma (vvp E) Rc ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb406c Mc modelc) (vK E).

(* [comment removed for export] *)
Lemma dg_memset E (X : dkc L ar HI E) axc (fx : FPState) Ra Mc modelc LKc Ac (d c n ra : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> vF E + 32 <= d -> d + n <= vF E + 504 -> 0 < n <= 2 ^ 27 -> PMSPA.accA Mc d n ->
  getr Ra (reg 10) = Z_to_bv 64 d -> getr Ra (reg 11) = Z_to_bv 64 c -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (forall Rb Mb modelb, regs_preserved Ra Rb -> dsg L ar HI E axc Mb modelb LKc Ac ->
     (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at Mb (PNADD.SH (vF E) + 4) 18) ->
     (forall i, 0 <= i < n -> Mb (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 (c mod 256))) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0x78130 Mc modelc) (vK E).
Proof.
  intros ST Hd1 Hd2 Hn ACC Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 KC.
  pose proof ST as (BI & _). pose proof BI as (HHc & AMc & _ & _ & _ & ASTKc & _). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
  assert (U2 : bv_unsigned (getr Ra 2%bv) = vsp E - 256) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - SR; lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (_ & WF & _).
  destruct (WF (vF E, 3, vsp E - 256 + 32) ltac:(left; reflexivity)) as (_ & _ & _ & _ & FDEF & _). cbn [ff_addr ff_class fst snd] in FDEF. change (ff_bytes 3) with 512 in FDEF.
  unfold PMSPA.cfg. apply (MS fx Ra Mc modelc (vLB E) (PNADK.FF' E) LKc (vcr E) Ac d c n (vK E)); clear MS.
  - split; [exact HHc|]. split; [exact (proj1 AMc)|]. split; [exact (proj2 AMc)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear - Hn; lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Mc Mc (vsp E) 18432 256 2560 ASTKc (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
             replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
             pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [exact ACC|].
    split. { intros i Hi. rewrite U2. apply (L5SAR.fframe_client L ar _ (PNADK.FF' E) _ _ (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Hi Hd1 Hd2; lia. }
    split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Mc (vF E) 512 FDEF ltac:(clear - GFF1; lia) ltac:(clear - GFF1; lia)) as WR.
             replace (d + i) with (vF E + (d - vF E + i)) by (clear; lia). apply WR; clear - Hi Hm Hd1 Hd2; lia. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ d n HHc); [clear - GFS1 Hd1; lia| clear - GFS2 Hd2; lia].
  - rewrite L5K.rl11. exact Ra11.
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (AMb : L5CA.amodel_ok Ac modelb) by (split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMc)| exact MIb]).
    assert (BY : forall i, 0 <= i < n -> Mb (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 (c mod 256))).
    { intros i Hi. destruct (BYTES i Hi) as (v & Ev & Bv). unfold byte_at in Bv. rewrite Bv. subst v. reflexivity. }
    destruct (PNADK.dg_memcall L ar C HI LY HIok E X axc Mc modelc LKc Ac Mb modelb (fun a => d <= a < d + n) ST HHb AMb RTb PRES SDEFb) as (STb & ZSb).
    + intros a Ha. replace a with (d + (a - d)) by (clear; lia). rewrite BY by (clear - Ha; lia). discriminate.
    + intros a. destruct (L5SAR.rng_dec a d (d + n)) as [Y|Y]; [left; exact Y| right; exact Y].
    + intros a Ha. left. clear - Ha Hd1 Hd2; lia.
    + exact (KC Rb Mb modelb RPb STb ZSb BY).
Qed.

(* [comment removed for export] *)
Lemma zeros18 (M : mem) a : 0x696000 <= a -> a + 18 <= 2 ^ 64 ->
  (forall i, 0 <= i < 18 -> L5.u8_at RSEGS M (a + i) 0) -> L5KA.zeros_at M a 18.
Proof.
  intros Ha Hb U i Hi. apply (L5ADHR.byte_of_u8 M (a + i) 0 (U i Hi)); [right; clear - Ha Hi; lia| clear - Ha Hb Hi; lia].
Qed.
(* [comment removed for export] *)
Lemma aacc_of_zeros (M : mem) p n : p mod 8 = 0 -> 0 <= n -> L5KA.zeros_at M (p / 8 + 2147450880) ((n + 7) / 8) -> PMSPA.accA M p n.
Proof.
  intros P8 Hn Z a Ha. left. unfold byte_at. pose proof (PNADK.S_rng p n a P8 Hn Ha) as SR.
  replace (S a) with (p / 8 + 2147450880 + (S a - (p / 8 + 2147450880))) by (clear; lia). apply Z. clear - SR. lia.
Qed.

Theorem frame_tail : at_signj -> at_b2.
Proof.
  intros SIGNJ E X fx Rc Mc modelc LKc Ac ST RG.
  dgeom L ar HI E X. gfacts L ar C HI LY HIok E X ST.
  destruct RG as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20 & Q24). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  assert (Y1 : 4096 <= vF E <= 140737488354816) by (clear - GFF1; lia).
  assert (Y2 : (65536 + 6840320 <= ((vF E / 8) + 2147450880) \/ ((vF E / 8) + 2147450880) + 64 <= 65536)) by (left; clear - GFF1; pose proof (Z.div_pos (vF E) 8 ltac:(lia) ltac:(lia)); lia).
  LeanFeed.pfeed P (PNADP1.adkB2_conc fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 34%nat => vvp E | 50%nat => vF E | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & T1 & T10 & T11 & T12 & T18 & T23 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17).
  apply (PNADK.dg_piece L ar C HI LY HIok E X _ fx fx2 Rc R2 0xb3fcc 0x78130 Mc modelc LKc Ac M2v (fun a => vF E / 8 + 2147450880 + 4 <= a < vF E / 8 + 2147450880 + 4 + 18) ST MS2 MG2).
  { intros a Ha N. apply FRZ2; [exact Ha| exact N]. }
  { intros a Wa. do 4 right; left. unfold PNADD.SH, PNADD.SBv. clear - Wa; lia. }
  intros M3 model3 ST3 HID3 VIS3 FR3.
  assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  assert (ZV : L5KA.zeros_at M2v (vF E / 8 + 2147450880 + 4) 18).
  { apply zeros18; [clear - E0; lia| clear - E0; lia|]. intros i Hi.
    assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17) by (clear - Hi; lia).
    clear - Hc Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17.
    repeat (destruct Hc as [->|Hc]; [first [ apply (u8_eqaddr _ _ _ _ Z0); clear; lia | apply (u8_eqaddr _ _ _ _ Z1); clear; lia | apply (u8_eqaddr _ _ _ _ Z2); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z3); clear; lia | apply (u8_eqaddr _ _ _ _ Z4); clear; lia | apply (u8_eqaddr _ _ _ _ Z5); clear; lia | apply (u8_eqaddr _ _ _ _ Z6); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z7); clear; lia | apply (u8_eqaddr _ _ _ _ Z8); clear; lia | apply (u8_eqaddr _ _ _ _ Z9); clear; lia | apply (u8_eqaddr _ _ _ _ Z10); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z11); clear; lia | apply (u8_eqaddr _ _ _ _ Z12); clear; lia | apply (u8_eqaddr _ _ _ _ Z13); clear; lia | apply (u8_eqaddr _ _ _ _ Z14); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z15); clear; lia | apply (u8_eqaddr _ _ _ _ Z16); clear; lia | apply (u8_eqaddr _ _ _ _ Z17); clear; lia ]|]).
    subst i. first [ apply (u8_eqaddr _ _ _ _ Z0); clear; lia | apply (u8_eqaddr _ _ _ _ Z1); clear; lia | apply (u8_eqaddr _ _ _ _ Z2); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z3); clear; lia | apply (u8_eqaddr _ _ _ _ Z4); clear; lia | apply (u8_eqaddr _ _ _ _ Z5); clear; lia | apply (u8_eqaddr _ _ _ _ Z6); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z7); clear; lia | apply (u8_eqaddr _ _ _ _ Z8); clear; lia | apply (u8_eqaddr _ _ _ _ Z9); clear; lia | apply (u8_eqaddr _ _ _ _ Z10); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z11); clear; lia | apply (u8_eqaddr _ _ _ _ Z12); clear; lia | apply (u8_eqaddr _ _ _ _ Z13); clear; lia | apply (u8_eqaddr _ _ _ _ Z14); clear; lia
      | apply (u8_eqaddr _ _ _ _ Z15); clear; lia | apply (u8_eqaddr _ _ _ _ Z16); clear; lia | apply (u8_eqaddr _ _ _ _ Z17); clear; lia ]. }
  assert (ZS3 : L5KA.zeros_at M3 (PNADD.SH (vF E) + 4) 18).
  { unfold PNADD.SH, PNADD.SBv. apply (proj1 (L5A.zeros_at_vis (ahid Ac modelc) M3 _ 18 (L5A.avis_sub _ _ _ (vF E / 8 + 2147450880 + 4) 18 VSHV ltac:(clear; lia) ltac:(clear; lia)))).
    rewrite VIS3. exact ZV. }
  (* [comment removed for export] *)
  assert (K2 : forall j, In j [2; 3; 4; 8; 9; 19; 20; 24; 26; 27]%nat -> getr R2 (reg j) = getr Rc (reg j)).
  { intros j Hj. apply KS2. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 24; 26; 27]%nat). vm_compute. reflexivity. }
  assert (F8' : vF E mod 8 = 0) by (apply mod32_8; exact GFF32).
  assert (ACC3 : PMSPA.accA M3 (vF E + 32) 144).
  { apply aacc_of_zeros; [replace (vF E + 32) with (vF E + 4 * 8) by (clear; lia); rewrite Z_mod_plus_full; exact F8'| clear; lia|]. change ((144 + 7) / 8) with 18.
    replace ((vF E + 32) / 8) with (vF E / 8 + 4) by (clear; replace (vF E + 32) with (vF E + 4 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
    unfold PNADD.SH, PNADD.SBv in ZS3. intros i Hi. replace (vF E / 8 + 4 + 2147450880 + i) with (vF E / 8 + 2147450880 + 4 + i) by (clear; lia). exact (ZS3 i Hi). }
  apply (dg_memset E X _ fx2 R2 M3 model3 LKc Ac (vF E + 32) 0 144 737320 ST3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC3 T10 T11 T12).
  { rewrite (K2 4%nat) by inl. rewrite Q4. exact (c_Rtp L ar HI E X). }
  { exact T1. } { reflexivity. } { clear; lia. } { rewrite (K2 2%nat) by inl. exact Q2. }
  intros R4 M4 model4 RP4 ST4 ZS4 BY4.
  assert (DST4 : dst L ar HI E M4 model4 LKc Ac) by (apply (PNADK.dst_of_dsg L ar HI E _ _ _ _ ST4); exact (ZS4 ZS3)).
  (* [comment removed for export] *)
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R2 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R2 R4 j RP4 Hj). }
  clear MWS MWF MFW MFSW MFLW MIMGC MCSB MCUAR MOWN MC128 MFLC MZF6 lo hi Hlo Hhi MVlo MVhi MVZ MIMG0 MRMS MFD VSV VF42 VFV VSHV VS6 VIV MS8 MS16 MS24 MS32 MS40 MS48 MS56 MS64 MS72 MS80 MS88 MS96 MS104.
  dfacts L ar C HI LY HIok E X DST4.
  set (MV4 := mrestrict (ahid Ac model4) M4) in *.
  assert (C2 : getr R4 (reg 2) = Z_to_bv 64 (vsp E - 256)) by (rewrite (R4c 2%nat) by inl; rewrite (K2 2%nat) by inl; exact Q2).
  assert (C8 : getr R4 (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite (R4c 8%nat) by inl; rewrite (K2 8%nat) by inl; exact Q8).
  assert (C9 : getr R4 (reg 9) = Z_to_bv 64 (vsp E - 256)) by (rewrite (R4c 9%nat) by inl; rewrite (K2 9%nat) by inl; exact Q9).
  assert (C23 : getr R4 (reg 23) = Z_to_bv 64 (vF E / 8 + 2147450880)) by (rewrite (R4c 23%nat) by inl; exact T23).
  assert (C19 : getr R4 (reg 19) = Z_to_bv 64 PNADD.SBv) by (rewrite (R4c 19%nat) by inl; rewrite (K2 19%nat) by inl; exact Q19).
  assert (C20 : getr R4 (reg 20) = Z_to_bv 64 (vfirst E)) by (rewrite (R4c 20%nat) by inl; rewrite (K2 20%nat) by inl; exact Q20).
  assert (C18 : getr R4 (reg 18) = Z_to_bv 64 (vF E + 32)) by (rewrite (R4c 18%nat) by inl; exact T18).
  assert (C24 : getr R4 (reg 24) = Z_to_bv 64 (vvp E)) by (rewrite (R4c 24%nat) by inl; rewrite (K2 24%nat) by inl; exact Q24).
  assert (C26 : getr R4 (reg 26) = Z_to_bv 64 (vF E)) by (rewrite (R4c 26%nat) by inl; rewrite (K2 26%nat) by inl; exact Q26).
  assert (C27 : getr R4 (reg 27) = Z_to_bv 64 (vF E)) by (rewrite (R4c 27%nat) by inl; rewrite (K2 27%nat) by inl; exact Q27).
  assert (C3 : getr R4 (reg 3) = getr (vR E) (reg 3)) by (rewrite (R4c 3%nat) by inl; rewrite (K2 3%nat) by inl; exact Q3).
  assert (C4 : getr R4 (reg 4) = getr (vR E) (reg 4)) by (rewrite (R4c 4%nat) by inl; rewrite (K2 4%nat) by inl; exact Q4).
  LeanFeed.pfeed P (PNADP1.adkC_conc fx2 R4 MV4 (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 34%nat => vvp E | 35%nat => lo | 36%nat => hi | 50%nat => vF E | _ => 0 end)) ltac:(PNADK.dsc).
  (* [comment removed for export] *)
  assert (ZSIG4 : L5KA.zeros_at MV4 (vF E + 32) 144).
  { pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ ST4) as (_ & (_ & _ & VF4 & _)).
    apply (proj2 (L5A.zeros_at_vis (ahid Ac model4) M4 _ 144 (L5A.avis_sub _ _ _ (vF E + 32) 144 VF4 ltac:(clear; lia) ltac:(clear; lia)))).
    intros i Hi. exact (BY4 i Hi). }
  assert (STEP : forall fx5 R5 M5v (sigma : Z), 0 <= sigma <= 1 ->
            msteps RSEGS (st fx2 R4 0xb4028 MV4) (st fx5 R5 0xb406c M5v) -> mem_grows MV4 M5v ->
            (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (vfirst E + 0 <= i < vfirst E + 0 + 1) -> M5v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i)) ->
            (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%nat -> getr R5 (reg x) = getr R4 (reg x)) ->
            getr R5 (reg 10) = Z_to_bv 64 (vvp E + 8) -> getr R5 (reg 11) = Z_to_bv 64 ((vvp E + 8) / 8 + 2147450880) -> getr R5 (reg 30) = Z_to_bv 64 (vfirst E + sigma) ->
            srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R4 0xb4028 M4 model4) (vK E)).
  { intros fx5 R5 M5v sigma Hs MS5 MG5 FRZ5 KS5 E10 E11 E21.
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx2 fx5 R4 R5 0xb4028 0xb406c M4 model4 LKc Ac M5v (fun a => vfirst E + 0 <= a < vfirst E + 0 + 1) DST4 MS5 MG5 FRZ5).
    { intros a Wa. do 5 right. clear - Wa; lia. }
    intros M6 model6 ST6 HID6 VIS6.
    apply (SIGNJ E X fx5 R5 M6 model6 LKc Ac sigma ST6).
    - rewrite HID6, VIS6. intros i Hi. rewrite FRZ5; [exact (ZSIG4 i Hi)| clear - Hi GFF1; lia| clear - Hi GFFf; lia].
    - exact Hs.
    - unfold PNADD.stJ, PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv.
      split.
      { split.
        { split; [rewrite (KS5 2%nat) by inl; exact C2|]. split; [rewrite (KS5 3%nat) by inl; exact C3|]. split; [rewrite (KS5 4%nat) by inl; exact C4|].
          split; [rewrite (KS5 8%nat) by inl; exact C8|]. split; [rewrite (KS5 9%nat) by inl; exact C9|]. split; [rewrite (KS5 23%nat) by inl; exact C23|].
          split; [rewrite (KS5 26%nat) by inl; exact C26|]. rewrite (KS5 27%nat) by inl; exact C27. }
        split; [rewrite (KS5 19%nat) by inl; exact C19|]. split; [rewrite (KS5 20%nat) by inl; exact C20| exact E21]. }
      split; [rewrite (KS5 18%nat) by inl; exact C18|]. split; [rewrite (KS5 24%nat) by inl; exact C24|]. split; [exact E10| exact E11]. }
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & [(MS5 & KS5 & E10 & E11 & E12 & E21)|(MS5 & KS5 & E10 & E11 & E12 & E21 & _)]).
  - apply (STEP fx5 R5 M5v 0 ltac:(clear; lia) MS5 MG5 FRZ5); [| exact E10| exact E11| rewrite Z.add_0_r; exact E21].
    intros x Hx. apply KS5. revert x Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%nat). vm_compute. reflexivity.
  - apply (STEP fx5 R5 M5v 1 ltac:(clear; lia) MS5 MG5 FRZ5); [| exact E10| exact E11| exact E21].
    intros x Hx. apply KS5. revert x Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%nat). vm_compute. reflexivity.
Qed.

End WithHeap.
End SCFG_1.
End PNADS.
