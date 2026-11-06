(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySetGa0.v; 132 of its 161 lines of code are new or changed and 150 lines of the source are left out. *)
(* What the cases of the head of the hand-built allocation phase of LLVMFuzzerTestOneInput
   (ASan build, 0x812b4 .. 0x81328, GR_hd0I / GR_hd1I / GR_hd2I to GR_malI) share, and what
   the head itself (GrantEntryRawHead.v) uses.

   The symbolic states of the three cases at 0x812b4 are ss_r0 / ss_r1 / ss_r2 with their
   shadow entries SH_r0 / SH_r1 / SH_r2. Each one runs to 0xc78 on the engine with shadow
   tokens (paj_run_to_tok, Bx = RH_Bx, span RH_Bspan) with no open obligation (checked by
   vm_compute). The input bytes read are data slot 0 of the environment at atom 32
   (c_p + pos_end); `raw` is atom 25 (s9) and slot 88 is in the stack window at s1
   (atom 9); the shadow offset is atom 21 (s5). The shadow entry of the input bytes comes
   from the input block (range_addressable_of_block), the one of `raw` from the frame's
   shadow byte 70 (rh_raw_addressable). With those entries the tokens take each check, and
   its slow path (0x81a3c, 0x81a70) is not reached.

   hmem is the memory a case keeps; hmem_tr carries it across a run that writes only slot
   88 and `raw`. fin_mal gives GR_malI from the facts such a run leaves at 0x81328. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC45 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntryRawDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic states of the three cases at 0x812b4 ---- *)
(* 0x812b4: the shadow offset is in s5 (x21), atom 21, as in GrantEntrySweepS2.v. *)
Definition RH_Bx : sv := SOff 21 0.
Definition RH_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* `raw` at s9 (x25), written; slot 88 at s1 (x9), read and written; the bytes of the
   input read, data slot 0 at atom 32 (read-only). *)
Definition R_raw : YP09.region := YP09.mkRegion (Some 25%nat) 0 2 0 2 [].
Definition R_s88 : YP09.region := YP09.mkRegion (Some 9%nat) 88 96 88 96 [YP09.mkChunk 88 (CVal 8 (SOff 32 0))].
Definition R_in (n : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0 n 0 0 [YP09.mkChunk 0 (CData 0 0 n)].
Definition RH_PTR : afact := mkAF 4096 140737479966720 0.
Definition RH_SP : afact := mkAF (2 ^ 46) (2 ^ 47) 5.
Definition RH_SB : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
(* No byte left: s8 is 0. *)
Definition ss_r0 : sstate :=
  mkSS GR_hd (sr_set sr_atoms 24%bv (SLit 0)) [R_raw] None (mkFacts [(21%nat, RH_SB); (25%nat, RH_PTR)] [] []).
Definition SH_r0 : list shent := [mkSHE 25 0 2].
(* One byte left: s8 is 1. *)
Definition ss_r1 : sstate :=
  mkSS GR_hd (sr_set sr_atoms 24%bv (SLit 1)) [R_in 1; R_s88; R_raw] None
    (mkFacts [(9%nat, RH_SP); (21%nat, RH_SB); (25%nat, RH_PTR); (32%nat, RH_PTR)] [] []).
Definition SH_r1 : list shent := [mkSHE 32 0 1; mkSHE 25 0 2].
(* Two bytes or more left: s8 is at least 2. *)
Definition ss_r2 : sstate :=
  mkSS GR_hd sr_atoms [R_in 2; R_s88; R_raw] None
    (mkFacts [(9%nat, RH_SP); (21%nat, RH_SB); (24%nat, mkAF 2 (2 ^ 26) 0); (25%nat, RH_PTR); (32%nat, RH_PTR)] [] []).
Definition SH_r2 : list shent := [mkSHE 32 0 2; mkSHE 25 0 2].

(* ---- the frame's shadow with `raw` marked usable ---- *)
Lemma gsh_raw_len : length GSH_raw = GE_NSH.
Proof. vm_compute. reflexivity. Qed.
Lemma gsh_raw_70 : nth 70 GSH_raw 0 = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma gsh_raw_other : forall i, (i < 104)%nat -> i <> 70%nat -> nth i GSH_raw 0 = nth i GSH_a 0.
Proof. intros i Hi Hne. do 104 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.

(* The two bytes of `raw` are usable when shadow byte 70 of the frame is 2. *)
Lemma rh_raw_addressable : forall (rd : Z -> option Z) f,
  f mod 64 = 0 -> 0 <= f -> rd (SHADOW_OFF + f / 8 + 70) = Some 2 ->
  range_addressable rd SHADOW_OFF (f + GO_RAW) 2.
Proof.
  intros rd f Hf H0 Hs x Hx. unfold GO_RAW in Hx.
  assert (H8 : f mod 8 = 0).
  { rewrite (Z.div_mod f 64) by lia. rewrite Hf, Z.add_0_r.
    replace (64 * (f / 64)) with ((8 * (f / 64)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod f 8 ltac:(lia)) as Hd. rewrite H8, Z.add_0_r in Hd.
  assert (Hq : x / 8 = f / 8 + 70) by (symmetry; apply (Z.div_unique x 8 (f / 8 + 70) (x - f - 560)); lia).
  assert (Hr : x mod 8 = x - f - 560) by (symmetry; apply (Z.mod_unique x 8 (f / 8 + 70) (x - f - 560)); lia).
  exists 2. unfold shadow_of_addr, saddr_ok. rewrite Hq, Z.add_assoc. split; [exact Hs | right; lia].
Qed.

Ltac rh_cur HS := lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => m end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

(* A byte of the caller's input, from the input block's bytes. *)
Lemma rh_in_byte : forall (m : word -> option byte) p (pl : list byte) j,
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) pl) -> (j < length pl)%nat ->
  mbyte SEGS m (p + Z.of_nat j) = Some (nth j pl (Z_to_bv 8 0)).
Proof.
  intros m p pl j H Hj.
  rewrite (garr8_mbyte SEGS m p _ j H) by (rewrite length_map; exact Hj).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* The memory every cut of the head keeps: the saved registers, the frame's flag, the
   input, the spill slots, the table's bytes and the two arrays of the frame. *)
Definition hmem (cx : ecx) (fp t : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gsaved cx W3 ms3 /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + 1016) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gslots_late cx fp W3 ms3 /\
  gtabb W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)).

(* An address of the program's memory (not the shadow band) outside slot 88 and `raw`. *)
Definition happ (cx : ecx) (fp a : Z) : Prop :=
  (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ ~ (c_sp1 cx + 88 <= a < c_sp1 cx + 96) /\
  ~ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2).

Lemma hmem_tr : forall cx fp t ly3 W3 ms ms',
  glayout cx fp t ly3 ->
  (forall a, 0 <= a < 2 ^ 64 -> happ cx fp a ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  hmem cx fp t W3 ms -> hmem cx fp t W3 ms'.
Proof.
  intros cx fp t ly3 W3 ms ms' HL HK
    ((Hra & Hsv) & Hfl & Hin & ((M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8) & S8 & S32 & S40 & S72 & S80 & S104 & S112 & S128)
     & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (LT & LW & LS & _ & _).
  unfold happ, GO_RAW, kLowShadowBeg, kHighMemBeg in HK. unfold kLowShadowBeg, kHighMemBeg in *.
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= c_sp1 cx + 88 \/ c_sp1 cx + 96 <= a) ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H3 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply HK; lia. }
  unfold hmem, gsaved, gslots_late, gslots_mid, gslot, gfarr, gtabb in *.
  split; [split|].
  { apply RDK; [lia | lia | lia | exact Hra]. }
  { intros j Hj. apply RDK; [lia | lia | lia | apply Hsv, Hj]. }
  split.
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016)); [exact Hfl|].
    intros j Hj. apply HK; lia. }
  split.
  { apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') (c_p cx) _); [|exact Hin].
    intros a Ha. rewrite length_map in Ha.
    destruct (L16 ltac:(unfold c_n; lia)) as (P1 & P2 & P3 & P4 & P5). unfold c_n in *. apply HK; lia. }
  split; [splits; apply RDK; first [lia | assumption]|].
  split.
  { intros j H1 H2 H3 H4. rewrite HK; [apply HT; assumption | lia | lia]. }
  split.
  { apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') _ _); [|exact Hws].
    intros a Ha. rewrite length_map, LW in Ha. unfold GO_WAS in Ha. apply HK; lia. }
  { apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') _ _); [|exact Hst].
    intros a Ha. rewrite length_map, LS in Ha. unfold GO_SET in Ha. apply HK; lia. }
Qed.

(* The frame's shadow bytes lie in the shadow band, outside slot 88 and `raw`. *)
Lemma gshadow_band : forall cx fp t ly3 i,
  glayout cx fp t ly3 -> 0 <= i < 104 ->
  kLowShadowBeg <= gSH cx fp + i < kHighMemBeg /\ c_sp1 cx > kHighMemBeg /\
  (gF cx fp + 1024 <= kLowShadowBeg \/ kHighMemBeg <= gF cx fp).
Proof.
  intros cx fp t ly3 i HL Hi.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  assert (H1 : 512 <= gF cx fp / 8) by (apply Z.div_le_lower_bound; lia).
  assert (H2 : gF cx fp / 8 < 2 ^ 44 - 1048576) by (apply Z.div_lt_upper_bound; lia).
  rewrite L11. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* GR_malI from the facts the walk leaves at 0x81328. *)
Lemma fin_mal : forall cx fp k acc ly3 S3 W3 ms md t,
  gmach cx ms GR_mal -> k <= 3 -> acc <= GE_A2 MT -> gblk1 B cx ly3 S3 t ->
  In (t, 460) (ablocks B ly3 S3) -> 0 < t -> length (GrantSlotPlan.T_end (c_pl cx)) = 460%nat -> c_n cx < 2 ^ 26 ->
  gshadow cx fp W3 ms GSH_raw -> hmem cx fp t W3 ms ->
  getr (ms_regs ms) 20 = w64 t -> getr (ms_regs ms) 21 = w64 SHADOW_OFF -> getr (ms_regs ms) 22 = w64 (gSH cx fp) ->
  getr (ms_regs ms) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) ->
  getr (ms_regs ms) 25 = w64 (gF cx fp + GO_RAW) -> getr (ms_regs ms) 10 = w64 RAW_SW ->
  gslot cx W3 ms 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) ->
  gfb cx fp W3 ms GO_RAW (raw_b cx) -> gfb cx fp W3 ms (GO_RAW + 1) (raw_w cx) ->
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) ->
  SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)) ->
  GR_malI B MT cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros cx fp k acc ly3 S3 W3 ms md t (Pc & Prv & Psv & Pro & Pfr & Pfc & HG) Hk Hacc Hbl HinT Ht0 HLT Hn Hsh
    (Hsv & Hfl & Hin & Hsl & HT & Hws & Hst) R20 R21 R22 R24 R25 R10 S88 B0 B1 Hrel HI1.
  exists t. unfold rcore, ge_body, gtab. unfold gtabb in HT.
  splits; try assumption. apply gsh_raw_len.
Qed.

End c.
End b.
End a.
