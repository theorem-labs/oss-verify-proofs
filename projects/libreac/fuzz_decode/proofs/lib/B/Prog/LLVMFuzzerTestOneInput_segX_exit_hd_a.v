(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_loop.v, with its module names, addresses and numbers changed; 564 of its 627 lines of code are new or changed and 137 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segX_exit_hd_a: the straight-line stretches of the image-B exit group of
   LLVMFuzzerTestOneInput between +0x96c and +0xab8, each a Pa run (lib/B/Prog/DecodeBPaLib.v) from a concrete
   configuration to the next cut, as lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_c.v does for the up group:
   - hd_96c  +0x96c .. +0x974: `li a2, -1` and the channel-count test `bge zero, s5` (+0x970); a count of -1 goes
     straight to +0xa24;
   - hd_974  +0x974 .. +0xa24: the frame-header check, four ASan-checked byte reads of the payload copy (s11 + 12,
     s11 + 13, s11 + len - 2, s11 + len - 1) against 0x88 0x19 0xc2 0xea, with their UBSan wrap guards (+0x97c,
     +0x9a4, +0x9d0, +0x9f8, all refuted) and the in-line result a2 = 12 or -1 (+0xa14 .. +0xa20);
   - hd_A24  +0xa24 .. +0xa34 or the check_round_trip call (+0xaa0): `bne a0, a2` (+0xa24, the abort edge to
     +0xb88, refuted: a0 is reac_upstream_decode's 12 / -1, a2 the header's, and they agree), then a0 = -1 to the
     scan loop L6's head (+0xa34) or a0 = 12 through +0xa7c .. +0xa9c (the guards +0xa80 / +0xa88 refuted, s2
     reloaded from 80(s1)) to check_round_trip #2;
   - hd_AA4  +0xaa4 .. the check_braid call (+0xab4).
   The header read uses one seat (hd_seat974) whose env names the four bytes as atoms 34 .. 37 and s11 + len as
   atom 33 (with the alias s11 + s6 = atom 33), the bytes as one-byte regions, and s2 as the shadow base of the
   engine's ASan tokens; its shape is lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_loop.v up_lseat. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_c reac_upstream_channels_c
  LLVMFuzzerTestOneInput_segX_up_arith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segX_up_den LLVMFuzzerTestOneInput_segX_up_a LLVMFuzzerTestOneInput_segX_up_b
LLVMFuzzerTestOneInput_segX_up_c LLVMFuzzerTestOneInput_segX_up_loop LLVMFuzzerTestOneInput_segX_crt1_braid.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN1y.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ZBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

Ltac hd_in := repeat (first [left; reflexivity | right]).

(* The registers the stretches of this file never write (sp, gp, tp, s0, s1, s5 .. s9, s11). *)
Definition hd_keep : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv].

(* The byte i of a list, as the header check reads it (reac_frame_inspect_c.v:11 inspect_byte). *)
Definition hd_b (body : list byte) (i : Z) : Z := inspect_byte body (Z.to_nat i).

(* The header seat (+0x974): atom 32 the shadow base, 33 = s11 + len, 34 .. 37 the four header bytes. *)
Definition hd_extra (res len : Z) (body : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (res + len); Z_to_bv 64 (hd_b body 12); Z_to_bv 64 (hd_b body 13);
   Z_to_bv 64 (hd_b body (len - 2)); Z_to_bv 64 (hd_b body (len - 1))].
Definition hd_r27 : YP09.region := YP09.mkRegion (Some 27%nat) 12 14 0 0
  [YP09.mkChunk 12 (CVal 1 (SOff 34 0)); YP09.mkChunk 13 (CVal 1 (SOff 35 0))].
Definition hd_r33 : YP09.region := YP09.mkRegion (Some 33%nat) (-2) 0 0 0
  [YP09.mkChunk (-2) (CVal 1 (SOff 36 0)); YP09.mkChunk (-1) (CVal 1 (SOff 37 0))].
Definition hd_facts : facts :=
  mkFacts [(18%nat, mkAF 2147450880 2147450880 0); (27%nat, mkAF 4096 UP_BLK_HI 0); (33%nat, mkAF 4096 UP_BLK_HI 0);
           (22%nat, mkAF 124 67108864 0)] []
    [(SAlu ALU_ADD (SOff 27 0) (SOff 22 0), SOff 33 0)].
Definition ss_974 : sstate := mkSS 0x974 sr_atoms [hd_r27; hd_r33] None hd_facts.
Definition hd_SH : list shent := [mkSHE 27 12 14; mkSHE 33 (-2) 0].

(* The seat at +0xa24: the slot 80(s1) holding s11 + 50, read at +0xa90. *)
Definition hd_slot80 : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 0 0 [YP09.mkChunk 80 (CVal 8 (SOff 27 50))].
Definition hd_afacts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 0); (27%nat, mkAF 4096 UP_BLK_HI 0)] [] [].
Definition ss_a24 : sstate := mkSS 0xa24 sr_atoms [hd_slot80] None hd_afacts.

Lemma hd_b_range : forall body i, 0 <= hd_b body i < 256.
Proof.
intros body i. unfold hd_b, inspect_byte. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) body (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.

(* The byte i of the copy, as a one-byte value of memory. *)
Lemma hd_val_b : forall (W : world decodesegsB0) mem res body i,
  garr8 decodesegsB0 (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) body) ->
  0 <= i < Z.of_nat (length body) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) (res + i) 1 (hd_b body i).
Proof.
intros W mem res body i G Hi.
destruct (G (Z.to_nat i) ltac:(rewrite length_map; lia)) as [V _].
rewrite Z2Nat.id in V by lia. rewrite c1b_nth_map_bv in V. exact V.
Qed.

(* The header bytes decide reac_upstream_decode's verdict once its other conditions hold. *)
Lemma hd_up_ok : forall res upb len body, res <> 0 -> upb <> 0 -> 0 <= reac_upstream_decode_c.up_nch len ->
  reac_upstream_decode_c.up_ok res upb len body =
  ((hd_b body 12 =? 136) && (hd_b body 13 =? 25) && (hd_b body (len - 2) =? 194) && (hd_b body (len - 1) =? 234))%bool.
Proof.
intros res upb len body Hr Hu Hn. unfold reac_upstream_decode_c.up_ok, hd_b.
replace (res =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
replace (upb =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hu).
replace (0 <=? reac_upstream_decode_c.up_nch len) with true by (symmetry; apply Z.leb_le; exact Hn).
reflexivity.
Qed.

(* ---- values of the expressions the runs build ---- *)

Definition EH {rc : YM05.RunCeil} (regs : bvmap 5 word) (res len : Z) (body : list byte) : env := Eimg (Ereg regs (hd_extra res len body)).

Lemma EH_agree {rc : YM05.RunCeil} : forall regs res len body, env_agree 38 (Ereg regs (hd_extra res len body)) (EH regs res len body).
Proof.
intros regs res len body. split; [intros n Hn; unfold EH; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
  | reflexivity].
Qed.

Lemma hd_zc : forall z, 0 <= z < 18446744073709551616 -> zcanon z = z.
Proof. intros z Hz. apply zcanon_id. change M64 with 18446744073709551616. exact Hz. Qed.

Lemma hd_den : forall regs extra E' (n : nat) (r : bv 5),
  env_agree 32 (Ereg regs extra) E' -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  sv_denot E' (SOff n 0) = getr regs r.
Proof.
intros regs extra E' n r HA Hn Hl. cbn [sv_denot].
rewrite (proj1 HA n Hl), (ew_Ereg_nat regs extra n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma hd_den_off : forall regs extra E' (n : nat) (r : bv 5) v z,
  env_agree 32 (Ereg regs extra) E' -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  getr regs r = w64 v -> 0 <= v < 18446744073709551616 -> sv_denot E' (SOff n z) = w64 (v + z).
Proof.
intros regs extra E' n r v z HA Hn Hl Hr Hv. cbn [sv_denot].
rewrite (proj1 HA n Hl), (ew_Ereg_nat regs extra n r Hn), Hr. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with 18446744073709551616. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma hd_agree_le : forall X Y, env_agree 38 X Y -> env_agree 32 X Y.
Proof. intros X Y [A D]. split; [intros n Hn; apply A; lia | exact D]. Qed.

Lemma hd_w64_U : forall E e v, U E e = v mod 18446744073709551616 -> sv_denot E e = w64 v.
Proof.
intros E e v H. apply bv_eq. change (bv_unsigned (sv_denot E e)) with (U E e). rewrite H. unfold w64.
rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* +0x9cc / +0x9d0: ~s11 = 2^64 - 1 - s11. *)
Lemma hd_U_not : forall E res, U E (SOff 27 0) = res -> 0 <= res < 18446744073709551616 ->
  U E (SAlu ALU_XOR (SOff 27 0) (SLit (-1))) = 18446744073709551615 - res.
Proof.
intros E res H Hr. rewrite U_SAlu, H, U_SLit. cbn [zalu_raw]. change (zcanon (-1)) with 18446744073709551615.
rewrite ZBridge.zb_lxor_ones by (change (2 ^ 64) with 18446744073709551616; lia).
unfold zcanon. change M64 with 18446744073709551616. apply Z.mod_small. lia.
Qed.

(* +0xa10 .. +0xa20: a2 = 12 when the last header byte is 0xea, else -1. *)
Definition hd_a2 : sv :=
  SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff 37 0)) (SLit (-234))) (SLit 1)) (SLit (-1)))
    (SLit 12).

Lemma hd_U_zx8 : forall E a v, U E a = v -> 0 <= v < 256 -> U E (SExt false 8 a) = v.
Proof. intros E a v H Hv. rewrite U_SExt, H. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply hd_zc. lia. Qed.

Lemma hd_U_a2 : forall E x, U E (SOff 37 0) = x -> 0 <= x < 256 ->
  U E hd_a2 = (if x =? 234 then 12 else -1) mod 18446744073709551616.
Proof.
intros E x H Hx.
assert (H1 : U E (SAlu ALU_ADD (SExt false 8 (SOff 37 0)) (SLit (-234))) = (x - 234) mod 18446744073709551616).
{ rewrite U_SAlu, (hd_U_zx8 E _ x H Hx), U_SLit. cbn [zalu_raw]. change (zcanon (-234)) with 18446744073709551382.
  unfold zcanon. change M64 with 18446744073709551616.
  replace (x + 18446744073709551382) with ((x - 234) + 1 * 18446744073709551616) by ring.
  rewrite Z.mod_add by discriminate. reflexivity. }
unfold hd_a2. do 3 rewrite U_SAlu. rewrite H1, !U_SLit. cbn [zalu_raw].
destruct (Z.eqb_spec x 234) as [->|Hne].
- vm_compute. reflexivity.
- assert (Hm : 1 <= (x - 234) mod 18446744073709551616 < 18446744073709551616).
  { destruct (Z.ltb_spec x 234).
    - rewrite <- (Z.mod_add (x - 234) 1 18446744073709551616) by discriminate. rewrite Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia. }
  change (zcanon 1) with 1.
  replace ((x - 234) mod 18446744073709551616 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  vm_compute. reflexivity.
Qed.

(* The agreement of the env of a symbolic state with the entry registers, through the fresh atoms. *)
Ltac hd_agreeU HS regs H :=
  pose proof (up_agree regs) as HAE0;
  lazymatch type of HS with
  | st_ok_pi _ _ ?E _ _ => assert (H : env_agree 32 (Ereg regs up_extra) E) by up_agree_ext
  | st_ok _ ?E _ _ => assert (H : env_agree 32 (Ereg regs up_extra) E) by up_agree_ext
  end; clear HAE0.

(* The img_env of the env of a symbolic state. *)
Ltac hd_codeptr HS off :=
  lazymatch type of HS with
  | st_ok _ ?E _ _ => lazymatch goal with Hx : img_env _ _ E |- _ => exact (codeptr_val E off Hx) end
  | st_ok_pi _ _ ?E _ _ => lazymatch goal with Hx : img_env _ _ E |- _ => exact (codeptr_val E off Hx) end
  end.

(* Land a run at its stop: the memory is the run's start memory, the configuration a concrete one. *)
Ltac hd_land HS HJ :=
  lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem in HJ end;
  pmkst HS;
  lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem end.

(* A header byte through an env that agrees with the header seat's below 38. *)
Lemma hd_U_byte : forall regs res len body E' (i : nat) idx, env_agree 38 (Ereg regs (hd_extra res len body)) E' ->
  (i < 6)%nat -> nth i (hd_extra res len body) (Z_to_bv 64 0) = Z_to_bv 64 (hd_b body idx) ->
  U E' (SOff (32 + i) 0) = hd_b body idx.
Proof.
intros regs res len body E' i idx HA Hi Hn. pose proof (hd_b_range body idx) as R.
rewrite U_SOff, (proj1 HA (32 + i)%nat ltac:(lia)), (ew_Ereg_extra regs _ i), Hn, Z.add_0_r, Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. rewrite Z.mod_small by lia. apply hd_zc. lia.
Qed.

Lemma hd_U_reg38 : forall regs extra E' (n : nat) (r : bv 5) v z, env_agree 38 (Ereg regs extra) E' ->
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> getr regs r = w64 v -> 0 <= v < 18446744073709551616 ->
  U E' (SOff n z) = zcanon (v + z).
Proof.
intros regs extra E' n r v z HA Hn Hl Hr Hv. rewrite U_SOff, (proj1 HA n ltac:(lia)), (ew_Ereg_nat regs extra n r Hn), Hr.
unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma hd_bge_blt : forall a b, branch_taken BC_GE a b = negb (branch_taken BC_LT a b).
Proof. intros a b. change BC_GE with (neg_bc BC_LT). apply branch_taken_neg. Qed.

Ltac hd_agreeH HS regs res len body H :=
  pose proof (EH_agree regs res len body) as HAE0;
  lazymatch type of HS with
  | st_ok_pi _ _ ?E _ _ => assert (H : env_agree 38 (Ereg regs (hd_extra res len body)) E) by up_agree_ext
  | st_ok _ ?E _ _ => assert (H : env_agree 38 (Ereg regs (hd_extra res len body)) E) by up_agree_ext
  end; clear HAE0.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ decodeb_listing PI_decodeb).
#[local] Abbreviation VAL := (@pa_val _ decodeb_listing PI_decodeb).
#[local] Abbreviation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let RUNTO := @paj_run_to fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.


(* An atom's unsigned value, through an env that agrees with Ereg regs extra below K. *)
Lemma hd_U_x : forall regs extra K E' (n : nat) v z, env_agree K (Ereg regs extra) E' -> (n < K)%nat ->
  ew (Ereg regs extra) n = Z_to_bv 64 v -> 0 <= v < 18446744073709551616 -> U E' (SOff n z) = zcanon (v + z).
Proof.
intros regs extra K E' n v z HA Hn Hv Hr. rewrite U_SOff, (proj1 HA n Hn), Hv, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with 18446744073709551616. rewrite (Z.mod_small v) by exact Hr. reflexivity.
Qed.

Lemma hd_ew_reg : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> ew (Ereg regs extra) n = Z_to_bv 64 v.
Proof. intros regs extra n r v Hn Hr. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. reflexivity. Qed.

(* The header seat. *)
Lemma hd_seat974 : forall regs (W : world SEGS) mem md ly S res len body,
  AR SEGS B ly S W mem md -> In (res, len) (ablocks B ly S) -> 124 <= len < 67108864 ->
  Z.of_nat (length body) = len ->
  garr8 SEGS (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) body) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 27 = w64 res -> getr regs 22 = w64 len ->
  st_ok_pi SEGS VAL (EH regs res len body) ss_974
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x974)) mem (seg_rom SEGS))) /\
  sh_ok SEGS LBx hd_SH (EH regs res len body) (mrestrict (w_H W) mem).
Proof.
intros regs W mem md ly S res len body HAR Hin Hlen Hbl G H18 H27 H22.
destruct (al_blocks _ _ LAWS ly S W mem md res len HAR Hin) as (_ & H4096 & Hc & Happ & _).
pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := EH regs res len body).
pose proof (EH_agree regs res len body) as HA. fold E in HA.
assert (UR : forall (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> getr regs r = w64 v ->
  0 <= v < 18446744073709551616 -> U E (SOff n 0) = v).
{ intros n r v Hn Hl Hr Hv. rewrite (hd_U_x regs _ 38 E n v 0 HA ltac:(lia) (hd_ew_reg regs _ n r v Hn Hr) Hv).
  rewrite Z.add_0_r. exact (hd_zc v Hv). }
assert (UX : forall (i : nat) v, (i < 6)%nat -> nth i (hd_extra res len body) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 18446744073709551616 -> U E (SOff (32 + i) 0) = v).
{ intros i v Hi Hv Hr. rewrite (hd_U_x regs _ 38 E (32 + i) v 0 HA ltac:(lia)); [rewrite Z.add_0_r; exact (hd_zc v Hr) | | exact Hr].
  rewrite (ew_Ereg_extra regs _ i). exact Hv. }
assert (U18 : U E (SOff 18 0) = SHADOW_OFF) by (apply (UR 18%nat 18%bv); [reflexivity | lia | exact H18 | unfold SHADOW_OFF; lia]).
assert (U27 : U E (SOff 27 0) = res) by (apply (UR 27%nat 27%bv); [reflexivity | lia | exact H27 | lia]).
assert (U22 : U E (SOff 22 0) = len) by (apply (UR 22%nat 22%bv); [reflexivity | lia | exact H22 | lia]).
assert (U33 : U E (SOff 33 0) = res + len) by (apply (UX 1%nat); [lia | reflexivity | lia]).
pose proof (hd_b_range body 12) as R12. pose proof (hd_b_range body 13) as R13.
pose proof (hd_b_range body (len - 2)) as R2. pose proof (hd_b_range body (len - 1)) as R1.
assert (U34 : U E (SOff 34 0) = hd_b body 12) by (apply (UX 2%nat); [lia | reflexivity | lia]).
assert (U35 : U E (SOff 35 0) = hd_b body 13) by (apply (UX 3%nat); [lia | reflexivity | lia]).
assert (U36 : U E (SOff 36 0) = hd_b body (len - 2)) by (apply (UX 4%nat); [lia | reflexivity | lia]).
assert (U37 : U E (SOff 37 0) = hd_b body (len - 1)) by (apply (UX 5%nat); [lia | reflexivity | lia]).
assert (B27 : bv_unsigned (ew E 27) = res) by (rewrite <- U27, U_SOff, Z.add_0_r; symmetry; apply zcanon_id;
  change M64 with (bv_modulus 64); apply bv_unsigned_in_range).
assert (B33 : bv_unsigned (ew E 33) = res + len) by (rewrite <- U33, U_SOff, Z.add_0_r; symmetry; apply zcanon_id;
  change M64 with (bv_modulus 64); apply bv_unsigned_in_range).
assert (B22 : bv_unsigned (ew E 22) = len) by (rewrite <- U22, U_SOff, Z.add_0_r; symmetry; apply zcanon_id;
  change M64 with (bv_modulus 64); apply bv_unsigned_in_range).
assert (B18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite <- U18, U_SOff, Z.add_0_r; symmetry; apply zcanon_id;
  change M64 with (bv_modulus 64); apply bv_unsigned_in_range).
assert (DX : forall n v, U E (SOff n 0) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
  rewrite Hv, Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Z.mod_small. subst v. unfold U.
  apply bv_unsigned_in_range. }
rewrite restrict_mkst_fx. split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]]; unfold region_ok, hd_r27, hd_r33;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite B27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ res 12 1 (SOff 34 0) (hd_b body 12));
           [exact (DX 34%nat _ U34) | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
         exact (hd_val_b W mem res body 12 G ltac:(lia)).
      -- apply (chunk_ok_val SEGS E _ res 13 1 (SOff 35 0) (hd_b body 13));
           [exact (DX 35%nat _ U35) | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
         exact (hd_val_b W mem res body 13 G ltac:(lia)).
    * rewrite B33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (res + len) (-2) 1 (SOff 36 0) (hd_b body (len - 2)));
           [exact (DX 36%nat _ U36) | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
         replace (res + len + -2) with (res + (len - 2)) by ring.
         exact (hd_val_b W mem res body (len - 2) G ltac:(lia)).
      -- apply (chunk_ok_val SEGS E _ (res + len) (-1) 1 (SOff 37 0) (hd_b body (len - 1)));
           [exact (DX 37%nat _ U37) | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
         replace (res + len + -1) with (res + (len - 1)) by ring.
         exact (hd_val_b W mem res body (len - 1) G ltac:(lia)).
  + apply pairwise_disjoint_of_extents.
    unfold hd_r27, hd_r33, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite B27, B33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I. left. lia.
  + split; [|split].
    * cbn [f_atoms atoms_ok hd_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite B18, B27, B33, B22. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold UP_BLK_HI, SHADOW_OFF.
      repeat split; try exact I; lia.
    * exact I.
    * cbn [f_alias alias_ok hd_facts]. split; [|exact I].
      apply U_inj. rewrite U_SAlu, U27, U22, U33. cbn [zalu_raw]. apply hd_zc. lia.
- constructor; [|constructor; [|constructor]]; split.
  + cbn [she_m she_lo she_hi]. rewrite U27. change (14 - 12) with 2.
    apply (obl_of_block SEGS B LAWS ly S W mem md E LBx (res + 12) 2 res len HAR Hin U18); lia.
  + unfold app_apart, LBx. cbn [she_m she_lo she_hi]. rewrite U27, U18. intros a Ha'.
    change (Z.min 12 14) with 12 in Ha'. change (Z.max 12 14) with 14 in Ha'.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
  + cbn [she_m she_lo she_hi]. rewrite U33. change (0 - -2) with 2.
    apply (obl_of_block SEGS B LAWS ly S W mem md E LBx (res + len + -2) 2 res len HAR Hin U18); lia.
  + unfold app_apart, LBx. cbn [she_m she_lo she_hi]. rewrite U33, U18. intros a Ha'.
    change (Z.min (-2) 0) with (-2) in Ha'. change (Z.max (-2) 0) with 0 in Ha'.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
Qed.

(* The seat at +0xa24. *)
Lemma hd_seat_a24 : forall regs (W : world SEGS) mem res sp1,
  getr regs 9 = w64 sp1 -> 70368744177664 <= sp1 <= 140737488355328 - 88 ->
  getr regs 27 = w64 res -> 4096 <= res <= UP_BLK_HI ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 80) = Some (res + 50) ->
  st_ok_pi SEGS VAL (EUP regs) ss_a24 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xa24)) mem (seg_rom SEGS))) /\
  sh_ok SEGS UPBx [] (EUP regs) (mrestrict (w_H W) mem).
Proof.
intros regs W mem res sp1 H9 Hsp H27 Hres Hslot.
assert (U9 : bv_unsigned (ew (EUP regs) 9) = sp1)
  by (rewrite (EUP_reg regs 9%bv 9 eq_refl), H9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (EUP regs) 27) = res)
  by (rewrite (EUP_reg regs 27%bv 27 eq_refl), H27; apply unsigned_lit_small; unfold UP_BLK_HI in *; lia).
rewrite restrict_mkst_fx. split; [|apply Forall_nil].
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, hd_slot80.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS (EUP regs) _ sp1 80 8 (SOff 27 50) (res + 50));
    [cbn [sv_denot]; rewrite U27; reflexivity | unfold UP_BLK_HI in *; zside | zside |].
  exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hslot).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok hd_afacts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U27. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold UP_BLK_HI in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.
(* +0xa24 .. the scan loop L6 (a0 = -1) or the check_round_trip call (a0 = 12). *)
Lemma hd_A24 : forall (W : world SEGS) regs mem md (regs0 : bvmap 5 word) (ok : bool) res sp1
    (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall x, In x hd_keep -> getr regs x = getr regs0 x) ->
  getr regs 10 = w64 (if ok then 12 else -1) -> getr regs 12 = w64 (if ok then 12 else -1) ->
  getr regs 18 = w64 SHADOW_OFF ->
  getr regs 9 = w64 sp1 -> 70368744177664 <= sp1 <= 140737488355328 - 88 ->
  getr regs 27 = w64 res -> 4096 <= res <= UP_BLK_HI ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 80) = Some (res + 50) ->
  (ok = false -> forall regsT mdT,
     getr regsT 10 = w64 (-1) -> getr regsT 12 = w64 0 -> getr regsT 13 = w64 0 ->
     getr regsT 18 = w64 SHADOW_OFF -> (forall x, In x hd_keep -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 0xa34)) mem (seg_rom SEGS)) mdT) Q) ->
  (ok = true -> forall regsT mdT,
     getr regsT 10 = w64 (res + 50) -> getr regsT 11 = getr regs0 23 -> getr regsT 12 = getr regs0 21 ->
     getr regsT 13 = w64 12 -> getr regsT 18 = w64 (res + 50) -> getr regsT 1 = Z_to_bv 64 (BASE + 0xaa4) ->
     (forall x, In x hd_keep -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_check_round_trip)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xa24)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md regs0 ok res sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ Hkeep H10 H12 H18 H9 Hsp H27 Hres
  Hslot K1 K2.
destruct (hd_seat_a24 regs W mem res sp1 H9 Hsp H27 Hres Hslot) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb0.
{ exfalso. hd_agreeU HS regs HA. rewrite branch_ne_U in Hb0. unfold U in Hb0.
  rewrite (hd_den regs _ _ 10 10%bv HA eq_refl ltac:(lia)), (hd_den regs _ _ 12 12%bv HA eq_refl ltac:(lia)),
    H10, H12, Z.eqb_refl in Hb0. discriminate. }
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1;
  hd_agreeU HS regs HA1; rewrite (hd_den regs _ _ 10 10%bv HA1 eq_refl ltac:(lia)), H10 in Hb1;
  cbn [sv_denot] in Hb1; destruct ok; vm_compute in Hb1; try discriminate.
- (* a0 = 12: +0xa7c .. check_round_trip *)
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2.
  { exfalso. hd_agreeU HS regs HA2. rewrite (hd_den regs _ _ 10 10%bv HA2 eq_refl ltac:(lia)), H10 in Hb2.
    cbn [sv_denot] in Hb2. vm_compute in Hb2. discriminate. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|].
  hd_agreeU HS regs HA3.
  up_land HF HS HJ. apply (K2 eq_refl).
  + up_rege HS (10%bv : bv 5) (SOff 27 50). exact (hd_den_off regs _ _ 27 27%bv res 50 HA3 eq_refl ltac:(lia) H27 ltac:(unfold UP_BLK_HI in *; lia)).
  + up_rege HS (11%bv : bv 5) (SOff 23 0). rewrite (hd_den regs _ _ 23 23%bv HA3 eq_refl ltac:(lia)). apply Hkeep. hd_in.
  + up_rege HS (12%bv : bv 5) (SOff 21 0). rewrite (hd_den regs _ _ 21 21%bv HA3 eq_refl ltac:(lia)). apply Hkeep. hd_in.
  + up_rege HS (13%bv : bv 5) (SLit 12). reflexivity.
  + up_rege HS (18%bv : bv 5) (SOff 27 50). exact (hd_den_off regs _ _ 27 27%bv res 50 HA3 eq_refl ltac:(lia) H27 ltac:(unfold UP_BLK_HI in *; lia)).
  + up_rege HS (1%bv : bv 5) (SOff 240 2724). hd_codeptr HS 2724.
  + intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs up_extra hd_keep HA3.
  + exact HJ.
- (* a0 = -1: +0xa2c .. the loop head *)
  paj_run_to_tok RUNTO HS HJ SHOK UPspan 0xa34; [awr_ro|]. up_memeq HF.
  hd_agreeU HS regs HA2. hd_land HS HJ. apply (K1 eq_refl).
  + up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA2 eq_refl ltac:(lia)). exact H10.
  + up_rege HS (12%bv : bv 5) (SLit 0). reflexivity.
  + up_rege HS (13%bv : bv 5) (SLit 0). reflexivity.
  + up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA2 eq_refl ltac:(lia)). exact H18.
  + intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs up_extra hd_keep HA2.
  + exact HJ.
Qed.
(* +0x974 .. +0xa24: the frame-header check. *)
Lemma hd_974 : forall (W : world SEGS) regs mem md (regs0 : bvmap 5 word) res upb len body r sp1
    (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall x, In x hd_keep -> getr regs x = getr regs0 x) ->
  In (res, len) (ablocks B lyc Sc) -> Z.of_nat (length body) = len ->
  garr8 SEGS (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) body) ->
  0 <= len < 67108864 -> r = upstream_result len -> 0 < r -> 4096 <= upb ->
  getr regs 10 = w64 (if reac_upstream_decode_c.up_ok res upb len body then 12 else -1) ->
  getr regs 12 = w64 (-1) -> getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 len -> getr regs 27 = w64 res ->
  getr regs 9 = w64 sp1 -> 70368744177664 <= sp1 <= 140737488355328 - 88 ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 80) = Some (res + 50) ->
  (reac_upstream_decode_c.up_ok res upb len body = false -> forall regsT mdT,
     getr regsT 10 = w64 (-1) -> getr regsT 12 = w64 0 -> getr regsT 13 = w64 0 ->
     getr regsT 18 = w64 SHADOW_OFF -> (forall x, In x hd_keep -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 0xa34)) mem (seg_rom SEGS)) mdT) Q) ->
  (reac_upstream_decode_c.up_ok res upb len body = true -> forall regsT mdT,
     getr regsT 10 = w64 (res + 50) -> getr regsT 11 = getr regs0 23 -> getr regsT 12 = getr regs0 21 ->
     getr regsT 13 = w64 12 -> getr regsT 18 = w64 (res + 50) -> getr regsT 1 = Z_to_bv 64 (BASE + 0xaa4) ->
     (forall x, In x hd_keep -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_check_round_trip)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x974)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md regs0 res upb len body r sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ Hkeep Hin Hbl G Hlen
  Hr Hr0 Hupb H10 H12 H18 H22 H27 H9 Hsp Hslot K1 K2.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hin) as (_ & H4096 & Hbc & _).
pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (up_result_cases len ltac:(unfold UP_NMAX; lia)) as [Hm1 | (Hq & H2 & Hev)]; [lia|].
assert (H124 : 124 <= len).
{ pose proof (Z.div_mod (len - 52) 36 ltac:(lia)). pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)). lia. }
assert (Hnch : 0 <= reac_upstream_decode_c.up_nch len) by (rewrite up_nch_result by (unfold UP_NMAX; lia); lia).
pose proof (hd_up_ok res upb len body ltac:(lia) ltac:(lia) Hnch) as Hok.
pose proof (hd_b_range body (len - 1)) as R1.
destruct (hd_seat974 regs W mem md lyc Sc res len body HAR Hin ltac:(lia) Hbl G H18 H27 H22) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EH regs res len body)) by (unfold EH; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1;
  hd_agreeH HS regs res len body HB1;
  pose proof (hd_U_byte regs res len body _ 2 12 HB1 ltac:(lia) eq_refl) as U34; change (32 + 2)%nat with 34%nat in U34;
  rewrite branch_ne_U, (hd_U_zx8 _ _ _ U34 (hd_b_range body 12)), U_SLit in Hb1; change (zcanon 136) with 136 in Hb1.
{ (* byte 12 is not 0x88 *)
  assert (Hf : reac_upstream_decode_c.up_ok res upb len body = false).
  { rewrite Hok. apply negb_true_iff in Hb1. rewrite Hb1. reflexivity. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  hd_agreeH HS regs res len body HA. pose proof (hd_agree_le _ _ HA) as HA32.
  hd_land HS HJ.
  refine (hd_A24 _ _ _ _ regs0 (reac_upstream_decode_c.up_ok res upb len body) res sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ
    _ _ _ _ _ _ _ _ _ K1 K2).
  - intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs (hd_extra res len body) hd_keep HA32.
  - up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA32 eq_refl ltac:(lia)). exact H10.
  - up_rege HS (12%bv : bv 5) (SOff 12 0). rewrite (hd_den regs _ _ 12 12%bv HA32 eq_refl ltac:(lia)), H12, Hf. reflexivity.
  - up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA32 eq_refl ltac:(lia)). exact H18.
  - up_rege HS (9%bv : bv 5) (SOff 9 0). rewrite (hd_den regs _ _ 9 9%bv HA32 eq_refl ltac:(lia)). exact H9.
  - exact Hsp.
  - up_rege HS (27%bv : bv 5) (SOff 27 0). rewrite (hd_den regs _ _ 27 27%bv HA32 eq_refl ltac:(lia)). exact H27.
  - unfold UP_BLK_HI. lia.
  - exact Hslot.
  }
apply negb_false_iff, Z.eqb_eq in Hb1.
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2;
  hd_agreeH HS regs res len body HB2;
  pose proof (hd_U_byte regs res len body _ 3 13 HB2 ltac:(lia) eq_refl) as U35; change (32 + 3)%nat with 35%nat in U35;
  rewrite branch_ne_U, (hd_U_zx8 _ _ _ U35 (hd_b_range body 13)), U_SLit in Hb2; change (zcanon 25) with 25 in Hb2.
{ (* byte 13 is not 0x19 *)
  assert (Hf : reac_upstream_decode_c.up_ok res upb len body = false).
  { rewrite Hok. apply negb_true_iff in Hb2. rewrite Hb2, Bool.andb_false_r. reflexivity. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  hd_agreeH HS regs res len body HA. pose proof (hd_agree_le _ _ HA) as HA32.
  hd_land HS HJ.
  refine (hd_A24 _ _ _ _ regs0 (reac_upstream_decode_c.up_ok res upb len body) res sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ
    _ _ _ _ _ _ _ _ _ K1 K2).
  - intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs (hd_extra res len body) hd_keep HA32.
  - up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA32 eq_refl ltac:(lia)). exact H10.
  - up_rege HS (12%bv : bv 5) (SOff 12 0). rewrite (hd_den regs _ _ 12 12%bv HA32 eq_refl ltac:(lia)), H12, Hf. reflexivity.
  - up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA32 eq_refl ltac:(lia)). exact H18.
  - up_rege HS (9%bv : bv 5) (SOff 9 0). rewrite (hd_den regs _ _ 9 9%bv HA32 eq_refl ltac:(lia)). exact H9.
  - exact Hsp.
  - up_rege HS (27%bv : bv 5) (SOff 27 0). rewrite (hd_den regs _ _ 27 27%bv HA32 eq_refl ltac:(lia)). exact H27.
  - unfold UP_BLK_HI. lia.
  - exact Hslot.
  }
apply negb_false_iff, Z.eqb_eq in Hb2.
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb3.
{ (* +0x9d0: s11 + len - 2 does not wrap *)
  exfalso. hd_agreeH HS regs res len body HB3.
  rewrite branch_ltu_U, (hd_U_not _ res (eq_trans (hd_U_reg38 regs _ _ 27 27%bv res 0 HB3 eq_refl ltac:(lia) H27 ltac:(lia))
    (eq_trans (f_equal zcanon (Z.add_0_r res)) (hd_zc res ltac:(lia)))) ltac:(lia)),
    (hd_U_reg38 regs _ _ 22 22%bv len (-2) HB3 eq_refl ltac:(lia) H22 ltac:(lia)), (hd_zc (len + -2)) in Hb3 by lia.
  apply Z.ltb_lt in Hb3. unfold UP_BLK_HI in *. lia. }
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb4;
  hd_agreeH HS regs res len body HB4;
  pose proof (hd_U_byte regs res len body _ 4 (len - 2) HB4 ltac:(lia) eq_refl) as U36; change (32 + 4)%nat with 36%nat in U36;
  rewrite branch_ne_U, (hd_U_zx8 _ _ _ U36 (hd_b_range body (len - 2))), U_SLit in Hb4; change (zcanon 194) with 194 in Hb4.
{ (* byte len - 2 is not 0xc2 *)
  assert (Hf : reac_upstream_decode_c.up_ok res upb len body = false).
  { rewrite Hok. apply negb_true_iff in Hb4. rewrite Hb4, !Bool.andb_false_r. reflexivity. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  hd_agreeH HS regs res len body HA. pose proof (hd_agree_le _ _ HA) as HA32.
  hd_land HS HJ.
  refine (hd_A24 _ _ _ _ regs0 (reac_upstream_decode_c.up_ok res upb len body) res sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ
    _ _ _ _ _ _ _ _ _ K1 K2).
  - intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs (hd_extra res len body) hd_keep HA32.
  - up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA32 eq_refl ltac:(lia)). exact H10.
  - up_rege HS (12%bv : bv 5) (SOff 12 0). rewrite (hd_den regs _ _ 12 12%bv HA32 eq_refl ltac:(lia)), H12, Hf. reflexivity.
  - up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA32 eq_refl ltac:(lia)). exact H18.
  - up_rege HS (9%bv : bv 5) (SOff 9 0). rewrite (hd_den regs _ _ 9 9%bv HA32 eq_refl ltac:(lia)). exact H9.
  - exact Hsp.
  - up_rege HS (27%bv : bv 5) (SOff 27 0). rewrite (hd_den regs _ _ 27 27%bv HA32 eq_refl ltac:(lia)). exact H27.
  - unfold UP_BLK_HI. lia.
  - exact Hslot.
  }
apply negb_false_iff, Z.eqb_eq in Hb4.
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb5.
{ (* +0x9f8: s11 + len - 1 does not wrap *)
  exfalso. hd_agreeH HS regs res len body HB5.
  rewrite branch_ltu_U, (hd_U_not _ res (eq_trans (hd_U_reg38 regs _ _ 27 27%bv res 0 HB5 eq_refl ltac:(lia) H27 ltac:(lia))
    (eq_trans (f_equal zcanon (Z.add_0_r res)) (hd_zc res ltac:(lia)))) ltac:(lia)),
    (hd_U_reg38 regs _ _ 22 22%bv len (-1) HB5 eq_refl ltac:(lia) H22 ltac:(lia)), (hd_zc (len + -1)) in Hb5 by lia.
  apply Z.ltb_lt in Hb5. unfold UP_BLK_HI in *. lia. }
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
(* +0xa24 with a2 the header's verdict *)
assert (Hok2 : reac_upstream_decode_c.up_ok res upb len body = (hd_b body (len - 1) =? 234)).
{ rewrite Hok, Hb1, Hb2, Hb4. reflexivity. }
hd_agreeH HS regs res len body HA. pose proof (hd_agree_le _ _ HA) as HA32.
pose proof (hd_U_byte regs res len body _ 5 (len - 1) HA ltac:(lia) eq_refl) as U37; change (32 + 5)%nat with 37%nat in U37.
hd_land HS HJ.
refine (hd_A24 _ _ _ _ regs0 (reac_upstream_decode_c.up_ok res upb len body) res sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ
    _ _ _ _ _ _ _ _ _ K1 K2).
- intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs (hd_extra res len body) hd_keep HA32.
- up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA32 eq_refl ltac:(lia)). exact H10.
- up_rege HS (12%bv : bv 5) hd_a2.
  apply hd_w64_U. rewrite (hd_U_a2 _ _ U37 R1), Hok2. reflexivity.
- up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA32 eq_refl ltac:(lia)). exact H18.
- up_rege HS (9%bv : bv 5) (SOff 9 0). rewrite (hd_den regs _ _ 9 9%bv HA32 eq_refl ltac:(lia)). exact H9.
- exact Hsp.
- up_rege HS (27%bv : bv 5) (SOff 27 0). rewrite (hd_den regs _ _ 27 27%bv HA32 eq_refl ltac:(lia)). exact H27.
- unfold UP_BLK_HI. lia.
- exact Hslot.
Qed.
(* +0x96c .. +0x974 / +0xa24: `li a2, -1` and the channel-count test. *)
Lemma hd_96c : forall (W : world SEGS) regs mem md (regs0 : bvmap 5 word) res upb len body r sp1
    (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall x, In x hd_keep -> getr regs x = getr regs0 x) ->
  In (res, len) (ablocks B lyc Sc) -> Z.of_nat (length body) = len ->
  garr8 SEGS (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) body) ->
  0 <= len < 67108864 -> r = upstream_result len -> 4096 <= upb ->
  getr regs 10 = w64 (if reac_upstream_decode_c.up_ok res upb len body then 12 else -1) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 21 = w64 r -> getr regs 22 = w64 len -> getr regs 27 = w64 res ->
  getr regs 9 = w64 sp1 -> 70368744177664 <= sp1 <= 140737488355328 - 88 ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 80) = Some (res + 50) ->
  (reac_upstream_decode_c.up_ok res upb len body = false -> forall regsT mdT,
     getr regsT 10 = w64 (-1) -> getr regsT 12 = w64 0 -> getr regsT 13 = w64 0 ->
     getr regsT 18 = w64 SHADOW_OFF -> (forall x, In x hd_keep -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 0xa34)) mem (seg_rom SEGS)) mdT) Q) ->
  (reac_upstream_decode_c.up_ok res upb len body = true -> forall regsT mdT,
     getr regsT 10 = w64 (res + 50) -> getr regsT 11 = getr regs0 23 -> getr regsT 12 = getr regs0 21 ->
     getr regsT 13 = w64 12 -> getr regsT 18 = w64 (res + 50) -> getr regsT 1 = Z_to_bv 64 (BASE + 0xaa4) ->
     (forall x, In x hd_keep -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_check_round_trip)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x96c)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md regs0 res upb len body r sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ Hkeep Hin Hbl G Hlen
  Hr Hupb H10 H18 H21 H22 H27 H9 Hsp Hslot K1 K2.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hin) as (_ & H4096 & Hbc & _).
pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (up_result_range len ltac:(unfold UP_NMAX; lia)) as Hrr.
destruct (up_seat0 0x96c regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb;
  hd_agreeU HS regs HB; rewrite hd_bge_blt in Hb;
  lazymatch type of Hb with context [sv_denot ?E (SOff 21 0)] =>
    rewrite (up_lt0_s5 E r (eq_trans (proj1 HB 21%nat ltac:(lia)) (hd_ew_reg regs _ 21 21%bv r eq_refl H21))
      ltac:(lia)) in Hb end.
- (* 0 >= s5: the count is -1, and so is the verdict *)
  apply negb_true_iff, Z.ltb_ge in Hb.
  assert (Hf : reac_upstream_decode_c.up_ok res upb len body = false).
  { unfold reac_upstream_decode_c.up_ok. rewrite (up_nch_result len ltac:(unfold UP_NMAX; lia)), <- Hr.
    replace (0 <=? r) with false by (symmetry; apply Z.leb_gt;
      destruct (up_result_cases len ltac:(unfold UP_NMAX; lia)) as [Hm | (Hq & H2 & _)]; lia).
    rewrite Bool.andb_false_r. reflexivity. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  hd_agreeU HS regs HA. hd_land HS HJ.
  refine (hd_A24 _ _ _ _ regs0 (reac_upstream_decode_c.up_ok res upb len body) res sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ
    _ _ _ _ _ _ _ _ _ K1 K2).
  + intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs up_extra hd_keep HA.
  + up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA eq_refl ltac:(lia)). exact H10.
  + up_rege HS (12%bv : bv 5) (SLit 18446744073709551615). rewrite Hf. apply bv_eq. vm_compute. reflexivity.
  + up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA eq_refl ltac:(lia)). exact H18.
  + up_rege HS (9%bv : bv 5) (SOff 9 0). rewrite (hd_den regs _ _ 9 9%bv HA eq_refl ltac:(lia)). exact H9.
  + exact Hsp.
  + up_rege HS (27%bv : bv 5) (SOff 27 0). rewrite (hd_den regs _ _ 27 27%bv HA eq_refl ltac:(lia)). exact H27.
  + unfold UP_BLK_HI. lia.
  + exact Hslot.
- (* 0 < s5: the header check *)
  apply negb_false_iff, Z.ltb_lt in Hb.
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  hd_agreeU HS regs HA. hd_land HS HJ.
  refine (hd_974 _ _ _ _ regs0 res upb len body r sp1 Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ _ Hin Hbl G Hlen Hr Hb
    Hupb _ _ _ _ _ _ Hsp _ K1 K2).
  + intros x Hx. rewrite <- (Hkeep x Hx). revert x Hx. up_kept HS regs up_extra hd_keep HA.
  + up_rege HS (10%bv : bv 5) (SOff 10 0). rewrite (hd_den regs _ _ 10 10%bv HA eq_refl ltac:(lia)). exact H10.
  + up_rege HS (12%bv : bv 5) (SLit 18446744073709551615). apply bv_eq. vm_compute. reflexivity.
  + up_rege HS (18%bv : bv 5) (SOff 18 0). rewrite (hd_den regs _ _ 18 18%bv HA eq_refl ltac:(lia)). exact H18.
  + up_rege HS (22%bv : bv 5) (SOff 22 0). rewrite (hd_den regs _ _ 22 22%bv HA eq_refl ltac:(lia)). exact H22.
  + up_rege HS (27%bv : bv 5) (SOff 27 0). rewrite (hd_den regs _ _ 27 27%bv HA eq_refl ltac:(lia)). exact H27.
  + up_rege HS (9%bv : bv 5) (SOff 9 0). rewrite (hd_den regs _ _ 9 9%bv HA eq_refl ltac:(lia)). exact H9.
  + exact Hslot.
Qed.

(* The registers +0xaa4 .. +0xab4 leave alone. *)
Definition hd_keepB : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv].

(* +0xaa4 .. the check_braid call (+0xab4): a3 = 12, a0 = s2, a1 = s7, a2 = s5. *)
Lemma hd_AA4 : forall (W : world SEGS) regs mem md (Q : world SEGS -> config -> Prop)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall regsT mdT,
     getr regsT 10 = getr regs 18 -> getr regsT 11 = getr regs 23 -> getr regsT 12 = getr regs 21 ->
     getr regsT 13 = w64 12 -> getr regsT 1 = Z_to_bv 64 (BASE + 0xab8) ->
     (forall x, In x hd_keepB -> getr regsT x = getr regs x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_check_braid)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xaa4)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ HK.
destruct (up_seat0 0xaa4 regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|].
hd_agreeU HS regs HA. up_land HF HS HJ. apply HK.
- up_rege HS (10%bv : bv 5) (SOff 18 0). exact (hd_den regs _ _ 18 18%bv HA eq_refl ltac:(lia)).
- up_rege HS (11%bv : bv 5) (SOff 23 0). exact (hd_den regs _ _ 23 23%bv HA eq_refl ltac:(lia)).
- up_rege HS (12%bv : bv 5) (SOff 21 0). exact (hd_den regs _ _ 21 21%bv HA eq_refl ltac:(lia)).
- up_rege HS (13%bv : bv 5) (SLit 12). reflexivity.
- up_rege HS (1%bv : bv 5) (SOff 240 2744). hd_codeptr HS 2744.
- up_kept HS regs up_extra hd_keepB HA.
- exact HJ.
Qed.
End g.
