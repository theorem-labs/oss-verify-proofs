(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the address and class-constant table of lib/A/Rt/StackFree6S.v (the class-6 release entry __asan_stack_free_6 of libreac/fuzz_disco's ASan build), split from it as lib/A/Rt/StackMalloc6Tbl.v is from StackMalloc6.v: the entry's code ranges and control points, the class-6 frame constants, the constant row of the fill pattern at 0x10350 (an AR constant cell, as cgif_rgb_fuzzer YF3h.v's sf_rodata rows are), the symbolic states of the walk and their computed facts; module names. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0s YG0t.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AB1w.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition CID : Z := 6.
Definition SF_ENTRY : Z := 0x3dc5c.
Definition SF6_ENTRY : Z := AB1w.tfib_A___asan_stack_free_6.
Definition SF_FILL : Z := 0x3dc84.
Definition SF_RET : Z := 0x3dca0.
Definition SF_HELP : Z := 0x3dca4.
Definition SF_K : Z := 0x10350.
Definition SF_WIN : Z := 16.
Definition FS_B : Z := 4096.
Definition FS_N : Z := 256.
Definition FS_FLOFF : Z := 0x8e00.
Definition FS_FROFF : Z := 0x609000.
Definition F5W : Z := 0xf5f5f5f5f5f5f5f5.
Definition SH_REL : Z := 0xf5.
Definition SH_N : Z := 512.
Definition FILL_N : Z := 64.
Definition FF_OFF : Z := FS_B - 8.
Definition RO_END : Z := 0xa6908.
Definition sf_keep : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sf_ranges : list (Z * nat) := [(SF_ENTRY, 18%nat); (SF_HELP, 28%nat)].
Definition tbl_sf : ctable := Eval vm_compute in build_ranges sf_ranges TEmpty.
Lemma tbl_sf_eq : tbl_sf = build_ranges sf_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_sf). Qed.
Lemma tbl_sf_ok : table_ok tfibsegs tbl_sf.
Proof. rewrite tbl_sf_eq. apply build_ranges_ok; [unfold sf_ranges; repeat constructor; cbn; discriminate | apply table_ok_empty]. Qed.
Lemma ret_at_end : clookup tbl_sf SF_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
Lemma sf_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_sf FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_sf tbl_sf_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1.
split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma sf_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_sf FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_sf tbl_sf_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1.
split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition aFLG : nat := 32.
Definition aSH : nat := 33.
Definition stk : YP09.region := YP09.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 [].
Definition rFF : YP09.region := YP09.mkRegion (Some 10%nat) FF_OFF FS_B FF_OFF FF_OFF [YP09.mkChunk FF_OFF (CVal 8 (SOff aFLG 0))].
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [].
Definition sf_rodata : list (Z * Z * list (Z * N * Z)) := (SF_K, 8, [(0, 8%N, F5W)]) :: icpt_rodata.
Definition rSH : YP09.region := YP09.mkRegion (Some aSH) 0 SH_N 0 SH_N [].
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else AF0x.TFIB_IMG_END.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition sf_facts (hi : bool) : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + SF_WIN) kHighMemEnd 4); (10%nat, mkAF (ffLO hi) (ffHI hi) 5);
(aFLG, mkAF AF0x.TFIB_IMG_END (CEIL_MAX - 1) 0)].
Definition sf_mem : smem := stk :: rFF :: rFLG :: map ro_region sf_rodata.
Definition ss0 (hi : bool) : sstate := mkSS SF_ENTRY sr_atoms sf_mem None (mkFacts (sf_facts hi) [] []).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_sf FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sf FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition e1H : sstate := Eval vm_compute in fst (RUNTO SF_FILL (ss0 true)).
Definition e1L : sstate := Eval vm_compute in fst (RUNTO SF_FILL (ss0 false)).
Definition e1 (hi : bool) : sstate := if hi then e1H else e1L.
Lemma r_1 : forall hi, RUNTO SF_FILL (ss0 hi) = (e1 hi, RS_running).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition memE1 : smem := Eval vm_compute in ss_mem e1H.
Lemma e1_mem : forall hi, ss_mem (e1 hi) = memE1.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition ssC (hi : bool) : sstate :=
mkSS (ss_pc (e1 hi)) (sr_set (ss_regs (e1 hi)) 10%bv (SOff aSH 0)) (rSH :: ss_mem (e1 hi)) (ss_resv (e1 hi)) (ss_facts (e1 hi)).
Definition e2H : sstate := Eval vm_compute in fst (RUN (ssC true)).
Definition e2L : sstate := Eval vm_compute in fst (RUN (ssC false)).
Definition e2 (hi : bool) : sstate := if hi then e2H else e2L.
Lemma r_2 : forall hi, RUN (ssC hi) = (e2 hi, RS_stopped (SR_jalr (SOff 1 0))).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition a0e : sv := SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Lemma e1_facts : forall hi, ss_pc (e1 hi) = SF_FILL /\ ss_resv (e1 hi) = None /\ RG (e1 hi) 10 = a0e.
Proof. intros [|]; repeat split; vm_compute; reflexivity. Qed.
Lemma rSH_wf : YP09.region_wf rSH = true.
Proof. vm_compute. reflexivity. Qed.
Definition rSH2 : YP09.region := Eval vm_compute in nth 0 (ss_mem e2H) stk.
Definition rSTK2 : YP09.region := Eval vm_compute in nth 1 (ss_mem e2H) stk.
Definition rFF2 : YP09.region := Eval vm_compute in nth 2 (ss_mem e2H) stk.
Definition rFLG2 : YP09.region := Eval vm_compute in nth 3 (ss_mem e2H) stk.
Lemma e2_regions : forall hi, nth_error (ss_mem (e2 hi)) 0 = Some rSH2 /\ nth_error (ss_mem (e2 hi)) 1 = Some rSTK2 /\
nth_error (ss_mem (e2 hi)) 2 = Some rFF2 /\ nth_error (ss_mem (e2 hi)) 3 = Some rFLG2.
Proof. intros [|]; repeat split; vm_compute; reflexivity. Qed.
Lemma e2_facts : forall hi, ss_pc (e2 hi) = SF_RET /\ ss_resv (e2 hi) = None /\
forallb (fun r => sv_eqb (RG (e2 hi) r) (SOff (Z.to_nat r) 0)) sf_keep = true.
Proof. intros [|]; repeat split; vm_compute; reflexivity. Qed.
Lemma rSH2_shape : YP09.r_base rSH2 = Some aSH /\ YP09.r_wlo rSH2 = 0 /\ YP09.r_whi rSH2 = 512 /\
forall j, (j < 64)%nat -> nth_error (YP09.r_chunks rSH2) j = Some (YP09.mkChunk (504 - 8 * Z.of_nat j) (CVal 8 (SLit F5W))).
Proof.
repeat split; try (vm_compute; reflexivity).
intros j Hj. do 64 (destruct j as [|j]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.
Lemma rSH2_nth : forall q, 0 <= q < FILL_N ->
nth_error (YP09.r_chunks rSH2) (Z.to_nat (FILL_N - 1 - q)) = Some (YP09.mkChunk (8 * q) (CVal 8 (SLit F5W))).
Proof.
intros q Hq. unfold FILL_N in *. pose proof (proj2 (proj2 (proj2 rSH2_shape)) (Z.to_nat (63 - q)) ltac:(lia)) as X.
replace (64 - 1 - q) with (63 - q) by lia. rewrite X. do 3 f_equal. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma rSTK2_shape : YP09.r_base rSTK2 = Some 2%nat /\ YP09.r_wlo rSTK2 = - SF_WIN /\ YP09.r_whi rSTK2 = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma rFLG2_shape : YP09.r_base rFLG2 = Some aFLG /\ YP09.r_wlo rFLG2 = 0 /\ YP09.r_whi rFLG2 = 1 /\
nth_error (YP09.r_chunks rFLG2) 0 = Some (YP09.mkChunk 0 (CVal 1 (SLit 0))).
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma sf_windows : forall E a, in_wrange E sf_mem a ->
(bv_unsigned (ew E 2) - SF_WIN <= a < bv_unsigned (ew E 2)) \/ a = bv_unsigned (ew E aFLG).
Proof.
intros E a Hin. unfold SF_WIN, aFLG. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hb).
vm_compute in Ht.
repeat (destruct Ht as [Hq | Ht];
[injection Hq as <- <- <-; cbn [base_val] in Hb;
first [right; lia | left; lia | exfalso; lia] |]).
destruct Ht.
Qed.
Lemma ssC_windows : forall hi E a, in_wrange E (ss_mem (ssC hi)) a ->
(bv_unsigned (ew E aSH) <= a < bv_unsigned (ew E aSH) + SH_N) \/
(bv_unsigned (ew E 2) - SF_WIN <= a < bv_unsigned (ew E 2)) \/ a = bv_unsigned (ew E aFLG).
Proof.
intros zhi E a Hin. unfold SF_WIN, SH_N, aSH, aFLG. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hb).
destruct zhi; vm_compute in Ht;
repeat (destruct Ht as [Hq | Ht];
[injection Hq as <- <- <-; cbn [base_val] in Hb;
first [left; lia | right; right; lia | right; left; lia | exfalso; lia] |]);
destruct Ht.
Qed.
Lemma a0e_denot : forall E FF, bv_unsigned (ew E 10) = FF -> 0 <= FF < 2 ^ 64 ->
sv_denot E a0e = Z_to_bv 64 (SHADOW_OFF + FF / 8).
Proof.
intros E FF HFF Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a0e)). f_equal.
change (bv_unsigned (sv_denot E a0e)) with (U E a0e). rewrite (U_zev E a0e) by (vm_compute; reflexivity).
unfold a0e. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, !Z.add_0_r.
change (Z.land (zcanon 3) 63) with 3. change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SHADOW_OFF.
pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound FF 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small FF) by lia. rewrite (zcanon_small (FF / 8)) by lia. apply zcanon_small. lia.
Qed.
Lemma aview_of_val_mem : forall (Hh : word -> bool) mem a (k : nat) (w : nat) v,
val_mem tfibsegs (mrestrict Hh mem) a w v -> (k < w)%nat ->
aview tfibsegs Hh mem (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros Hh mem a k w v Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k).
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma f5_byte : forall k, (k < 8)%nat -> YG0f.le_byte F5W 8 k = SH_REL.
Proof. intros k Hk. unfold SH_REL. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso. lia. Qed.
Lemma F5W_range : 0 <= F5W < 2 ^ (8 * Z.of_N 8).
Proof. unfold F5W. split; [discriminate | reflexivity]. Qed.
Lemma hs_kept_gen : forall (Hh : word -> bool) (mem mem' : word -> option byte) (P : Z -> Prop),
(forall z : word, ~ P (bv_unsigned z) -> mem' z = mem z) ->
(forall a, P a -> exists m0, apresent Hh m0 a) ->
forall a, in_band_rw a -> Hh (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros Hh mem mem' P MEQ PRES a Ha Hhid. rewrite MEQ; [reflexivity|]. intros HP.
rewrite unsigned_lit_small in HP by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (PRES a HP) as (m0 & Hf & _). rewrite Hhid in Hf. discriminate Hf.
Qed.
Lemma frame_off_6 : forall p, fs_frame_off CID p = FS_FROFF + p * FS_B.
Proof.
intros p. unfold fs_frame_off, CID, FS_FROFF, FS_B.
change (Z.shiftl 1 kStackSizeLog) with 1048576. change kFakeFramesOff with 36864.
change (fs_frame_bytes 6) with 4096. lia.
Qed.
Lemma flag_off_6 : forall p, fs_flag_off CID p = FS_FLOFF + p.
Proof.
intros p. unfold fs_flag_off, CID, FS_FLOFF.
change kFakeFlagsOff with 4096. change (fs_flags_off 6) with 32256. lia.
Qed.
Lemma frames_6 : fs_frames CID = FS_N.
Proof. vm_compute. reflexivity. Qed.
Lemma fbytes_6 : fs_frame_bytes CID = FS_B.
Proof. vm_compute. reflexivity. Qed.
Lemma gconsts :
kHighMemBeg = 17594333495296 /\ kHighMemEnd = 140737488355328 /\
kLowShadowBeg = 2147446784 /\ kLowShadowEnd = 2415882240 /\ kLowMemEnd = 2147450880 /\
kHighShadowBeg = 2201439137792 /\ kFakeStackSize = 11571200 /\ SHADOW_OFF = 2147450880 /\
ESTACK = 4096 /\ AF0x.TFIB_IMG_LO < kFakeStackSize /\
RO_END = 0xa6908 /\ RO_END < AF0x.TFIB_IMG_END /\ AF0x.TFIB_IMG_END <= kLowMemEnd /\
AF0x.TFIB_IMG_END + kFakeStackSize <= kLowShadowBeg /\
FS_B = 4096 /\ FS_N = 256 /\ FS_FROFF = 6328320 /\ FS_FLOFF = 36352 /\ SF_WIN = 16 /\ SH_N = 512 /\ FILL_N = 64.
Proof. repeat split; vm_compute; first [reflexivity | discriminate]. Qed.
Lemma sf_rodata_chk : forall ly, rodata_chk ly sf_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma sf_span_cid : forall n, sf_span CID n = SH_N.
Proof. intros n. vm_compute. reflexivity. Qed.
Lemma SF6_ENTRY_eq : SF6_ENTRY = SF_ENTRY.
Proof. vm_compute. reflexivity. Qed.
Lemma sf_keep_ok : forall rz, In rz sf_keep -> 0 <= rz /\ bv_unsigned (Z_to_bv 5 rz) = rz.
Proof.
intros rz Hrz. assert (Hr : 0 <= rz < 32) by (unfold sf_keep in Hrz; cbn in Hrz; lia).
split; [lia|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. exact Hr.
Qed.
Lemma sf_keep_callee : forall r, acallee_saved r -> In r sf_keep.
Proof. intros r Hr. unfold acallee_saved in Hr. unfold sf_keep. cbn. lia. Qed.
Lemma al_pows : 2 ^ 4 = 16 /\ 2 ^ 5 = 32 /\ 2 ^ 0 = 1.
Proof. repeat split; reflexivity. Qed.
End e.
