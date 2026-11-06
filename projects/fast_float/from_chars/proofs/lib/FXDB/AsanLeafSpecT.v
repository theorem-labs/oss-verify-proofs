(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg FxLin FxCore FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxWvC FxChMain.

Module AsanSpec.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTbl AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition M1c : smodel := M1.
Definition H0 : positive := Eval vm_compute in s_next S1.
Definition hvar (k : nat) : lin := lvar (dvar H0 k).
Definition HFACTS (lo hi : Z) : list fact :=
  FRange (hvar 17) 1 4095 :: FRange (hvar 16) lo hi :: List.map (fun k => FRange (hvar k) 0 255) (List.seq 0 16).
Definition S1c (lo hi : Z) : sst := SST (s_pc S1) (s_regs S1) (s_rgs S1) (HFACTS lo hi ++ s_facts S1) (dvar H0 18) (s_resv S1).
Definition ARGC : lin := lvar 5.
Definition LARGV0 : lin := lvar 11.

(* [comment removed for export] *)
Definition USAGE_PRE : list Z := [117;115;97;103;101;58;32].                        (* [comment removed for export] *)
Definition USAGE_SUF : list Z := [32;73;78;80;85;84;10].                            (* [comment removed for export] *)
Definition CANNOT_PRE : list Z := [99;108;105;58;32;99;97;110;110;111;116;32;111;112;101;110;32].   (* [comment removed for export] *)
Definition MSG_SHORT : list Z := [99;108;105;58;32;105;110;112;117;116;32;115;104;111;114;116;101;114;32;116;104;97;110;32;104;101;97;100;101;114;10].
Definition MSG_OVR : list Z := [99;108;105;58;32;99;111;110;102;105;103;95;108;101;110;32;111;118;101;114;114;117;110;115;32;105;110;112;117;116;10].
Definition SH_USAGE : shp := ShEmit [PD 2 (SArgs USAGE_PRE 0 LARGV0 USAGE_SUF) (lconst 0)] 2.
Definition SH_CANNOT : shp := ShEmit [PD 2 (SArgs CANNOT_PRE 1 (hvar 17) [10]) (lconst 0)] 2.
Definition SH_TOP (file : shp) : shp := ShIf ARGC 2 2 (ShAlt2 SH_CANNOT file) SH_USAGE.

(* [comment removed for export] *)
Definition SH_SHORT : shp := ShEmit [PD 2 (SLit MSG_SHORT) (lconst 0)] 2.
Definition SH_OVR : shp := ShEmit [PD 2 (SLit MSG_OVR) (lconst 0)] 2.
Fixpoint zl (n : nat) : list Z := match n with O => [] | Datatypes.S k => 48 :: 10 :: zl k end.
Definition CALLS (n : nat) : shp := ShEmit [PD 1 (SLit (zl n)) (lconst 0)] 0.
Definition BODYC (cl : lin) : shp :=
  ShIf cl 0 0 (CALLS 1) (ShBit (hvar 2) 1 (ShBit (hvar 2) 0 (CALLS 4) (CALLS 3)) (ShBit (hvar 2) 0 (CALLS 2) (CALLS 1))).
Definition T63 : Z := 9223372036854775808.
Definition CLA : lin := Eval vm_compute in ladd (hvar 0) (lscale 256 (hvar 1)).
Definition CLB : lin := Eval vm_compute in laddc CLA (- 32768).
Definition LA : lin := Eval vm_compute in ladd (laddc CLA 5) (lneg (hvar 16)).      (* [comment removed for export] *)
Definition LB : lin := Eval vm_compute in laddc LA (- 32768).
Definition FILE_W : shp := ShIf (hvar 1) 0 127 (ShIf LA 0 T63 SH_OVR (BODYC CLA)) (ShIf LB 0 T63 SH_OVR (BODYC CLB)).

(* [comment removed for export] *)
Definition TOPK {N : Type} (kfile : @mchain N) : @mchain N :=
  MSplit ARGC 1 (MSel MEnd MEnd) (MSplit ARGC 2 (MSel kfile MEnd) (MSel MEnd MEnd)).
(* [comment removed for export] *)
End AsanSpec.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafSpecT.AsanSpec OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCoNFT.

Module AsanLeafSpec.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg FxLin FxCore FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxWvC FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafSpecT.AsanSpec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCoNFT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT.AsanCoNFDefs.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma uE_lconst0 : forall E, Z.to_nat (uE E (lconst 0)) = O.
Proof. intros E. unfold uE. rewrite lden_lconst. reflexivity. Qed.

Lemma pre_usage : s2b "usage: " = List.map (Z_to_bv 8) USG_PRE. Proof. vm_compute. reflexivity. Qed.
Lemma suf_usage : s2b " INPUT" ++ nl = List.map (Z_to_bv 8) USG_SUF. Proof. vm_compute. reflexivity. Qed.
Lemma pre_cannot : s2b "cli: cannot open " = List.map (Z_to_bv 8) CANNOT_PRE. Proof. vm_compute. reflexivity. Qed.
Lemma pre_cannot_n : s2b "cli: cannot open " = List.map (Z_to_bv 8) CO_PRE_N. Proof. vm_compute. reflexivity. Qed.
Lemma suf_nl : nl = List.map (Z_to_bv 8) [10]. Proof. vm_compute. reflexivity. Qed.

Section Den.
Variables (path0 : path) (fs0 : Fs.Fs) (argv0 : list byte).

(* [comment removed for export] *)
#[using="Type"] Theorem shu_spec : forall E, uE E (lvar 11) = Z.of_nat (length argv0) ->
  shp_den path0 fs0 argv0 E SHU = t_die (msg_usage argv0) fs0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E HL. unfold SHU, t_die, msg_usage, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes sarg].
  rewrite uE_lconst0, skipn_O, app_nil_r, HL, Nat2Z.id, firstn_all. rewrite pre_usage, <- suf_usage. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem shcannot_spec : forall E, uE E (hvar 17) = Z.of_nat (length path0) ->
  shp_den path0 fs0 argv0 E SH_CANNOT = t_die (msg_cannot_open path0) fs0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E HL. unfold SH_CANNOT, t_die, msg_cannot_open, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes sarg].
  rewrite uE_lconst0, skipn_O, app_nil_r, HL, Nat2Z.id, firstn_all. rewrite pre_cannot, suf_nl. reflexivity.
Qed.
End Den.

(* [comment removed for export] *)
Theorem shnf_spec : forall path0 fs0 p E, uE E LPNF = Z.of_nat (length p) ->
  shp_den path0 fs0 p E SH_NF = t_die (msg_cannot_open p) fs0.
Proof.
  intros path0 fs0 p E HL. unfold SH_NF, t_die, msg_cannot_open, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes sarg].
  rewrite uE_lconst0, skipn_O, app_nil_r, HL, Nat2Z.id, firstn_all. rewrite pre_cannot_n, suf_nl. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem shd_spec : forall path0 fs0 argv0 E, shp_den path0 fs0 argv0 E SHD =
  t_alt2 (t_die (msg_cannot_open [Z_to_bv 8 46]) fs0) (t_die (msg_read_error [Z_to_bv 8 46]) fs0).
Proof.
  intros path0 fs0 argv0 E. unfold SHD, t_die, msg_cannot_open, msg_read_error, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs.
  cbn [pd_ch pd_off pd_src src_bytes]. rewrite !uE_lconst0, !skipn_O, !app_nil_r. reflexivity.
Qed.
(* [comment removed for export] *)
End AsanLeafSpec.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT AsanCoNFT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafSpecT.AsanLeafSpec OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem shnf_specT : forall path0 fs0 p E, uE E LPNFT = Z.of_nat (length p) ->
  shp_den path0 fs0 p E SH_NFT = t_die (msg_cannot_open p) fs0.
Proof.
  intros path0 fs0 p E HL. unfold SH_NFT, t_die, msg_cannot_open, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes sarg].
  rewrite uE_lconst0, skipn_O, app_nil_r, HL, Nat2Z.id, firstn_all. rewrite pre_cannot_n, suf_nl. reflexivity.
Qed.
(* [comment removed for export] *)
