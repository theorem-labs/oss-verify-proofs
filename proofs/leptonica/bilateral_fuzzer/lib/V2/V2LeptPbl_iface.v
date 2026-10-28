(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoomBL LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixHdr V2LeptPixCreate V2LeptPixCopyT V2LeptBl_iface V2LeptBilCW3 V2LeptBilCW4 V2LeptBilGrayW.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptPbl_iface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptRoomBL7RB_pixTK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure?alloc_margin_geC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure<alloc_marginC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45RB_bcK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00c5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface<RB_bc_nonnegC56Stdlib6ZArith6BinInt1Z3eqbc5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPbl_iface6RB_pbl".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition PBL_WIN : Z := 112 + 64 + 5120.
Definition PC_pixBilateral : Z := 234140.
Definition RK_pbl : Z := (3 * (RK_pix + RK_bg) + RK_pix)%Z.
Definition RB_pbl32 (w h : Z) : Z := (3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bg w h) + RB_pixT (4 * (wpl_of w 32 * h)))%Z.
Definition RB_pbl (w h d : Z) : Z := if (d =? 8)%Z then RB_bg w h else if (d =? 32)%Z then RB_pbl32 w h else 0%Z.

Lemma RB_bc_nonneg : forall w h, (0 <= h)%Z -> (0 <= RB_bc w h)%Z.
Proof.
  intros w h Hh. unfold RB_bc, RB_it, RB_amb.
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 2 * 11) 8 * (h + 2 * 11)))).
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 22) 8 * (h + 22)))). pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))).
  pose proof (alloc_margin_ge 80 ltac:(lia)). pose proof (alloc_margin_ge (8 * h) ltac:(lia)). lia.
Qed.
Lemma RB_pbl_nonneg : forall w h d, (0 <= h)%Z -> (0 <= RB_pbl w h d)%Z.
Proof.
  intros w h d Hh. pose proof (RB_bc_nonneg w h Hh).
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))). pose proof (RB_pixT_nonneg (4 * (wpl_of w 32 * h))).
  unfold RB_pbl, RB_pbl32, RB_bg. destruct (d =? 8)%Z; [lia|]. destruct (d =? 32)%Z; lia.
Qed.
Lemma RK_pbl_val : RK_pbl = 269%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptPbl_iface ()) [] "p;1p;2g0000j10Tg0013j11Tg000Uj13Tg009[j22Tg00MTg00PX#0#0#0#0#1#1#0#1#3'2o"). Qed.

Section PblIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition pixBilateral_contract : Prop :=
  forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.

Definition pixBilateral_null_contract : Prop :=
  forall fr cs C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 0 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  (forall fr' cs' m' regs', W C A m' md -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
End PblIface.
