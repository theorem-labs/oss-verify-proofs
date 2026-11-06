(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec RefLayout ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChEnt FxChSep FxChain FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanErrT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanErrT.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxSNodes AsanRdErr AsanLayoutT AsanLeafEntryT AsanTop0.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageThmT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLayoutT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafEntryT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTop0 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageThmT.AsanLeafLib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma H0_next : s_next TMAIN = H0. Proof. reflexivity. Qed.
Lemma H0_17 : (17 <= H0)%positive. Proof. vm_compute. discriminate. Qed.
Lemma dvar_ge : forall h k, (h <= dvar h k)%positive.
Proof. intros h k. unfold dvar. apply Pos2Nat.inj_le. rewrite Nat2Pos.id by lia. lia. Qed.
Lemma dvar_lt' : forall h i j, (i < j)%nat -> (dvar h i < dvar h j)%positive.
Proof. intros h i j H. unfold dvar. apply Pos2Nat.inj_lt. rewrite !Nat2Pos.id by lia. lia. Qed.
Lemma dvar_sub : forall h k, (Pos.to_nat (dvar h k) - Pos.to_nat h)%nat = k.
Proof. intros h k. unfold dvar. rewrite Nat2Pos.id by lia. lia. Qed.

(* [comment removed for export] *)
Section Vals.
Variables (data : list byte) (p1 : list byte).
Definition dval (k : nat) : word :=
  if Nat.ltb k 16 then Z_to_bv 64 (bv_unsigned (nth k data (Z_to_bv 8 0)))
  else if Nat.eqb k 16 then Z_to_bv 64 (flen_of (length data)) else Z_to_bv 64 (Z.of_nat (length p1)).
Definition ext (E : valu) : valu :=
  fun x => if (Pos.leb H0 x && Pos.ltb x (dvar H0 18))%bool then dval (Pos.to_nat x - Pos.to_nat H0) else E x.
#[using="Type"] Lemma ext_agree : forall E, agree H0 E (ext E).
Proof. LiaFast.lf_pins LiaFast.u0. intros E x Hx. unfold ext. replace (Pos.leb H0 x) with false by (symmetry; apply Pos.leb_gt; exact Hx). reflexivity. Qed.
#[using="Type"] Lemma ext_at : forall E k, (k < 18)%nat -> ext E (dvar H0 k) = dval k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E k Hk. unfold ext. replace (Pos.leb H0 (dvar H0 k)) with true by (symmetry; apply Pos.leb_le; apply dvar_ge).
  replace (Pos.ltb (dvar H0 k) (dvar H0 18)) with true by (symmetry; apply Pos.ltb_lt; apply dvar_lt'; exact Hk).
  cbn [andb]. rewrite dvar_sub. reflexivity.
Qed.
#[using="Type"] Lemma ext_u17 : forall E l, lwf 17 l = true -> uE (ext E) l = uE E l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E l Hl. unfold uE. symmetry. rewrite (lden_agree 17 E (ext E) l Hl); [reflexivity|].
  exact (agree_mono 17 H0 E (ext E) H0_17 (ext_agree E)).
Qed.
#[using="Type"] Lemma u_hvar : forall E k, (k < 18)%nat -> uE (ext E) (hvar k) = bv_unsigned (dval k).
Proof. LiaFast.lf_pins LiaFast.u0. intros E k Hk. unfold uE, hvar. rewrite lden_lvar, (ext_at E k Hk). reflexivity. Qed.
#[using="Type"] Lemma dval_byte : forall k, (k < 16)%nat -> bv_unsigned (dval k) = bv_unsigned (nth k data (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k Hk. unfold dval. replace (Nat.ltb k 16) with true by (symmetry; apply Nat.ltb_lt; exact Hk).
  pose proof (bv_unsigned_in_range 8 (nth k data (Z_to_bv 8 0))) as X. change (bv_modulus 8) with 256 in X.
  apply u_small64. unfold two64. lia.
Qed.
End Vals.

(* [comment removed for export] *)
Fixpoint addfs (S : sst) (fs : list fact) : sst := match fs with [] => S | f :: r => addfs (add_fact S f) r end.
Lemma addfs_next : forall fs S, s_next (addfs S fs) = s_next S.
Proof. induction fs as [|f r IH]; intros S; cbn [addfs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Definition CLSF (lo hi : Z) : list fact := rev (HFACTS lo hi) ++ [FRange ARGC 2 2] ++ FSC.
Lemma S1c2_eq : forall lo hi, S1c2 lo hi = addfs (bump TMAIN (dvar H0 18)) (CLSF lo hi).
Proof. intros lo hi. reflexivity. Qed.
Lemma S1c2_next : forall lo hi, s_next (S1c2 lo hi) = dvar H0 18.
Proof. intros lo hi. rewrite S1c2_eq, addfs_next. reflexivity. Qed.
Lemma CLSF_wf : forall lo hi, forallb (fwf (dvar H0 18)) (CLSF lo hi) = true.
Proof. intros lo hi. vm_compute. reflexivity. Qed.

Section Den.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
#[using="Type"] Lemma den_addfs : forall fs E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  Forall (fun g => fwf (s_next S) g = true /\ fact_ok E g) fs -> DEN segs LIMIT model0 mem0 E (addfs S fs) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs as [|g r IH]; intros E S M ms model Hd Hfs; cbn [addfs]; [exact Hd|].
  inversion Hfs as [|? ? [Hw Hg] Hr]; subst.
  apply IH; [|exact Hr].
  apply den_addfact; [exact Hd|]. intros E' Ha. exact (fact_ok_agree _ E E' g Hw Ha Hg).
Qed.
End Den.

Section Entry.
Variables (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis H2 : length (in_argv inp) = 2%nat.
Let p1 : list byte := nth 1 (in_argv inp) [].
Variable data : list byte.
Hypothesis Hlk : fs_lookup (in_fs inp) p1 = Some data.
Hypothesis Hne : path_eqb p1 [] = false.
Hypothesis Hlt : (length p1 < 4096)%nat.
Variables (lo hi : Z).
Hypothesis HLEN : lo <= flen_of (length data) <= hi.      (* [comment removed for export] *)
Variable E : valu.
Hypothesis Hag : agree 17 (E0 sp brk0 draw inp) E.

Let E1 : valu := ext data p1 E.
Let A1 : Z := usp sp + 8 * AC inp + 8 * EC inp + 184 + L0 inp + 1.
Let L1 : Z := Z.of_nat (length p1).
Let HC : OFS sp <= OFS sp <= OFS sp. Proof. lia. Qed.

#[using="sp H2 data Hlk Hne Hlt E A1"] Lemma L1_pos : 1 <= L1 <= 4095.
Proof. LiaFast.lf_pins (fun (sp H2 data Hlk Hne Hlt E A1 : LiaFast.U) => LiaFast.u0). unfold L1. destruct p1 as [|b r] eqn:Hp; [cbn in Hne; discriminate|]. cbn [length] in *. lia. Qed.
#[using="brk0 draw Hsp Hfit Hva Hve H2 Hag"] Lemma uPV1 : uE E1 (lvar 8) = A1.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve H2 Hag : LiaFast.U) => LiaFast.u0). unfold E1. change (lvar 8) with AsanRdErr.PV. rewrite ext_u17 by (vm_compute; reflexivity). exact (uPV2T sp brk0 draw inp Hsp Hfit Hva Hve E Hag H2). Qed.
#[using="brk0 draw Hsp Hfit Hva Hve H2 Hlt Hag A1 L1 HC"] Lemma uSP1 : uE E1 (sm_sp MMAIN) = usp sp.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve H2 Hlt Hag A1 L1 HC : LiaFast.U) => LiaFast.u0). unfold E1. rewrite MMAIN_sp, ext_u17 by (vm_compute; reflexivity). exact (uSP sp brk0 draw inp Hsp Hfit Hva Hve _ _ HC E Hag). Qed.
#[using="brk0 draw Hsp Hfit Hva Hve H2 Hlt Hag A1 L1 HC"] Lemma uP01 : uE E1 P0 = usp sp + 8 * AC inp + 8 * EC inp + 184.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve H2 Hlt Hag A1 L1 HC : LiaFast.U) => LiaFast.u0). unfold E1. rewrite ext_u17 by (vm_compute; reflexivity). exact (uP0 sp brk0 draw inp Hsp Hfit Hva Hve _ _ HC E Hag). Qed.
#[using="brk0 draw Hsp Hfit Hva Hve H2 Hlt Hag A1 L1 HC"] Lemma uRP1 : uE E1 RANDP = RP sp inp.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve H2 Hlt Hag A1 L1 HC : LiaFast.U) => LiaFast.u0). unfold E1. rewrite ext_u17 by (vm_compute; reflexivity). exact (uRANDP sp brk0 draw inp Hsp Hfit Hva Hve _ _ HC E Hag). Qed.
#[using="sp brk0 draw Hva H2 Hag"] Lemma uARGC1 : uE E1 ARGC = 2.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hva H2 Hag : LiaFast.U) => LiaFast.u0). unfold E1, ARGC. rewrite ext_u17 by (vm_compute; reflexivity). rewrite (uARGC sp brk0 draw inp Hva E Hag). unfold AC. rewrite H2. reflexivity. Qed.
#[using="sp H2 Hlk Hne Hlt A1"] Lemma uL17 : uE E1 (hvar 17) = L1.
Proof. LiaFast.lf_pins (fun (sp H2 Hlk Hne Hlt A1 : LiaFast.U) => LiaFast.u0).
  unfold E1. rewrite u_hvar by lia. unfold dval. cbn [Nat.ltb Nat.leb Nat.eqb]. pose proof L1_pos. apply u_small64. unfold two64, L1 in *. lia.
Qed.
#[using="sp inp H2 p1 Hlt A1 L1"] Lemma flen_rng : 0 <= flen_of (length data) <= 4611686018427387903.
Proof. LiaFast.lf_pins (fun (sp inp H2 p1 Hlt A1 L1 : LiaFast.U) => LiaFast.u0). unfold flen_of, FLT. lia. Qed.
#[using="sp H2 Hlt A1 L1"] Lemma uL16 : uE E1 (hvar 16) = flen_of (length data).
Proof. LiaFast.lf_pins (fun (sp H2 Hlt A1 L1 : LiaFast.U) => LiaFast.u0). unfold E1. rewrite u_hvar by lia. unfold dval. cbn [Nat.ltb Nat.leb Nat.eqb]. pose proof flen_rng. apply u_small64. unfold two64. lia. Qed.
#[using="sp H2 Hlt A1 L1"] Lemma uByte : forall k, (k < 16)%nat -> uE E1 (hvar k) = bv_unsigned (nth k data (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (sp H2 Hlt A1 L1 : LiaFast.U) => LiaFast.u0). intros k Hk. unfold E1. rewrite u_hvar by lia. apply dval_byte. exact Hk. Qed.

#[using="draw Hsp Hfit Hva Hve H2 Hlt"] Lemma nums : 0x7fff80000000 <= usp sp /\ usp sp + 8 * AC inp + 8 * EC inp + 184 <= A1 /\ A1 + L1 + 1 <= RP sp inp /\ RP sp inp + 16 <= 0x800000000000 /\
  RP sp inp mod 8 = 0 /\ RP sp inp - (usp sp + 8 * AC inp + 8 * EC inp + 184) <= 2240000 /\ 1 <= AC inp <= 1024 /\ 0 <= EC inp <= 256 /\ 0 <= L0 inp <= 131071.
Proof. LiaFast.lf_pins (fun (draw Hsp Hfit Hva Hve H2 Hlt : LiaFast.U) => LiaFast.u0).
  pose proof (lay_nums sp draw inp Hsp Hfit Hva Hve) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof (lay1_numsT sp draw inp Hsp Hfit Hva Hve H2) as (K1 & K2). fold p1 in K1, K2. fold L1 in K1, K2. unfold A1. lia.
Qed.

(* [comment removed for export] *)
#[using="sp brk0 draw Hsp Hfit Hva Hve H2 Hlk Hne Hlt HLEN Hag A1 L1 HC"] Lemma clsf_ok : Forall (fun g => fwf (dvar H0 18) g = true /\ fact_ok E1 g) (CLSF lo hi).
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hsp Hfit Hva Hve H2 Hlk Hne Hlt HLEN Hag A1 L1 HC : LiaFast.U) => LiaFast.u0).
  pose proof (CLSF_wf lo hi) as HW. rewrite forallb_forall in HW.
  apply Forall_forall. intros g Hg. split; [exact (HW g Hg)|].
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof L1_pos as HL1.
  change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8) in *.
  assert (HPL : uE E1 (ladd (lvar 8) LPATH) = A1 + L1).
  { rewrite uE_ladd_small; unfold LPATH; rewrite ?uPV1, ?uL17; [reflexivity | unfold two64; lia]. }
  unfold CLSF in Hg. apply in_app_or in Hg as [Hg|Hg]; [|apply in_app_or in Hg as [Hg|Hg]].
  - (* [comment removed for export] *)
    apply in_rev in Hg. unfold HFACTS in Hg. destruct Hg as [<-|[<-|Hg]].
    + cbn [fact_ok]. fold (uE E1 (hvar 17)). rewrite uL17. lia.
    + cbn [fact_ok]. fold (uE E1 (hvar 16)). rewrite uL16. lia.
    + apply in_map_iff in Hg as (k & <- & Hk). apply in_seq in Hk. cbn [fact_ok]. fold (uE E1 (hvar k)). rewrite uByte by lia.
      pose proof (bv_unsigned_in_range 8 (nth k data (Z_to_bv 8 0))) as X. change (bv_modulus 8) with 256 in X. lia.
  - destruct Hg as [<-|[]]. cbn [fact_ok]. fold (uE E1 ARGC). rewrite uARGC1. lia.
  - unfold FSC in Hg. destruct Hg as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + cbn [fact_ok FV8C]. change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8). fold (uE E1 (lvar 8)). rewrite uPV1. lia.
    + cbn [fact_ok FV8SPC]. change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8). fold (uE E1 (lsub (lvar 8) (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?uPV1, ?uSP1; lia.
    + cbn [fact_ok FENDP0]. change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8). fold (uE E1 (ladd (lvar 8) LPATH)). rewrite HPL. lia.
    + cbn [fact_ok FENDP2]. change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8). fold (uE E1 (lsub (ladd (lvar 8) LPATH) (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?HPL, ?uSP1; lia.
    + cbn [fact_ok FRZP]. change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8). replace (laddc AsanErrT.RANDP16 (-16)) with RANDP by (vm_compute; reflexivity). fold (uE E1 (lsub RANDP (ladd (lvar 8) LPATH))). rewrite uE_lsub_small; rewrite ?uRP1, ?HPL; lia.
    + cbn [fact_ok FPV0]. change OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort.PV with (lvar 8). fold (uE E1 (lsub (lvar 8) P0)). rewrite uE_lsub_small; rewrite ?uPV1, ?uP01; lia.
Qed.

(* [comment removed for export] *)
#[using="sp brk0 draw Hsp Hfit Hva Hve H2 Hlk Hne Hlt HLEN Hag A1 L1 HC"] Theorem den_entry : forall LIMIT model0 mem0 ms model, DEN ASEGS LIMIT model0 mem0 E TMAIN MMAIN ms model ->
  DEN ASEGS LIMIT model0 mem0 E1 (S1c2 lo hi) MMAIN ms model.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hsp Hfit Hva Hve H2 Hlk Hne Hlt HLEN Hag A1 L1 HC : LiaFast.U) => LiaFast.u0).
  intros LIMIT model0 mem0 ms model Hd. rewrite S1c2_eq.
  apply den_addfs; [|cbn [bump s_next]; exact clsf_ok].
  apply den_bump; [|rewrite H0_next; apply dvar_ge].
  apply (den_agree ASEGS LIMIT model0 mem0 E E1 TMAIN MMAIN ms model Hd). rewrite H0_next. exact (ext_agree data p1 E).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AMAIN_wf18 : awf (dvar H0 18) AMAIN = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Theorem hax_entry : forall mem0, HA E MMAIN AMAIN mem0 -> HAX awf HA E1 (S1c2 lo hi) MMAIN AMAIN mem0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 HAa. split; [rewrite S1c2_next; exact AMAIN_wf18|].
  apply (HA_agree (s_next TMAIN) E E1 MMAIN AMAIN mem0 MMAIN_wfT AMAIN_wf); [|exact HAa].
  rewrite H0_next. exact (ext_agree data p1 E).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma PV_wf18 : lwf (dvar H0 18) (lvar 8) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Hsp Hfit Hva Hve H2 Hlk Hne Hlt Hag A1 L1 HC"] Theorem inv_entry : forall lim mem0,
  (forall p, In p (sm_frz M1) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w)) ->
  INV (lvar 8) p1 data (in_fs inp) false (Some H0) mem0 E1 (S1c2 lo hi) MMAIN FSClosed (model0 sp brk0 mb lim inp).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve H2 Hlk Hne Hlt Hag A1 L1 HC : LiaFast.U) => LiaFast.u0).
  intros lim mem0 Hsame.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof L1_pos as HL1.
  assert (HP0 : uE E P0 = usp sp + 8 * AC inp + 8 * EC inp + 184) by exact (uP0 sp brk0 draw inp Hsp Hfit Hva Hve _ _ HC E Hag).
  assert (HRP : uE E RANDP = RP sp inp) by exact (uRANDP sp brk0 draw inp Hsp Hfit Hva Hve _ _ HC E Hag).
  assert (HRS : uE E (lsub RANDP P0) = RP sp inp - (usp sp + 8 * AC inp + 8 * EC inp + 184)) by (rewrite uE_lsub_small; rewrite ?HRP, ?HP0; lia).
  assert (HRS1 : uE E1 (lsub RANDP P0) = RP sp inp - (usp sp + 8 * AC inp + 8 * EC inp + 184)) by (rewrite uE_lsub_small; rewrite ?uRP1, ?uP01; lia).
  assert (Hin : In (P0, lsub RANDP P0) (sm_frz MMAIN)) by (rewrite MMAIN_frz, M1_frz; right; left; reflexivity).
  assert (Hin1 : In (P0, lsub RANDP P0) (sm_frz M1)) by (rewrite M1_frz; right; left; reflexivity).
  (* [comment removed for export] *)
  assert (Hfz : forall w, A1 <= w < RP sp inp -> (exists p, In p (sm_frz MMAIN) /\ uE E1 (fst p) <= w < uE E1 (fst p) + uE E1 (snd p)) /\
                  mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w) /\ m0 sp draw inp (Z_to_bv 64 w) <> None).
  { intros w Hw. split; [|split].
    - exists (P0, lsub RANDP P0). split; [exact Hin|]. cbn [fst snd]. rewrite uP01, HRS1. lia.
    - apply (Hsame (P0, lsub RANDP P0) Hin1). cbn [fst snd]. rewrite HP0, HRS. lia.
    - destruct (m0_in sp draw inp (Z_to_bv 64 w)) as (b & Hb & _); [|rewrite Hb; discriminate].
      rewrite u_small64 by (unfold two64; lia).
      pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & _). unfold A1 in *. lia. }
  assert (Hpv : bv_unsigned (lden E1 (lvar 8)) = A1) by exact uPV1.
  unfold INV. rewrite Hpv.
  refine (conj _ (conj eq_refl (conj _ (conj (conj _ _) (conj _ (conj _ (conj eq_refl (conj _ (conj eq_refl (conj eq_refl _)))))))))).
  - rewrite S1c2_next. exact PV_wf18.
  - intros _ k Hk. fold p1 in Hk. destruct (Hfz (A1 + Z.of_nat k) ltac:(unfold L1 in *; lia)) as (X & _). exact X.
  - intros _ k Hk. destruct (Hfz (A1 + Z.of_nat k) ltac:(unfold L1 in *; lia)) as (_ & X & _). rewrite X.
    exact (argv1_byteT sp draw inp Hsp Hfit Hva Hve H2 k Hk).
  - intros _ w Hw. fold L1 in Hw.
    assert (Hwe : 8 * ((A1 + L1) / 8 + 1) <= RP sp inp).
    { pose proof (Z.div_mod (A1 + L1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (A1 + L1) 8 ltac:(lia)).
      pose proof (Z.div_mod (RP sp inp) 8 ltac:(lia)). lia. }
    destruct (Hfz w ltac:(lia)) as (X & Y & Z0). split; [exact X|]. rewrite Y. exact Z0.
  - fold L1. lia.
  - intros _. exact Hlk.
  - split; reflexivity.
  - (* [comment removed for export] *)
    cbn [hv_inv]. rewrite S1c2_next. split; [apply Pos.le_refl|]. split; [|split].
    + intros i Hi _. unfold E1. rewrite ext_at by lia. unfold dval. replace (Nat.ltb i 16) with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
    + unfold E1. rewrite ext_at by lia. unfold dval. cbn [Nat.ltb Nat.leb Nat.eqb]. pose proof flen_rng. unfold flen. apply u_small64. unfold two64. lia.
    + unfold E1. rewrite ext_at by lia. unfold dval. cbn [Nat.ltb Nat.leb Nat.eqb]. apply u_small64. unfold two64, L1 in *. lia.
Qed.
End Entry.
(* [comment removed for export] *)
