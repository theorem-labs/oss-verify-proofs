(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (busy_of_Some_In, NoDup_app_disjoint, nth_error_map_inv and 15 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepKit () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List=repeat_lengthI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someI47Corelib4Init5Logic3and00C46Stdlib5Lists4List6filterC46Stdlib5Lists4List2InC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib4Init9Datatypes4list00C47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2eq01C46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z8eqb_reflK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List5NoDup00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW7ARepKitBNoDup_app_disjointC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00C47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib5BothW7ARepKitAnth_error_map_invC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK47Corelib4Init5Logic2or01c59OSSVerify5KrLib5BothW7ARepKit?busy_of_Some_InC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List=nth_error_mapC46Stdlib5Lists4List>nth_error_app1C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC59OSSVerify5KrLib5BothW4ARepBkit_cache_pop_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib5Lists7ListDef6repeatC47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib5BothW7ARepKit>firstn_repeat'C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subc59OSSVerify5KrLib5BothW7ARepKit=skipn_repeat'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat7inj_addI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List:repeat_appC59OSSVerify5KrLib5BothW6ABytes8c8_of_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes:c8c8_of_CBC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes9hdr_of_CBC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac?rw_cells_forgetC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARepKit;hdr_of_junkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARepKit<c8c8_of_junkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics5Riscv3Sem2w0c59OSSVerify5KrLib5BothW7ARepKit:fill_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARepKit:c1_of_fillC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma busy_of_Some_In : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b H. unfold busy_of, busy_slots in *.
  apply find_some in H. destruct H as [HIn HP]. apply andb_true_iff in HP. destruct HP as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  apply in_map_iff. exists b. split; [reflexivity|]. apply filter_In. split; [exact HIn| apply Z.eqb_refl].
Qed.

Lemma NoDup_app_disjoint : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [exact H1|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct H1 as [<-|H1].
  - apply NI. apply in_app_iff. right. exact H2.
  - exact (IH l2 x ND' H1 H2).
Qed.

Lemma nth_error_map_inv : forall {A B} (f : A -> B) l i y,
  nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ y = f x.
Proof.
  intros A B f l. induction l as [|a l IH]; intros [|i] y H; cbn in H; try discriminate.
  - injection H as <-. exists a. split; reflexivity.
  - apply IH. exact H.
Qed.

Section Kit.
Variable H : aholes.

Theorem kit_cache_pop : kit_cache_pop_stmt H.
Proof.
  unfold kit_cache_pop_stmt. intros L st X m c cnt AR HC CNT POS.
  destruct AR as (WF & RT & INST & THR & CLS & HOLES).
  destruct THR as (T0 & T40 & CACHES & CSTATS & ASTATS & UNW).
  destruct (CACHES c HC) as [tail (CR & CH & LEN)].
  destruct (CLS c HC) as (REG & FARR & SLOTS & SHADOW).
  destruct WF as (SB & PA & AL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  (* [comment removed for export] *)
  assert (CI : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite <- CNT in POS. lia. }
  (* [comment removed for export] *)
  assert (LT : (Z.to_nat (cnt - 1) < length (xc_cache (x_cls X c)))%nat) by lia.
  destruct (nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1))) as [k|] eqn:NK.
  2: { exfalso. apply nth_error_None in NK. lia. }
  assert (INK : In k (xc_cache (x_cls X c))) by (eapply nth_error_In; exact NK).
  assert (KR : 0 <= k < ndist st c) by (apply RANGE; apply in_app_iff; right; apply in_app_iff; left; exact INK).
  assert (NB : busy_of X c k = None).
  { destruct (busy_of X c k) as [b|] eqn:E; [|reflexivity]. exfalso.
    apply busy_of_Some_In in E. rewrite app_assoc in ND.
    eapply (NoDup_app_disjoint (xc_free (x_cls X c) ++ xc_cache (x_cls X c)) (busy_slots X c) k ND); [| exact E].
    apply in_app_iff. right. exact INK. }
  exists k, (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail).
  split; [first [exact NK | reflexivity]|]. split; [exact NB|]. split; [exact KR|].
  split. { rewrite <- CNT. rewrite CI in CR. unfold max_count in CR |- *. rewrite CI in CR |- *. exact CR. }
  split; [exact CH|]. split; [rewrite length_app, length_map; lia|].
  split. { rewrite nth_error_app1 by (rewrite length_map; lia). rewrite nth_error_map, ?NK. reflexivity. }
  split.
  - destruct SLOTS as [SL _]. specialize (SL k KR). rewrite NB in SL. exact SL.
  - destruct SHADOW as [SH _]. specialize (SH k KR). rewrite NB in SH. unfold fill_at. cbn [slot_shadow_bytes] in SH. exact SH.
Qed.
End Kit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ABytes.

Section CANSEC2. Context {rc : runConstT}.
Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
Lemma skipn_repeat' : forall {A} (x : A) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Lemma junk_split : forall m A a b, junk_at m A (a + b) -> 0 <= a -> 0 <= b ->
  junk_at m A a /\ junk_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB bsegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app bsegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

Lemma junk_merge : forall m A a b, junk_at m A a -> junk_at m (A + a) b -> 0 <= a -> 0 <= b -> junk_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  pose proof H1 as W1. destruct W1 as [[[L1 _] _] _]. cbn in L1.
  assert (H : rw_cells bsegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge bsegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exists (bs1 ++ bs2). rewrite Z2Nat.inj_add by lia. exact M.
Qed.

Lemma fill_split : forall m A a b v, fill_at m A (a + b) v -> 0 <= a -> 0 <= b ->
  fill_at m A a v /\ fill_at m (A + a) b v.
Proof.
  intros m A a b v H Ha Hb. unfold fill_at in *.
  pose proof (rw_cells_split_CB bsegs m A [] (Z.to_nat (a + b)) (repeat (Z_to_bv 8 v) (Z.to_nat (a + b))) [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app bsegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  rewrite firstn_repeat' in H1 by lia. rewrite skipn_repeat', firstn_repeat' in H2 by lia.
  split; assumption.
Qed.

Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v H1 H2 Ha Hb. unfold fill_at in *.
  assert (H : rw_cells bsegs m A ([CB (Z.to_nat a) (repeat (Z_to_bv 8 v) (Z.to_nat a))] ++ [CB (Z.to_nat b) (repeat (Z_to_bv 8 v) (Z.to_nat b))])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge bsegs m A [] ([CB (Z.to_nat a) (repeat (Z_to_bv 8 v) (Z.to_nat a))] ++ [CB (Z.to_nat b) (repeat (Z_to_bv 8 v) (Z.to_nat b))]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r, <- repeat_app in M. rewrite Z2Nat.inj_add by lia. exact M.
Qed.

Lemma fill_is_junk : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v H. eexists. exact H. Qed.

(* [comment removed for export] *)
Lemma c8_of_junk : forall m A, junk_at m A 8 -> exists w : word, rw_cells bsegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
Lemma c8c8_of_junk : forall m A, junk_at m A 16 -> exists w1 w2 : word, rw_cells bsegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
Lemma hdr_of_junk : forall m A, junk_at m A 16 ->
  exists b0 b1 szh szl ctxj : Z,
    rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b0 < 256 /\ 0 <= b1 < 256.
Proof. intros m A [bs H]. exact (hdr_of_CB m A bs H). Qed.
Lemma c1_of_fill : forall m A v, 0 <= v < 256 -> fill_at m A 1 v -> rw_cells bsegs m A [C1 (Z_to_bv 8 v)].
Proof.
  intros m A v Hv H. unfold fill_at in H. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op] in H.
  eapply InitMem.rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
Lemma junk_of_cells : forall m A cs, rw_cells bsegs m A cs -> junk_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. destruct (rw_cells_forget bsegs m A cs H) as [junk H']. exists junk. rewrite Nat2Z.id. exact H'.
Qed.

(* [comment removed for export] *)
Lemma slot_carve : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ rz = 32 \/ rz = 64) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells bsegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells bsegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells bsegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    destruct (hdr_of_junk m AB HJ) as (b0 & b1 & szh & szl & ctxj & HDR & B0 & B1).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. replace (S - 16 - n) with (S - 16 - n) by lia. exact TL.
  - assert (RZ2 : rz = 32 \/ rz = 64) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    destruct (hdr_of_junk m _ HJ) as (b0 & b1 & szh & szl & ctxj & HDR & B0 & B1).
    destruct (c8c8_of_junk m AB LHJ) as (j1 & j2 & LH).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
Lemma shadow_carve : forall m SA gS grz g (room : Z),
  fill_at m SA gS 0xfa -> 2 <= grz -> 0 <= g -> grz + g + room <= gS -> 0 <= room <= 1 ->
     rw_cells bsegs m SA [C1 (Z_to_bv 8 0xfa)]
  /\ fill_at m (SA + 1) (grz - 1) 0xfa
  /\ (exists sj, rw_cells bsegs m (SA + grz) [CB (Z.to_nat g) sj])
  /\ (room = 1 -> rw_cells bsegs m (SA + grz + g) [C1 (Z_to_bv 8 0xfa)])
  /\ fill_at m (SA + grz + g + room) (gS - grz - g - room) 0xfa.
Proof.
  intros m SA gS grz g room F GRZ G FIT ROOM.
  destruct (fill_split m SA 1 (gS - 1) 0xfa ltac:(replace (1 + (gS - 1)) with gS by lia; exact F) ltac:(lia) ltac:(lia)) as [F0 R1].
  destruct (fill_split m (SA + 1) (grz - 1) (gS - grz) 0xfa ltac:(replace (grz - 1 + (gS - grz)) with (gS - 1) by lia; exact R1) ltac:(lia) ltac:(lia)) as [F1 R2].
  replace (SA + 1 + (grz - 1)) with (SA + grz) in R2 by lia.
  destruct (fill_split m (SA + grz) g (gS - grz - g) 0xfa ltac:(replace (g + (gS - grz - g)) with (gS - grz) by lia; exact R2) ltac:(lia) ltac:(lia)) as [F2 R3].
  destruct (fill_split m (SA + grz + g) room (gS - grz - g - room) 0xfa ltac:(replace (room + (gS - grz - g - room)) with (gS - grz - g) by lia; exact R3) ltac:(lia) ltac:(lia)) as [F3 R4].
  split; [apply c1_of_fill; [lia| exact F0]|]. split; [exact F1|]. split; [eexists; exact F2|].
  split; [| exact R4]. intros ->. apply c1_of_fill; [lia| exact F3].
Qed.
End CANSEC2.
