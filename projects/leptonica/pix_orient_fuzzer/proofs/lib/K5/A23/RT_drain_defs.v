(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_cache_defs R_prim_defs R_depot_defs R_fs_defs RT_state RT_rep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_drain_defs () := "C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthc69OSSVerify5KrLib2K53A23=RT_drain_defs4updfC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C35stdpp4base6ElemOfC46Stdlib5Lists4List8flat_mapI35stdpp4base<list_elem_of00C46Stdlib5Lists4List8nil_consC69OSSVerify5KrLib2K53A238RT_state5batchC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00I47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat8eqb_specC56Stdlib5Arith8PeanoNat3Nat3eqbI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC56Stdlib5Arith8PeanoNat3Nat3ltbK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C56Stdlib5Arith8PeanoNat3Nat8ltb_specC47Corelib4Init5Peano2ltI47Corelib4Init5Peano2le00I47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib2K53Lib3ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI69OSSVerify5KrLib2K53A238RT_state4ckst00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List6nth_okI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib2K53A23=RT_drain_defs;swap_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state2qgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state2qlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc69OSSVerify5KrLib2K53A23=RT_drain_defs5qallPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A238RT_state4rtsA00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib2K53A23=RT_drain_defs9qallP_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23=RT_drain_defs6qentsPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state5qentsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23=RT_drain_defs6rt_wfPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state7live_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state6sec_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23=RT_drain_defs8quar_wfPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state3depC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2K53A238RT_state5rt_wfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib2K53A238RT_state7qent_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state6p_abegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state5l_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state9budget_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state7dep_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23=RT_drain_defs9rt_countPC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A238RT_state4ckst03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53A238RT_state3secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state6s_quarC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state4s_mbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state3s_nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23=RT_drain_defs:qentsP_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state7quar_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state8rt_countC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53A23<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state6qbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state4r_stC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A238RT_state6QMAX_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_state6QMAX_GC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A238RT_state4ckst04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib2K53A238RT_state5secst00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition updf {A : Type} (f : Z -> A) (c : Z) (x : A) : Z -> A := fun c' => if c' =? c then x else f c'.

Lemma updf_same : forall {A} (f : Z -> A) c x, updf f c x c = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_defs ()) [] "h01Ah11bh21ch31fh41xp;3p;2p;1p;6p;5p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8p200R0g000mR1p4p710p8g001kj30Tg002Ej25Tg002_j22Tg003<j11Tg003^j64TP1j53Tg004<R1f1R2[f2R3g004ZR4g005:f4P4f5f0R5P2f3R6P3O1n0100000020000;02X1415651222%12E4P6P3P2P5P2D3=065eW4X21W3X00o"). Qed.
Lemma updf_other : forall {A} (f : Z -> A) c x c', c' <> c -> updf f c x c' = f c'.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_defs ()) [] "p'0h01Ah11Hh23Heqh31bi001bh41ch52c'h61ei011eh71fh81ni021nh91ri031rh:1xp;3p;1p;2p;5p200R0g000mR1p4p710p8g001kj30Tg005Zj12Tg0063j23Tg002_j21Tg006UR2j27Tg0078j26Tg002Ej25TP1j54Tg004<R1f1R3[f2R4f0R5=014#2f3R6,33A01361136'7f4R7,14g004ZR8P2f5R29016f9R9P8f:R8P3f6R:f8P2O1R;n0100000020000;0;P3A017:R<P5f7R=9012P9P:O1908=P2P5O1'6b2W6P5O1%2<159;W8P5O1n10210010300021010110102b3b9P2P7P6P4P3D4P7P3O1502eW1X51W:X41W7X00o"). Qed.

(* [comment removed for export] *)
Definition ureg (r : regst) (i : nat) (st : ckst) : regst := mkReg (r_muser r) (r_mfa r) (upd (r_st r) i st) (r_fl r).

Lemma nth_upd_ck : forall (l : list ckst) i j x,
  nth_error (upd l i x) j = if Nat.eqb i j then (if Nat.ltb j (length l) then Some x else None) else nth_error l j.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_defs ()) [] "p'0h01lh11ni001nh21Ah31Lh44__x1h54__x2h61bi011bh71ih81Hh93Hneh:2L0h;7__arithh<4__ffh=8__varmaph>5__with?2b0h@4cstrhA5cstr0hB1ei021ehC1jhD1ri031rhE1xp;1p;2p;3p;4p;5p;7p;8p;6p;<p-1R0p1007Wp4p710p8P0p1007nR1p4p710p8P0P1p4p7210p8P0p1008Jp4p710p8P0p1008kR1p4p710R2p8P0P1p4p7210R1p8P0p1009?R3p4p710p8P0P3p4p7210p8P0p1009\p4p710R0p8p100:8p4p710R3g003^R4p4p710R5p8p100:Up4p70R6p100;Op4p710p8P6P3p8P6P5p8P6p100;kp4p710p8p100<Hp4p710R6P2p8P6P1p8P6P0p8g00<]j19Tg00==j2]Tg001kj30Tg00=bj2ATg006UR0j2\Tg00>Bj18Tg00>dj47Tg00?Wj33Tg00@5j2>Tg00@Uj2<Tg00A7j16Tg00AYj2CTg00B>j2=Tg00BVR6j22Tg00C0R1j3VTg00CTj5UTg000Mj2;Tg00DVj3TTg00E9R2j14Tg00EYR5j25Tg002Ej2:Tg00F5j4MTg00F\j1@Tg00GAj1LTg00Gaj2KTg00H?j1HTg00H]j4GTg00I;j1ITg00IYj1JTg00JDj2?Tg00Jgj1FTg00KLj4ETg00L7j7DTg00L[j8OTg00M?j2PTg00Maj2QTg00NMj3RTg00Nlj4STg00O^j4[Tg00PIj4ZTP4j6BTg005Zj1WTg00QCj6XTg00RFl<YTg00RkR4f0R3';p=1g00SfR7g004<R8P6P2P5g00TEf5R5f4R2f3R6f2R9f1R:P3M<Yp=N%941]9:A079:1A9:'\1A69g004ZR;P0A0726%84R0P4f7R<f6R=P2C7=345P;P0P:P;P0%1<R>,>5R?1<42%64R@n0100000020000A34<5n010000002000030P:A0752RAP7P5P4f8RBP3P5C7=34=P;P0%1B,>=RC1<45P@n0100000020000500X771C5>1=5>12>5;V?PCP;P1f9R1#1RC,=<12C<P4f;RCP1PBC7=341P;P0P:1<4BP@n0100000020000500P:f:R0#1R@,=BP4PCP1PBP3DUW3P3O112@Bg00Tgp4p710R@%93RBg00UB%89A39:3%69301;69/2:R?[1;9:/23%86A369:%6630[R>%82A3269%6230\?AT9:3P3n2001000000120000000X17W0W2P>^17^0B^2@P3P4P4f<R@P0P1C7RBP0P7%1@R>123CX1712>0R?%4>RD%40RE'5RFP>PD1:8DP0PE1:8EENREP?PFPEP:CMPF%@Cg00U]RF%4C'5f>RC#1RE#@%4E,5Fg00V;RE#L%9EP81K89P:%H8CG%I8%J8REg00VgR?g00WFRDPDg00WfR>PEP?PDPDP>P8g00XFR?,?8g00Xk%F?,?8CEg00YRFDR?%6DP?GO1PE>P3P9g005:R>,:;1Q39=0;>dAR8F:CSb<b=b>X48X58153:15:9[^48^58P3%4Cf@#1#4P6O3b;bAb@b:C[%1BP4P@P0P1CZEBO4b8W3P3O1n200210100000021000011000b?b6P=P3EBWBP3O1%WAP4P<P=P5P2P3EXW9P3O1n10210110300021110210100b6bDXE4XC7X77W0o"). Qed.

Definition set_st (Σ : rtsA) (c : Z) (i : nat) (st : ckst) : rtsA :=
  mkRtsA (lay Σ) (updf (pr Σ) c (ureg (pr Σ c) i st)) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fc3 Σ) (fc4 Σ) (fc7 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition set_sec (Σ : rtsA) (l : list secst) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) l (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fc3 Σ) (fc4 Σ) (fc7 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition set_q (Σ : rtsA) (l g : list batch) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) l g (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fc3 Σ) (fc4 Σ) (fc7 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dh_keep (c : Z) : nat := Z.to_nat (MaxCount c - MaxCount c / 2).
Definition dh_nf (c : Z) (r : regst) : Z := Z.of_nat (length (r_fl r)) + MaxCount c / 2.
Definition dh_grow (c : Z) (r : regst) : bool := r_mfa r <? 4 * dh_nf c r.
Definition dh_mfa (c : Z) (r : regst) : Z := if dh_grow c r then round_fa (4 * dh_nf c r) else r_mfa r.
Definition cdeal_full (c : Z) (l : list Z) : bool := MaxCount c <=? Z.of_nat (length l).

Definition cdeal_reg (c : Z) (r : regst) (l : list Z) : regst :=
  if cdeal_full c l then mkReg (r_muser r) (dh_mfa c r) (r_st r) (r_fl r ++ skipn (dh_keep c) l) else r.
Definition cdeal_ca (c : Z) (i : nat) (l : list Z) : list Z :=
  (if cdeal_full c l then firstn (dh_keep c) l else l) ++ [Z.of_nat i].

(* [comment removed for export] *)
Definition cdealΣ (Σ : rtsA) (c : Z) (i : nat) : rtsA :=
  mkRtsA (lay Σ) (updf (pr Σ) c (cdeal_reg c (pr Σ c) (ca Σ c))) (updf (ca Σ) c (cdeal_ca c i (ca Σ c))) (ca_init Σ) (sec Σ)
    (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fc3 Σ) (fc4 Σ) (fc7 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition recp (Σ : rtsA) (c : Z) (i : nat) : rtsA := cdealΣ (set_st Σ c i CkIdle) c i.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition swap_remove {X : Type} (k : nat) (l : list X) : list X :=
  match l with
  | [] => []
  | x :: _ => if Nat.eqb (S k) (length l) then removelast l else upd (removelast l) k (last l x)
  end.

Definition recs (Σ : rtsA) (k : nat) : rtsA := set_sec Σ (swap_remove k (sec Σ)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition qallP (Σ : rtsA) (P : list batch) : list batch := ql Σ ++ qg Σ ++ P.
Definition qentsP (Σ : rtsA) (P : list batch) : list (Z * Z) := flat_map snd (qallP Σ P).

Definition quar_wfP (Σ : rtsA) (P : list batch) : Prop :=
  qbytes (ql Σ) <= QMAX_L + 0x10000 /\ qbytes (qg Σ) <= QMAX_G + 0x10000 /\ qbytes P <= 2 ^ 40
  /\ Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (qallP Σ P)
  /\ NoDup (map fst (qallP Σ P))
  /\ Forall (fun b => (length (snd b) <= 1021)%nat) (qallP Σ P)
  /\ Forall (qent_ok Σ) (qentsP Σ P) /\ NoDup (map fst (qentsP Σ P))
  /\ (forall c i, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some CkBatch ->
        c = 24 /\ In (p_abeg (l_SB (lay Σ)) 24 i) (map fst (qallP Σ P))).

Definition rt_countP (Σ : rtsA) (P : list batch) : Prop :=
  (forall c i n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
     In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n) (qentsP Σ P))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qentsP Σ P)).

Definition rt_wfP (Σ : rtsA) (P : list batch) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wfP Σ P /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (dep Σ) /\ rt_countP Σ P.

Lemma qallP_nil : forall Σ, qallP Σ [] = ql Σ ++ qg Σ.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_defs ()) [] "h01lh12Σp;1p;3p;2p;6p100Z2p4p710R0p100>dp4p710p8P0p1000Mp4p710p8P0p100Tgp4p710p8g00<]j19Tg00[7j11Tg00[nj12Tg00;kj30Tg001kj33Tg002Ej28Tg00GAj17Tg00\ej24Tg003^j65Tg00]Cj26Tg00^Bg00:UR0#9R1f0R2#1R3f1R4#2R5=002%149005531X01%22=003R5,81%70R490031403E51624=315eW1o"). Qed.
Lemma qentsP_nil : forall Σ, qentsP Σ [] = qents Σ.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_defs ()) [] "h01lh12Σp;1p;3p;2p;4p;6g00<]j16Tg00[nj13Tg00[7j11Tg00;kj34Tg00_=j25Tg00_]j2<Tg009?j40Tg001kj32Tg002Ej2;Tg00GAj1:Tg00]Cj27Tg00`:j18Tg003^j69Tg00a=j2>Tg00b=j1=Tg00^Bg00:UR0#6R1f0R2#3%12540R3g004<R4/54R5#6R61546R7P51<46R4P2C0P7P5P4f1R8#3%18540C032X01P7P5P4P3C0,;6%:0R0,72%82E91>20%=2526eW1o"). Qed.

Lemma rt_wfP_nil : forall Σ, rt_wfP Σ [] -> rt_wf Σ.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_defs ()) [] "h01ih11ch21Hh31bh41lh51nh61sh72C1h82C2h92Q4h:2Q5h;2Q6h<2Q7h=2Q8h>2Q9h?2H1h@3H10hA3H11hB2H2hC2H3hD2H4hE2H6hF2H7hG2H8hH2H9hI2Q1hJ2Q2hK2_HhL2Σp&0p;1p;2p;3p;6p;4g00GAk10OTg00c7k20NTg00d7j14Tg00doj1xTg00emj1jTg00fij1YTg00gej1NTg00h`j2UTg00ibj12Tg00Jgj1[Tg00jZj1HTg00k8j2wTg00kUj1_Tg00l:j19Tg00[nj1KTg00m4j2BTg00[7j1CTg00_=k202Tg00<]k100Tg00>Bk10ETg00@Uj2~Tg0000k30Bj2|Tg00]Cj2:Tg00_]k30:Tg000Mk209Tg00mQj10Tg00BVk20ITg00n0j1STg00a=j26Tg00EYj2gTg00UBR0j21Tg00nlj1WTg008Jj3;Tg00oej3RTg010`j1rTg011Zj1dTg012Tj1VTg013Nj1QTg014Jj1cTg015Hj1qTg016Dj1aTg017Bj1`Tg018>j2oTg019Ak10FTg01:<k10DTg01;:j2bTg01;Wj3=Tg01;nj1nTg01<fk10CTg001kj3fTg01=ak10ATg01>Zk10@Tg00`:j1mTg00;Oj6OTg00b=j1PTg01?Rj1lTg01@Vk10?Tg01ARk10>Tg01BOj4yTg01Bjj2kTg01CFj4pTg01DGk10=Tg01EBj2}Tg01F9k106Tg00?Wk308Tg01G2k20<Tg007nj4vTg00<Hj2iTg01GLk40;Tg00;kk30JTf0R1#[#[p=G%_1#_p=hf2R2#`f1R3/o1'1p=5f6R4#qf5R5'Bf4R6'kf3R7#a/B2/k3/11'1p=8%r4%c5P6%d7%V2%Q3Cp/11'1'1p=<1131,12p=A1U23/11p=s&0=3/g1p=J%41#Wp=Lg004<R8AR2317f7p=Eg00RkR91}67$06<082=f53/11p=Fg00SfR:00<1p=DP2P8P3P1Cvp=@%01#0#0#0p>0M%01#0#0#0#0#0#0#0p>0L%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0K%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=31}72$06>0893=f61p=7Af831p>0H%47#W?R23==81,16p=>P7P8P2P3Cv,i8/11p=?A;456A;723/11'1p=^A;6721i83/11'1p=u%S2=;73/11p=]1i86A;723/11'1p=tA=831,12p>071i81p>0GP2P8P3P1Cv,i8p=MP7P8P21:31Cvp=X%S3=;21p=e%W7?R23==81,16p>05%c5P6P7P2P3Cp/11'1p>04P6%d7%V2P3Cp/11p>03P7%d2P3P1Cpp={1B23/k1p=Z%a5/B6/k7%`21o31'1'1p>01%42#W?R31p=zP8P8P3P1H0;p=\g00:UR;@0J31p=TP4P5P6P7P2P3P1CyCyp=Ig00^B&0O;R<-0N1P0%43R=#x%j3%Y3%N31U3<P3P3%23R>P=P=P=P>g00XFR=#[R?#HR@%[?#GRA#HRB,w@RCP>%_=RD#_#hRE#_#h#HRF%_?R?#GRG#H,w@RHA5>3<F8F<3A3A%92P1%47#x%j6%Y6%N61U6<P6P6%26R>%46RIPIPIP>P@PCP>PFPHA5>6<F8F<3A3AP0%j5%Y5%N5P5P5%25R>%45RIPIPIP>P@PCP>PFPHA5>5<F8F<9s5<3A%94P1f7R>#jf8RI#Y%NIPIPI%2IRJ%4IRKPKPKPJP@PCPJPFPHA5JI<F8F<9sI<3AP0f9RI#Y%NI1UI<PIPI%2IRJ%4IRKPKPKPJP@PCPJPFPHA5JI<F8F<3Af:#9P1f;#Yf<RJ#N1UJ<PJPJ%2JRI%4JRKPKPKPIP@PCPIPFPHA5IJ<F8F<3AP0f=RI#NPIPI%2IRJ%4IRKPKPKPJP@PCPJPFPHA5JI<F8F<9sI<f>#9P1f?#Nf@RJPJPJ%2JRK%4JRLPLPLPKP@PCPKPFPHA5KJ<F8F<7s<P0fARK/U<PKPK%2KRJ%4KRLPLPLPJP@PCPJPFPHA5JK<F8F<fB#9P1fC/U<P0fDRJ#Kg01Gl%GA#G#G#G#G#G#HRA'BRL'J%CJg01Hg/BARA'J%[G#H,w@,J<RG20288RM$00RN-028RO&0E9RPfFRQ%[D#G#HRDP1g01Ib,~9RRB0B8N3RS%LQPDP1CEEFX0:#DX3O1:J<RT1|8NRU=@OTPOB0:8N1-09Mg01J]#0$0M$0L$0K#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3#3+0IX3ORVPTPM%SJ16J<RJPM1|88RTPJ%H=R=/g3%HERE,g3'1RJPPfGRWP2P3PRD720H7DRXfHRYPDP21:Y<RZ9@OUR[D>[[^0:^18C?F^Du3AfER\P\%2\R]%4\R^P^P^P]P@PCP]PFPHA5]\<F8F<%9Q[P1%KQ/JL%CW/JAPOPPfIRQPDP1PRPS%4QR]#WPDP1CEEFX0:#DX3O1:W<R^A@OU^POPVP^PM%SW16W<RWPMPTPWPPfJRWP2P3PRD7PXfKR^PDP21:^<R_9@OUR`D>[\J^0:^18C?F^Du7AGP0%CY/JAPPPWPDP1PRPS%LWPDP1CEEFX0:#DX3O=;OZP[POPVPZPMPY16Y<RYPMPTPYPPP^P2P3PRD7PXfLRYPDP21:Y<RZ9@OUR[D>[\J^0:^18C?C]Dt5AGPQPQ%2QRaP]P]P]PaP@PCPaPFPHA5aQ<F8F<%9W[P1%CW/JAPPfMRWPDP1PRPS%4WRa#WPDP1CEEFX0:#DX3O=;O_P`POPVP_PMP^16^<R^PMPTP^PPfNR^P2P3PRD7PXfOR_PDP21:_<R`9@OUR]D>[\J^0:^18C?C]Dt5AGP0PGPOPPP^PDP1PRPS%L^PDP1CEEFX0:#DX3OPZP[POPVPZPM%SY16Y<RYPMPTPYPPP_P2P3PRD7PXfPRYPDP21:Y<RZ9@OUR[D>[\J^0:^18C?F^DuPWPW%2WRbPaPaPaPbP@PCPbPFPHA5bW<F8F<%9^[P1POPPfQR^PDP1PRPS%4^Rb#WPDP1CEEFX0:#DX3OP`P]POPVP`PM%S_16_<R_PMPTP_PPfRR_P2P3PRD7PXfSR`PDP21:`<R]9@OURaD>[\J^0:^18C?F^DuP0PPP_PDP1PRPS%L_PDP1CEEFX0:#DX3O=;OZP[POPVPZPMPY16Y<RZPMPTPZPPP`P2P3PRD7fTRZ#LR[?RD21:Z<Rc9@OURd607X[\J^0:^18C?C]DtP^P^%2^RePbPbPbPeP@PCPePFPHA5e^<F8F<%9_[P1PPPZPDP1PRPSP[PDP1CEEFX0:#DX3O1:_<5;OPaPOPVP]PMP`16`<R]PMPTP]PPfVR]P2P3PRD7PXfWRaPDP21:a<R_9@OUD>[\J^0:^18C?C]DtP0&0GdPOPVPcPM%SZ16Z<RZPMPTPZPPPaP2P3PRD7PXfXRZPDP21:Z<Rc9@OUD>[\J^0:^18C?F^fURdPd%2dR[%4dRePePeP[P@PCP[PFPHA5[d<F8F<%9][P11:]<9MOUPOPVP_PM%Sa16a<RaPMPTPaPPfZRaP2P3PRD7PXf[R_PDP2POPUP_P<CXD>[\J^0:^18C?F^P0A;OVcPMPZ16Z<RcPMPTPcPPP_P2P3PRD7PXf\RcPDP2POPUPcP<CXD>[\J^0:^18C?C]fYR[P[%2[Rd%4[RePePePdP@PCPdPFPHA5d[<F8F<%9a[P11:a<9;OVPMP_16_<RaPMPTPaPPf^RaP2P3PRD7PXf_RdPDP2POPUPdP<CXD>[\J^0:^18C?C]P016c<R[9eMcPMPTP[PPPdP2P3PRD7PXf`R[PDP2POPUP[P<CXD>[\J^0:^18C?f]RcPc%2cRe%4cRbPbPbPeP@PCPePFPHA5ec<F8F<%9a[P116a<9eMaPMPT16d<PPfbRdP2P3PRD7PXfcRePDP2POPUPeP<CXD>[\J^0:^18C?P016[<9MMTPPPeP2P3PRD7PXfdRe#4R[PDP2POPUPeP<CXI05[\J^0:^18faRcPc%2cRb%4cRfPfPfPbP@PCPbPFPHA5bc<F8F<%9d[P116d<9MMTPPffRdP2P3PRD7PXfgRbPDP2POPUPbP<CXD>[\J^0:^18PePe%2eRcP[P[P[PcP@PCPcPFPHA5ce<F8F<P0feRc#rPc%2cRe%4cR[#d%V[%Q[PeP@PCPePFPHA5ec<F8J04%9dP1%rbfhRb%2bRd%4bRe#d%Ve%QePdP@PCPdPFPHA5db<F8J04P0fiRd#c%2dRb%4dRePe%QePbP@PCPbPFPHA5bd<F8I03fj#9P1fk#cflRb#2Rd%4bRePe%QePdP@PCPdPFPHA5db<F8I03P0fmRd#2Rb%4dRe%Ve%QeC{PbP@PCPbPFPHA5bd<F8fnRb#9P1foRd#2%4dRd%Vd%QdC{fpRd#2ReP@PCPePFPHA5ed<F8P0fqRe#2Rd#q?Z@CPdPFPHPdPeP<J01frRe#9P1fs#2#q?Z@CftRd#2RcPFPHPcPdP<J01P0fuRd#2Rc#a?ZFHA5cd<fv#9P1fw#2#a?ZFHfxRc#2?5c<P0fyRc#2#`1oc<fz#9P1f{#2#`f|/o<P01g=21g2E'1REPPp+01BR=P7P2&0F3,~9R9D7p+01CR0?z67&0D2Rd'B/bB/\2160<5=M[[^58^0:^18g01K<R[f~Rf#n9=[1g004Z&0C3g005:3fRg&0A2%h?#h#h#G#G#H'B&0@2'\R?p+01A/6<5=M[[]6%9fP1PPp+01DRfP7P2P9D7p+01ERh#LRi?R67/Bd/bB/\216h<5=M[\E^58^0:^18%n=9=[116f<9=M?\g[^6[&00;R;1:=<PPPhPDP1PRPSPiPDP1CEEFX0:#DX3O=;O1X4;Pa%K=%C='TRa%m=EOPPPfPDP1PRPS%LfPDP1CEEFX0:#DX3O=;OaP;1:0<AMOU1X4;P_%K0%C0'TR_%m0EOAMOU_P;1:f<A;OV1X4;PZ%Kf%Cf'TRZ%mfEOA;OVZP;1:h<PPp+01IRZP2P3PRD7PXp+01JRf#4R_PDP2A@OU6I05[\J^0:^18X4;PY%Kh%Ch'T%mhEOPPp+01HRhP2P3PRD7PXPZPDP2%KZ%CZ'T9@OUD>[\J^0:^18PNp+01FRY/6<p+01GR;=eM1X4NP]%PYR]%lYEOAeMY]PN16;<AMMT1X4NP`%P;R`%l;EOAMMT`PN16h<PPp+01MR`P7P2P9D7p+01NR;#LR]?R67/Bd/bB/\2==M5[\E^58^0:^18X4NP>%Ph%lhEOPPp+01LRhP7P2P9D7Az`67/Bd/bB/\2%P`R05=M[\E^58^0:^18PN16Z<p+01K#n9=[1R<A=M?7\g[^6[X4NP>%PZ%lZEO%nf9=[1%Ph9=M?\g[^6[%x_%jfRZ%YfRN%NfRa&0?fRi%rfRj%cfRk%2fRlP_%V_%Q_C{R_%ql?Z@CRC%al?ZFHRH%`lRl&0>fRF'1R@'1Rm'1Rn'1Ro'1Rp'1Rq'1Rr'1Rs'1Rt'1PYPZPtP=PNPsf}PaPrPcPiPq%KfRq/JL%CfRL/JARAPPPhPDP1PRPS%LhPDP1CEEFX0:#DX3O1TqLRL5;ORqAMOULRhA;OVLRL%PfRV9eMfRfAMMTVRVPPP`P2P3PRD7AR]D2%K;%C;'T9@OU607X[\J^0:^18RJ'1RX'1RU'1RO'1R]'1RD'1PePAPDPbPqP]P>PhPOP4PLPUP5PfPXP7PVPJP2P6CyFIFIFIPjPpP^PkPoPWP_PnPQPCPmP\PHP@PKPlPFPIPPP;P7P2P9D7p+01OR9?z67/Bd/bB/\2%P95=M[\E^58^0:^18A=M?0\g\<^6[P3P1FIFIFIFIFIFIb8b7b=b<b>b;b:b9W8W7P3P1O2n2001000000121000000W2WAP3P1O2n2001000000121000000W2W@P3P1O2n2001000000121000000W2WHP3P1O2n2001000000121000000W2WGP3P1O2n2001000000121000000W2WFP3P1O2n2001000000121000000W2WEP3P1O2n2001000000121000000W2W>W=P3P1O2n2001000000121000000W2W<P3P1O2n2001000000121000000W2W;P3P1O2n2101000000121000000W2W:P3P1O2n2011000000121000000W2W9P3P1O2n2011000000121000000W2XKGP3P1O2n2011000000121000000W2WJP3P1O2n2011000000121000000W2WIP3P1O2n2011000000121000000W2P3P1O2n2001000000121000000W2WDP3P1O2n2001000000121000000W2WCP3P1O2n2001000000121000000W2WBP3P1O2n2001000000121000000W2W?P3P1O2n2001000000121000000W2WLo"). Qed.
