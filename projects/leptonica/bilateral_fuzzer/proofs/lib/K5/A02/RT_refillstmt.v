(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Exec RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_fk.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import R_cache_defs R_prim_defs R_thread R_refill RT_state RT_rep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_refillstmt () := "C69OSSVerify5KrLib2K53A028RT_state3layC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A028RT_state4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state8sec_nresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state2awC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state2qlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state2qgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3fs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3fs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3fs4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7ia_initC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2K53A028RT_state2prC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02=RT_refillstmt:refill_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02=RT_refillstmt9refill_caC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state2caC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z8eqb_reflK47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53A028RT_state3fs1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A028RT_state4rtsA01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7ca_initC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02=RT_refillstmt8refillΣC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53A028RT_state4fsst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state5regst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state4rtsA00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state7layoutA00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib2K53A02<R_depot_defs5depot00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state5secst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5batchC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53A028RT_state7r_muserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4r_stC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A02;R_prim_defs8round_faC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53A02;R_prim_defs;round_fa_geC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib2K53A028RT_state4r_flC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List3revC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_revC46Stdlib5Lists4List:length_appC69OSSVerify5KrLib2K53A028RT_state5r_mfaC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatK69OSSVerify5KrLib2K53A028RT_state5regst01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02=RT_refillstmt8populateC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I69OSSVerify5KrLib2K53A028RT_state4ckst00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K69OSSVerify5KrLib2K53A028RT_state4ckst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6reg_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass>MaxCount_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass8MaxCountC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7ClassIDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef5skipnc69OSSVerify5KrLib2K53A02=RT_refillstmt?populate_fl_lenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnI35stdpp4base5NoDup00C46Stdlib5Lists4List9nth_errorI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53A028RT_state6kFaCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5kUMapC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53A028RT_state8kUserCapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition populate (r : regst) (S k : Z) : regst :=
  let auser := S * Z.of_nat (length (r_st r)) in
  let msz := if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0 in
  let muser' := r_muser r + msz in
  let newc := (muser' - auser) / S in
  let nf' := Z.of_nat (length (r_fl r)) + newc in
  let mfa' := if r_mfa r <? 4 * nf' then round_fa (4 * nf') else r_mfa r in
  mkReg muser' mfa' (r_st r ++ repeat CkIdle (Z.to_nat newc))
        (r_fl r ++ rev (map (fun j => Z.of_nat (length (r_st r)) + Z.of_nat j) (seq 0 (Z.to_nat newc)))).

(* [comment removed for export] *)
Definition refill_reg (r : regst) (c : Z) : regst :=
  let n := MaxCount c / 2 in
  let r1 := if Z.of_nat (length (r_fl r)) <? n then populate r (ClassSize c) (n - Z.of_nat (length (r_fl r))) else r in
  mkReg (r_muser r1) (r_mfa r1) (r_st r1) (firstn (length (r_fl r1) - Z.to_nat n) (r_fl r1)).
(* [comment removed for export] *)
Definition refill_ca (r : regst) (c : Z) : list Z :=
  let n := MaxCount c / 2 in
  let r1 := if Z.of_nat (length (r_fl r)) <? n then populate r (ClassSize c) (n - Z.of_nat (length (r_fl r))) else r in
  skipn (length (r_fl r1) - Z.to_nat n) (r_fl r1).

Definition refillΣ (Σ : rtsA) (c : Z) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? c then refill_reg (pr Σ c) c else pr Σ c')
    (fun c' => if c' =? c then refill_ca (pr Σ c) c else ca Σ c') true (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition refill_entry_st (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (T c : Z) (m : mem) : machine_state :=
  entry_st ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (pc_addr T c)) (Z_to_bv 64 INST)
           (Z_to_bv 64 c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc refill_entry m.

(* [comment removed for export] *)
Definition refill_stmt : Prop :=
  forall (Σ : rtsA) PMc (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (c lo : Z),
  fdfs_only PMc -> mat_stable PMc -> 1 <= c <= 30 -> ca Σ c = [] ->
  ART_A Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> l_ACEIL (lay Σ) <= lo -> lo + 0x400 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 47 ->
  cps asegs (ASTA RTA Σ PMc (eq (refill_entry_st ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                    F fc (l_T (lay Σ)) c m)))
    (ASTA RTA (refillΣ Σ c) PMc
       (fun ms => exists m', ret_stF ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) F m' ms   (* [comment removed for export] *)
          /\ ART_A (refillΣ Σ c) m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ rt_pres (live Σ) (frames Σ) (bv_unsigned sp) m m')).

(* [comment removed for export] *)
Lemma refillΣ_facts : forall Σ c,
  lay (refillΣ Σ c) = lay Σ /\ live (refillΣ Σ c) = live Σ /\ frames (refillΣ Σ c) = frames Σ /\ credit (refillΣ Σ c) = credit Σ
  /\ dep (refillΣ Σ c) = dep Σ /\ sec (refillΣ Σ c) = sec Σ /\ sec_nres (refillΣ Σ c) = sec_nres Σ /\ aw (refillΣ Σ c) = aw Σ
  /\ ql (refillΣ Σ c) = ql Σ /\ qg (refillΣ Σ c) = qg Σ /\ fs0 (refillΣ Σ c) = fs0 Σ /\ fs2 (refillΣ Σ c) = fs2 Σ
  /\ fs4 (refillΣ Σ c) = fs4 Σ /\ ia_init (refillΣ Σ c) = ia_init Σ /\ ca_init (refillΣ Σ c) = true
  /\ (forall c', c' <> c -> pr (refillΣ Σ c) c' = pr Σ c' /\ ca (refillΣ Σ c) c' = ca Σ c')
  /\ ca (refillΣ Σ c) c = refill_ca (pr Σ c) c /\ pr (refillΣ Σ c) c = refill_reg (pr Σ c) c.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_refillstmt ()) [] "h02c'h11bh23Hneh31ch42Σp;1p;3p;2p;4p;6p;Bg0000j1>Tg000hj30Tg001Bj2TTg001bj1:Tg002Bj1KTg003;j1FTg0046j1BTg0051j1?Tg005ij1ITg006aj1=Tg007^j1<Tg008Uj1HTg009Lj1JTg00:Cj1GTg00;;j1ETg00<3j1DTg00<kj1CTg00=gj1MTg00>@j2;Tg00>]j23Tg00?Tj2ATg00@Xj2@Tg00A[j24Tg00BRj21Tg00Bmj2LTg00CGj2XTg00Chj4WTg00DCj6STg00Daj1VTg00ECj4OTg00E^j1PTg00FVlBQTg00GQj1NTg00HMj2UTg00IOR0f1R1f0R230p=7g00ImR3?012p=6g00JhR4?012p=5f3R5f2R6;01/12p=9f4R7P51L61P2COp=2f5?0751112,16'1p=8A0561/12,17p=Rg00Kdg00L_R8%>1R9;091T00#:R:%K1R;;0;R<g00M],T0#:R=%F1R>;0>R?%B1R@/7@RAg00N<RB%?1RC;0CRDg00O<#:RE%I1RF;0FRG%=1RH/7HRI%<1RJ=0:JRKg00P8#:RL%H1RM;0MRN%J1RO=0LORP%G1RQ/6QRR%E1RS/6SRT%D1RU/6URVg00Q2RW%C1RX;0XRYg00QRRZ=0WZR[1721#MR\PWP41;16R]1356R^/A61351R_n0100000020000/5_%:0R`PWP`P]1@^61451R^n0100000020000;0^'1[^00RaP`PWP`1;22Rb1312Rc/@2Rd1412n0100000020000PdPWP4Pb1Ac2RePcn0100000020000/5eC9Rc'1Rf'1Rg'1Rh'1Ri'1Rj'1Rk'1Rl'1Rm'1Rn'1Ro'1Rp'1Rq'1Rr'1Rs'1P8P9P<PsP:P;P?PrP=P>PAPqP0P@PDPpPBPCPGPoPEPFPIPnP0PHPKPmP:PJPNPlPLPMPPPkPLPOPRPjP3PQPTPiP3PSPVPhP3PUPYPgPWPXP[PfPWPZPaPcPWg00R2RcPWP4P21375Ra/A5Rf1376R[n0100000020000/5[PWP`P21@a5Ra1476R[n0100000020000=0`['1X1W15__A0`^^P4P_1L`^D2P]A0W]c1765#M[1716#M1;65=0Wc[1X16P2CWESX2\X00PWPZP`PWP`P21361Rc/@1R]1461n0100000020000P]PWP4P21Ac1R[Pcn0100000020000/5[C9X1WA0`dd15eeP`Pd1L4eD2Pb%V2ESCOD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2P8P9PWP41;21RbP[1362n0100000020000X00PWP`PbP]1462n0100000020000X00PZPFPHPJPMPOPCPQPSPU%P1PXP@P;P>MBQR]#>P9P:%K]P;P=%F]P>%B]/7@%?]=0BCPE%I]PF%=]/7H%<]=0:JPL%H]PMPL%J]PO%G]/6Q%E]/6S%D]/6UPW%C]PXPW%N]PZ%>5PWP41;25R4Pf1372n0100000020000X00PWP`P4Pa1472n0100000020000X00PZ%I5%=5%<5%H5%J5%?5%G5%E5%D5%P5%C5%B5%K5%F5MBQR7/31/5_1471=0`^'1\\^0014]2=0`d13]2/5eE8DRE8C9E8E8C9C9eP81U12R8#>P9P:%K8P;P=%F8P>%B8/7@%?8=0BCPE%I8PF%=8/7H%<8=0:JPL%H8PMPL%J8PO%G8/6Q%E8/6S%D8/6UPW%C8PXPW%N8PZ1U56R6/31/5_1461=0`^'1\\^001482=0`d1382/5eE8DRE8C9E8E8C9C9eX30W4o"). Qed.

(* [comment removed for export] *)
Lemma populate_fl_len : forall r S k, 1 <= S -> 1 <= k -> S * Z.of_nat (length (r_st r)) <= r_muser r ->
  Z.of_nat (length (r_fl (populate r S k))) = Z.of_nat (length (r_fl r)) + (r_muser (populate r S k) - S * Z.of_nat (length (r_st r))) / S
  /\ k <= (r_muser (populate r S k) - S * Z.of_nat (length (r_st r))) / S.
Proof.
  intros r S k HS Hk Hau. unfold populate. cbn [r_fl r_muser].
  set (auser := S * Z.of_nat (length (r_st r))) in *.
  assert (Hm : auser + k * S <= r_muser r + (if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0)).
  { destruct (Z.ltb_spec (r_muser r) (auser + k * S)) as [X|X]; [pose proof (round_fa_ge (auser + k * S - r_muser r) ltac:(lia)); lia | lia]. }
  assert (Hk' : k <= (r_muser r + (if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0) - auser) / S).
  { apply Z.div_le_lower_bound; lia. }
  split; [|exact Hk'].
  rewrite length_app, length_rev, length_map, length_seq, Nat2Z.inj_add, Z2Nat.id; [reflexivity|].
  pose proof (Z.div_pos (r_muser r + (if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0) - auser) S ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma refill_ca_len : forall r c, 1 <= c <= 30 -> reg_wf c r -> Z.of_nat (length (refill_ca r c)) = MaxCount c / 2.
Proof.
  intros r c Hc HW. pose proof (MaxCount_range c ltac:(lia)) as (Hm1 & Hm2). pose proof (ClassSize_range c ltac:(lia)) as (Hs & _).
  destruct HW as (_ & _ & W3 & _).
  assert (Hn : 1 <= MaxCount c / 2 <= 8) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
  unfold refill_ca. destruct (Z.ltb_spec (Z.of_nat (length (r_fl r))) (MaxCount c / 2)) as [X|X].
  - destruct (populate_fl_len r (ClassSize c) (MaxCount c / 2 - Z.of_nat (length (r_fl r))) ltac:(lia) ltac:(lia) W3) as (E1 & E2).
    rewrite length_skipn. lia.
  - rewrite length_skipn. lia.
Qed.
