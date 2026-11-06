(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ABudget ASecB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.

Module APopG3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMalmys AMal9l1 ATransp ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@G; @Ha; @LKS; @UMS; @FAM; @Hi__; @Ha'; @D; @U1; @F1'; @SG; @Hi; @Gt; @BX; @BZ; @LK; @RB'; @HR; @Hc'; @Pthr; @H; @B; @THF; @CR; @RB; @G15; @G18; @T6; @Pctx; @Hc; @HCR; @Hx; @I6; @NC; @H1; @NEc; @CSR; @H0; @CE'; @CE; @S; @B1; @Gt'; @B2; @L; @LEN; @LT; @GE; @NZ; @Hk; @Eau; @N2; @RSB; @G7; @G8; @Erb; @OK; @T1; @SN; @H2; @BB; @He1; @Hj; @Hd; @Eks; @Et; @HB6; @A5; @A1; @N1; @F1; @SPR; @G9; @G11; @G3; @G4; @B3; @S1; @S2; @HB; @Hz; @E1; @E2; @NT; @RES; @B5; @NS2; @RG; @Hcz; @E0; @He3; @He2; @PthrC; @PctxC; @Hc''; @Hn; @Emu; @Ecs; @Ens; @Et2])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation apart := AMallocA.apart (only parsing).
#[local] Notation WF := (WF AL_pasan).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
Definition pop_W (slo shi thr E R fa nf nc rb mu ums mfa fam : Z) (ci : bool) : list (Z * Z) :=
  [(slo, shi); (R, R + 8); (R + 16, R + 40); (R + 48, R + 56); (R + 68, R + 69);
   (fa + 4 * nf, fa + 4 * (nf + nc)); ((if ci then thr + 2768 else thr + 288), thr + 3168); (E, E + 80);
   (rb + mu, rb + mu + ums); (sh (rb + mu), sh (rb + mu) + ums / 8);
   (fa + mfa, fa + mfa + fam); (sh (fa + mfa), sh (fa + mfa) + fam / 8); (0x137620, 0x137621)].

(* [comment removed for export] *)
Definition const_nooom (cst : Z * list byte) : bool := (fst cst + Z.of_nat (length (snd cst)) <=? 0x137620) || (0x137621 <=? fst cst).
Lemma pa_consts_nooom : forallb const_nooom pa_consts = true.
Proof. vm_compute. reflexivity. Qed.

Section ReprPop.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (c ums fam nc : Z) (spa : word) (v' : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned spa - 1024.
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation n0 := (p_nodes0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation f0 := (p_frames0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) c).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) c + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation fr := (rg_free (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A c)))).
  #[warnings="-notation-for-abbreviation"] Local Notation cc := (rg_allocated_user (a_reg A c) / class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation Ag := (popg A c ums fam nc).
  #[warnings="-notation-for-abbreviation"] Local Notation W := (pop_W (bv_unsigned spa - 1024) (bv_unsigned spa) thr E R fa nf nc rb mu ums mfa fam (a_cache_inited A)).
  (* [comment removed for export] *)
  Hypothesis UMS : 0 <= ums /\ ums mod kUserMapSize = 0 /\ mu + ums < au + 9 * class_size c + kUserMapSize /\
                   au <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.   (* [comment removed for export] *)
  Hypothesis FAM : 0 <= fam /\ fam mod kFreeArrayMapSize = 0 /\ mfa + fam <= 4 * (au / class_size c) + kFreeArrayMapSize /\ mfa + fam <= kFreeArraySize.
  Hypothesis NC : 0 <= nc /\ au + nc * class_size c <= mu + ums /\ 4 * (nf + nc) <= mfa + fam.
  Hypothesis POS : mu + ums = 0 -> fam = 0 /\ nc = 0.

  (* [comment removed for export] *)
  Hypothesis MU : munch W v v'.
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let RR : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (conj WF0 RR). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.

  (* [comment removed for export] *)
  #[using="CE WF0 NC FAM UMS CEIL CR AI md m"] Lemma GEO :
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ kHighMemBeg <= sb /\ sb + kSpaceSize + 4096 <= alloc_ceiling /\ sb mod 4096 = 0 /\
    ri = sb + kSpaceSize /\ rb = sb + c * kRegionSize /\ 1 <= c <= 30 /\
    0 <= au <= mu /\ mu <= kFreeArrayOffset /\ 0 <= mfa <= kFreeArraySize /\ mu mod 8 = 0 /\ au mod 8 = 0 /\ mfa mod 8 = 0 /\
    0 <= ums /\ ums mod 8 = 0 /\ mu + ums <= kAuCap /\ 0 <= fam /\ fam mod 8 = 0 /\ mfa + fam <= kFreeArraySize /\   (* [comment removed for export] *)
    0 <= nc /\ 0 <= nf /\ 4 * nf <= mfa /\ 4 * (nf + nc) <= mfa + fam /\ 32 <= class_size c <= kMaxSize /\
    4096 <= n0 /\ n0 + kDepotNodesBlock <= alloc_ceiling /\ 4096 <= f0 /\ f0 + kStackStoreBlockBytes <= alloc_ceiling /\
    alloc_ceiling <= bv_unsigned spa - 1024 /\ bv_unsigned spa < 2^64 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
  Proof.
    pose proof (region_piece_bounds A c WF0 CR) as RB. cbv zeta in RB. pose proof (class_size_range c CR) as CSR.
    (first [ pose proof ((sb_facts A WF0)) as dR_1; dand5 dR_1 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]). assert (RIE : ri = sb + kSpaceSize) by reflexivity.
    (first [ pose proof ((hit_sep A m md AI)) as dR_2; dand13 dR_2 as _ _ _ _ _ _ _ _ _ N1 N2 F1 F2 | destruct (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & F1 & F2) ]). apply aobj_facts in N1. apply aobj_facts in F1.
    pose proof (place_facts A WF0) as (Pthr & _). cbv zeta in Pthr. (first [ dand3 Pthr as Pthr PthrC PthrM | destruct Pthr as (Pthr & PthrC & PthrM) ]). apply app_facts in Pthr.
    (first [ pose proof ((wfR A WF0)) as dR_4; dand3 dR_4 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_5; dand8 dR_5 as A1 A2 A3 A4 A5 A6 A7 _ | destruct (WR c CR) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _) ]).
    pose proof (zr_word spa) as SPR; unfold inr64 in SPR. destruct UMS as (U1 & U2 & U3 & U4). destruct FAM as (F1' & F2' & F3' & F4'). destruct NC as (N1' & N2' & N3').
    pose proof (wf_au_cap A c WF0 CR) as [AUC _]. unfold kAuCap, kUserMapSize, kMaxSize in *.
    assert (SB4 : sb mod 4096 = 0) by (apply (mod0_down _ 0x10000 4096); [exists 16; reflexivity| exact SBA]).
    assert (U8 : ums mod 8 = 0) by (apply (mod0_down _ kUserMapSize 8); [exists 32768; reflexivity| exact U2]).
    assert (F8 : fam mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists 32768; reflexivity| exact F2']).
    unfold region_beg in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
    all: clear - U3 AUC CSR; Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Qed.
  #[using="AI md m"] Lemma GEOP : aobj thr 4096 /\ aobj n0 kDepotNodesBlock /\ aobj f0 kStackStoreBlockBytes.
  Proof.
    (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as _ _ _ _ _ _ _ _ _ N1 _ F1 _ | destruct (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & F1 & _) ]).
    destruct (hit_place A m md AI) as (T1 & _). exact (conj T1 (conj N1 F1)).
  Qed.
  Ltac geop := let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in
    (first [ pose proof (GEOP) as dR_7; dand3 dR_7 as Gt Gn Gf | pose proof GEOP as (Gt & Gn & Gf) ]); aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf.
  (* [comment removed for export] *)
  #[using="CE WF0 POS NC FAM UMS CEIL CR AI spa nc md m Clg"] Lemma SHG : sh (rb + mu) = sh rb + mu / 8 /\ sh (rb + mu) + ums / 8 = sh rb + (mu + ums) / 8 /\
              sh (fa + mfa) = sh fa + mfa / 8 /\ sh (fa + mfa) + fam / 8 = sh fa + (mfa + fam) / 8 /\
              sh rb = rb / 8 + kShadowOffset /\ sh fa = sh rb + 469762048 /\ rb = 8 * (rb / 8) /\
              kHighShadowMapBeg <= sh rb /\ sh fa + 67108864 <= kHighMemBeg /\
              mu = 8 * (mu / 8) /\ ums = 8 * (ums / 8) /\ mfa = 8 * (mfa / 8) /\ fam = 8 * (fam / 8) /\ au = 8 * (au / 8).
  Proof.
    (first [ pose proof (GEO) as dR_8; dand20 dR_8 as G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 Grest | pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & Grest) ]).
    assert (D8 : forall x, x mod 8 = 0 -> x = 8 * (x / 8)) by (intros x Hx; pose proof (Z_div_mod_eq_full x 8); lia).
    assert (DA : forall q y, (8 * q + y) / 8 = q + y / 8) by (intros q y; rewrite Z.mul_comm, Z.div_add_l by lia; reflexivity).
    assert (SB8 : sb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact G5]).
    assert (RB8 : rb mod 8 = 0).
    { rewrite G7. unfold kRegionSize. rewrite Z.add_mod, Z.mul_mod, SB8 by lia. replace (2 ^ 32 mod 8) with 0 by reflexivity. rewrite Z.mul_0_r. reflexivity. }
    pose proof (D8 _ RB8) as Erb. pose proof (D8 _ G12) as Emu. pose proof (D8 _ G13) as Eau. pose proof (D8 _ G14) as Emfa.
    pose proof (D8 _ G16) as Eums. pose proof (D8 _ G19) as Efam.
    unfold sh. kung_all.
    assert (E1 : (rb + mu) / 8 = rb / 8 + mu / 8) by (rewrite Erb at 1; rewrite DA; reflexivity).
    assert (E2 : (mu + ums) / 8 = mu / 8 + ums / 8) by (rewrite Emu at 1; rewrite DA; reflexivity).
    assert (E3 : (rb + 3758096384 + mfa) / 8 = rb / 8 + 469762048 + mfa / 8).
    { rewrite Erb at 1. replace (8 * (rb / 8) + 3758096384 + mfa) with (8 * (rb / 8 + 469762048) + mfa) by lia. rewrite DA. reflexivity. }
    assert (E4 : (mfa + fam) / 8 = mfa / 8 + fam / 8) by (rewrite Emfa at 1; rewrite DA; reflexivity).
    assert (E5 : (rb + 3758096384) / 8 = rb / 8 + 469762048).
    { rewrite Erb at 1. replace (8 * (rb / 8) + 3758096384) with (8 * (rb / 8 + 469762048) + 0) by lia. rewrite DA. change (0 / 8) with 0. lia. }
    rewrite E1, E2, E3, E4, E5.
    (* [comment removed for export] *)
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [ assumption | clear - Erb G3 G4 G7 G8 CE; lia | lia ].
  Qed.

  (* [comment removed for export] *)
  #[using="MU"] Lemma AGW : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. Qed.

  Lemma W_shape : forall a,
    ~ (bv_unsigned spa - 1024 <= a < bv_unsigned spa) ->
    ~ (R <= a < R + 8) -> ~ (R + 16 <= a < R + 40) -> ~ (R + 48 <= a < R + 56) -> ~ (R + 68 <= a < R + 69) ->
    ~ (fa + 4 * nf <= a < fa + 4 * (nf + nc)) ->
    ~ ((if a_cache_inited A then thr + 2768 else thr + 288) <= a < thr + 3168) -> ~ (E <= a < E + 80) ->
    ~ (rb + mu <= a < rb + mu + ums) -> ~ (sh (rb + mu) <= a < sh (rb + mu) + ums / 8) ->
    ~ (fa + mfa <= a < fa + mfa + fam) -> ~ (sh (fa + mfa) <= a < sh (fa + mfa) + fam / 8) -> ~ (0x137620 <= a < 0x137621) ->
    outside W a.
  Proof.
    intros a X1 X2 X3 X4 X5 X6 X7 X7b X8 X9 X10 X11 X12. unfold pop_W. cbn [app outside].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
  (* [comment removed for export] *)
  Ltac wsolve Ha G SG Gt := apply W_shape;
    [ clear - Ha G | clear - Ha G | clear - Ha G | clear - Ha G | clear - Ha G | clear - Ha G
    | clear - Ha G Gt; destruct (a_cache_inited A) | clear - Ha G Gt | clear - Ha G | clear - Ha G SG | clear - Ha G | clear - Ha G SG | clear - Ha G ]; kung_all; lia.
  Ltac prep := pose proof GEO as G; pose proof SHG as SG; geop; kung_all.

  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGlow : forall a, kLowShadowMapBeg <= a < kHighShadowMapBeg -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha. prep. apply AGW; [clear - Ha; lia|]. wsolve Ha G SG Gt. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> a <> 0x137620 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Hx. assert (Ha' : 0x10000 <= a < 0x60a000 /\ a <> 0x137620) by (split; assumption). clear Ha Hx. prep. apply AGW; [clear - Ha'; lia|]. wsolve Ha' G SG Gt. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGstat : forall a, rt_statics AL_pasan a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. unfold rt_statics in H. apply AGimg; revert H; offs; unfold kDepotNodesL1; lia. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGshared : forall a, cl_shared LPA a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGimg; lia. Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGconst : forall cst a, In cst (cl_consts LPA) -> fst cst <= a < fst cst + Z.of_nat (length (snd cst)) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros cst a Hin Ha. cbn [cl_consts LPA] in Hin.
    pose proof pa_consts_nooom as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). unfold const_nooom in OK. apply orb_true_iff in OK. rewrite !Z.leb_le in OK.
    destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
    - apply AGimg; [unfold pa_shared in S; lia| clear - OK Ha; lia].
    - unfold pa_image_shadow, sh in S. apply AGlow; unfold kLowShadowMapBeg, kHighShadowMapBeg, kShadowOffset in *.
      replace (0x10000 / 8) with 8192 in S by reflexivity. replace (0x60a000 / 8) with 791552 in S by reflexivity. lia.
    - pose proof (pa_static_low a S). apply AGimg; [unfold pa_static in S; lia| clear - OK Ha; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 FAM UMS AI fam ums c md m Clg"] Lemma SEP6 : forall i b s, nth_error (big_maps A) i = Some (b, s) -> (i <> 0 /\ i <> 2 /\ i <> 3 /\ i <> 4)%nat ->
    apart b s (a_b6 A) kSpaceReserve /\ apart b s thr 4096 /\ 0 <= b /\ b + s <= 2^47.
  Proof.
    intros i b s Hn Hi. (first [ pose proof ((bm_nth_fixed A)) as dR_9; dand6 dR_9 as E0 E1 E2 E3 E4 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & _) ]). unfold a_thr in *.
    split; [exact (bm_sep A i 0 _ _ _ _ WF0 Hn E0 ltac:(lia))|]. split; [exact (bm_sep A i 4 _ _ _ _ WF0 Hn E4 ltac:(lia))|].
    destruct (wfM A WF0) as [_ BND]. (first [ pose proof ((BND b s (nth_error_In _ _ Hn))) as dR_10; dand3 dR_10 as B1 B2 B3 | destruct (BND b s (nth_error_In _ _ Hn)) as (B1 & B2 & B3) ]). lia.
  Qed.
  #[using="WF0 AI fam ums c md m Clg"] Lemma IN6 : a_b6 A <= sb /\ sb + kSpaceSize + 4096 <= a_b6 A + kSpaceReserve.
  Proof. (first [ pose proof ((sb_facts A WF0)) as dR_11; dand5 dR_11 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold kSpaceSize, kSpaceReserve. lia. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGmap : forall b s a, apart b s (a_b6 A) kSpaceReserve -> apart b s thr 4096 -> aobj b s -> b <= a < b + s ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros b s a S1 S2 HB Ha. prep. pose proof IN6 as I6. aobj_lin1 HB. unfold apart in *. kung_all.
    assert (Ha' : b <= a < b + s /\ 4096 <= b /\ b + s <= alloc_ceiling /\ (b + s <= a_b6 A \/ a_b6 A + (137438953472 + 69632) <= b) /\ (b + s <= thr \/ thr + 4096 <= b) /\
                  a_b6 A <= sb /\ sb + 137438953472 + 4096 <= a_b6 A + (137438953472 + 69632) /\ (b + s <= 2147446784 \/ 17594333495296 <= b) /\ (b + s <= 65536 \/ 6332416 <= b)) by (clear - Ha S1 S2 HB I6; lia).
    clear Ha S1 S2 HB I6. apply AGW; [clear - Ha' G; lia|]. wsolve Ha' G SG Gt.
  Qed.
  Ltac aobj_of H := apply (proj1 (aobj_app_rangeA _ _)) in H.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGctx : forall a, p_ctx (a_pl A) <= a < p_ctx (a_pl A) + 0x10000 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_12; dand7 dR_12 as _ _ _ _ _ E5 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & E5 & _) ]). (first [ pose proof ((SEP6 5%nat _ _ E5 ltac:(lia))) as dR_13; dand3 dR_13 as S1 S2 _ | destruct (SEP6 5%nat _ _ E5 ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_14; dand3 dR_14 as _ Pctx _ | pose proof (place_facts A WF0) as (_ & Pctx & _) ]). cbv zeta in Pctx. destruct Pctx as (Pctx & _). aobj_of Pctx. unfold a_ctx in *.
    exact (AGmap _ _ a S1 S2 Pctx Ha).
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGdtls : forall a, p_dtls (a_pl A) <= a < p_dtls (a_pl A) + 4096 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_15; dand15 dR_15 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14) ]). (first [ pose proof ((SEP6 14%nat _ _ E14 ltac:(lia))) as dR_16; dand3 dR_16 as S1 S2 _ | destruct (SEP6 14%nat _ _ E14 ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_17; dand12 dR_17 as _ _ _ _ _ _ _ _ _ _ Pdtls _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pdtls & _) ]). cbv zeta in Pdtls. destruct Pdtls as (Pdtls & _). aobj_of Pdtls.
    exact (AGmap _ _ a S1 S2 Pdtls Ha).
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGfs : forall a, p_fs (a_pl A) <= a < p_fs (a_pl A) + kFakeStackBytes -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_18; dand8 dR_18 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). (first [ pose proof ((SEP6 6%nat _ _ E6 ltac:(lia))) as dR_19; dand3 dR_19 as S1 S2 _ | destruct (SEP6 6%nat _ _ E6 ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof ((place_fs A WF0)) as dR_20; dand3 dR_20 as F1 F2 _ | pose proof (place_fs A WF0) as (F1 & F2 & _) ]). aobj_of F1. unfold a_fs in *.
    exact (AGmap _ _ a S1 S2 F1 Ha).
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGpa : forall a, p_pa (a_pl A) <= a < p_pa (a_pl A) + 8 * kChunksBlockCount -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_21; dand3 dR_21 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]). (first [ pose proof ((SEP6 1%nat _ _ E1 ltac:(lia))) as dR_22; dand3 dR_22 as S1 S2 _ | destruct (SEP6 1%nat _ _ E1 ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_23; dand13 dR_23 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa. destruct Ppa as (Ppa & _). aobj_of Ppa.
    unfold a_pa in *. apply (AGmap _ _ a S1 S2 Ppa). unfold kChunksBlockCount, kPtrArrayReserve in *. lia.
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGn0 : forall a, n0 <= a < n0 + kDepotNodesBlock -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_24; dand9 dR_24 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]). (first [ pose proof ((SEP6 7%nat _ _ E7 ltac:(lia))) as dR_25; dand3 dR_25 as S1 S2 _ | destruct (SEP6 7%nat _ _ E7 ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof (GEOP) as dR_26; dand3 dR_26 as _ Gn _ | pose proof GEOP as (_ & Gn & _) ]). unfold a_nodes0 in *. exact (AGmap _ _ a S1 S2 Gn Ha).
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGf0 : forall a, f0 <= a < f0 + kStackStoreBlockBytes -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_27; dand10 dR_27 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]). (first [ pose proof ((SEP6 8%nat _ _ E8 ltac:(lia))) as dR_28; dand3 dR_28 as S1 S2 _ | destruct (SEP6 8%nat _ _ E8 ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof (GEOP) as dR_29; dand3 dR_29 as _ _ Gf | pose proof GEOP as (_ & _ & Gf) ]). unfold a_frames0 in *. exact (AGmap _ _ a S1 S2 Gf Ha).
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGsec : forall sc a, In sc (sr_chunks (a_sec A)) -> cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros sc a Hin Ha. destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
    (first [ pose proof ((SEP6 (15 + j)%nat _ _ Ej ltac:(lia))) as dR_30; dand3 dR_30 as S1 S2 _ | destruct (SEP6 (15 + j)%nat _ _ Ej ltac:(lia)) as (S1 & S2 & _) ]).
    (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_31; dand5 dR_31 as _ _ B3 B4 _ | pose proof (sec_chunk_bounds A sc WF0 Hin) as (_ & _ & B3 & B4 & _) ]). aobj_of B3.
    exact (AGmap _ _ a S1 S2 B3 Ha).
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa md"] Lemma AGprim : forall a, sb <= a < sb + kSpaceSize + 4096 ->
    ~ (R <= a < R + 8) -> ~ (R + 16 <= a < R + 40) -> ~ (R + 48 <= a < R + 56) -> ~ (R + 68 <= a < R + 69) ->
    ~ (fa + 4 * nf <= a < fa + 4 * (nf + nc)) -> ~ (rb + mu <= a < rb + mu + ums) -> ~ (fa + mfa <= a < fa + mfa + fam) ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha X2 X3 X4 X5 X6 X8 X10. prep. pose proof IN6 as I6.
    (first [ pose proof ((bm_nth_fixed A)) as dR_32; dand6 dR_32 as E0 _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _) ]). pose proof (bm_sep A 4 0 _ _ _ _ WF0 E4 E0 ltac:(lia)) as T1.
    unfold a_thr, a_b6 in *. unfold apart in *. kung_all.
    assert (Gt' : thr + 4096 <= sb \/ sb + 137438953472 + 4096 <= thr) by (clear - T1 I6; lia). clear T1 I6.
    apply AGW; [clear - Ha G; lia|].
    apply W_shape; [ clear - Ha G | exact X2 | exact X3 | exact X4 | exact X5 | exact X6 | clear - Ha G Gt'; destruct (a_cache_inited A) | clear - Ha G Gt'
                   | exact X8 | clear - Ha G SG | exact X10 | clear - Ha G SG | clear - Ha G ]; kung_all; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums md"] Lemma AGreg : forall c' a, 0 <= c' <= 31 -> c' <> c -> region_beg sb c' <= a < region_beg sb c' + kRegionSize -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros c' a Hc NE Ha. pose proof GEO as G.
    assert (B : sb <= region_beg sb c' /\ region_beg sb c' + kRegionSize <= sb + kSpaceSize) by (unfold region_beg; clear - Hc; kung_all; nia).
    destruct (regions_disjoint sb c' c NE ltac:(lia) ltac:(lia)) as [D|D]; apply AGprim; clear - Ha B G D; kung_all; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums md"] Lemma AGri : forall a, ri <= a < ri + 4096 ->
    ~ (R <= a < R + 8) -> ~ (R + 16 <= a < R + 40) -> ~ (R + 48 <= a < R + 56) -> ~ (R + 68 <= a < R + 69) ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha X2 X3 X4 X5. pose proof GEO as G. apply AGprim; try assumption; kung_all; lia. Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums md"] Lemma AGuser : forall a, rb <= a < rb + mu -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha. pose proof GEO as G. apply AGprim; kung_all; lia. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums md"] Lemma AGfaold : forall a, fa <= a < fa + 4 * nf -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha. pose proof GEO as G. apply AGprim; kung_all; unfold kFreeArraySize in *; lia. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums md"] Lemma AGthr_gen : forall a, thr <= a < thr + 4096 -> ~ ((if a_cache_inited A then thr + 2768 else thr + 288) <= a < thr + 3168) -> ~ (E <= a < E + 80) ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha X7 X7b. prep. pose proof IN6 as I6.
    (first [ pose proof ((bm_nth_fixed A)) as dR_33; dand6 dR_33 as E0 _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _) ]). pose proof (bm_sep A 4 0 _ _ _ _ WF0 E4 E0 ltac:(lia)) as T1. unfold a_thr, a_b6 in *.
    assert (T6 : thr + 4096 <= sb \/ sb + 137438953472 + 4096 <= thr) by (clear - T1 I6; kung_all; lia). clear T1 I6 E0 E4. kung_all.
    apply AGW; [clear - Ha G Gt; lia|].
    apply W_shape; [ clear - Ha G Gt | clear - Ha G Gt T6 | clear - Ha G Gt T6 | clear - Ha G Gt T6 | clear - Ha G Gt T6 | clear - Ha G Gt T6 | exact X7 | exact X7b
                   | clear - Ha G Gt T6 | clear - Ha G SG Gt | clear - Ha G Gt T6 | clear - Ha G SG Gt | clear - Ha G Gt ]; kung_all; lia.
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGthr : forall a, thr <= a < thr + 288 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha. pose proof CR as HCR. apply AGthr_gen; [clear - Ha; lia| clear - Ha; destruct (a_cache_inited A); lia| clear - Ha HCR; lia]. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGthrtop : forall a, thr + 3168 <= a < thr + 4096 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha. pose proof CR as HCR. apply AGthr_gen; [clear - Ha; lia| clear - Ha; destruct (a_cache_inited A); lia| clear - Ha HCR; lia]. Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums md"] Lemma AGlines : a_cache_inited A = true -> forall a, thr + 288 <= a < thr + 2768 -> ~ (E <= a < E + 80) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros CI a Ha Xc. apply AGthr_gen; [clear - Ha; lia| rewrite CI; clear - Ha; lia| exact Xc]. Qed.
  (* [comment removed for export] *)
  #[using="FAM UMS fam ums c A"] Lemma sh_back : forall x k z, x mod 8 = 0 -> sh x <= z < sh x + k / 8 -> x <= 8 * (z - kShadowOffset) < x + k.
  Proof.
    intros x k z Hx Hz. unfold sh in Hz. pose proof (Z_div_mod_eq_full x 8) as E1. pose proof (Z_div_mod_eq_full k 8) as E2.
    pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as B2. rewrite Hx, Z.add_0_r in E1. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CE AR RR WF0 POS NC FAM UMS CEIL CR AI spa nc md m Clg"] Lemma new_shadow_apart : forall z, heap_shadow A z ->
    ~ (sh (rb + mu) <= z < sh (rb + mu) + ums / 8) /\ ~ (sh (fa + mfa) <= z < sh (fa + mfa) + fam / 8).
  Proof.
    intros z HS. pose proof GEO as G. pose proof SHG as SG.
    assert (M1 : (rb + mu) mod 8 = 0) by (rewrite Z.add_mod by lia; replace (rb mod 8) with 0 by (symmetry; apply Z.mod_divide; [lia| exists (rb / 8); lia]); rewrite Z.add_0_l, Z.mod_mod by lia; tauto).
    assert (M2 : (fa + mfa) mod 8 = 0).
    { rewrite Z.add_mod by lia. replace (fa mod 8) with 0; [rewrite Z.add_0_l, Z.mod_mod by lia; tauto|].
      symmetry. rewrite Z.add_mod by lia. replace (rb mod 8) with 0 by (symmetry; apply Z.mod_divide; [lia| exists (rb / 8); lia]). reflexivity. }
    unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with sb in HS.
    split; intros X; [pose proof (sh_back _ _ _ M1 X) as BX| pose proof (sh_back _ _ _ M2 X) as BX];
      destruct HS as [(c' & Hc' & HS)|[(c' & Hc' & HS)|(s & Hs & HS)]]; cbv zeta in HS.
    - assert (M' : region_beg sb c' mod 8 = 0) by (unfold region_beg; rewrite Z.add_mod, Z.mul_mod by lia; replace (sb mod 8) with 0 by (symmetry; apply (mod0_down _ 4096 8); [exists 512; reflexivity| tauto]); replace (kRegionSize mod 8) with 0 by reflexivity; rewrite Z.mul_0_r; reflexivity).
      pose proof (sh_back _ _ _ M' HS) as BZ. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'.
      destruct (Z.eq_dec c' c) as [->|NE]; [clear - BX BZ G; kung_all; lia|].
      destruct (regions_disjoint sb c' c NE ltac:(lia) ltac:(lia)) as [D|D]; clear - BX BZ G RB' D; kung_all; lia.
    - assert (M' : (region_beg sb c' + kFreeArrayOffset) mod 8 = 0).
      { unfold region_beg. rewrite Z.add_mod, (Z.add_mod sb) , Z.mul_mod by lia. replace (sb mod 8) with 0 by (symmetry; apply (mod0_down _ 4096 8); [exists 512; reflexivity| tauto]).
        replace (kRegionSize mod 8) with 0 by reflexivity. replace (kFreeArrayOffset mod 8) with 0 by reflexivity. rewrite Z.mul_0_r. reflexivity. }
      pose proof (sh_back _ _ _ M' HS) as BZ. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'.
      destruct (Z.eq_dec c' c) as [->|NE]; [clear - BX BZ G; kung_all; lia|].
      destruct (regions_disjoint sb c' c NE ltac:(lia) ltac:(lia)) as [D|D]; clear - BX BZ G RB' D; kung_all; lia.
    - (first [ pose proof ((sec_chunk_bounds A s WF0 Hs)) as dR_34; dand4 dR_34 as SN SA B3 _ | pose proof (sec_chunk_bounds A s WF0 Hs) as (SN & SA & B3 & _) ]). apply app_facts in B3. pose proof (map_size_ge (cs_n s) ltac:(clear - SN; unfold kMaxPrimaryUser in SN; lia)) as MG.
      assert (M' : cs_map s mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact SA]).
      pose proof (sh_back _ _ _ M' HS) as BZ.
      destruct (In_nth_error' _ _ Hs) as [j Hj]. pose proof (bm_nth_fixed A) as (E0 & _).
      pose proof (bm_sep A (15 + j) 0 _ _ _ _ WF0 (bm_nth_sec A j s Hj) E0 ltac:(lia)) as D. pose proof IN6 as I6. unfold a_b6 in *.
      clear - BX BZ G D I6 MG. kung_all. lia.
    - assert (M' : region_beg sb c' mod 8 = 0) by (unfold region_beg; rewrite Z.add_mod, Z.mul_mod by lia; replace (sb mod 8) with 0 by (symmetry; apply (mod0_down _ 4096 8); [exists 512; reflexivity| tauto]); replace (kRegionSize mod 8) with 0 by reflexivity; rewrite Z.mul_0_r; reflexivity).
      pose proof (sh_back _ _ _ M' HS) as BZ. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'.
      destruct (Z.eq_dec c' c) as [->|NE]; [clear - BX BZ G; kung_all; lia|].
      destruct (regions_disjoint sb c' c NE ltac:(lia) ltac:(lia)) as [D|D]; clear - BX BZ G RB' D; kung_all; lia.
    - assert (M' : (region_beg sb c' + kFreeArrayOffset) mod 8 = 0).
      { unfold region_beg. rewrite Z.add_mod, (Z.add_mod sb) , Z.mul_mod by lia. replace (sb mod 8) with 0 by (symmetry; apply (mod0_down _ 4096 8); [exists 512; reflexivity| tauto]).
        replace (kRegionSize mod 8) with 0 by reflexivity. replace (kFreeArrayOffset mod 8) with 0 by reflexivity. rewrite Z.mul_0_r. reflexivity. }
      pose proof (sh_back _ _ _ M' HS) as BZ. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'.
      destruct (Z.eq_dec c' c) as [->|NE]; [clear - BX BZ G; kung_all; lia|].
      destruct (regions_disjoint sb c' c NE ltac:(lia) ltac:(lia)) as [D|D]; clear - BX BZ G RB' D; kung_all; lia.
    - (first [ pose proof ((sec_chunk_bounds A s WF0 Hs)) as dR_35; dand4 dR_35 as SN SA B3 _ | pose proof (sec_chunk_bounds A s WF0 Hs) as (SN & SA & B3 & _) ]). apply app_facts in B3. pose proof (map_size_ge (cs_n s) ltac:(clear - SN; unfold kMaxPrimaryUser in SN; lia)) as MG.
      assert (M' : cs_map s mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact SA]).
      pose proof (sh_back _ _ _ M' HS) as BZ.
      destruct (In_nth_error' _ _ Hs) as [j Hj]. pose proof (bm_nth_fixed A) as (E0 & _).
      pose proof (bm_sep A (15 + j) 0 _ _ _ _ WF0 (bm_nth_sec A j s Hj) E0 ltac:(lia)) as D. pose proof IN6 as I6. unfold a_b6 in *.
      clear - BX BZ G D I6 MG. kung_all. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGhs : forall a, heap_shadow A a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a HS. destruct (new_shadow_apart a HS) as [NS1 NS2]. prep. pose proof (heap_shadow_range A a WF0 HS) as HR. unfold in_shadow_maps in HR.
    unfold kLowShadowMapBeg, kHighShadowMapSize in HR. kung_all. apply AGW; [clear - HR; lia|].
    apply W_shape; [ clear - HR G | clear - HR G | clear - HR G | clear - HR G | clear - HR G | clear - HR G | clear - HR G Gt; destruct (a_cache_inited A) | clear - HR G Gt
                   | clear - HR G | exact NS1 | clear - HR G | exact NS2 | clear - HR G ]; kung_all; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGchunk : forall c' k a, 1 <= c' <= 30 -> 0 <= k < carved_count A c' ->
    chunk_addr sb c' k <= a < chunk_addr sb c' k + class_size c' -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros c' k a Hc Hk Ha. pose proof GEO as G. (first [ pose proof ((carved_chunk_bounds A c' k WF0 Hc Hk)) as dR_36; dand3 dR_36 as B1 B2 _ | pose proof (carved_chunk_bounds A c' k WF0 Hc Hk) as (B1 & B2 & _) ]).
    pose proof (region_piece_bounds A c' WF0 Hc) as RB'. cbv zeta in *.
    destruct (Z.eq_dec c' c) as [->|NE]; [apply AGuser; lia|]. apply (AGreg c'); [lia| exact NE| kung_all; lia].
  Qed.
  #[using="CE WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md"] Lemma AGcarved : forall ch a, carved A ch -> chunk_lo sb ch <= a < chunk_hi sb ch -> v' (wz a) = v (wz a).
  Proof.
    intros ch a C Ha. destruct ch as [[c' k']|[mb' n1]].
    - destruct C as (Hc & Hk). cbn [chunk_lo chunk_hi alloc_beg] in Ha. exact (AGchunk c' k' a Hc Hk Ha).
    - unfold carved in C. cbn [chunk_lo chunk_hi] in Ha. exact (AGsec _ a C Ha).
  Qed.

  (* [comment removed for export] *)
  #[using="NN FAM UMS fam ums c"] Lemma mapped_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped v a k -> mapped v' a k.
  Proof. intros a k H0 H1 H2 M. eapply mapped_mono; [exact M|]. intros i Hi. apply NN; lia. Qed.
  #[using="NN FAM UMS fam ums c"] Lemma junk_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> junk_at rsegs v a k -> junk_at rsegs v' a k.
  Proof.
    (intros a k H0 H1; (first [ intro dR_52; dex1 dR_52 as bs; destruct dR_52 as [L B] | intro dR_52; dand3 dR_52 as bs L B | intros (bs & L & B) ])). pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite L in BB.
    apply junk_at_of_mapped; [lia| lia| lia|]. apply mapped_N; [lia| lia| lia|]. rewrite <- L. eapply bytes_at_mapped_gen; [exact B| lia| lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Cells.
  Variables (ksc : list word).
  Hypothesis EMP : pk_chunks (a_cache A c) = [].
  Hypothesis LKS : length ksc = 16%nat.
  (* [comment removed for export] *)
  Hypothesis P_mx : rw_cells rsegs v' R [C8 (wz 0)].
  Hypothesis P_nf : rw_cells rsegs v' (R + 16) [C8 (wz (nf + nc))].
  Hypothesis P_mfa : rw_cells rsegs v' (R + 24) [C8 (wz (mfa + fam))].
  Hypothesis P_au : rw_cells rsegs v' (R + 32) [C8 (wz (au + nc * class_size c))].
  Hypothesis P_mu : rw_cells rsegs v' (R + 48) [C8 (wz (mu + ums))].
  Hypothesis P_ex : rw_cells rsegs v' (R + 68) [C1 (Z_to_bv 8 0)].
  (* [comment removed for export] *)
  Hypothesis P_fa : u32arr rsegs v' (fa + 4 * nf) (map (fun k => wz (k * class_size c / kCompactPtrScale)) (newfree cc nc)).
  (* [comment removed for export] *)
  Hypothesis P_newU : mapped v' (rb + mu) ums.
  Hypothesis P_newF : mapped v' (fa + mfa) fam.
  Hypothesis P_shU : bytes_at rsegs v' (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ums / 8))).
  Hypothesis P_shF : bytes_at rsegs v' (sh (fa + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (fam / 8))).
  (* [comment removed for export] *)
  Hypothesis P_line : rw_cells rsegs v' E [C4 (wz 0); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s ksc)].
  (* [comment removed for export] *)
  Hypothesis P_lines : a_cache_inited A = false -> forall i, 1 <= i <= 31 -> i <> c ->
    exists ks, length ks = 16%nat /\ rw_cells rsegs v' (thr + 208 + 80 * i) [C4 (wz 0); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s ks)].

  (* [comment removed for export] *)
  Ltac trim := repeat match goal with H : _ /\ _ /\ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : arepr _ _ _ _ _ |- _ => clear H end.
  Ltac by_stat := apply AGstat; trim; unfold rt_statics; offs; lia.
  Ltac by_thr := apply AGthr; trim; unfold a_thr; offs; lia.
  Ltac by_ctx := apply AGctx; trim; unfold a_ctx; offs; lia.
  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.
  Ltac walk H AG :=
    lazymatch goal with
    | |- _ /\ _ => let H1 := fresh "L" in let H2 := fresh "L" in destruct H as [H1 H2]; split; [walk H1 AG | walk H2 AG]
    | |- _ => leaf H AG
    end.
  (* [comment removed for export] *)
  Lemma cell8 : forall (mm : mem) a z, rw_cells rsegs mm a [C8 (wz z)] -> u64_at rsegs mm a z.
  Proof. intros mm a z [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.
  Lemma cell1 : forall (mm : mem) a z, rw_cells rsegs mm a [C1 (Z_to_bv 8 z)] -> u8_at rsegs mm a z.
  Proof. intros mm a z [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

  (* [comment removed for export] *)
  #[using="LKS ksc CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma consts_Pg : consts_repr_ LPA AL_pasan (a_pl A) v'.
  Proof.
    pose proof alloc_ceiling_val as CE'. pose proof TPV as TP.
    apply (consts_P A v v' AR).
    - intros cst a Hin Ha. exact (AGconst cst a Hin Ha).
    - exact AGshared.
    - intros a Ha. unfold cfoot_stat in Ha. cbv zeta in Ha.
      cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
           al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in Ha.
      unfold off_primary_reserved_base, off_primary_reserved_size, off_SpaceBeg, off_release_interval, off_RegionInfo_ptr, off_PremappedHeap,
        off_sec_page_size, off_sec_chunks, off_sec_ptr_array_base, off_sec_ptr_array_size, off_q_max_size, off_q_min_size, off_q_max_cache_size,
        off_max_user_malloc, off_min_redzone, off_max_redzone, off_alloc_dealloc_mismatch in Ha.
      apply AGimg; lia.
    - intros a Ha. unfold cfoot_thr in Ha. destruct (Z.eq_dec a (thr + off_th_unwinding)) as [->|NT]; [apply AGthrtop; unfold off_th_unwinding; lia|].
      apply AGthr. unfold off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in *. clear - Ha NT. lia.
    - intros a Ha. unfold cfoot_misc in Ha. rewrite TP in Ha.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
      + apply AGctx. clear - Ha; lia.
      + apply AGctx. clear - Ha; lia.
      + apply AGimg; clear - Ha; lia.
      + apply AGimg; clear - Ha; lia.
      + apply AGimg; clear - Ha; lia.
      + apply AGdtls. clear - Ha; lia.
  Qed.

  #[using="P_mx LKS ksc CE RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma locks_Pg : locks_repr_ LPA AL_pasan (a_pl A) [] v'.
  Proof.
    pose proof (ar_locks _ _ _ _ _ RR) as C. pose proof CR as HCR. pose proof GEO as G. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. change (p_ri (a_pl A)) with ri in X, Y |- *. unfold kRegionInfoSize in *.
      destruct (Z.eq_dec c' c) as [->|NEc].
      + split.
        * rewrite Z.add_0_r. exact (cell8 _ _ _ P_mx).
        * leaf Y ltac:(apply AGri; offs; clear - Hi__ HCR; lia).
      + split; [leaf X ltac:(apply AGri; offs; clear - Hi__ HCR Hc NEc; lia) | leaf Y ltac:(apply AGri; offs; clear - Hi__ HCR Hc NEc; lia)].
    - walk C by_stat.
  Qed.

  #[using="CE AR RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma sec_Pg : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v'.
  Proof.
    apply (sec_P A v v' AR NN).
    - intros a Ha. unfold sfoot_stat in Ha. offs_h Ha.
      cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
           al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in Ha.
      apply AGimg; clear - Ha; lia.
    - intros a Ha. apply AGpa. (first [ pose proof ((wfS A WF0)) as dR_37; dand4 dR_37 as _ LEN RES _ | destruct (wfS A WF0) as (_ & LEN & RES & _) ]). unfold a_pa, kChunksBlockCount in *. clear - Ha LEN RES. lia.
    - intros sc a Hin Ha. apply (AGsec sc a Hin).
      (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_38; dand5 dR_38 as SN _ _ _ B5 | pose proof (sec_chunk_bounds A sc WF0 Hin) as (SN & _ & _ & _ & B5) ]). pose proof (needed_size2_secondary (cs_n sc) ltac:(clear - SN; exact (proj1 SN))) as NS2.
      pose proof (rounded_size_ge (cs_n sc)) as RG. unfold kSecondaryHeaderSize, kPageSize in *. clear - Ha B5 NS2 RG. lia.
  Qed.

  #[using="CE RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma depot_Pg : depot_repr_ LPA AL_pasan (a_pl A) (a_depot A) v'.
  Proof.
    apply (depot_P A v' (a_depot A) v (ar_depot _ _ _ _ _ RR)). intros a Ha. unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Ha. unfold kDepotNodesL1 in Ha.
    destruct Ha as [Ha|[Ha|Ha]]; [apply AGimg; clear - Ha; lia| exact (AGn0 a Ha)| exact (AGf0 a Ha)].
  Qed.

  #[using="CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma ia_Pg : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof.
    apply (ia_P A v v' AR). intros a Ha. unfold iafoot in Ha. cbv zeta in Ha.
    cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in Ha. apply AGimg; clear - Ha; lia.
  Qed.

  #[using="CE AR RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma fsbase_Pg : fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof. apply (fsbase_P A v v' AR NN). intros a Ha. apply AGfs. unfold a_fs, kFakeFlagsOffset, kFakeStackBytes in *. clear - Ha. lia. Qed.
  #[using="CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma fsptrs_Pg : fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsptrs_P A v v' AR). intros a Ha. apply AGfs. unfold a_fs, kFakeFramesOffset, kFakeStackBytes in *. clear - Ha. lia. Qed.
  #[using="CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma fsflags_Pg : fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsflags_P A v v' AR). intros a Ha. apply AGfs. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. clear - Ha. lia. Qed.
  #[using="AR RR WF0 NN AI md m"] Lemma maps_Pg : maps_repr_ AL_pasan (a_pl A) v'.
  Proof. exact (maps_P A v v' AR NN). Qed.

  (* [comment removed for export] *)
  #[using="CE AR RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma live_Pg : live_repr_ LPA sb (a_livemap A) v'.
  Proof.
    apply (live_sub_P A v v' AR NN (a_livemap A) (fun u li Hu => Hu)). intros u li a Hu Ha.
    exact (AGcarved _ a (known_carved A v AR _ _ (known_live A v AR u li Hu)) Ha).
  Qed.
  #[using="CE AR RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma quar_Pg : quarantine_repr_ LPA AL_pasan (a_pl A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF.
    apply (quar_P A v v' AR NN).
    - intros a Ha. unfold off_th_qcache in Ha. apply AGthr. clear - Ha. lia.
    - intros a Ha. cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
           al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in Ha. unfold off_q_cache_list_size in Ha. apply AGimg; clear - Ha; lia.
    - intros b a Hb Ha. exact (AGcarved _ a (batch_carved A v AR b Hb) Ha).
    - intros e a He Ha. exact (AGcarved _ a (known_carved A v AR _ _ (known_quar A v AR e He)) Ha).
  Qed.

  (* [comment removed for export] *)
  #[using="LKS ksc fam ums c A"] Lemma u32s_entry : forall (mm : mem) a ws i w, bytes_at rsegs mm a (u32s ws) -> nth_error ws i = Some w ->
    bytes_at rsegs mm (a + 4 * Z.of_nat i) (le4 w).
  Proof.
    intros mm a ws. revert a. induction ws as [|x ws IH]; intros a i w B EE; [destruct i; discriminate|].
    cbn [u32s] in B. apply bytes_at_app in B as [B0 B1]. rewrite length_le4 in B1. destruct i as [|i].
    - injection EE as ->. rewrite Z.mul_0_r, Z.add_0_r. exact B0.
    - cbn in EE. replace (a + 4 * Z.of_nat (S i)) with (a + Z.of_nat 4 + 4 * Z.of_nat i) by lia. exact (IH _ i w B1 EE).
  Qed.

  #[using="P_newF P_newU P_fa P_ex P_mu P_au P_mfa P_nf LKS ksc CE AR RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa md m Clg"] Lemma regions_Pg : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (a_reg Ag c') v' c'.
  Proof.
    intros c' Hc. pose proof CR as HCR. pose proof GEO as G.
    pose proof (region_piece_bounds A c' WF0 Hc) as RB'. cbv zeta in RB'.
    destruct (Z.eq_dec c' c) as [->|NEc].
    - rewrite popg_reg_c. pose proof (ar_regions _ _ _ _ _ RR c Hc) as C. unfold region_repr_ in *. cbv zeta in *.
      cbn [grow rg_free rg_mapped_fa rg_allocated_user rg_mapped_user].
      assert (RIA : region_info_addr sb c = R) by (unfold region_info_addr, kRegionInfoSize, a_ri, p_ri, a_sb; lia). rewrite RIA in *.
      unfold free_array_beg in *.
      assert (AGR : forall x, R <= x < R + 128 -> ~ (R <= x < R + 8) -> ~ (R + 16 <= x < R + 40) -> ~ (R + 48 <= x < R + 56) -> ~ (R + 68 <= x < R + 69) -> v' (wz x) = v (wz x)).
      { intros x Hx Y1 Y2 Y3 Y4. apply AGri; [clear - Hx HCR G; kung_all; lia| exact Y1| exact Y2| exact Y3| exact Y4]. }
      (first [ dand13 C as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt CF M1 M2 | destruct C as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & CF & M1 & M2) ]).
      unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_allocated_user, off_ri_allocated_meta, off_ri_mapped_user, off_ri_mapped_meta,
             off_ri_exhausted, off_ri_n_allocated, off_ri_rtoi in *.
      rewrite app_length, newfree_length by lia.
      split; [replace (Z.of_nat (length fr + Z.to_nat nc)) with (nf + nc) by lia; exact (cell8 _ _ _ P_nf)|].
      split; [exact (cell8 _ _ _ P_mfa)|]. split; [exact (cell8 _ _ _ P_au)|].
      split; [leaf Ham ltac:(apply AGR; clear - Hi__; lia)|]. split; [exact (cell8 _ _ _ P_mu)|].
      split; [leaf Hmm ltac:(apply AGR; clear - Hi__; lia)|]. split; [exact (cell1 _ _ _ P_ex)|].
      split; [apply junk_N; [clear - G; kung_all; lia| right; clear - G; kung_all; lia| exact J64]|].
      split; [apply junk_N; [clear - G; kung_all; lia| right; clear - G; kung_all; lia| exact Jna]|].
      split; [apply junk_N; [clear - G; kung_all; lia| right; clear - G; kung_all; lia| exact Jrt]|].
      split; [|split].
      + intros i k EE. destruct (Nat.lt_ge_cases i (length fr)) as [LT|GE].
        * rewrite nth_error_app1 in EE by exact LT. pose proof (CF i k EE) as LF. leaf LF ltac:(apply AGfaold; offs; clear - Hi__ LT; lia).
        * rewrite nth_error_app2 in EE by exact GE.
          assert (EK : nth_error (map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) (newfree cc nc)) (i - length fr) = Some (wz (k * class_size c / kCompactPtrScale)))
            by (rewrite nth_error_map, EE; reflexivity).
          destruct P_fa as [B _]. pose proof (u32s_entry v' _ _ _ _ B EK) as X. unfold u32_at.
          replace (region_beg sb c + kFreeArrayOffset + 4 * Z.of_nat i) with (region_beg sb c + kFreeArrayOffset + 4 * nf + 4 * Z.of_nat (i - length fr)) by lia. exact X.
      + (* [comment removed for export] *)
        intros i Hi. destruct (Z_lt_le_dec i mfa) as [LT|GE].
        * apply NN; [clear - G Hi; kung_all; lia| right; clear - G Hi; kung_all; lia| clear - G RB' Hi; kung_all; unfold kFreeArraySize in *; lia| exact (M1 i ltac:(clear - Hi LT RB'; lia))].
        * replace (region_beg sb c + kFreeArrayOffset + i) with (region_beg sb c + kFreeArrayOffset + mfa + (i - mfa)) by lia. apply P_newF. clear - Hi GE. lia.
      + intros i Hi. destruct (Z_lt_le_dec i mu) as [LT|GE].
        * apply NN; [clear - G Hi; kung_all; lia| right; clear - G Hi; kung_all; lia| clear - G RB' Hi; kung_all; lia| exact (M2 i ltac:(clear - Hi LT RB'; lia))].
        * replace (region_beg sb c + i) with (region_beg sb c + mu + (i - mu)) by lia. apply P_newU. clear - Hi GE. lia.
    - rewrite popg_reg_other by exact NEc. apply (region_P A v v' AR NN c' Hc). intros a Ha. unfold rfoot in Ha.
      unfold region_info_addr, free_array_beg, kRegionInfoSize in Ha. change (p_sb (a_pl A)) with sb in *.
      destruct Ha as [Ha|Ha].
      + apply AGri; clear - Ha Hc NEc HCR G; kung_all; unfold a_ri, p_ri, a_sb in *; lia.
      + apply (AGreg c'); [clear - Hc; lia| exact NEc| clear - Ha RB'; kung_all; unfold kFreeArraySize in *; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="LKS ksc fam ums c A"] Lemma line_of_cells : forall (mm : mem) e cz ks, length ks = 16%nat -> 1 <= cz <= 31 ->
    rw_cells rsegs mm e [C4 (wz 0); C4 (wz (max_count cz)); C8 (wz (class_size cz)); CB 64 (u32s ks)] ->
    4096 <= e -> (e + 80 <= 0x10000 \/ 0x60a000 <= e) -> e + 80 <= 2^64 ->
    Z.of_nat (length (@nil Z)) <= 16 /\
    u32_at rsegs mm (e + off_pc_count) (Z.of_nat (length (@nil Z))) /\
    (if true && negb (cz =? 0) then u32_at rsegs mm (e + off_pc_max_count) (max_count cz) /\ u64_at rsegs mm (e + off_pc_class_size) (class_size cz)
     else u32_at rsegs mm (e + off_pc_max_count) 0 /\ u64_at rsegs mm (e + off_pc_class_size) 0) /\
    (forall i k, nth_error (@nil Z) i = Some k -> u32_at rsegs mm (e + off_pc_chunk (Z.of_nat i)) (k * class_size cz / kCompactPtrScale)) /\
    junk_at rsegs mm (e + off_pc_chunk (Z.of_nat (length (@nil Z)))) (4 * (16 - Z.of_nat (length (@nil Z)))).
  Proof.
    intros mm e cz ks LK Hcz P He1 He2 He3. destruct P as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    apply bytes_at_app in B as [Bcnt B]. apply bytes_at_app in B as [Bmax B]. apply bytes_at_app in B as [Bsz Bks].
    rewrite !length_le4, !length_le8 in *. cbn [length Z.of_nat]. unfold u32_at, u64_at. offs.
    destruct (Z.eqb_spec cz 0) as [E0|_]; [lia|]. cbn [andb negb].
    split; [lia|]. split; [rewrite Z.add_0_r; exact Bcnt|]. split.
    { split; [replace (e + 4) with (e + Z.of_nat 4) by lia; exact Bmax| replace (e + 8) with (e + Z.of_nat 4 + Z.of_nat 4) by lia; exact Bsz]. }
    split; [intros [|i] k EE; discriminate|].
    apply junk_at_of_mapped; [lia| lia| lia|].
    pose proof (bytes_at_mapped_gen mm _ _ Bks ltac:(lia) ltac:(rewrite u32s_length, LK; lia)) as MK. rewrite u32s_length, LK in MK.
    intros j Hj. replace (e + (16 + 4 * Z.of_nat 0) + j) with (e + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + j) by lia. apply MK. lia.
  Qed.

  #[using="P_lines P_line LKS EMP ksc CE RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa nc fam ums c md m Clg"] Lemma cache_Pg : cache_repr_ LPA (a_pl A) (a_cache A) true v'.
  Proof.
    pose proof (ar_cache _ _ _ _ _ RR) as C. pose proof alloc_ceiling_val as CE'. pose proof GEO as G. pose proof CR as HCR.
    pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF.
    (first [ pose proof ((place_facts A WF0)) as dR_40; dand3 dR_40 as Pthr Pctx _ | pose proof (place_facts A WF0) as (Pthr & Pctx & _) ]). cbv zeta in Pthr, Pctx.
    unfold cache_repr_ in *. cbv zeta in *. (first [ dand5 C as C0 J1 J2 M1 M2 | destruct C as (C0 & J1 & J2 & M1 & M2) ]).
    (first [ dand3 Pthr as Pthr PthrC _ | destruct Pthr as (Pthr & PthrC & _) ]). apply app_facts in Pthr. (first [ dand3 Pctx as Pctx PctxC _ | destruct Pctx as (Pctx & PctxC & _) ]). apply app_facts in Pctx.
    split; [| split; [apply junk_N; [kung_all; offs; lia| offs; clear - Pthr; lia| exact J1] | split; [apply junk_N; [kung_all; offs; lia| offs; clear - Pthr; lia| exact J2]| split; (apply mapped_N; [| | | eassumption]); clear - Pthr PthrC Pctx PctxC CE'; kung_all; lia]]].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NEQ].
    - (* [comment removed for export] *) rewrite EMP. unfold off_th_per_class, off_th_alloc_cache, kPerClassSize. pose proof P_line as PL.
      replace (thr + 208 + 80 * c) with (thr + (208 + 80 * c)) in PL by lia.
      apply (line_of_cells v' _ c ksc LKS ltac:(lia)); [exact PL| clear - THF HCR; lia| clear - THF HCR; lia| clear - THF HCR CE'; lia].
    - (* [comment removed for export] *)
      destruct (Bool.bool_dec (a_cache_inited A) true) as [CI|CI]; [| apply Bool.not_true_is_false in CI].
      + (* [comment removed for export] *)
        (first [ pose proof ((C0 c' Hc')) as dR_44; dand5 dR_44 as LEN X1 X2 X3 X4 | destruct (C0 c' Hc') as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|]. rewrite CI in X2.
        assert (AGe : forall x, thr + off_th_per_class c' <= x < thr + off_th_per_class c' + 80 -> v' (wz x) = v (wz x)).
        { intros x Hx. offs_h Hx. unfold kPerClassSize in Hx. destruct (Z.eq_dec c' 0) as [->|NZ].
          - apply AGthr. clear - Hx. lia.
          - apply (AGlines CI); clear -Hx HCR Hc' NEQ NZ; nia. }
        split; [leaf X1 ltac:(apply AGe; offs; lia)|]. split; [|split].
        * cbn [andb] in X2 |- *. destruct (negb (c' =? 0)); destruct X2 as [Y1 Y2]; split; first [leaf Y1 ltac:(apply AGe; offs; lia) | leaf Y2 ltac:(apply AGe; offs; lia)].
        * intros i k EE. pose proof (X3 i k EE) as L.
          assert (Z.of_nat i < Z.of_nat (length (pk_chunks (a_cache A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite EE; discriminate)); lia).
          leaf L ltac:(apply AGe; offs; lia).
        * apply junk_N; [kung_all; offs; lia| offs; pose proof Hc' as Hc''; clear - Pthr Hc''; lia| exact X4].
      + (* [comment removed for export] *)
        (first [ pose proof ((wfC A WF0)) as dR_45; dand3 dR_45 as WC _ _ | destruct (wfC A WF0) as (WC & _ & _) ]).
        destruct (Z.eq_dec c' 0) as [->|NZ].
        * (first [ pose proof ((C0 0 ltac:(lia))) as dR_46; dand5 dR_46 as LEN X1 X2 X3 X4 | destruct (C0 0 ltac:(lia)) as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|]. rewrite CI in X2.
          assert (AGe : forall x, thr + off_th_per_class 0 <= x < thr + off_th_per_class 0 + 80 -> v' (wz x) = v (wz x)).
          { intros x Hx. offs_h Hx. unfold kPerClassSize in Hx. apply AGthr. clear - Hx. lia. }
          split; [leaf X1 ltac:(apply AGe; offs; lia)|]. split; [|split].
          -- cbn [andb negb Z.eqb] in X2 |- *. destruct X2 as [Y1 Y2]; split; first [leaf Y1 ltac:(apply AGe; offs; lia) | leaf Y2 ltac:(apply AGe; offs; lia)].
          -- intros i k EE. pose proof (X3 i k EE) as L.
             assert (Z.of_nat i < Z.of_nat (length (pk_chunks (a_cache A 0)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite EE; discriminate)); lia).
             leaf L ltac:(apply AGe; offs; lia).
          -- apply junk_N; [kung_all; offs; lia| offs; clear - Pthr; lia| exact X4].
        * (first [ pose proof ((P_lines CI c' ltac:(lia) NEQ)) as dR_47; dex1 dR_47 as ks; destruct dR_47 as [LK PL] | pose proof ((P_lines CI c' ltac:(lia) NEQ)) as dR_47; dand3 dR_47 as ks LK PL | destruct (P_lines CI c' ltac:(lia) NEQ) as (ks & LK & PL) ]).
          assert (EMP' : pk_chunks (a_cache A c') = []) by ((first [ pose proof ((WC c' ltac:(lia))) as dR_48; dand4 dR_48 as _ _ _ Z4 | destruct (WC c' ltac:(lia)) as (_ & _ & _ & Z4) ]); exact (Z4 CI)).
          rewrite EMP'. unfold off_th_per_class, off_th_alloc_cache, kPerClassSize.
          replace (thr + (208 + 80 * c')) with (thr + 208 + 80 * c') by lia.
          apply (line_of_cells v' _ c' ks LK ltac:(lia)); [exact PL| clear - THF Hc'; lia| clear - THF Hc'; lia| clear - THF Hc' CE'; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="LKS ksc fam ums c A"] Lemma fill_join : forall (mm : mem) a n1 n2 bv, 0 <= n1 -> 0 <= n2 -> fill_at rsegs mm a n1 bv -> fill_at rsegs mm (a + n1) n2 bv -> fill_at rsegs mm a (n1 + n2) bv.
  Proof.
    intros mm a n1 n2 bv H1 H2 F1 F2. unfold fill_at in *. rewrite Z2Nat.inj_add, repeat_app by lia. apply bytes_at_app. split; [exact F1|].
    rewrite repeat_length, Z2Nat.id by lia. exact F2.
  Qed.
  #[using="LKS ksc FAM UMS fam ums c A"] Lemma fill_sub : forall (mm : mem) a n d k bv, 0 <= d -> 0 <= k -> d + k <= n -> fill_at rsegs mm a n bv -> fill_at rsegs mm (a + d) k bv.
  Proof.
    intros mm a n d k bv Hd Hk Hn F. unfold fill_at in *.
    replace (Z.to_nat n) with (Z.to_nat d + (Z.to_nat k + Z.to_nat (n - d - k)))%nat in F by lia. rewrite !repeat_app in F.
    apply bytes_at_app in F as [_ F]. rewrite repeat_length, Z2Nat.id in F by lia. apply bytes_at_app in F as [F _]. exact F.
  Qed.
  (* [comment removed for export] *)
  #[using="LKS ksc FAM UMS fam ums c A"] Lemma D8 : forall x, x mod 8 = 0 -> x = 8 * (x / 8).
  Proof. intros x Hx. pose proof (Z_div_mod_eq_full x 8). lia. Qed.

  (* [comment removed for export] *)
  #[using="P_shU LKS ksc CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc fam md m Clg"] Lemma fill_tail_user : fill_at rsegs v' (sh (rb + au)) ((mu + ums - au) / 8) kAsanHeapLeftRedzoneMagic.
  Proof.
    pose proof GEO as G. pose proof SHG as SG.
    (first [ pose proof ((shadow_P0 A v v' AR AGhs)) as dR_49; dand5 dR_49 as _ _ _ T4 _ | pose proof (shadow_P0 A v v' AR AGhs) as (_ & _ & _ & T4 & _) ]). destruct (T4 c CR) as [TU _]. cbv zeta in TU. change (p_sb (a_pl A)) with sb in TU.
    assert (MU8 : mu mod 8 = 0) by tauto. assert (AU8 : au mod 8 = 0) by tauto. assert (UM8 : ums mod 8 = 0) by tauto.
    assert (RB8 : rb mod 8 = 0) by (apply Z.mod_divide; [lia| exists (rb / 8); lia]).
    pose proof (D8 _ MU8) as Emu. pose proof (D8 _ AU8) as Eau. pose proof (D8 _ UM8) as Eum.
    assert (E1 : (mu - au) / 8 = mu / 8 - au / 8) by (rewrite Emu, Eau at 1; replace (8 * (mu / 8) - 8 * (au / 8)) with ((mu / 8 - au / 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (E2 : (mu + ums - au) / 8 = (mu / 8 - au / 8) + ums / 8)
      by (rewrite Emu, Eau, Eum at 1; replace (8 * (mu / 8) + 8 * (ums / 8) - 8 * (au / 8)) with ((mu / 8 - au / 8 + ums / 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (E3 : sh (rb + au) = sh rb + au / 8) by (apply sh_add; [exact RB8| exact AU8]).
    rewrite E2. apply fill_join; [clear - G Emu Eau; lia| clear - G Eum; lia| rewrite <- E1; exact TU|].
    rewrite E3. replace (sh rb + au / 8 + (mu / 8 - au / 8)) with (sh (rb + mu)) by (clear - SG; lia). exact P_shU.
  Qed.
  #[using="P_shF LKS ksc CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa nc ums md m Clg"] Lemma fill_tail_fa : fill_at rsegs v' (sh fa) ((mfa + fam) / 8) kAsanHeapLeftRedzoneMagic.
  Proof.
    pose proof GEO as G. pose proof SHG as SG.
    (first [ pose proof ((shadow_P0 A v v' AR AGhs)) as dR_50; dand5 dR_50 as _ _ _ T4 _ | pose proof (shadow_P0 A v v' AR AGhs) as (_ & _ & _ & T4 & _) ]). destruct (T4 c CR) as [_ TF]. cbv zeta in TF. change (p_sb (a_pl A)) with sb in TF.
    assert (MF8 : mfa mod 8 = 0) by tauto. assert (FM8 : fam mod 8 = 0) by tauto.
    pose proof (D8 _ MF8) as Emfa. pose proof (D8 _ FM8) as Efam.
    assert (E2 : (mfa + fam) / 8 = mfa / 8 + fam / 8)
      by (rewrite Emfa, Efam at 1; replace (8 * (mfa / 8) + 8 * (fam / 8)) with ((mfa / 8 + fam / 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    rewrite E2. apply fill_join; [clear - G Emfa; lia| clear - G Efam; lia| exact TF|].
    replace (sh fa + mfa / 8) with (sh (fa + mfa)) by (clear - SG; lia). exact P_shF.
  Qed.

  #[using="P_shF P_shU LKS ksc CE AR RR WF0 MU POS NC FAM UMS CEIL CR AI spa md m Clg"] Lemma shadow_Pg : shadow_repr_ LPA sb (a_reg Ag) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    pose proof GEO as G. pose proof SHG as SG. pose proof CR as HCR. pose proof (class_size_mod32 c CR) as CM32.
    (first [ pose proof ((shadow_P0 A v v' AR AGhs)) as dR_51; dand6 dR_51 as S1 S2 S3 S4 S5 S6 | pose proof (shadow_P0 A v v' AR AGhs) as (S1 & S2 & S3 & S4 & S5 & S6) ]).
    pose proof fill_tail_user as FU. pose proof fill_tail_fa as FF.
    assert (AU8 : au mod 8 = 0) by tauto. assert (MU8 : mu mod 8 = 0) by tauto. assert (UM8 : ums mod 8 = 0) by tauto.
    assert (CS8 : class_size c mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM32]).
    assert (RB8 : rb mod 8 = 0) by (apply Z.mod_divide; [lia| exists (rb / 8); lia]).
    pose proof (D8 _ AU8) as Eau. pose proof (D8 _ MU8) as Emu. pose proof (D8 _ UM8) as Eum. pose proof (D8 _ CS8) as Ecs.
    pose proof (g1_cc A c ums fam WF0 CR UMS FAM) as [CC0 AUE].
    split; [| split; [exact S2| split; [exact S3| split; [| exact (conj S5 S6)]]]].
    - (* [comment removed for export] *)
      intros c' k Hc ST. change (a_reg Ag) with (a_reg (popg A c ums fam nc)) in ST.
      assert (ST' : (p_free_ (a_reg A) c' k \/ p_cached_ (a_cache A) c' k \/ p_batch_ (a_qthread A) (a_qglobal A) c' k) \/ (c' = c /\ cc <= k < cc + nc)).
      { destruct ST as [F|R']; [| left; right; exact R']. apply (popg_free_iff A c ums fam nc CR UMS FAM NC) in F. destruct F as [F|F]; [left; left; exact F| right; exact F]. }
      destruct ST' as [OLD|[-> Hk]]; [exact (S1 c' k Hc OLD)|].
      unfold pshadow_free, fa8. unfold chunk_addr.
      assert (KS8 : (k * class_size c) mod 8 = 0) by (rewrite Z.mul_mod, CS8, Z.mul_0_r by lia; reflexivity).
      pose proof (D8 _ KS8) as Eks.
      assert (EQ : sh (rb + k * class_size c) = sh (rb + au) + (k * class_size c - au) / 8).
      { rewrite (sh_add rb (k * class_size c) RB8 KS8), (sh_add rb au RB8 AU8). rewrite Eks, Eau at 2.
        replace (8 * (k * class_size c / 8) - 8 * (au / 8)) with ((k * class_size c / 8 - au / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      rewrite EQ. apply (fill_sub v' _ ((mu + ums - au) / 8)); [| | | exact FU].
      + assert (au <= k * class_size c) by (rewrite AUE; apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Eks, Eau at 1. replace (8 * (k * class_size c / 8) - 8 * (au / 8)) with ((k * class_size c / 8 - au / 8) * 8) by lia. rewrite Z.div_mul by lia. clear - H Eks Eau. lia.
      + apply Z.div_pos; lia.
      + assert (L : k * class_size c + class_size c <= au + nc * class_size c).
        { rewrite AUE. replace (cc * class_size c + nc * class_size c) with ((cc + nc) * class_size c) by lia.
          replace (k * class_size c + class_size c) with ((k + 1) * class_size c) by lia. apply Z.mul_le_mono_nonneg_r; lia. }
        destruct NC as (_ & N2 & _).
        pose proof (D8 (mu + ums - au) ltac:(rewrite Zminus_mod, Zplus_mod, MU8, UM8, AU8; reflexivity)) as Et.
        rewrite Eks, Eau at 1. replace (8 * (k * class_size c / 8) - 8 * (au / 8)) with ((k * class_size c / 8 - au / 8) * 8) by lia. rewrite Z.div_mul by lia.
        clear - L N2 Eks Eau Ecs Et G. lia.
    - (* [comment removed for export] *)
      intros c' Hc. destruct (Z.eq_dec c' c) as [->|NEc].
      + rewrite popg_reg_c. cbn [grow rg_allocated_user rg_mapped_user rg_mapped_fa]. cbv zeta. change (a_sb Ag) with sb. split; [| exact FF].
        assert (NS8 : (nc * class_size c) mod 8 = 0) by (rewrite Z.mul_mod, CS8, Z.mul_0_r by lia; reflexivity). pose proof (D8 _ NS8) as Ens.
        assert (AN8 : (au + nc * class_size c) mod 8 = 0) by (rewrite Zplus_mod, AU8, NS8; reflexivity).
        rewrite (sh_add rb (au + nc * class_size c) RB8 AN8). rewrite (sh_add rb au RB8 AU8) in FU.
        assert (E1 : (au + nc * class_size c) / 8 = au / 8 + nc * class_size c / 8)
          by (rewrite Eau, Ens at 1; replace (8 * (au / 8) + 8 * (nc * class_size c / 8)) with ((au / 8 + nc * class_size c / 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
        rewrite E1, Z.add_assoc. destruct NC as (N1 & N2 & _).
        pose proof (D8 (mu + ums - au) ltac:(rewrite Zminus_mod, Zplus_mod, MU8, UM8, AU8; reflexivity)) as Et.
        pose proof (D8 (mu + ums - (au + nc * class_size c)) ltac:(rewrite Zminus_mod, Zplus_mod, MU8, UM8, AN8; reflexivity)) as Et2.
        apply (fill_sub v' _ ((mu + ums - au) / 8)); [clear - N1 G Ens; assert (0 <= nc * class_size c) by (apply Z.mul_nonneg_nonneg; lia); lia| clear - N2 Et2; lia| clear - N2 Et Et2 Ens; lia| exact FU].
      + rewrite popg_reg_other by exact NEc. exact (S4 c' Hc).
  Qed.

  (* [comment removed for export] *)
  #[using="P_lines P_line P_shF P_shU P_newF P_newU P_fa P_ex P_mu P_au P_mfa P_nf P_mx LKS EMP ksc CE AR RR WF0 NN MU POS NC FAM UMS CEIL CR AI spa md m"] Theorem pop_arepr : @arepr _ DepotRepL LPA AL_pasan [] Ag v'.
  Proof.
    constructor; cbn [popg set_cache_inited set_reg a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes].
    - exact consts_Pg. - exact locks_Pg. - exact regions_Pg. - exact cache_Pg. - exact live_Pg. - exact quar_Pg. - exact sec_Pg.
    - exact depot_Pg. - exact ia_Pg. - exact fsbase_Pg. - exact fsptrs_Pg. - exact fsflags_Pg. - exact maps_Pg. - exact shadow_Pg.
  Qed.
  End Cells.

End ReprPop.
End APopG3.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module APopG4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMal9l1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
From Stdlib Require Import FunctionalExtensionality Classical_Prop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reg_upd_same : forall reg c, reg_upd reg c (reg c) = reg.
Proof. intros reg c. apply functional_extensionality. intros c'. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|]; reflexivity. Qed.
Lemma popg_zero : forall A c, popg A c 0 0 0 = set_cache_inited A true.
Proof. intros A c. unfold popg. rewrite grow_zero, reg_upd_same. reflexivity. Qed.

Section Tiny.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Tiny.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Carve.
Context {Clg : Ceiling}.
  Lemma popg_hull_nc : forall A c ums fam nc nc', pa_hull (popg A c ums fam nc) = pa_hull (popg A c ums fam nc').
  Proof.
    intros. unfold pa_hull, ahull_of, ahull_of_, aregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh]. f_equal. f_equal. f_equal. f_equal.
    assert (E : forall n, classes_regions_ (p_sb (a_pl A)) (reg_upd (a_reg A) c (grow c (a_reg A c) ums fam nc)) n =
                          classes_regions_ (p_sb (a_pl A)) (reg_upd (a_reg A) c (grow c (a_reg A c) ums fam nc')) n).
    { induction n as [|n IH]; [reflexivity|]. cbn [classes_regions_]. rewrite IH. f_equal. unfold reg_upd. destruct (Z.eqb (Z.of_nat (S n)) c); reflexivity. }
    rewrite E. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma popg_lhull_nc : forall A c ums fam nc nc', pa_lhull (popg A c ums fam nc) = pa_lhull (popg A c ums fam nc').
  Proof.
    intros. unfold pa_lhull, alhull_of, alhull_of_, alregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh]. f_equal. f_equal. f_equal. f_equal.
    assert (E : forall n, lclasses_regions_ (p_sb (a_pl A)) (reg_upd (a_reg A) c (grow c (a_reg A c) ums fam nc)) n =
                          lclasses_regions_ (p_sb (a_pl A)) (reg_upd (a_reg A) c (grow c (a_reg A c) ums fam nc')) n).
    { induction n as [|n IH]; [reflexivity|]. cbn [lclasses_regions_]. rewrite IH. f_equal. unfold reg_upd. destruct (Z.eqb (Z.of_nat (S n)) c); reflexivity. }
    rewrite E. reflexivity.
  Qed.
  Lemma popg_mapped_nc : forall A c ums fam nc nc' c',
    rg_mapped_user (a_reg (popg A c ums fam nc) c') = rg_mapped_user (a_reg (popg A c ums fam nc') c') /\
    rg_mapped_fa (a_reg (popg A c ums fam nc) c') = rg_mapped_fa (a_reg (popg A c ums fam nc') c').
  Proof. intros. cbn [popg set_cache_inited set_reg a_reg]. unfold reg_upd. destruct (Z.eqb c' c); split; reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Carve.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Hidden.
Context {Clg : Ceiling}.
  Variables (A : AState) (c ums fam nc : Z) (m m' : mem).
  Hypothesis W : WF A.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis UMS : 0 <= ums /\ ums mod kUserMapSize = 0 /\ rg_mapped_user (a_reg A c) + ums < rg_allocated_user (a_reg A c) + 9 * class_size c + kUserMapSize /\
                   rg_allocated_user (a_reg A c) <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.   (* [comment removed for export] *)
  Hypothesis FAM : 0 <= fam /\ fam mod kFreeArrayMapSize = 0 /\
                   rg_mapped_fa (a_reg A c) + fam <= 4 * (rg_allocated_user (a_reg A c) / class_size c) + kFreeArrayMapSize /\ rg_mapped_fa (a_reg A c) + fam <= kFreeArraySize.
  Hypothesis NC : 0 <= nc /\ rg_allocated_user (a_reg A c) + nc * class_size c <= rg_mapped_user (a_reg A c) + ums /\
                  4 * (Z.of_nat (length (rg_free (a_reg A c))) + nc) <= rg_mapped_fa (a_reg A c) + fam.
  Hypothesis POS : rg_mapped_user (a_reg A c) + ums = 0 -> fam = 0 /\ nc = 0.
  Local Notation Ag := (popg A c ums fam nc).
  Hypothesis HID : hidden_repr (a_pl A) (a_reg A) (a_sec A) m.
  (* [comment removed for export] *)
  Hypothesis AGG : forall z, ghost_hs_ (a_pl A) z -> m' (wz z) = m (wz z) \/ (heap_shadow Ag z /\ m' (wz z) <> None).
  (* [comment removed for export] *)
  Hypothesis LOWP : forall z, kLowShadowMapBeg <= z < kLowShadowMapBeg + 0x10000000 -> m (wz z) <> None -> m' (wz z) <> None.

  Lemma pop_hidden : hidden_repr (a_pl A) (a_reg Ag) (a_sec A) m'.
  Proof.
    destruct HID as [H1 H2]. split.
    - intros z Gz. destruct (H1 z Gz) as [P Q]. destruct (AGG z Gz) as [E|[HS P']].
      + rewrite E. split; [exact P|]. intros NH. apply Q. intros X. apply NH.
        pose proof (popg_heap_shadow A c ums fam nc UMS FAM z X) as Y. exact Y.
      + split; [exact P'|]. intros NH. exfalso. exact (NH HS).
    - intros z Hz NV. apply LOWP; [exact Hz| exact (H2 z Hz NV)].
  Qed.
End Hidden.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Context {Clg : Ceiling}.
  Variables (O Og O' NB : Z -> Prop) (hi win : Z) (v vg v' : mem).
  Let window (a : Z) : Prop := hi - win <= a < hi.
  Let errno (a : Z) : Prop := cl_errno LPA <= a < cl_errno LPA + 4.
  (* [comment removed for export] *)
  Hypothesis G_mono : forall a, O a -> Og a.
  Hypothesis G_new : forall a, 0 <= a < 2^64 -> Og a -> ~ O a -> v (wz a) = None /\ heap_zone LPA a.
  Hypothesis G_agree : forall a, 0 <= a < 2^64 -> ~ Og a -> ~ window a -> vg (wz a) = v (wz a).
  Hypothesis G_pres : forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v (wz a) <> None -> vg (wz a) <> None.
  (* [comment removed for export] *)
  Hypothesis RF : frame_ok LPA Og O' hi win nowhere NB vg v'.
  (* [comment removed for export] *)
  Hypothesis OW : forall a, Og a -> ~ window a /\ ~ errno a.

  Lemma frame_grow_refill : frame_ok LPA O O' hi win nowhere NB v v'.
  Proof.
    destruct RF as (F1 & F2 & F3 & F4 & F5 & F6 & F7). unfold frame_ok.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE NV NN. destruct (classic (Og a)) as [Hg|Ng].
      + destruct (G_new a Ha Hg NO) as [VN _]. destruct (F6 a Ha Hg NO') as [X|X]; [exfalso; exact (NN X)|]. rewrite X, VN. reflexivity.
      + rewrite (F1 a Ha Ng NO' NW NE NV NN). exact (G_agree a Ha Ng NW).
    - intros a Ha NI Hv. destruct (classic (Og a)) as [Hg|Ng].
      + destruct (classic (O a)) as [Ho|No]; [left; exact Ho|]. exfalso. destruct (G_new a Ha Hg No) as [VN _]. exact (Hv VN).
      + destruct (F2 a Ha NI (G_pres a Ha NI Hv)) as [X|[X|X]]; [exfalso; exact (Ng X)| right; left; exact X| right; right; exact X].
    - exact F3.
    - intros a Ha HB. destruct (F4 a Ha HB) as [Hg|[[]|[VN HZ]]].
      + destruct (classic (O a)) as [Ho|No]; [left; exact Ho|]. right. right. exact (G_new a Ha Hg No).
      + right. right. split; [| exact HZ]. destruct (v (wz a)) eqn:E; [| reflexivity]. exfalso.
        assert (NI : ~ in_image LPA a) by (destruct HZ as [_ NI]; exact NI).
        apply (G_pres a Ha NI); [rewrite E; discriminate| exact VN].
    - intros a Ha Ho'. destruct (F5 a Ha Ho') as [Hg|[[]|[VN HZ]]].
      + destruct (classic (O a)) as [Ho|No]; [left; exact Ho|]. right. right. exact (G_new a Ha Hg No).
      + right. right. split; [| exact HZ]. destruct (v (wz a)) eqn:E; [| reflexivity]. exfalso.
        assert (NI : ~ in_image LPA a) by (destruct HZ as [_ NI]; exact NI).
        apply (G_pres a Ha NI); [rewrite E; discriminate| exact VN].
    - intros a Ha Ho NO'. exact (F6 a Ha (G_mono a Ho) NO').
    - intros a Ha [].
  Qed.
End Frame.

(* [comment removed for export] *)
Section Frame0.
Context {Clg : Ceiling}.
  Variables (O Og : Z -> Prop) (hi win : Z) (v vg : mem).
  Let window (a : Z) : Prop := hi - win <= a < hi.
  Hypothesis G_mono : forall a, O a -> Og a.
  Hypothesis G_new : forall a, 0 <= a < 2^64 -> Og a -> ~ O a -> v (wz a) = None /\ heap_zone LPA a.
  Hypothesis G_agree : forall a, 0 <= a < 2^64 -> ~ Og a -> ~ window a -> vg (wz a) = v (wz a).
  Hypothesis G_pres : forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v (wz a) <> None -> vg (wz a) <> None.
  Hypothesis G_map : mapped vg (hi - win) win.

  (* [comment removed for export] *)
End Frame0.
End APopG4.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section GrowLe.
  Variables (A0 A1 : hull) (W : list (Z * Z)).
  Hypothesis LE : hull_le A0 A1.
  Hypothesis NEW : forall x, in_hullb A1 x = true -> in_hullb A0 x = false -> ~ outside W x.

  #[using="LE"] Lemma hidc_grow_le : forall a, hidc A1 a = true -> hidc A0 a = true.
  Proof.
    intros a H. unfold hidc in *. apply negb_true_iff in H. apply negb_true_iff.
    destruct (in_hullb A0 (bv_unsigned a)) eqn:E; [| reflexivity]. exfalso. rewrite (in_hullb_mono A0 A1 _ LE E) in H. discriminate.
  Qed.

  Variables (full m0' mz : word -> option byte).
  Hypothesis CLEAN : forall a, hidc A0 a = true -> m0' a = None.
  Hypothesis MZ : forall a, outside W (bv_unsigned a) -> mz a = munrestrict (hidc A0) full m0' a.

  #[using="MZ CLEAN full NEW LE A0"] Lemma restrict_grow_munch_le : munch W m0' (mrestrict (hidc A1) mz).
  Proof.
    intros x Hout. unfold mrestrict. destruct (hidc A1 x) eqn:V1.
    - symmetry. apply CLEAN. apply hidc_grow_le. exact V1.
    - rewrite (MZ x Hout). unfold munrestrict. destruct (hidc A0 x) eqn:V0; [| reflexivity].
      exfalso. apply (NEW (bv_unsigned x)); [| | exact Hout]; unfold hidc in *.
      + apply negb_false_iff in V1. exact V1.
      + apply negb_true_iff in V0. exact V0.
  Qed.

  Hypothesis PRESV : forall a, hidc A0 a = false -> m0' a <> None -> mz a <> None.

  #[using="PRESV CLEAN LE A0"] Lemma restrict_grow_wmono_le : forall segs, wmono segs m0' (mrestrict (hidc A1) mz).
  Proof.
    intros segs x Hx. unfold wview in *. unfold mrestrict.
    destruct (m0' x) as [b|] eqn:M0.
    - assert (V0 : hidc A0 x = false) by (destruct (hidc A0 x) eqn:V0; [rewrite (CLEAN x V0) in M0; discriminate| reflexivity]).
      assert (V1 : hidc A1 x = false) by (destruct (hidc A1 x) eqn:V1; [pose proof (hidc_grow_le x V1); congruence| reflexivity]).
      rewrite V1. destruct (mz x) as [b'|] eqn:MZx; [discriminate|]. exfalso. apply (PRESV x V0); congruence.
    - destruct (hidc A1 x); [exact Hx|]. destruct (mz x); [discriminate| exact Hx].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End GrowLe.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HullCases.
Context {Clg : Ceiling}.
  Variables (A : AState) (c ums fam nc : Z).
  Hypothesis W : WF A.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis UMS : 0 <= ums /\ ums mod kUserMapSize = 0 /\ rg_mapped_user (a_reg A c) + ums < rg_allocated_user (a_reg A c) + 9 * class_size c + kUserMapSize /\
                   rg_allocated_user (a_reg A c) <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.   (* [comment removed for export] *)
  Hypothesis FAM : 0 <= fam /\ fam mod kFreeArrayMapSize = 0 /\
                   rg_mapped_fa (a_reg A c) + fam <= 4 * (rg_allocated_user (a_reg A c) / class_size c) + kFreeArrayMapSize /\ rg_mapped_fa (a_reg A c) + fam <= kFreeArraySize.
  Local Notation Ag := (popg A c ums fam nc).
  Local Notation sb := (a_sb A).
  Local Notation rb := (region_beg (a_sb A) c).
  Local Notation fa := (region_beg (a_sb A) c + kFreeArrayOffset).
  Local Notation mu := (rg_mapped_user (a_reg A c)).
  Local Notation mfa := (rg_mapped_fa (a_reg A c)).

  #[using="FAM UMS CR W Clg"] Lemma hc_align : rb mod 64 = 0 /\ fa mod 64 = 0 /\ mu mod 64 = 0 /\ mfa mod 64 = 0 /\ ums mod 64 = 0 /\ fam mod 64 = 0 /\ 0 <= mu /\ 0 <= mfa.
  Proof.
    (first [ pose proof ((wfR A W)) as dR_1; dand3 dR_1 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_2; dand7 dR_2 as A1 A2 A3 A4 A5 A6 _ | destruct (WR c CR) as (A1 & A2 & A3 & A4 & A5 & A6 & _) ]).
    pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB. destruct RB as (_ & _ & _ & _ & _ & _ & _ & _ & R9 & _).
    assert (RB64 : rb mod 64 = 0) by (apply (mod0_down _ 0x10000 64); [exists 1024; reflexivity| exact R9]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
    - exact RB64.
    - rewrite Zplus_mod, RB64. replace (kFreeArrayOffset mod 64) with 0 by reflexivity. reflexivity.
    - apply (mod0_down _ kUserMapSize 64); [exists 4096; reflexivity| exact A3].
    - apply (mod0_down _ kFreeArrayMapSize 64); [exists 4096; reflexivity| exact A6].
    - apply (mod0_down _ kUserMapSize 64); [exists 4096; reflexivity| exact (proj1 (proj2 UMS))].
    - apply (mod0_down _ kFreeArrayMapSize 64); [exists 4096; reflexivity| exact (proj1 (proj2 FAM))].
    - lia.
    - lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="FAM UMS CR W Clg"] Lemma class_ivs_new : forall lo hi, In (lo, hi) (hull_of (class_regions_ sb (a_reg Ag c) c)) ->
    (lo = rb /\ hi = rb + (mu + ums) /\ mu + ums <> 0) \/ (lo = sh rb /\ hi = sh rb + (mu + ums) / 8 /\ mu + ums <> 0) \/
    (lo = fa /\ hi = fa + (mfa + fam) /\ mfa + fam <> 0) \/ (lo = sh fa /\ hi = sh fa + (mfa + fam) / 8 /\ mfa + fam <> 0).
  Proof.
    intros lo hi Hin. (first [ pose proof (hc_align) as dR_4; dand8 dR_4 as M1 M2 M3 M4 M5 M6 P1 P2 | pose proof hc_align as (M1 & M2 & M3 & M4 & M5 & M6 & P1 & P2) ]). rewrite popg_reg_c in Hin.
    unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & E & Hin). cbn [fst snd] in E.
    injection E as <- <-. apply class_regions_inv in Hin. cbv zeta in Hin. cbn [grow rg_mapped_user rg_mapped_fa] in Hin.
    assert (M3' : (mu + ums) mod 64 = 0) by (rewrite Zplus_mod, M3, M5; reflexivity).
    assert (M4' : (mfa + fam) mod 64 = 0) by (rewrite Zplus_mod, M4, M6; reflexivity).
    destruct Hin as [[E NZ]|[[E NZ]|[[E NZ]|[E NZ]]]].
    - injection E as -> ->. left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
    - rewrite (shadow_region_aligned _ _ M1 M3' ltac:(lia)) in E. injection E as -> ->. right; left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
    - injection E as -> ->. right; right; left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
    - unfold free_array_beg in E |- *. rewrite (shadow_region_aligned _ _ M2 M4' ltac:(lia)) in E. injection E as -> ->. right; right; right. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
  Qed.
  (* [comment removed for export] *)
  #[using="FAM UMS CR W fam ums"] Lemma old_has : (mu <> 0 -> In (rb, rb + mu) (pa_hull A) /\ In (sh rb, sh rb + mu / 8) (pa_hull A)) /\
                  (mfa <> 0 -> In (fa, fa + mfa) (pa_hull A) /\ In (sh fa, sh fa + mfa / 8) (pa_hull A)).
  Proof.
    (first [ pose proof (hc_align) as dR_5; dand8 dR_5 as M1 M2 M3 M4 _ _ P1 P2 | pose proof hc_align as (M1 & M2 & M3 & M4 & _ & _ & P1 & P2) ]).
    assert (IN : forall r, In r (class_regions_ sb (a_reg A c) c) -> In (fst r, fst r + snd r) (pa_hull A)).
    { intros r Hr. unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists r. split; [reflexivity|].
      exact (class_in_aregions A r c ltac:(lia) Hr). }
    unfold class_regions_ in IN. cbv zeta in IN. unfold free_array_beg in IN. split; intros NZ.
    - rewrite (proj2 (Z.eqb_neq mu 0) NZ) in IN. split.
      + apply (IN (rb, mu)). apply in_or_app. left. left. reflexivity.
      + pose proof (IN (shadow_region rb mu) ltac:(apply in_or_app; left; right; left; reflexivity)) as X. rewrite (shadow_region_aligned _ _ M1 M3 ltac:(lia)) in X. exact X.
    - rewrite (proj2 (Z.eqb_neq mfa 0) NZ) in IN. split.
      + apply (IN (fa, mfa)). apply in_or_app. right. left. reflexivity.
      + pose proof (IN (shadow_region fa mfa) ltac:(apply in_or_app; right; right; left; reflexivity)) as X.
        rewrite (shadow_region_aligned _ _ M2 M4 ltac:(lia)) in X. exact X.
  Qed.

  #[using="FAM UMS CR W"] Theorem pop_hull_cases : forall x, in_hullb (pa_hull Ag) x = true ->
    in_hullb (pa_hull A) x = true \/ (rb + mu <= x < rb + mu + ums) \/ (sh (rb + mu) <= x < sh (rb + mu) + ums / 8) \/
    (fa + mfa <= x < fa + mfa + fam) \/ (sh (fa + mfa) <= x < sh (fa + mfa) + fam / 8).
  Proof.
    intros x H. (first [ pose proof (hc_align) as dR_6; dand8 dR_6 as M1 M2 M3 M4 M5 M6 P1 P2 | pose proof hc_align as (M1 & M2 & M3 & M4 & M5 & M6 & P1 & P2) ]).
    assert (M1' : rb mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M1]).
    assert (M2' : fa mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M2]).
    assert (M3' : mu mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M3]).
    assert (M4' : mfa mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M4]).
    assert (M5' : ums mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M5]).
    assert (M6' : fam mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M6]).
    pose proof (sh_add rb mu M1' M3') as E1. pose proof (sh_add fa mfa M2' M4') as E2.
    assert (D1 : (mu + ums) / 8 = mu / 8 + ums / 8).
    { pose proof (Z_div_mod_eq_full mu 8). pose proof (Z_div_mod_eq_full ums 8). rewrite M3' in *. rewrite M5' in *.
      replace (mu + ums) with ((mu / 8 + ums / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    assert (D2 : (mfa + fam) / 8 = mfa / 8 + fam / 8).
    { pose proof (Z_div_mod_eq_full mfa 8). pose proof (Z_div_mod_eq_full fam 8). rewrite M4' in *. rewrite M6' in *.
      replace (mfa + fam) with ((mfa / 8 + fam / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    apply in_hullb_true in H as (lo & hi & Hin & Rg).
    unfold pa_hull, ahull_of, ahull_of_, aregions_ in Hin. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh] in Hin.
    rewrite !hull_of_app, !in_app_iff in Hin.
    assert (OLD_or : In (lo, hi) (pa_hull A) \/ In (lo, hi) (hull_of (class_regions_ sb (a_reg Ag c) c))).
    { unfold pa_hull, ahull_of, ahull_of_, aregions_. rewrite !hull_of_app, !in_app_iff. change (p_sb (a_pl A)) with sb in *.
      destruct Hin as [Hin|[[Hin|[Hin|Hin]]|[Hin|Hin]]]; try tauto.
      (* [comment removed for export] *)
      unfold hull_of in Hin. apply in_map_iff in Hin as (r & E & Hr). apply classes_regions_inv in Hr as (c' & Hc' & Hr).
      unfold reg_upd in Hr. destruct (Z.eqb_spec c' c) as [->|NE].
      - right. rewrite popg_reg_c. unfold hull_of. apply in_map_iff. exists r. split; [exact E| exact Hr].
      - left. right. left. right. left. unfold hull_of. apply in_map_iff. exists r. split; [exact E|].
        replace c' with (Z.of_nat (Z.to_nat c')) in Hr by lia. apply (classes_regions_in _ _ 31 r (Z.to_nat c')); [lia| lia| exact Hr]. }
    destruct OLD_or as [OLD|NEWc]; [left; apply (in_hullb_intro _ _ _ _ OLD); exact Rg|].
    pose proof old_has as [OU OF].
    destruct (class_ivs_new lo hi NEWc) as [(-> & -> & NZ)|[(-> & -> & NZ)|[(-> & -> & NZ)|(-> & -> & NZ)]]].
    - destruct (Z_lt_le_dec x (rb + mu)) as [L|L]; [| right; left; lia]. left. destruct (OU ltac:(lia)) as [I _]. apply (in_hullb_intro _ _ _ _ I). lia.
    - destruct (Z_lt_le_dec x (sh rb + mu / 8)) as [L|L]; [| right; right; left; rewrite E1; lia]. left.
      assert (NZ' : mu <> 0) by (intros E0; rewrite E0 in L; change (0 / 8) with 0 in L; lia).
      destruct (OU NZ') as [_ I]. apply (in_hullb_intro _ _ _ _ I). lia.
    - destruct (Z_lt_le_dec x (fa + mfa)) as [L|L]; [| right; right; right; left; lia]. left. destruct (OF ltac:(lia)) as [I _]. apply (in_hullb_intro _ _ _ _ I). lia.
    - destruct (Z_lt_le_dec x (sh fa + mfa / 8)) as [L|L]; [| right; right; right; right; rewrite E2; lia]. left.
      assert (NZ' : mfa <> 0) by (intros E0; rewrite E0 in L; change (0 / 8) with 0 in L; lia).
      destruct (OF NZ') as [_ I]. apply (in_hullb_intro _ _ _ _ I). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR"] Lemma pop_vis_user : 0 < mu + ums -> forall x, rb <= x < rb + (mu + ums) -> in_hullb (pa_hull Ag) x = true.
  Proof.
    intros P x Hx. apply (in_hullb_intro _ _ rb (rb + (mu + ums))); [| exact Hx].
    unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists (rb, mu + ums). split; [reflexivity|].
    apply (class_in_aregions Ag _ c ltac:(lia)). rewrite popg_reg_c. unfold class_regions_. cbv zeta. cbn [grow rg_mapped_user]. change (a_sb Ag) with sb.
    destruct (Z.eqb_spec (mu + ums) 0); [lia|]. apply in_or_app. left. left. reflexivity.
  Qed.
  #[using="FAM UMS CR W"] Lemma pop_vis_ush : 0 < mu + ums -> forall x, sh rb <= x < sh rb + (mu + ums) / 8 -> in_hullb (pa_hull Ag) x = true.
  Proof.
    intros P x Hx. (first [ pose proof (hc_align) as dR_7; dand8 dR_7 as M1 M2 M3 M4 M5 M6 P1 P2 | pose proof hc_align as (M1 & M2 & M3 & M4 & M5 & M6 & P1 & P2) ]).
    assert (M3' : (mu + ums) mod 64 = 0) by (rewrite Zplus_mod, M3, M5; reflexivity).
    apply (in_hullb_intro _ _ (sh rb) (sh rb + (mu + ums) / 8)); [| exact Hx].
    unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists (shadow_region rb (mu + ums)).
    split; [rewrite (shadow_region_aligned _ _ M1 M3' P); reflexivity|].
    apply (class_in_aregions Ag _ c ltac:(lia)). rewrite popg_reg_c. unfold class_regions_. cbv zeta. cbn [grow rg_mapped_user]. change (a_sb Ag) with sb.
    destruct (Z.eqb_spec (mu + ums) 0); [lia|]. apply in_or_app. left. right. left. reflexivity.
  Qed.
  #[using="CR"] Lemma pop_vis_fa : 0 < mfa + fam -> forall x, fa <= x < fa + (mfa + fam) -> in_hullb (pa_hull Ag) x = true.
  Proof.
    intros P x Hx. apply (in_hullb_intro _ _ fa (fa + (mfa + fam))); [| exact Hx].
    unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists (fa, mfa + fam). split; [reflexivity|].
    apply (class_in_aregions Ag _ c ltac:(lia)). rewrite popg_reg_c. unfold class_regions_. cbv zeta. cbn [grow rg_mapped_user rg_mapped_fa]. unfold free_array_beg. change (a_sb Ag) with sb.
    destruct (Z.eqb_spec (mfa + fam) 0); [lia|]. apply in_or_app. right. left. reflexivity.
  Qed.
  #[using="FAM UMS CR W"] Lemma pop_vis_fsh : 0 < mfa + fam -> forall x, sh fa <= x < sh fa + (mfa + fam) / 8 -> in_hullb (pa_hull Ag) x = true.
  Proof.
    intros P x Hx. (first [ pose proof (hc_align) as dR_8; dand8 dR_8 as M1 M2 M3 M4 M5 M6 P1 P2 | pose proof hc_align as (M1 & M2 & M3 & M4 & M5 & M6 & P1 & P2) ]).
    assert (M4' : (mfa + fam) mod 64 = 0) by (rewrite Zplus_mod, M4, M6; reflexivity).
    apply (in_hullb_intro _ _ (sh fa) (sh fa + (mfa + fam) / 8)); [| exact Hx].
    unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists (shadow_region fa (mfa + fam)).
    split; [rewrite (shadow_region_aligned _ _ M2 M4' P); reflexivity|].
    apply (class_in_aregions Ag _ c ltac:(lia)). rewrite popg_reg_c. unfold class_regions_. cbv zeta. cbn [grow rg_mapped_user rg_mapped_fa]. unfold free_array_beg. change (a_sb Ag) with sb.
    destruct (Z.eqb_spec (mfa + fam) 0); [lia|]. apply in_or_app. right. right. left. reflexivity.
  Qed.
End HullCases.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Owned.
Context {Clg : Ceiling}.
  Variables (A : AState).
  Hypothesis W : WF A.
  Local Notation sb := (a_sb A).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="W"] Lemma ri_owned' : forall a, a_ri A <= a < a_ri A + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((sb_facts A W)) as dR_13; dand5 dR_13 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). assert (RIE : a_ri A = sb + kSpaceSize) by reflexivity.
    apply (owned_rt A a (a_ri A) 4096); [apply rt_fixed_in; cbn; tauto| exact Ha| |].
    - intros LU. destruct (live_user_zone A a W LU) as [[_ SB]|(i & s & Hs & RG)]; [kung_all; lia|].
      pose proof (bm_nth_sec A i s Hs) as Es. pose proof (bm_nth_fixed A) as (E0 & _).
      pose proof (bm_sep A (15 + i) 0 _ _ _ _ W Es E0 ltac:(lia)) as D. pose proof (primary_in_b6 A a W ltac:(kung_all; lia)) as B6.
      unfold a_b6 in *. kung_all. lia.
    - apply b6_no_live_frame; [exact W|]. apply primary_in_b6; [exact W|]. kung_all. lia.
  Qed.
  #[using="W"] Lemma thr_owned' : forall a, p_thr (a_pl A) <= a < p_thr (a_pl A) + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_14; dand6 dR_14 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
    apply (owned_rt A a (p_thr (a_pl A)) 4096); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 4); [exact W| lia| exact E4| exact Ha]
      | eapply (fixed_bm_no_live_frame A 4); [exact W| lia| lia| exact E4| exact Ha]].
  Qed.
  Lemma oom_owned : pa_owned A 0x137620.
  Proof. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. lia. Qed.

  (* [comment removed for export] *)
  #[using="W"] Lemma prim_shadow_ghost : forall z, sh sb <= z < sh sb + kSpaceSize / 8 -> ghost_hs_ (a_pl A) z.
  Proof.
    intros z Hz. (first [ pose proof ((sb_facts A W)) as dR_15; dand5 dR_15 as _ SBM HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBM & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_16; dand15 dR_16 as E0 E1 _ _ E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    unfold a_sb, a_b6, a_pa, a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_itab, a_m64k in *.
    (first [ pose proof ((place_facts A W)) as dR_17; dand14 dR_17 as Pthr Pctx Pn0 Pf0 Pfs Pitab Pm64k Pgvec Pdvec Pm11 Pdtls Ppa Psp0 _ | pose proof (place_facts A W) as (Pthr & Pctx & Pn0 & Pf0 & Pfs & Pitab & Pm64k & Pgvec & Pdvec & Pm11 & Pdtls & Ppa & Psp0 & _) ]).
    cbv zeta in Pthr, Pctx, Pn0, Pf0, Pfs, Pitab, Pm64k, Pgvec, Pdvec, Pm11, Pdtls, Ppa, Psp0.
    assert (SB8 : sb mod 8 = 0) by (unfold a_sb; apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact SBM]).
    pose proof (Z_div_mod_eq_full (p_sb (a_pl A)) 8) as DQ. unfold a_sb in SB8. rewrite SB8 in DQ.
    (* [comment removed for export] *)
    assert (APT : forall b k, 0 <= b -> 0 <= k -> (b + k <= p_sb (a_pl A) \/ p_sb (a_pl A) + kSpaceSize <= b) ->
              ~ (kShadowOffset + b / 8 <= z < kShadowOffset + (b + k) / 8)).
    { intros b k Hb Hk D X. unfold sh in Hz. unfold a_sb in Hz. kung_all. change (2 ^ 37 / 8) with 17179869184 in Hz.
      destruct D as [D|D].
      - assert ((b + k) / 8 <= p_sb (a_pl A) / 8) by (apply Z.div_le_mono; lia). lia.
      - assert ((p_sb (a_pl A) + 137438953472) / 8 <= b / 8) by (apply Z.div_le_mono; lia).
        assert (EQ : (p_sb (a_pl A) + 137438953472) / 8 = p_sb (a_pl A) / 8 + 17179869184).
        { rewrite DQ at 1. replace (8 * (p_sb (a_pl A) / 8) + 0 + 137438953472) with ((p_sb (a_pl A) / 8 + 17179869184) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
        rewrite EQ in H. lia. }
    assert (APL : forall i p k k', nth_error (big_maps A) i = Some (p, k) -> i <> 0%nat -> app_rangeA AL_pasan p k /\ p + k <= alloc_ceiling /\ p mod 4096 = 0 -> 0 <= k' <= k ->
              ~ (kShadowOffset + p / 8 <= z < kShadowOffset + (p + k') / 8)).
    { (intros i p k k' Hi Hi0; (first [ intro dR_24; dand3 dR_24 as X1 _ _ | intros (X1 & _ & _) ]); intros Hk). apply app_facts in X1. apply APT; [lia| lia|].
      pose proof (bm_sep A i 0 _ _ _ _ W Hi E0 Hi0) as D. unfold a_sb. clear - D Hk HB6 RSB SCE. kung_all. lia. }
    split.
    - unfold in_shadow_maps. right. pose proof (sh_high_range (p_sb (a_pl A)) ltac:(unfold a_sb in *; kung_all; lia)) as [H1 _].
      unfold sh, a_sb in *. kung_all. change (2 ^ 37 / 8) with 17179869184 in Hz. lia.
    - ((first [ intro dR_25; dex2 dR_25 as b nn; destruct dR_25 as [Hin Hzz] | intro dR_25; dand4 dR_25 as b nn Hin Hzz | intros (b & nn & Hin & Hzz) ])). unfold VIS0 in Hin. cbn [In] in Hin.
      destruct Hin as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]]]]]]]]];
        [ injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E11 ltac:(discriminate) Pgvec _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E12 ltac:(discriminate) Pdvec _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E8 ltac:(discriminate) Pf0 _ Hzz); clear; unfold kStackStoreBlockBytes; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E7 ltac:(discriminate) Pn0 _ Hzz); clear; unfold kDepotNodesBlock; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E6 ltac:(discriminate) Pfs _ Hzz); clear; unfold kFakeStackBytes; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E4 ltac:(discriminate) Pthr _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E13 ltac:(discriminate) Pm11 _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E5 ltac:(discriminate) Pctx _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E14 ltac:(discriminate) Pdtls _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APT _ _ _ _ _ Hzz); unfold p_ri; clear - HB6 RSB; unfold a_sb in *; kung_all; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E9 ltac:(discriminate) Pitab _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E10 ltac:(discriminate) Pm64k _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APT _ _ _ _ _ Hzz); clear - HB6 RSB; unfold a_sb in *; kung_all; lia
        | unfold stack_band_iv in Q; injection Q as Q1 Q2; subst b nn; refine (APT _ _ _ _ _ Hzz); clear - HB6 RSB SCE CE; unfold a_sb in *; kung_all; lia ].
  Qed.
  (* [comment removed for export] *)
  #[using="W Clg"] Lemma prim_zone_free : forall c a, 1 <= c <= 30 ->
    region_beg sb c + rg_allocated_user (a_reg A c) <= a < region_beg sb c + kRegionSize -> ~ in_live_user A a /\ ~ in_live_frame A a.
  Proof.
    intros c a Hc Ha. pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB. split.
    - ((first [ intro dR_26; dex2 dR_26 as p li; destruct dR_26 as [Hl Hp] | intro dR_26; dand4 dR_26 as p li Hl Hp | intros (p & li & Hl & Hp) ])). pose proof (live_user_where A p li a W Hl Hp) as X. destruct (li_chunk li) as [[c' k']|s'].
      + (first [ dand9 X as Hc' Hk' _ _ _ R1 R2 R3 _ | destruct X as (Hc' & Hk' & _ & _ & _ & R1 & R2 & R3 & _) ]). pose proof (region_piece_bounds A c' W Hc') as RB'. cbv zeta in RB'.
        destruct (Z.eq_dec c' c) as [->|NE]; [lia|]. destruct (regions_disjoint sb c' c NE ltac:(lia) ltac:(lia)); kung_all; lia.
      + (first [ dand5 X as Hin _ _ _ R1 | destruct X as (Hin & _ & _ & _ & R1) ]). destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_fixed A) as (E0 & _).
        pose proof (bm_sep A (15 + j) 0 _ _ _ _ W (bm_nth_sec A j _ Hj) E0 ltac:(lia)) as D. pose proof (primary_in_b6 A a W ltac:(kung_all; lia)). unfold a_b6 in *.
        pose proof (sec_chunk_bounds A s' W Hin) as (SN & _). pose proof (map_size_ge (cs_n s') ltac:(clear - SN; unfold kMaxPrimaryUser in SN; lia)). kung_all. lia.
    - apply b6_no_live_frame; [exact W|]. apply primary_in_b6; [exact W|]. kung_all. lia.
  Qed.
  #[using="W"] Lemma prim_shadow_owned : forall z, sh sb <= z < sh sb + kSpaceSize / 8 -> pa_owned A z.
  Proof. intros z Hz. left. right. right. exact (prim_shadow_ghost z Hz). Qed.
End Owned.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OwnedG.
Context {Clg : Ceiling}.
  Variables (A : AState) (c ums fam nc : Z).
  Hypothesis W : WF A.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis UMS : 0 <= ums /\ ums mod kUserMapSize = 0 /\ rg_mapped_user (a_reg A c) + ums < rg_allocated_user (a_reg A c) + 9 * class_size c + kUserMapSize /\
                   rg_allocated_user (a_reg A c) <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.   (* [comment removed for export] *)
  Hypothesis FAM : 0 <= fam /\ fam mod kFreeArrayMapSize = 0 /\
                   rg_mapped_fa (a_reg A c) + fam <= 4 * (rg_allocated_user (a_reg A c) / class_size c) + kFreeArrayMapSize /\ rg_mapped_fa (a_reg A c) + fam <= kFreeArraySize.
  Hypothesis NC : 0 <= nc /\ rg_allocated_user (a_reg A c) + nc * class_size c <= rg_mapped_user (a_reg A c) + ums /\
                  4 * (Z.of_nat (length (rg_free (a_reg A c))) + nc) <= rg_mapped_fa (a_reg A c) + fam.
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) c).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) c + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A c)))).
  #[warnings="-notation-for-abbreviation"] Local Notation Ag := (popg A c ums fam nc).

  Let RB := region_piece_bounds A c W CR.

  #[using="RB UMS CR W"] Lemma newU_owned : forall a, rb + mu <= a < rb + mu + ums -> pa_owned Ag a.
  Proof.
    intros a Ha. pose proof RB as X. cbv zeta in X. pose proof (proj1 (rt_class_in Ag c CR)) as RIN. rewrite popg_reg_c in RIN. cbn [grow rg_mapped_user] in RIN.
    change (a_sb Ag) with sb in RIN.
    pose proof (proj1 (wf_au_cap A c W CR)) as AUC'. pose proof (class_size_range c CR) as CSR'. destruct (prim_zone_free A W c a CR ltac:(clear - Ha X UMS AUC' CSR'; kung_all; lia)) as [NU NF].
    exact (owned_rt Ag a rb (mu + ums) RIN ltac:(clear - Ha X; lia) NU NF).
  Qed.
  #[using="RB NC FAM CR W"] Lemma faz_owned : forall a, fa + 4 * nf <= a < fa + 4 * (nf + nc) -> pa_owned Ag a.
  Proof.
    intros a Ha. pose proof RB as X. cbv zeta in X. pose proof (proj2 (rt_class_in Ag c CR)) as RIN. rewrite popg_reg_c in RIN. cbn [grow rg_mapped_fa] in RIN.
    change (a_sb Ag) with sb in RIN.
    destruct (prim_zone_free A W c a CR ltac:(clear - Ha X FAM NC; kung_all; lia)) as [NU NF].
    exact (owned_rt Ag a fa (mfa + fam) RIN ltac:(clear - Ha X NC; lia) NU NF).
  Qed.
  #[using="RB FAM UMS CR W fam"] Lemma newUsh_ownedA : forall z, sh (rb + mu) <= z < sh (rb + mu) + ums / 8 -> pa_owned A z.
  Proof.
    intros z Hz. pose proof RB as X. cbv zeta in X. apply (prim_shadow_owned A W).
    unfold sh in *. unfold region_beg in *.
    assert (L1 : sb / 8 <= (sb + c * kRegionSize + mu) / 8) by (apply Z.div_le_mono; lia).
    assert (L2a : (sb + c * kRegionSize + mu) / 8 + ums / 8 <= (sb + c * kRegionSize + mu + ums) / 8).
    { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (sb + c * kRegionSize + mu) 8). pose proof (Z.mul_div_le ums 8). lia. }
    pose proof (proj1 (wf_au_cap A c W CR)) as AUC'. pose proof (class_size_range c CR) as CSR'. assert (L2b : (sb + c * kRegionSize + mu + ums) / 8 <= (sb + kSpaceSize) / 8) by (apply Z.div_le_mono; [lia| clear - X UMS CR AUC' CSR'; kung_all; lia]).
    assert (E3 : (sb + kSpaceSize) / 8 = sb / 8 + kSpaceSize / 8).
    { (first [ pose proof ((sb_facts A W)) as dR_20; dand3 dR_20 as _ SBM _ | pose proof (sb_facts A W) as (_ & SBM & _) ]). assert (SB8 : sb mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact SBM]).
      pose proof (Z_div_mod_eq_full sb 8) as DQ. rewrite SB8, Z.add_0_r in DQ. rewrite DQ at 1. unfold kSpaceSize.
      replace (8 * (sb / 8) + 2 ^ 37) with ((sb / 8 + 2^34) * 8) by lia. rewrite Z.div_mul by lia. change (2^37 / 8) with (2^34). reflexivity. }
    lia.
  Qed.
  #[using="RB FAM UMS CR W"] Lemma newUsh_owned : forall z, sh (rb + mu) <= z < sh (rb + mu) + ums / 8 -> pa_owned Ag z.
  Proof. intros z Hz. apply (popg_owned_mono A c ums fam nc UMS FAM). exact (newUsh_ownedA z Hz). Qed.
  #[using="RB FAM UMS CR W ums"] Lemma newFsh_ownedA : forall z, sh (fa + mfa) <= z < sh (fa + mfa) + fam / 8 -> pa_owned A z.
  Proof.
    intros z Hz. pose proof RB as X. cbv zeta in X. apply (prim_shadow_owned A W).
    unfold sh in *. unfold region_beg in *.
    assert (L1 : sb / 8 <= (sb + c * kRegionSize + kFreeArrayOffset + mfa) / 8) by (apply Z.div_le_mono; [lia| clear - X CR; kung_all; lia]).
    assert (L2a : (sb + c * kRegionSize + kFreeArrayOffset + mfa) / 8 + fam / 8 <= (sb + c * kRegionSize + kFreeArrayOffset + mfa + fam) / 8).
    { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (sb + c * kRegionSize + kFreeArrayOffset + mfa) 8). pose proof (Z.mul_div_le fam 8). lia. }
    assert (L2b : (sb + c * kRegionSize + kFreeArrayOffset + mfa + fam) / 8 <= (sb + kSpaceSize) / 8) by (apply Z.div_le_mono; [lia| clear - X FAM CR; kung_all; lia]).
    assert (E3 : (sb + kSpaceSize) / 8 = sb / 8 + kSpaceSize / 8).
    { (first [ pose proof ((sb_facts A W)) as dR_21; dand3 dR_21 as _ SBM _ | pose proof (sb_facts A W) as (_ & SBM & _) ]). assert (SB8 : sb mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact SBM]).
      pose proof (Z_div_mod_eq_full sb 8) as DQ. rewrite SB8, Z.add_0_r in DQ. rewrite DQ at 1. unfold kSpaceSize.
      replace (8 * (sb / 8) + 2 ^ 37) with ((sb / 8 + 2^34) * 8) by lia. rewrite Z.div_mul by lia. change (2^37 / 8) with (2^34). reflexivity. }
    lia.
  Qed.
  #[using="RB FAM UMS CR W"] Lemma newFsh_owned : forall z, sh (fa + mfa) <= z < sh (fa + mfa) + fam / 8 -> pa_owned Ag z.
  Proof. intros z Hz. apply (popg_owned_mono A c ums fam nc UMS FAM). exact (newFsh_ownedA z Hz). Qed.
  #[using="FAM UMS CR W"] Lemma Rpage_owned : forall a, R <= a < R + 128 -> pa_owned Ag a.
  Proof. intros a Ha. apply (popg_owned_mono A c ums fam nc UMS FAM). apply (ri_owned' A W). clear - Ha CR. lia. Qed.
  #[using="FAM UMS W"] Lemma thrpage_owned : forall a, thr + 208 <= a < thr + 3168 -> pa_owned Ag a.
  Proof. intros a Ha. apply (popg_owned_mono A c ums fam nc UMS FAM). apply (thr_owned' A W). change (p_thr (a_pl Ag)) with thr. clear - Ha. lia. Qed.
  #[using="FAM UMS"] Lemma oom_ownedg : pa_owned Ag 0x137620.
  Proof. apply (popg_owned_mono A c ums fam nc UMS FAM). exact (oom_owned A). Qed.

  #[using="RB NC FAM UMS CR W"] Theorem W_owned : forall slo shi a, ~ (slo <= a < shi) -> ~ pa_owned Ag a ->
    outside (pop_W slo shi thr E R fa nf nc rb mu ums mfa fam (a_cache_inited A)) a.
  Proof.
    intros slo shi a NW NO. unfold pop_W. cbn [outside app]. pose proof (proj1 NC) as N0.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; try exact NW; intros X; apply NO.
    - apply Rpage_owned. clear - X. lia.
    - apply Rpage_owned. clear - X. lia.
    - apply Rpage_owned. clear - X. lia.
    - apply Rpage_owned. clear - X. lia.
    - apply faz_owned. exact X.
    - apply thrpage_owned. clear - X. destruct (a_cache_inited A); lia.
    - apply thrpage_owned. clear - X CR. lia.
    - apply newU_owned. exact X.
    - apply newUsh_owned. exact X.
    - pose proof RB as Y. cbv zeta in Y. pose proof (proj2 (rt_class_in Ag c CR)) as RIN. rewrite popg_reg_c in RIN. cbn [grow rg_mapped_fa] in RIN.
      change (a_sb Ag) with sb in RIN.
      destruct (prim_zone_free A W c a CR ltac:(clear - X Y FAM; kung_all; lia)) as [NU NF].
      exact (owned_rt Ag a fa (mfa + fam) RIN ltac:(clear - X Y; lia) NU NF).
    - apply newFsh_owned. exact X.
    - replace a with 0x137620 by (clear - X; lia). exact oom_ownedg.
  Qed.
End OwnedG.
