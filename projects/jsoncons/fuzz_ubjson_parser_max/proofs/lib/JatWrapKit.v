(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct AsanPlanSoundSums HeapIface HeapIfaceA As0Tables
ArtMem ArtRuns ArtRunsMem JatCls JatFp JatCellEx JatCARSpec JatDepot JatUnwind ArtBridge JatAllocate3 JatInv JatInvMallocFp JatInvMalloc JatLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInvMallocFp."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1bool"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2or"; "3Z"]; ["4Model"; "0M"; "0MAPS0"; "0NOACC0"; "0RESV0"; "5BInv"; "5art_live"; "5in_ev_ranges"; "6apart"; "7aev"; "8art_ca_events"; "9art_cls"; "9art_cls_mfa'"; "9art_cls_needs_populate"; "9art_cls_new"; "9art_cls_ok"]; ["9cl_cache"; "9cl_free"; "9cl_mu"; ":art_kn_ok"; ":art_objs"; ":art_run"; ":rn_HI"; ";art_malloc_fp"; "<loaded_segments"; "0Sp"; "=In"; ">add"; ">le"; ">lt"; ">mul"; ">of_nat"]; ["0ab"; "0blk"; "0c"; "0cl"; "0km"; "0l2"; "0log"; "0model"; "0n"; "0o"; "0p"; "0qs"; "0ris"; "0rn"; "0rs"; "0rz"]; ["0spb"; "?bv"; "0t"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Kit.
Variable FSG : Type.
Section SE.
Local Abbreviation SEC_T_art_stack_vis := (forall rn (G : art_gs FSG) A lazy, art_run_ok rn -> art_lazy_ok FSG rn G A lazy ->
forall x : word, rn_HI rn <= U x -> mkH lazy A x = false) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_stack_vis) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_stack_vis) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_stack_vis) 2%nat 0%nat).
Variable lazy : ltac:(sec_ty2 constr:(SEC_T_art_stack_vis) 3%nat 0%nat).
Lemma art_stack_vis : ltac:(sec_stmt2 constr:(SEC_T_art_stack_vis) 4%nat 0%nat).
Proof using Type rn G A lazy.
intros ROK (LZ & _) x Hx.
destruct (mkH lazy A x) eqn:E; [|reflexivity]. exfalso.
unfold mkH in E. apply andb_prop in E as [E _]. specialize (LZ x E).
rok_open ROK. geo_open GEO. unfold art_lazy_zone in LZ. destruct LZ as [Z|[Z|[[Z|Z] _]]]; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_stack_wr := (forall rn (G : art_gs FSG) A lazy (M : word -> option byte) Sp scr, art_run_ok rn -> art_lazy_ok FSG rn G A lazy ->
rn_HI rn <= Sp - scr -> 0 <= scr -> Sp <= 2 ^ 47 ->
(forall d (m : nat), 0 <= d -> d + Z.of_nat m <= scr -> store_ok ASEGS M (Z_to_bv 64 (Sp - scr + d)) m = true) ->
wrA (mrestrict (mkH lazy A) M) (Sp - scr) scr) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 2%nat 0%nat).
Variable lazy : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 4%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 5%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_stack_wr) 6%nat 0%nat).
Lemma art_stack_wr : ltac:(sec_stmt2 constr:(SEC_T_art_stack_wr) 7%nat 0%nat).
Proof using Type rn G A lazy M Sp scr.
intros ROK LZ HHI Hscr HS W.
pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
apply (proj2 (art_wr_vis (mkH lazy A) M (Sp - scr) scr ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply (art_stack_vis rn G A lazy ROK LZ); lia))).
intros d k Hd Hk. apply W; assumption.
Qed.
End SE.
#[using="Type"] Lemma art_stack_readable : forall rn (G : art_gs FSG) A lazy (M : word -> option byte) Sp top, art_run_ok rn -> art_lazy_ok FSG rn G A lazy ->
rn_HI rn <= Sp -> top <= 2 ^ 47 + 4096 -> defined M Sp (top - Sp) -> readable8 (mrestrict (mkH lazy A) M) Sp top.
Proof.
intros rn G A lazy M Sp top ROK LZ HHI Htop D a Ha Ha8 Hm.
pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
destruct (art_rdn_defined 8 (mrestrict (mkH lazy A) M) a ltac:(lia) ltac:(cbn; lia)) as (bs & Rd & Lb).
{ intros x Hx. cbn in Hx. rewrite art_byte_vis by (apply (art_stack_vis rn G A lazy ROK LZ); lia).
pose proof (D (U x - Sp) ltac:(lia)) as Dx. replace (Sp + (U x - Sp)) with (U x) in Dx by lia. rewrite Z_to_bv_bv_unsigned in Dx. exact Dx. }
exists (Z_to_bv 64 (bytes_le_to_Z bs)).
pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B.
rewrite art_u_lit by (change (8 * Z.of_nat 8) with 64 in B; lia).
unfold cell. rewrite Rd. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|lia].
Qed.
#[using="Type"] Lemma art_live_of_binv : ltac2:(TCodec.tc2 tcn__JatWrapKit "RH'6'9'R1yR0%211%4211%611'?'Q5'I%:11%:244%<11'8y8%=11%311p0=1'@'E&Q8r:r9r8&Q6r5%211r7r6r4r3r2r1%>;=<;:7654321&Q3r;%231?8&Q:&F%11<%33M81'<&Q=z&4%13Q6Q6>%4231&:%13Q9Q9A%7261&Q<&Q;%1274%M1O%4221'>+QoonlP0%7251+`PQoooPP0%921>%5231&Q4%11Q9%J3QDO1&H%E3QJQJQ4%C3QKQKQ5%3421FCp051pSDQJ1%M2:1%N2A1%O2G1%Q02K1p0Q21pSFR01p0Q81p0Q<1pS@QL1pQ4QN1p2R41pS>R71pSLR:1p6R<1p4R=1pQ8R?1pQ:R@1pQ6RA1").
Proof.
intros MAPS0 RESV0 NOACC0 BASE BUDGET rn log A M model B KN p Hp.
destruct (bi_live _ _ _ _ _ _ _ _ _ _ _ B) as (LO & _). destruct (LO p Hp) as (P0 & P1 & _ & _ & P4 & P5 & P6).
unfold SHLO, SHHI in P5. split; [exact P0|]. split; [exact P1|]. split; [exact P4|]. split; [exact P5|].
intros o Ho. destruct (KN o Ho) as (q & Hq & Q1 & Q2). specialize (P6 q Hq). unfold apart. lia.
Qed.
End Kit.
Lemma art_ca_events_in_fp : ltac2:(TCodec.tc2 tcn__JatWrapKit "RJ'?'K'<&Q<+1r:%3221+N%5231%7231&Or;r3%3221'=&Q2r4%211&Q>+XPP0%2219%73E41'6%11G&Q0r5%211(7%11L%?3631'3&Mr>r6%3221(;%F3621&Lr7&Q;&Q?&5&Q1%115%32Q<1%511&Nr?%221:%:241%=2<1+`PPPP0%QA221p0A1p0I1&G&JrA%231JI%421Q2&Q7rDrCrBr@r=r<r9r8%9>876<5FQ543QJR021Q4p0;1p0A1p0QC1p0QL1p0R11pT8R;1pS8R;1pS4R=1pS<R>1pSNR?1pSBR@1pT0RA1pS2RB1pS:RC1pS6RD1pSHRE1pSJRF1pT2RG1pT6RH1pRDRI1").
Proof.
intros Sp t spb ris qs c km ab rz n rs l2 blk cl z Hc OK Emu Room (ev & Hev & Hz).
pose proof OK as (_ & _ & _ & _ & _ & _ & _ & (Hmfa0 & _) & _).
assert (RF : art_refill_fp (Sp - 2144 - 128 - 48) t spb ris qs c km z -> art_malloc_fp Sp t spb ris qs c km ab rz n rs l2 blk z).
{ intros F. right. unfold art_alloc3_fp. right. left. unfold art_ca_fp. right. left. exact F. }
apply RF. unfold art_refill_fp. unfold art_ca_events, art_refill_events in Hev.
destruct (cl_cache cl) eqn:Ec; [|destruct Hev]. destruct (art_cls_needs_populate c cl) eqn:NP; [|destruct Hev]. specialize (Room eq_refl eq_refl).
destruct Hev as [<-|Hev].
- cbn [art_ev_range fst snd] in Hz. do 5 right. left. lia.
- match type of Hev with In _ (if ?b then _ else _) => destruct b end; [destruct Hev|]. destruct Hev as [<-|[]].
cbn [art_ev_range fst snd] in Hz. do 6 right. left. lia.
Qed.
Lemma art_lift_grows : forall {fx : PropExec.FPState} A0 A1 (M0 M1 : word -> option byte) model0 model1 log0 log1,
bhist A0 M0 model0 log0 log1 A1 M1 model1 ->
mem_grows (mrestrict (bhid A0 model0) M0) (mrestrict (bhid A1 model1) M1) ->
(forall sfx, log1 = log0 ++ sfx -> forall x : word, in_ev_ranges sfx (U x) -> bhid A1 model1 x = false -> mrestrict (bhid A1 model1) M1 x <> None) ->
mem_grows M0 M1.
Proof.
intros fx A0 A1 M0 M1 model0 model1 log0 log1 (sfx & El & _ & B2 & B3 & _) GR DEF x Hx.
destruct (bhid A1 model1 x) eqn:E1.
- destruct (B2 x E1) as (_ & Eq). rewrite Eq. exact Hx.
- destruct (bhid A0 model0 x) eqn:E0.
+ pose proof (DEF sfx El x (B3 x E0 E1) E1) as D. unfold mrestrict in D. rewrite E1 in D. exact D.
+ pose proof (GR x) as Gx. unfold mrestrict in Gx. rewrite E0, E1 in Gx. exact (Gx Hx).
Qed.
