(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK HandoffLedgerK ArtRuns ArtBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__HandoffBInvK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlacement."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BackingAlgebra."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBInvK.BInvMain."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0B"; "0BL"; "0BUDGET"; "1app"; "1bool"; "1false"; "1list"; "1nil"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"]; ["3Z"; "0E"; "0FULL"; "0KMAX"; "0LENMAX"; "0LL"; "4segments_reserved"; "5Model"; "5m_vmmaps"; "5sp_window_hi"; "5sp_window_lo"; "5vm_limit"; "5vm_maps"; "5vm_noaccess"; "6BInv"; "6bridge_static"]; ["6in_shadow_rw"; "7aev"; "8A_bytes"; "8MInv"; "8eager_used"; "8page_allowedb"; "9gw_sizes"; ":a_maps"; ":am_base"; ":am_len"; ":amap"; ":e_sp0"; ":img_hi"; ";amap_den"; ";in_ivs"; ";sum_sizes"]; [";uE"; "<ELit"; "<expr"; "=covered"; ">A0_of"; ">BASE_of"; ">RES_of"; "0SEGS"; "?In"; "@add"; "@le"; "@lt"; "@pow"; "@sub"; "0b"; "0cs"]; ["0hi"; "0l"; "0lo"; "0m"; "0model"; "0p"; "0s"; "Abv"; "Abv_unsigned"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hl_minv_mono : ltac2:(TCodec.tc2 tcn__HandoffBInvK "Q='8';'@%2211%411'G'Q3r3r1%3221'R7yR0%211'>'6&Q5r5%2219(<%63521r2%6251%93814p041pT<<1&QJ&QI&Q4%11E&Q2r4%211%6241&K&H%11L%311%<251%Q02F8p021p0@1p0Q01pT8Q51p4Q71p2Q81").
Proof.
intros A A' m [N1 N2 N3 N4 N5] Hsub Hb. constructor; try assumption. intros p Hp. apply Hsub. exact (N3 p Hp).
Qed.
Lemma hl_A_bytes_app : ltac2:(TCodec.tc2 tcn__HandoffBInvK "C'8';'@%2211%411'>&Q2&5r2r1%33721%511&QI%715%815%3221%;3>51p6=1p2>1").
Proof. induction A as [|iv A IH]; intros B; cbn [A_bytes app]; [lia | rewrite IH; lia]. Qed.
Lemma hl_sum_gw : ltac2:(TCodec.tc2 tcn__HandoffBInvK "@'8';'R7yR0%211%4211%611'>'@&Q?r1%211&Q6%113%73631pT491").
Proof. induction l as [|q l IH]; [reflexivity|]. cbn [sum_sizes AsanPlacement.gw_sizes]. rewrite IH. reflexivity. Qed.
Definition M_LOW : amap := {| am_base := ELit 0x7fff7000; am_len := ELit 0x10000000; am_kind := KRWLAZY |}.
Definition M_GAP : amap := {| am_base := ELit 0x8fff7000; am_len := ELit 0x20000000000; am_kind := KNONELAZY |}.
Definition M_HIGH : amap := {| am_base := ELit 0x2008fff7000; am_len := ELit 0xdfff0001000; am_kind := KRWLAZY |}.
Section BInvMain.
Variable SEGS : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis IMG : img_facts SEGS A ph.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis HULL_below : img_hi A <= SHB_LO.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis RESV_pos : forall b s, In (b, s) (segments_reserved SEGS) -> 0 < bv_unsigned s.
Variable cs : acs.
Hypothesis NOFOG : no_fog (a_maps cs) = true.
Hypothesis HNA : hops_in_maps (a_maps cs) (a_hna cs) = true.
Hypothesis HLZ : hops_in_maps (a_maps cs) (a_hlz cs) = true.
Hypothesis VWR : forallb (vis_sh_wr A (kn cs)) (a_vis cs) = true.
Hypothesis VOFF : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true.
Hypothesis IN_LOW : In M_LOW (a_maps cs).
Hypothesis IN_GAP : In M_GAP (a_maps cs).
Hypothesis IN_HIGH : In M_HIGH (a_maps cs).
Variable RESm : list amap.
Hypothesis RESm_in : forall m, In m RESm -> In m (a_maps cs).
Hypothesis RESm_pos : forall m, In m RESm -> exists lo, xlo (kn cs) (am_base m) = Some lo /\ 0 < lo.
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
+ (Z.of_nat (length (segments_reserved SEGS) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
Definition resZ (E : env) (m : amap) : Z * Z := (uE E (am_base m), uE E (am_len m)).
Definition RES_of (E : env) : list (Z * Z) := map (resZ E) RESm.
Definition BASE_of : Z := a_eager cs + a_abytes cs + A_bytes EXTRA.
Definition A0_of (E : env) : list (Z * Z) := allowA A E cs ++ EXTRA.
Section Run.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
#[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
#[local] Notation RESV0 := (segments_reserved SEGS).
#[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
#[local] Notation CEIL0 := (uE E e_sp0 - 8388608).
Let Hmaps := hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC NOFOG.
Lemma hb_in_maps : ltac2:(TCodec.tc2 tcn__HandoffBInvK "H'Q:&QHr1&Q7vQO%211%53641';'R7yR0%211%4211&Q=vAr2%3221&L&HvR4%211%411%D3:61p0@1pT8G1").
Proof. intros m Hm. rewrite Hmaps. apply in_map. exact Hm. Qed.
Lemma hb_sp0_window : ltac2:(TCodec.tc2 tcn__HandoffBInvK ";'=&QJ&J&Q@vA&Q;%3221%6251&I%8231%:231").
Proof. exact (proj1 (proj2 (co_isp _ _ _ _ _ _ _ _ _ _ _ HC))). Qed.
Lemma hb_lit_covered : ltac2:(TCodec.tc2 tcn__HandoffBInvK "QL'Q:'@&QHr4&Q7vQO%211%53741'>'QB&Q8r5%211(QA%11;%73631&Q9r6%211%;3:15&QJz%2215&QK&QIr8r7%3221&QL+2+R0%3221%9251'=r9%?219%<22;%>2;1%5231'6&QC&L&HvR4%211%411%621E(<%Q83921p0;1p0B1p0M1p0N1p0Q21p0Q71p0Q@1pTDQG1pQ<QH1p8QI1pT8QK1").
Proof.
intros m BL LL x Hm Hb Hl H0 H1 H2 Hx. rewrite hl_covered_in_ivs. unfold in_ivs. apply existsb_exists.
exists (amap_den E m). split; [exact (hb_in_maps m Hm)|]. unfold amap_den. cbn [fst snd]. rewrite Hb, Hl. cbn [edenot].
rewrite !u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma hb_lit_entry : ltac2:(TCodec.tc2 tcn__HandoffBInvK "RA'Q:'@&QHr5&Q7vQO%211%53741'>'QB&Q8r6%211(QA%11;%73631&Q9r7%211%;3:15&QJz%2215&QK&QIr9r8%3221&QL+2+R0%3221%9251r:%>218r;%<213%A2;1'?'R7yR0%211'=';%1233(:r2r1%347721&L&HvR4%211%411%QD3:61&R8%12@:r<%Q6221%42C<%Q4241%Q92J1%D241%E291qT>G1%K2H1qSNI1%M2J1p0O1p0Q31p0Q61p0QA1p0QB1p0QF1p0QK1p0R41pT2R;1pT6R<1pQ<R=1p8R>1pT8R@1").
Proof.
intros m BL LL lo hi Hm Hb Hl H0 H1 H2 Hlo Hhi. exists (edenot E (am_base m)), (edenot E (am_len m)).
split; [exact (hb_in_maps m Hm)|]. rewrite Hb, Hl. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.
Lemma hb_shrw_facts : ltac2:(TCodec.tc2 tcn__HandoffBInvK "I'@&Q0r1%211'=&QJ&Q<v0%211r2%5221'>'6&Q>&M&HvR4%211%411%62:1(7%:3921%B2<1p0D1pTDH1").
Proof.
intros x Hx. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx. unfold SHB_LO in HULL_below. split; [lia|].
assert (Hw : 0 <= x < 2 ^ 64) by lia.
destruct Hx as [Hx|Hx].
- destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model M_LOW (Z_to_bv 64 x) HC IN_LOW eq_refl) as [Hn _].
+ cbn [M_LOW am_base am_len edenot]. rewrite !u64_lit by lia. lia.
+ rewrite u64_lit in Hn by lia. exact Hn.
- destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model M_HIGH (Z_to_bv 64 x) HC IN_HIGH eq_refl) as [Hn _].
+ cbn [M_HIGH am_base am_len edenot]. rewrite !u64_lit by lia. lia.
+ rewrite u64_lit in Hn by lia. exact Hn.
Qed.
Theorem hb_bridge_static : ltac2:(TCodec.tc2 tcn__HandoffBInvK "H'OvQG&L&HvR4%211%411&F%117&M%115&QFvA%211&QM&Q@&Q;%2251+XPPP0%5221v4vDvC%G9FA?=:4321").
Proof.
pose proof hb_sp0_window as [SPlo SPhi]. unfold sp_window_lo, sp_window_hi in *.
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
unfold SHB_LO in HULL_below.
constructor.
- exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)).
- intros q Hq. exact (proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq)).
- exact RESV_pos.
- apply hl_seps_nodup; [exact (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)|].
intros q Hq. exact (proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq)).
- exact (hl_seps_apart _ (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)).
- intros x Hx. destruct (hb_shrw_facts x Hx) as [Hh _].
assert (Hw : 0 <= x < 2 ^ 64) by (unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx; lia).
pose proof (SEGS_in_hull (Z_to_bv 64 x)) as Hs. rewrite u64_lit in Hs by lia. apply Hs.
unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. lia.
-
intros Rz HR. unfold RES_of in HR. apply in_map_iff in HR as (m & <- & Hm).
pose proof (hb_in_maps m (RESm_in m Hm)) as Hin.
destruct (RESm_pos m Hm) as (lo & Hlo & Hpos).
pose proof (xlo_sound SEGS E _ (kn cs) _ lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hlo) as Hb.
destruct (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model _ HC Hin) as [P1 P2]. unfold amap_den in P1, P2. cbn [fst snd] in P1, P2.
unfold resZ, toW. cbn [fst snd]. unfold uE. rewrite !Z_to_bv_bv_unsigned.
split; [exact Hin|]. pose proof (u64_range (edenot E (am_base m))). pose proof (u64_range (edenot E (am_len m))). unfold uE in *. lia.
-
intros Rz b s HR Hbs. unfold RES_of in HR. apply in_map_iff in HR as (m & <- & Hm).
pose proof (hb_in_maps m (RESm_in m Hm)) as Hin.
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as (_ & _ & _ & P4 & _).
pose proof (proj1 (Forall_forall _ _) RES_hull _ Hbs) as [Q1 Q2].
unfold amap_den in P4. cbn [fst snd] in P4, Q1, Q2. unfold resZ. cbn [fst snd]. unfold uE. lia.
-
intros x Hx. unfold SHLO, SHHI in Hx.
destruct (Z_lt_dec x 0x8fff7000); [|destruct (Z_lt_dec x 0x2008fff7000)].
+ apply (hb_lit_covered M_LOW _ _ x IN_LOW eq_refl eq_refl); lia.
+ apply (hb_lit_covered M_GAP _ _ x IN_GAP eq_refl eq_refl); lia.
+ apply (hb_lit_covered M_HIGH _ _ x IN_HIGH eq_refl eq_refl); lia.
-
intros lo hi Hlh [Hx|Hx]; unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx.
+ apply (hb_lit_entry M_LOW _ _ lo hi IN_LOW eq_refl eq_refl); lia.
+ apply (hb_lit_entry M_HIGH _ _ lo hi IN_HIGH eq_refl eq_refl); lia.
-
intros x b s Hx Hbs Hin. destruct (hb_shrw_facts x Hx) as [Hh _].
pose proof (proj1 (Forall_forall _ _) RES_hull _ Hbs) as [Q1 Q2]. cbn [fst snd] in Q1, Q2. lia.
-
intros x Hx. rewrite hl_covered_in_ivs. exact (proj2 (hb_shrw_facts x Hx)).
-
rewrite <- hl_sum_gw. rewrite length_app.
pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as Ht. rewrite (co_res _ _ _ _ _ _ _ _ _ _ _ HC) in Ht.
rewrite Hmaps at 2. rewrite length_map.
assert (0 <= LENMAX + 4095) by lia.
assert (0 <= Z.of_nat (length RESV0) + Z.of_nat (length (a_maps cs)) + KMAX) by lia.
rewrite Nat2Z.inj_add in GAP. nia.
- unfold SHHI, stack_max_size. lia.
- exact BUD.
Qed.
Theorem hb_binv_main : ltac2:(TCodec.tc2 tcn__HandoffBInvK "K'NvQG&L&HvR4%211%411&F%117&M%115&QM&Q@vA&Q;%3221+XPPP0%6221&QEv4(9'Q1%211&QD%11;vB%J;IDB@987421F").
Proof.
clear GAP RESm_in RESm_pos IN_GAP.
pose proof hb_sp0_window as [SPlo SPhi]. unfold sp_window_lo, sp_window_hi in *.
assert (Hsub : forall p, page_allowedb (allowA A E cs) p = true -> page_allowedb (A0_of E) p = true).
{ intros p Hp. unfold A0_of, page_allowedb in *. rewrite existsb_app, Hp. reflexivity. }
pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC) as He. pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC) as Ha.
pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ HC) as Hl.
assert (Hbud : eager_used model + A_bytes (A0_of E) <= BASE_of) by (unfold A0_of, BASE_of; rewrite hl_A_bytes_app; lia).
constructor.
- exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC).
- unfold A0_of. apply Forall_app. split; [exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) | exact EXTRA_wf].
- apply (hl_minv_mono (allowA A E cs)); [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hsub |]. unfold BASE_of in *. lia.
- exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC).
- reflexivity.
- exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC).
- exact (hl_alloc_top SEGS A LIMIT SINV argH FS0 E cs R FULL model HC).
- unfold BASE_of. lia.
- intros x Hx. exact Hx.
- exact (hl_noacc_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model HC NOFOG HNA).
- intros a Hp. destruct (hl_lazy_in SEGS A LIMIT SINV argH FS0 SEGS_in_hull E cs R FULL model HC NOFOG HLZ a Hp) as [H1 H2].
rewrite hl_covered_in_ivs. split; assumption.
- unfold live_ok. cbn. split; [intros p []|]. split; [constructor | intros p p' []].
- intros a Hh Hna. rewrite hl_covered_in_ivs in Hna.
apply (hl_hidden_zero SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok E cs R FULL model HC NOFOG HLZ a); [|exact Hna].
unfold bhid, mkH in Hh |- *. apply andb_prop in Hh as [H1 H2]. rewrite H1. cbn [andb].
apply negb_true_iff. apply negb_true_iff in H2.
destruct (page_allowedb (allowA A E cs) (page_base a)) eqn:Hp; [|reflexivity]. rewrite (Hsub _ Hp) in H2. discriminate.
- intros a Ha'. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Ha'. destruct Ha' as [Hx|Hx].
+ apply (hl_shadow_defined SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high SHADOW_ok HULL_below E cs R FULL model HC NOFOG VWR VOFF
M_LOW 0x7fff7000 0x10000000 IN_LOW eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
+ apply (hl_shadow_defined SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high SHADOW_ok HULL_below E cs R FULL model HC NOFOG VWR VOFF
M_HIGH 0x2008fff7000 0xdfff0001000 IN_HIGH eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
- intros w [].
- cbn. lia.
- cbn. lia.
- cbn. lia.
Qed.
End Run.
End BInvMain.
