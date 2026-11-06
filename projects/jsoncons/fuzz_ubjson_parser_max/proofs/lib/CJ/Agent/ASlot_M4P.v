(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W9 ASlot_W14.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_M4P () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M4P.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M4P.CEIL_WRAP_1.SMG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."; "stdpp.option."], [["1None"; "1Some"; "1bool"; "1false"; "1fst"; "1id"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2True"; "2and"; "2eq"]; ["2ex"; "2iff"; "2not"; "2or"; "3N"; "3Z"; "5sm_rec"; "4sm_rec"; "6rdv"; "7meta_slot"; "8mem"; "8pans_mem"; "9grp_hdr_cov"; ":UNIT"; ":aadd"; ":active"]; [":add_slots"; ":aptr"; ":area"; ":brkstate"; ":c_active"; ":c_brk"; ":c_free_meta_head"; ":c_mmap_counter"; ":c_usage"; ":conc"; ":ctx"; ":get_meta_rec"; ":get_shadow"; ":get_stride"; ":ghdr"; ":hav_add"]; [":hdr_havoc"; ":m_mem"; ":mask_upto"; ":mctx"; ":meta"; ":mkGhdr"; ":mkShadow"; ":mstate"; ":optr"; ":put_meta"; ":r_cells"; ":r_hav"; ":r_havp"; ":region"; ":s_areas"; ":s_groups"]; [":s_next_rid"; ":s_regions"; ":s_reserved"; ":s_shadow"; ":s_slots"; ":s_tick"; ":set_active_map"; ":set_usage_map"; ":shadow"; ":usage"; ":wr8"; ":zero_hdrs"; "0S"; ";add"; ";div"; ";eqb"]; [";land"; ";le"; ";lt"; ";modulo"; ";mul"; ";pow"; ";sub"; "0ai"; "0b"; "0b'"; "0c"; "0cnt"; "0g"; "0gh"; "0i"; "0k"]; ["0len"; "0m"; "0ml"; "0mt"; "0o"; "0off"; "0p"; "0q"; "0r"; "0rid"; "0rid'"; "0sc"; "0size"; "0st"; "0stF"; "0stT"]; ["<insert"; "<lookup"; "=N_countable"; "=Z_countable"; "=prod_countable"; ">prod_eq_dec"; "?map_insert"; "@gmap"; "@gmap_lookup"; "@gmap_partial_alter"; "Aeq_dec"; "Beq_dec"; "Cfrom_option"; "0stride"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma pos_iter_slots' (m p : aptr) (stride : Z) : forall n tb,
0 < stride ->
let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
fst (Pos.iter F (0, tb) n) = Z.pos n
/\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
/\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
- cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
- rewrite Pos.iter_succ. destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
split; [lia|]. split.
+ rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
+ intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
* right. exists (Z.pos n). split; [lia| reflexivity].
* rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.
Lemma add_slots_first' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "RH&Q1'E'QG&RA+1r2%3221&RBzr4%3221'>'?'9';%12?>%311&SA'SG&SE'D&SJ&SK%4432F1&SD&SB&SC%36762J51%:4L51=&SH%14N73?&Nr6&M%3221&R4&Q0r7r5r3%45382O1%611%I6Q:K><81(1(:%14Q=Q<8Q5%32O1%Q33O51&Br1r8%?51>C=Q:%A11%Q46QEQ6IG41(0%11Q8%Q<3Q831%911'C%H1E%Q;6QLQ=Q0NQG1%QA3Q=16%>11'@%QM2QH?%QJ2@L%QG221r9&R=&RD%12DE%32Q61%Q9251%QM3R9Q21%QO281qUNR:1%=2R;1%C2?1p0E1pV@R?1%R52Q11p0R71p0R<1pVLRA1pUFRC1pWLRD1pV>RF1pV4RG1").
Proof. intros m p stride c st.
intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
destruct (pos_iter_slots' m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.
Lemma mask_upto_range' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "J'E'>&RAzr1%3221+O%5231%7231+1&QBr2%211%;241&RB&RE+2+Q0%3221%5271%C271%625:%D21:%F231p0@1pV0I1").
Proof. intros k.
intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
change (2^32) with (2 * 2^31). lia.
Qed.
Lemma put_meta_wr8_comm : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "F&Q1'QD'E'QG'?&QIr5r4&R:r3r2r1%43321%83761%93873%73651%<3=31pVL>1pWN@1pV@C1pVBC1pV8E1").
Proof. intros mt r q v st. destruct st; reflexivity. Qed.
Lemma put_meta_zero_hdrs_comm : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "K&Q1'QD'E'7'QG'?&QIr7r6&R;r5r4r2r3r1%6554321%:3981%;3:93%9587651%>3?31pVL@1pUNC1pV0C1pVJE1pV>H1pVBH1pV8J1").
Proof. intros mt r p size. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH, put_meta_wr8_comm. reflexivity. Qed.
Lemma rec_zero_hdrs : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "H&Q1'E'7'QG'?'QD&Q;&R;r6r5r2r3r1%6554321r4%9221%:242%=3<21pVL?1pUNB1pV0B1pV@E1pVJE1pV>G1").
Proof. intros p size q. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. destruct st; reflexivity. Qed.
Section SMG.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis P0 : 0 <= snd p.
Definition sm_rec : meta :=
mkMeta (Some mt) (Some mt) (Some p) (mask_upto ai - 1) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.
Lemma smg_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "S4'>'?'SG'D&SJ&SB'QM%544321&R1vS>%211vS?%411%<3631'R8%=4<;:1&R3%118&Q@vS6%2219%511%E3751&Q1&SE'E&SK%34HG21&SD&SC%26KJI541'Q>%N49521&QO%11I&S@&SF&SI%14?;87%34@871(QE(1vS3%22D1&R@vRG+O%3221%8251%@1Q6%?7KCB;O21%QB3CA1'Q2%QC4NJG1&QN%11Q>%21Q=%QH3421&R5%11QB%21QA%QL3QJ21&R0%11QF%21QE%R03QN21'6';%12Q;Q;%311&R2%11QN%21QM%R83421'Q3&Q5&Q:%11R4%311%31R4%511%R@3731&Q7%116%215%RD3QL21&QH&Q6%11;%21:%RI3421%RK261%RL2;1%RM2D1%RN2M1%RO2Q21%S02Q71%S12Q>1%S22R<1%S32RF1").
Proof. repeat split; reflexivity. Qed.
Lemma smg_rec_mt : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "8'?'QD&Q;vS>vS3%3221&F%73621").
Proof.
unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
unfold stFin, stE. rewrite rec_set_active, get_meta_rec_put_same. reflexivity.
Qed.
Lemma smg_rec_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "A&Q1&B'?r1vS3%33521%511'QD&Q;vS>r2%3221vS?%5213%<3731p091pV@@1").
Proof. intros q.
intros NE. unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
unfold stFin, stE, stD, stC, stB, stA. rewrite rec_set_active, get_meta_rec_put_other, rec_put_group, get_meta_rec_put_other, rec_set_usage, rec_hdr_havoc by exact NE.
reflexivity.
Qed.
Lemma smg_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof.
unfold stF, st_model. cbv zeta. rewrite active_set_active. destruct (c =? sc); [reflexivity|].
rewrite !active_upd_meta. reflexivity.
Qed.
Lemma smg_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q7'?'QC&Q:vS>%211&R6&S@'E&Q1'SG&SK&SC%345214&SF&SI%148547%349841vS;vS3&Q4vS?%C11%311%A7@?;7651&R7%@4B?>B%<4C@?C%>4DD21&R=&R9%12:=vRK%4221&Q8%11=%M7LL:8B31%<21?%Q02>1%Q63Q5Q21").
Proof. reflexivity. Qed.
Lemma smg_usage i : usage stF i = if i =? sc then usage stT sc + cnt else usage stT i.
Proof.
unfold usage. rewrite smg_ctx. cbn [c_usage set_active_map set_usage_map].
destruct (Z.eqb_spec i sc) as [E|NE]; [rewrite E, lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
Lemma smg_stride : get_stride sm_rec = if (cnt =? 1) && negb (ml =? 0) then ml * 4096 - 16 else 16 * size_class sc.
Proof.
unfold get_stride, sm_rec. cbn [m_last_idx m_maplen m_sizeclass].
replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); try reflexivity; lia).
unfold UNIT. reflexivity.
Qed.
Lemma smg_slot0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q@&RBz&Q=&F%211%5241'?'9';&Q1'E%3221%511&SA'D%7215'SG&SE&SJ&SK%3462:1&SD&SB&SC%36:62>51%94@51>&SH%14B73@(:&4vS6%23AE1&R=&<%13DH4+@%4221%94GK61&R4vS>%211%L6JN@>41(1vS3%@4Q3Q21Q;%32Q21%Q83Q251p0Q:1").
Proof.
intros HS. unfold stF, st_model. cbv zeta.
match goal with |- s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ ?X))) !! _ = _ =>
change (s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ X)))) with (s_slots X) end.
match goal with |- s_slots (add_slots mt p ?s cnt ?X) !! _ = _ =>
replace s with (get_stride sm_rec) end.
2:{ unfold upd_meta. rewrite rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC. unfold get_stride, sm_rec.
cbn [m_last_idx m_maplen m_sizeclass m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
reflexivity. }
change (fst p, snd p + 16) with (aadd p UNIT).
apply (proj1 (add_slots_first' mt p (get_stride sm_rec) cnt _ ltac:(lia) HS)).
Qed.
Lemma smg_shadow_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "D'D&B'?r1&4'EvS6%33721%63851%811'R8&Q<vS>r2%3221vS?%5213%?3731p091pV@C1").
Proof. intros q.
intros NE. unfold get_shadow. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma smg_shadow_p : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "QG'?'R8&Q<vS>&4'D'EvS6%43321%7261(QF&QJvS?%;215%311&S@'6';%12<=%311'SG&SK&SC%34A214&SF&SI%14D547%34E841&R>&<%13IHG+@%4221&Q?+<&R5%11H&SL&5%11D(8%11G&SA&SH%14Q6GFI&QK%11Q1%56Q9LH3?1%;5MM971%@3?=1%Q37Q<OKGB14&QL%11Q7%Q;3Q731%QF3QEQ=1").
Proof.
unfold get_shadow at 1. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. reflexivity.
Qed.
Lemma smg_group_p : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q4'?'9'Q>%211&SA&Q1'SG&SE'D&SJ'E&SK%544321&SD&SB&SC%36872651%;4<51?&SH%14>73AvS6&QOvS>%211%D6CF7541(1(QEvS3%32G1&R@vRG+O%3221%7251%92Q01%Q33Q0;1").
Proof. rewrite (proj1 (proj2 (proj2 smg_proj))). apply lookup_insert_eq. Qed.
Lemma smg_groups_inv : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "QH&Q1'Q>'?'9%113&SA'SG&SE'D&SJ'E&SK%544321&SD&SB&SC%36872651%;4A51@&SH%14C73Br2&QOvS>%211%C6HG7541(1r1%22J1%J3H41'C'>r3vS6%O3Q121(QEvS3%;2Q41&R@vRG+O%3221%7251%Q83Q9F1%=2:1&B%11<vS?%J11%Q;6Q@Q?OMA1%H2Q@M%Q@3Q>21%E261%G291p0I1pULQE1pUDQG1").
Proof. intros b' gh.
rewrite (proj1 (proj2 (proj2 smg_proj))). intros H. destruct (decide (b' = p)) as [->|NE].
- left. rewrite lookup_insert_eq in H. inversion H. auto.
- right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.
Lemma smg_groups_old : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q<&Q1'Q>'?'9%113&SA'SG&SE'D&SJ'E&SK%544321&SD&SB&SC%36872651%;4A51@&SH%14C73BvS6&QOvS?%211%C6HG7541(0%11I%I3G31r3%H6ML<:16(1r2%22O1%O3M41r4vS>%?11%Q06Q5Q4DB31%82Q5:%Q53Q321p071p0>1pULQ91pUDQ;1").
Proof. intros b' gh.
intros GN H. rewrite (proj1 (proj2 (proj2 smg_proj))). rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite GN in H. discriminate.
Qed.
Lemma smg_grp_hdr_cov : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "G'E'>&RA&<'DvS6%33261r1%6221&RB&R=+<%2261%4261%=261&LvS>&4%13>B=r2%53421p071pV<F1").
Proof. intros off. intros Ho. exists p, (mkGhdr (Some mt) (Z.land ai 31)). split; [exact smg_group_p|]. split; [reflexivity| lia]. Qed.
Lemma smg_grp_hdr_cov_old : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q7'D'E'?'9'Q>%211&SA&Q1'SG&SE&SJ&SK%34<2;1&SD&SB&SC%36@62?51%94:51=&SH%14<73?vS6&QOvS?%211%B6AD7541(0%11F%I3F31&Lr3r2%33921vS>r4%63215p041p091pV<Q41pV@Q61").
Proof. intros q off. intros GN (b' & gh & Hb & Hf & Ho). exists b', gh. split; [apply smg_groups_old; assumption| auto]. Qed.
Lemma smg_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P ";&Q1'?'E&Q9vS>r1%3221vS?%5213%83731pV@:1").
Proof. intros q. unfold conc, get_region. rewrite (proj1 smg_proj). reflexivity. Qed.
Lemma smg_meta_slot : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P ":&Q1&A&IvS?r1%3221vS>%5213%7231pV@91").
Proof. intros q. split; intros H; (eapply meta_slot_same_areas; [| exact H]); rewrite (proj1 (proj2 (proj2 (proj2 smg_proj)))); reflexivity. Qed.
Lemma smg_ret_span : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "R4'D'E'@&Q1'>'?&QH&OvS>vS;%3221(1r2%22:1%93841&QA&Q;%1295%311r1%92A1%@3?31r5&4%13HG5%D3I31r4&R=&<%13ML:+@%4221&RD&Q=%11Az%4221%:261%Q13Q5<1r3&RF+4%2281%Q63Q:41%Q8261%Q92D1%Q:2I1%Q;2Q11qUBQ=1%Q?2Q>1qUJQ?1%QA2Q@1vS6%N3QEQD1%QA3QFL1%K3QGQF3%M21J%QD3QHB1&F%J11%D21C%QH3QLQA1%QJ251%QK291p0=1pV2R01pTJR11pVFR31").
Proof. intros rid' S len.
intros (g & b & HA & HM & -> & -> & ->). rewrite smg_active, Z.eqb_refl in HA. inversion HA; subst g.
rewrite smg_rec_mt in HM |- *. cbn in HM. inversion HM; subst b. split; [reflexivity| split; [lia| reflexivity]].
Qed.
End SMG.
Lemma Zle_1_nonneg' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "D'E'>&RA+1r1%3221&RB&RE+2+L%3221%5271%;271zr2%=221'=%@221p061pX0C1").
Proof. intros x. intros H. split; [lia| exact I]. Qed.
Section SM.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt : aptr) (rid : N) (r0 : region).
Let p : aptr := (rid, 0).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 1 <= ml < 2^28.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis HrT : (s_regions stT) !! rid = Some r0.
Hypothesis Hk0 : r_kind r0 = RKGroup.
Hypothesis SHT : (s_shadow stT) !! rid = None.
Hypothesis GNT : forall off, (s_groups stT) !! (rid, off) = None.
Let P0 : 0 <= snd p := Z.le_refl 0.
Let ML0 : 0 <= ml := proj1 (Zle_1_nonneg' ml ML).
Lemma sm_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "S4'>'?'SG'D&SJ&SB'QM%544321&R1vS>%211vS?%411%<3631'R8%=4<;:1&R3%118&Q@vS6%2219%511%E3751&Q1&SE'E&SK%34HG21&SD&SC%26KJI541'Q>%N49521&QO%11I&S@&SF&SI%14?;87%34@871(QE(1vS3%22D1&R@vRG+O%3221%8251%@1Q6%?7KCB;O21%QB3CA1'Q2%QC4NJG1&QN%11Q>%21Q=%QH3421&R5%11QB%21QA%QL3QJ21&R0%11QF%21QE%R03QN21'6';%12Q;Q;%311&R2%11QN%21QM%R83421'Q3&Q5&Q:%11R4%311%31R4%511%R@3731&Q7%116%215%RD3QL21&QH&Q6%11;%21:%RI3421%RK261%RL2;1%RM2D1%RN2M1%RO2Q21%S02Q71%S12Q>1%S22R<1%S32RF1").
Proof. exact (smg_proj stT sc cnt ai mt p). Qed.
Lemma sm_rec_mt : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P ">'?'QD&Q;vS>vS3%3221&GvS;vRKvRGvS2vS6%66543281%=3<81").
Proof. apply (smg_rec_mt stT sc cnt ai ml mt p); assumption. Qed.
Lemma sm_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof. exact (smg_active stT sc cnt ai mt p c). Qed.
Lemma sm_ml_nz : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "8'?'2&R?vS2z%3221(3%73621").
Proof. apply Z.eqb_neq. lia. Qed.
Lemma sm_stride : get_stride (sm_rec sc cnt ai ml mt p) = if cnt =? 1 then ml * 4096 - 16 else 16 * size_class sc.
Proof. rewrite (smg_stride sc cnt ai ml mt p) by assumption. rewrite sm_ml_nz, andb_true_r. reflexivity. Qed.
Lemma sm_slot0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q@&RBz&Q=&GvS;vRKvRGvS2vS3vS6%76654321%911%<2;1'?'9';&Q1'E%3221%511&SA'D%7215'SG&SE&SJ&SK%3462:1&SD&SB&SC%36:62>51%94@51>&SH%14B73@(:vS9+@%34AE21&R4vS>%211%F6DH:841(1%94LKQ4Q;%22K1%Q13K41p0Q31").
Proof. intros HS. apply (smg_slot0 stT sc cnt ai ml mt p); assumption. Qed.
Lemma sm_cell_read off : 0 <= off -> cell_read (get_shadow stF rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
intros Ho. unfold get_shadow. rewrite (proj1 (proj2 sm_proj)). fold (get_shadow (hdr_havoc p stT) rid).
apply cell_read_hh0; [exact SHT| exact Ho].
Qed.
Lemma sm_cells_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "J'E'?'9';'D%2251%411&SA'SG&SK&SC%34;216&SH%14=438r1&QJ&Q<vS>vS9%3221%511%>6E@:871(0%11B%G3B31pV<I1").
Proof. intros off.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_cells]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.
Lemma sm_hav_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "Q3'E&RA+@r1%3221'?'9'6';'D%22:1%411%611&SA'SG&SK&SC%34A216&SH%14C438&R>r2%221D&QK&Q<vS>vS9%3221%511%@6MB<:71(0%11D%K3D31p0M1pV<Q21").
Proof. intros off.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. intros Ho. change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_hav]. unfold p. cbn [fst snd]. change (0 / 16) with 0.
rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). unfold get_shadow. rewrite SHT. cbn. apply lookup_empty.
Qed.
Lemma sm_havp_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "H'E'?'9'D%211&SA'SG&SK&SC%349216&SH%14;438r1&QL&Q<vS>vS9%3221%511%>6C@:871(0%11B%E3B31pV0G1").
Proof. intros k.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_havp]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.
Lemma sm_shadow_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "A'D&B'?r1vS9%33521%511'R8&Q<vS>r2%3221vS?%5213%<3731p091pV@@1").
Proof. intros q. intros NE. exact (smg_shadow_other stT sc cnt ai mt p q NE). Qed.
Lemma sm_groups_rid : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "QC'E'Q>'?'9%113&SA';'D%2218'SG&Q1&SE&SJ&SK%3472>1&SD&SB&SC%36;62B51%:4951B&SH%14;73D(:vS9r2%34BI21&QOvS>%211%H6EL:841(1r1%22O1%O3M41'>r3z%Q33Q521(QEvS3%:2N1&R@vRG+O%3221%7251%Q<3Q=F1%=2:1p0?1pULQ@1pV<QB1").
Proof. intros off gh.
intros H. destruct (smg_groups_inv stT sc cnt ai mt p _ _ H) as [[E ->]|[NE H']].
- unfold p in E. inversion E. auto.
- rewrite GNT in H'. discriminate.
Qed.
Lemma sm_grp_hdr_cov : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "A'E'>&RAzr1%3221&RB+<%2241%8241&LvS>vS9r2%43321p061pV<@1").
Proof. intros off. clear ML0 P0 CNT AI ML REC HrT Hk0 GNT SHT. intros Ho. apply (smg_grp_hdr_cov stT sc cnt ai mt p SC off). cbn. lia. Qed.
Lemma sm_grp_hdr_cov_old : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "='D'E&LvS?r2r1%43321vS>r3%73215p041pV<:1pV@<1").
Proof. intros q off. intros H. exact (smg_grp_hdr_cov_old stT sc cnt ai mt p P0 q off (GNT 0) H). Qed.
Lemma sm_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P ";&Q1'?'E&Q9vS>r1%3221vS?%5213%83731pV@:1").
Proof. intros q. exact (smg_conc stT sc cnt ai mt p q). Qed.
Lemma sm_meta_slot : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P ":&Q1&A&IvS?r1%3221vS>%5213%7231pV@91").
Proof. intros q. exact (smg_meta_slot stT sc cnt ai mt p q). Qed.
Lemma sm_rdv : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "@&J'?'E&H&Kr1vS>(:'DvS9+=%443921%95<8761z%=3<21pV:?1").
Proof. intros o. clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. unfold rdv. cbn [fst snd]. rewrite sm_cell_read by lia. reflexivity. Qed.
Lemma sm_stride_mod16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "='?'E&RC&Q=&Q;vS>vS3%3221%511+@%8221z%<3;21").
Proof.
rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1).
- replace (ml * 4096 - 16) with ((256 * ml - 1) * 16) by lia. apply Z_mod_mult.
- rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Section SE.
Variables (req nd : Z).
Lemma sm_slot_ok : 0 <= req < 2^32 -> req + 4 <= 16 * size_class sc ->
r_len r0 = nd -> nd = 4096 * ml -> req + 20 <= nd -> 16 * size_class sc < 2^18 ->
(cnt = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * cnt + 16 <= nd /\ nd < 16 * size_class sc * cnt + 16 + 4096) ->
meta_slot stT mt ->
slot_ok stF mt p r0 0 req
/\ get_stride (get_meta_rec stF mt) = (if cnt =? 1 then nd - 16 else 16 * size_class sc)
/\ 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) <= nd.
Proof.
intros RQ FIT LEN EML NDR SZ NDC MS.
pose proof (size_class_range sc SC) as SZR.
assert (RU : round_up_pg nd = nd).
{ rewrite EML. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
replace (- (4096 * ml)) with ((- ml) * 4096) by lia. rewrite Z_mod_mult. lia. }
assert (STR : get_stride (get_meta_rec stF mt) = if cnt =? 1 then nd - 16 else 16 * size_class sc).
{ rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1); lia. }
assert (S20 : 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) * cnt <= nd
/\ req + 4 <= get_stride (get_meta_rec stF mt) /\ get_stride (get_meta_rec stF mt) - 4 - req < 2^31
/\ (forall off, 16 * off + req + 4 <= get_stride (get_meta_rec stF mt) -> off < 65536)).
{ rewrite STR. destruct (Z.eqb_spec cnt 1) as [E1|NE1].
- rewrite E1. destruct NDC as [[_ X]|[X1 X2]]; (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros off Hoff; lia).
- destruct NDC as [[X _]|[X1 X2]]; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros off Hoff. lia. }
destruct S20 as (G20 & GSP & GFIT & G31 & G18).
pose proof (mask_upto_range' ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
assert (AM : mask_upto ai <= mask_upto (cnt - 1)) by (unfold mask_upto; apply Z.sub_le_mono_r; apply Z.pow_le_mono_r; lia).
split; [| split; [exact STR| split; [exact G20| nia]]].
constructor.
- rewrite sm_rec_mt. reflexivity.
- rewrite (proj1 sm_proj). exact HrT.
- exact Hk0.
- unfold p. cbn [snd]. lia.
- reflexivity.
- rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
- replace (m_last_idx (get_meta_rec stF mt)) with (cnt - 1) by (rewrite sm_rec_mt; reflexivity).
rewrite LEN, RU. unfold p. cbn [snd]. replace (cnt - 1 + 1) with cnt by lia. lia.
- exact G20.
- apply sm_stride_mod16.
- exact G31.
- lia.
- exact GFIT.
- intros b' gh Hb' Hf. destruct b' as [b1 b2]. unfold p in Hf. cbn in Hf. subst b1. destruct (sm_groups_rid _ _ Hb') as [-> _]. unfold p. cbn [snd]. left. lia.
- unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0 - 4) with 12 by lia. rewrite sm_cell_read by lia. reflexivity.
- intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. apply G18. exact OF.
- unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0) with 16 by lia. apply sm_slot0. rewrite <- sm_rec_mt. lia.
- apply (proj1 (sm_meta_slot mt)). exact MS.
- rewrite sm_rec_mt. cbn [m_avail sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_freed sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_freeable sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_maplen sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.
End SE.
Lemma sm_ret_span : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4P "QL'D'E'@&Q1'>'?&QH&OvS>vS;%3221(1r2%22:1%93841&QA&Q;%1295%311r1%92A1%@3?31r5&4%13HG5%D3I31r4&R=&<%13ML:+@%4221&RD&Q=%11Az%4221%:261%Q13Q5<1r3&RF+4%2281%Q63Q:41%Q8261%Q92D1%Q:2I1%Q;2Q11qUBQ=1%Q?2Q>1qUJQ?1%QA2Q@1vS9%Q@3QEK1%QA3QE?H%QC221p051pV2QH1pTJQI1pVFQK1").
Proof. intros rid' S len.
intros H. destruct (smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H) as (-> & -> & _). unfold p. cbn. split; reflexivity.
Qed.
End SM.
End CEIL_WRAP_1.
