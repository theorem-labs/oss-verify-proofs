(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WGroup.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WCreate () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Shadow."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WCreate.CEIL_WRAP_1.CREATE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0B"; "0BL"; "0C"; "1None"; "1Some"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "2False"; "2and"; "2eq"; "2ex"]; ["2iff"; "2not"; "2or"; "3N"; "3Z"; "0D"; "0E"; "0L"; "0LS"; "0RUNp"; "4INVL"; "4MR"; "4blk"; "4bslot"; "4frontier"; "4gbase"]; ["4hosts"; "4known"; "4live_group"; "4one5"; "4sstart"; "4unknown"; "5hl_ticks"; "6nslot"; "7IB"; "7UNIT"; "7aptr"; "7cell_read"; "7cellval"; "7cptr"; "7get_head"; "7get_shadow"]; ["7get_stride"; "7ghdr"; "7lhead"; "7meta"; "7meta0"; "7optr"; "7r_hav"; "7region"; "7s_groups"; "7s_metas"; "7s_slots"; "7s_tick"; "7slot_start'"; "8In"; "9add"; "9le"]; ["9lt"; "9modulo"; "9mul"; "9sub"; "0X'"; "0a"; "0b"; "0cnt"; "0h"; "0hl"; "0i"; "0j"; "0k"; "0m"; "0mr'"; "0o"]; ["0p"; "0q"; "0r"; "0rid"; "0s"; "0st"; "0st'"; ":lookup"; ";N_countable"; ";Z_countable"; ";prod_countable"; "<prod_eq_dec"; "=gmap"; "=gmap_lookup"; ">eq_dec"; "?eq_dec"]; ["0stride'"; "0u"; "0v"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma res_excl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "J'D'>&R1r2+@%3221z%63721&QO+<%2215&A'=r4r3%7221&R0&QN%1259%3251%8251%:11p0<1p0@1pU0H1pT<I1").
Proof. intros a o.
intros Ha Ho [H1 H2]. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod o 16 ltac:(lia)) as Do.
pose proof (Z.mod_pos_bound o 16 ltac:(lia)) as Bo. rewrite Ha in Da.
set (qa := a / 16) in *. set (qo := o / 16) in *. set (r := o mod 16) in *. clearbody qa qo r. lia.
Qed.
Section SE.
Variables (A B E : Prop).
Variables (C D : Prop).
Lemma one5_iff_create : one5 A B False False E -> ~ C -> ~ D -> one5 A B C D E.
Proof.
unfold one5. tauto. Qed.
End SE.
Section CREATE.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m p : aptr) (ai : Z) (mr' : meta).
Hypothesis INV : INVL X st L BL LS.
Hypothesis IDLE : In m (x_idle X).
Let sc' := m_sizeclass mr'.
Let last' := m_last_idx mr'.
Let cnt := last' + 1.
Let stride' := get_stride mr'.
Hypothesis R_prev : m_prev mr' = None.
Hypothesis R_next : m_next mr' = None.
Hypothesis R_mem : m_mem mr' = Some p.
Hypothesis R_freeable : m_freeable mr' = 1.
Hypothesis R_maplen : 0 <= m_maplen mr'.
Hypothesis R_li : 0 <= last' <= 31.
Hypothesis R_ai : 0 <= ai <= last'.
Hypothesis R_full0 : sc' = 0 -> ai = last'.
Hypothesis R_sc : (0 <= sc' < 48 /\ m_maplen mr' <= 256) \/ (sc' = 63 /\ last' = 0 /\ m_maplen mr' <> 0).
Hypothesis R_masks : 0 <= m_avail mr' /\ 0 <= m_freed mr'
/\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> i <= ai)
/\ (forall i, 0 <= i -> tbit (m_freed mr') i = true -> i <= last')
/\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> tbit (m_freed mr') i = true -> False)
/\ (forall i, ai < i <= last' -> tbit (m_freed mr') i = true).
Hypothesis R_stride : sc' < 48 ->
(stride' <= UNIT * size_class sc' \/ 28 <= sc') /\ (last' = 0 -> m_maplen mr' <> 0 /\ 27 <= sc') /\ stride' * cnt < 2^20.
Hypothesis R_stride16 : 16 <= stride' /\ stride' mod 16 = 0.
Hypothesis R_align : 0 <= snd p /\ snd p mod UNIT = 0.
Hypothesis X_fresh : x_fresh X' = Some m \/ (sc' = 63 /\ x_fresh X' = x_fresh X).
Hypothesis X_fresh_old : x_fresh X = None.
Hypothesis X_idle : forall x, In x (x_idle X') -> In x (x_idle X) /\ x <> m.
Hypothesis X_zomb : x_zomb X' = x_zomb X.
Hypothesis X_nozomb : x_zomb X = [].
Hypothesis X_part : forall i, 0 <= i <= last' ->
one5 (tbit (m_avail mr') i = true) (tbit (m_freed mr') i = true) False False (x_pend X' = Some (fst p, snd p + UNIT + stride' * i)).
Hypothesis X_pend' : forall s, x_pend X' = Some s -> exists i, 0 <= i <= last' /\ s = (fst p, snd p + UNIT + stride' * i).
Hypothesis NOPART : ai < last' -> LS (LActive sc') = [].
Hypothesis SITE :
(m_maplen mr' <> 0 /\ snd p = 0 /\ x_orph X = Some (fst p) /\ x_orph X' = None /\ x_pend X = None
/\ exists r, s_regions st !! (fst p) = Some r /\ r_kind r = RKGroup /\ m_maplen mr' * 4096 = round_up_pg (r_len r)
/\ snd p + UNIT + stride' * cnt <= m_maplen mr' * 4096)
\/ (m_maplen mr' = 0 /\ x_pend X = Some p /\ x_pend X' = None /\ x_orph X' = x_orph X /\ x_orph X = None
/\ exists pm ip bpm, s_slots st !! p = Some (pm, ip) /\ hosts st bpm pm /\ fst bpm = fst p /\ 0 <= ip <= m_last_idx (MR st pm)
/\ p = (fst bpm, sstart (MR st pm) ip)
/\ snd p + UNIT + stride' * cnt <= sstart (MR st pm) ip + get_stride (MR st pm)
/\ sc' < m_sizeclass (MR st pm) < 48 /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
/\ (exists v3, known st (fst p, snd p - 3) v3 /\ Z.land v3 31 = ip /\ 0 <= v3 < 256)
/\ known st (fst p, snd p - 2) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 0)
/\ known st (fst p, snd p - 1) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 1)
/\ 0 <= (snd p - snd bpm - UNIT) / UNIT < 2^16).
Hypothesis SH_hdr0 : forall i, 0 <= i <= cnt -> known st (fst p, snd p + UNIT + stride' * i - IB) 0.
Hypothesis SH_ghdr : forall o v tk, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, tk) -> (tk < s_tick st)%N.
Hypothesis E_metas : s_metas st' = <[m := mr']> (s_metas st).
Hypothesis E_groups : s_groups st' = <[p := mkGhdr (Some m) ai]> (s_groups st).
Hypothesis E_slots : forall s, s_slots st' !! s =
if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride' =? 0) && ((snd s - snd p - UNIT) / stride' <? cnt)
then Some (m, (snd s - snd p - UNIT) / stride') else s_slots st !! s.
Hypothesis E_shadow : s_shadow st' = s_shadow (hdr_havoc p st).
Hypotheses (E_regions : s_regions st' = s_regions st) (E_areas : s_areas st' = s_areas st) (E_next_rid : s_next_rid st' = s_next_rid st)
(E_tick : s_tick st' = s_tick st) (E_secret : s_secret st' = s_secret st) (E_reserved : s_reserved st' = s_reserved st).
Hypothesis E_ctx :
c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st)
/\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st) /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st)
/\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st) /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st)
/\ c_active (s_ctx st') = c_active (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st)
/\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st).
Hypothesis E_mc : 0 <= c_mmap_counter (s_ctx st') < 2^32.
Hypothesis E_usage : forall sc0, 0 <= sc0 < 48 -> usage st' sc0 = usage st sc0 + (if sc0 =? sc' then cnt else 0).
Hypothesis E_usage_keys : forall sc0 v, c_usage (s_ctx st') !! sc0 = Some v -> 0 <= sc0 < 48.
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Ltac slim := try clear SITE; try clear E_ctx; try clear E_slots; try clear X_part; try clear X_pend'; try clear R_masks; try clear R_stride; try clear R_sc;
try clear E_usage; try clear E_usage_keys; try clear SH_hdr0; try clear SH_ghdr; try clear X_idle; try clear NOPART.
Local Tactic Notation "lia" := slim; Lia.lia.
Local Tactic Notation "nia" := slim; Lia.nia.
Lemma m_meta0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "M'>'8'QC%211&RG&Q:'RL&RK'C&RN'D&RO%544321&RJ&RH&RI%36872651%;4<51?&RM%14>73AvR=&QIvRE%211%D6CF7541(5&QD%22I1%L3I41"). Proof. exact (proj1 (im_idle _ _ _ IM m IDLE)). Qed.
Lemma m_unlisted : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ";'QB&A&QM&Q:vR=vHr1%211%63541%811pTB:1"). Proof. intros h. intros H. apply (proj2 (im_idle _ _ _ IM m IDLE)). exists h. exact H. Qed.
Lemma MRm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "8'>'QC&KvREvR=%3221&QD%73621"). Proof. unfold MR, get_meta_rec. rewrite m_meta0. reflexivity. Qed.
Lemma m_not_live : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "6&A&Q2vREvR=%3221%511"). Proof. exact (idle_not_live _ _ _ _ _ INV m IDLE). Qed.
Lemma C_MR x : MR st' x = if aptr_eqb x m then mr' else MR st x.
Proof. unfold MR, get_meta_rec. rewrite E_metas. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
Lemma C_MR_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "A&Q:&A'>r1vR=%33521%511'QC&KvRFr2%3221vRE%5213%<3731p091pV8@1"). Proof. intros x. intros NE. rewrite C_MR, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma C_MR_m : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "8'>'QC&KvRFvR=%3221vR>%73621"). Proof. rewrite C_MR, aptr_eqb_refl. reflexivity. Qed.
Lemma C_keys : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q6&Q:&@&A'>'8'QC%211&RG'RL&RK'C&RN'D&RO%544321&RJ&RH&RI%36872651%;4C51>&RM%14E73@r1&QIvRF%211%C6JE7541(4%11G%J3G31%L11vRE%911%J6Q1L><;1%O3L16%Q111%Q3261pV8Q51").
Proof. intros x. rewrite E_metas. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite lookup_insert_eq, m_meta0; split; discriminate| rewrite lookup_insert_ne by congruence; tauto]. Qed.
Lemma p_free : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "L'>'8'QA%211&RG&Q:'RL&RK'C&RN'D&RO%544321&RJ&RH&RI%36872651%;4<51?&RM%14>73AvR@&QHvRE%211%D6CF7541(4%11H%K3H31").
Proof.
destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & _)].
- destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). apply NG. reflexivity.
- destruct Hpm as [aipm Hpm]. pose proof (is_part _ _ _ IS _ _ _ ip Hpm Hip) as P. cbn zeta in P.
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm)), <- Ep, HP in P. unfold one5 in P.
destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.
Lemma C_groups b : s_groups st' !! b = if aptr_eqb b p then Some (mkGhdr (Some m) ai) else s_groups st !! b.
Proof. rewrite E_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
Lemma C_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "H&Q:&@&Q0vRFr2r1%43321'B'='>vR@%23;71vR=%43=81%6231&A%115vRE%@31>=%;231%=261%D2?1pV8F1pT>G1").
Proof. intros b x.
unfold hosts. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
- split; [intros [a H]; inversion H; auto| intros [[_ ->]|[NE _]]; [exists ai; reflexivity| congruence]].
- split; [intros H; right; auto| intros [[E _]|[_ H]]; [congruence| exact H]].
Qed.
Lemma C_hosts_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "<&Q:&Q0vREr2r1%43321vRFr3%73215p041pV8:1pT>;1").
Proof. intros b x. intros H. apply C_hosts. destruct (aptr_eq_dec b p) as [->|NE]; [| right; auto]. destruct H as [a H]. rewrite p_free in H. discriminate. Qed.
Lemma C_hosts_old_ne : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ">&Q:&Q0vREr2r1%43321&A'>vR=%23961%411p061pV8<1pT>=1").
Proof. intros b x. intros H ->. exact (m_not_live (ex_intro _ b H)). Qed.
Lemma C_MR_hosted : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "@&Q:&Q0vREr2r1%43321'>'QC&KvRF%2217%3298%63521p081pV8>1pT>?1").
Proof. intros b x. intros H. apply C_MR_other. exact (C_hosts_old_ne b x H). Qed.
Lemma gbase' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "7'>&Q:&OvR>%211vR@%63521"). Proof. unfold gbase. rewrite R_mem. reflexivity. Qed.
Lemma sstart' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "C'D'>&Q4vR>r1%3221&QN&;'CvR@%332:1&Q9%6221&R2vS0%221;%:241%@3A<1pTFB1"). Proof. intros i. unfold sstart. rewrite gbase'. reflexivity. Qed.
Lemma slot' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "H'D'>&Q:&QLvR>r1%3221(9'C&6vR@%233;1&QN&;%136>4&Q9%4221&R2vS0%221>%8241%>4=E:1%E3D@1pTFG1"). Proof. intros i. rewrite slot_start'_sstart, gbase', sstart'. reflexivity. Qed.
Definition nslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j).
Lemma C_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "R9&Q:'B'='>'8':'D%2271%411&RG'RL&RK'C&RN&RO%443291&RJ&RH&RI%36762=51%:4D51=&RM%14F73?r1&QJvRF%211%B6KD7541vRE%511%E6NG:871%L3G41&A&Q7%11;%311%Q2251'?&QOz%221A&R0vR7%22D1%Q:241r2(9&6vR@%23Q5Q;1&QN&;%13Q8Q>4&Q9%4221&R2vS0%221Q2%8241%=4Q?QE:1%QI3QL?1%QD6QMQFQ9Q7@Q3(5vR=%B4R0QJ1Q9%32QJ1%QO3QJ51%R1271%R22H1qTHQO1%Q12R01%R62Q31pU:R81").
Proof. intros s.
unfold nslot. pose proof (E_slots s) as ES. destruct R_stride16 as [SP SM]. clear - ES SP SM. subst cnt last'.
rewrite ES. clear ES. set (d := snd s - snd p - UNIT).
destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod stride' =? 0) && (d / stride' <? m_last_idx mr' + 1)) eqn:E.
- right. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
exists (d / stride'). split; [split; [apply Z.div_pos; lia| exact E4]|]. split; [| reflexivity].
pose proof (Z.div_mod d stride' ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. lia.
- left. split; [reflexivity|]. intros (j & Hj & Es). subst s. cbn in d.
assert (Ed : d = stride' * j) by (unfold d; lia). clearbody d.
rewrite N.eqb_refl in E. cbn in E.
assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
assert (E3 : (d mod stride' =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult). rewrite E3 in E. cbn in E.
assert (E4 : (d / stride' <? m_last_idx mr' + 1) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia). rewrite E4 in E. discriminate.
Qed.
Lemma C_slots_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q5&Q:&A&Q7r1%211%411'>'8':'D%22:1%411&RG'RL&RK'C&RN&RO%443291&RJ&RH&RI%36762=51%:4G51=&RM%14I73?r2&QJvRF%211%B6ND7541vRE%511%E6Q1G:871%L3G41p0N1pU:Q41").
Proof. intros s. intros N. destruct (C_slots s) as [[E _]|(j & Hj & Es & _)]; [exact E|]. exfalso. apply N. exists j. auto. Qed.
Lemma C_slots_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "QI'D'=&QOzr1%3221&R0vR7%2241%8241'>'8':&Q:%221>%411&RG'C%621B'RL&RK&RN&RO%3462G1&RJ&RH&RI%36:62K51%94?51>&RM%14A73@(9&6vR@%23AQ21&QN&;%13DQ54&Q9%4221&R2vS0r2%3221%9251%>4LQ=;1&QJvRF%211%Q16OQ3EC41(5vR=%E4Q7QD1:%32Q71%Q<3Q751p0Q>1pTHQH1").
Proof. intros j.
intros Hj. destruct (C_slots (fst p, snd p + UNIT + stride' * j)) as [[_ N]|(j' & Hj' & Es & E)]; [exfalso; apply N; exists j; auto|].
rewrite E. inversion Es. destruct R_stride16 as [SP _]. assert (j' = j) by (clear - H0 SP Hj Hj'; nia). subst. reflexivity.
Qed.
Lemma new_key_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "O'D'=&QOzr1%3221&R0vR7%2241%8241&;'CvR@%332=1&QN&Q9%2231&R2vS0r2%3221%7251%@291+@%:231%827B%<2:1%I231%K261p0D1pTHN1").
Proof. intros j. intros Hj. destruct R_stride16 as [SP _]. clear - Hj SP. subst cnt last'. unfold UNIT. split; [nia|]. assert (stride' * j + stride' <= stride' * (m_last_idx mr' + 1)) by nia. lia. Qed.
Lemma old_slot_not_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q:&Q:'D'>'8':%1254%311&RG'RL&RK'C&RN&RO%4432<1&RJ&RH&RI%36762@51%:4B51=&RM%14D73?r3&QJvRE%211%B6ID7541(5(9r2r1%34NM21%52J1%N3J71&A&Q7r4%211%411p061pTFQ61pV8Q81pU:Q91").
Proof. intros s x i.
intros Hs (j & Hj & ->). destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es. inversion Es.
destruct (new_key_range j Hj) as [K1 K2].
destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hf & Hip & Ep & FIT & _)].
-
destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx]. rewrite (NG bx) in Hxx; [discriminate|]. rewrite <- H0. reflexivity.
-
destruct Hpm as [aipm Hpm'].
assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
assert (Hf2 : fst bx = fst bpm) by (rewrite Ep in H0; cbn in H0; congruence).
assert (Hi2 : 0 <= i <= m_last_idx (MR st x) + 1) by (clear - Hi; lia).
pose proof (@sep_hdr0 _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi2) as D.
rewrite sstart_succ in D. rewrite Ep in H1, K1, K2, FIT. cbn in H1, K1, K2, FIT.
assert (NEQ : x <> pm \/ i <> ip).
{ destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->. clear - H1 K1. lia. }
specialize (D NEQ). clear - D H1 K1 K2 FIT Hj. lia.
Qed.
Lemma old_hosts_not_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ">&Q:&Q0vREr2r1%43321&A&Q7r3%211%411p061pV8<1pT>=1").
Proof. intros b x.
intros Hx N. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO).
destruct (Z.eq_dec (m_maplen (MR st x)) 0) as [Hml|Hml].
- destruct (g_nest _ _ _ _ _ _ GO Hml) as (px & ix & Hs & _). exact (old_slot_not_new _ _ _ Hs N).
- destruct (g_top _ _ _ _ _ _ GO Hml) as [B0 _]. destruct N as (j & Hj & ->). cbn in B0. destruct (new_key_range j Hj) as [K1 K2]. destruct R_align as [A0 _]. clear - B0 K1 A0. lia.
Qed.
Lemma p_not_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "5&A&Q7vR@%211%411").
Proof. intros (j & Hj & E). destruct (new_key_range j Hj) as [K _]. apply (f_equal snd) in E. cbn in E. clear - K E. lia. Qed.
Lemma blk_not_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ">&L&QMr1v2%33421&A&Q7&Mr2%211%411%611p081pTJ=1").
Proof. intros k. intros Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). exact (old_slot_not_new _ _ _ Hs). Qed.
Lemma new_not_group : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "QG'D'=&QOzr1%3221&R0vR7%2241%8241'>'8'QA%211&RG':'C%221A'RL&Q:&RK&RN&RO%3472G1&RJ&RH&RI%36;62K51%:4951@&RM%14;73B(9&6vR@%23BQ21&QN&;%13EQ54&Q9%4221&R2vS0r2%3221%9251%>4MQ=;1&QHvRE%211%Q36Q0Q5EC41(4%11Q7%Q:3Q731p0Q<1pTHQF1").
Proof. intros j.
intros Hj. destruct (s_groups st !! (fst p, snd p + UNIT + stride' * j)) as [h|] eqn:E; [| reflexivity]. exfalso.
destruct (im_hdr _ _ _ IM _ _ E) as (x & Ex & _). apply (old_hosts_not_new (fst p, snd p + UNIT + stride' * j) x); [| exists j; auto].
destruct h as [hm ha]. cbn in Ex. subst hm. exists ha. exact E.
Qed.
Lemma gcnt_C sc0 : gcnt st' sc0 = (if sc' =? sc0 then cnt else 0) + gcnt st sc0.
Proof.
rewrite !gcnt_unfold, E_groups.
rewrite (zsum_perm _ _ (Permutation_map (gterm st' sc0) (map_to_list_insert (s_groups st) p (mkGhdr (Some m) ai) p_free))). cbn.
unfold gterm at 1. cbn. rewrite C_MR_m. fold sc' cnt. f_equal.
f_equal. apply map_ext_in. intros [b hb] Hin. apply In_map_to_list_regions in Hin || (apply (proj2 (list_elem_of_In _ _)) in Hin; apply elem_of_map_to_list in Hin).
unfold gterm. cbn. destruct (g_meta hb) as [x|] eqn:Ex; [| reflexivity].
rewrite (C_MR_other x); [reflexivity|]. intros ->.
destruct (im_hdr _ _ _ IM _ _ Hin) as (x' & Ex' & Hmem & _). rewrite Ex in Ex'. inversion Ex'. subst x'. rewrite MRm in Hmem. discriminate.
Qed.
Lemma C_get_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ";'QB'>&QE&Q>vRFr1%3221vRE%5213%83731pTB:1").
Proof. intros h.
destruct E_ctx as (_ & _ & F3 & _ & _ & _ & _ & _ & _ & _ & F11 & _). destruct h; cbn; unfold active, ctx; rewrite ?F11, ?F3; reflexivity.
Qed.
Lemma C_frontier : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ">'C'QG'>'D&NvRFr2r1%43321vRE%63143%93831pU6;1pU8=1").
Proof. intros rid r. destruct E_ctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _). unfold frontier. rewrite F10. reflexivity. Qed.
Lemma C_TK : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q5'D'7':'C%2241%411'>'8%113&RG'RL&RO&RI%34=218&RM%14?43:r2&QF&Q?vRE&6vR@%23CF1%5241%711%@6ID<:91(5r1%22G1%G3E41&Q6&QK%11=%32A1p051pTDN1pV4Q41").
Proof. intros u hl.
intros Hu ch Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn in Hu.
- exact (proj1 (proj2 (ish_ticks _ _ ISH _ _ E)) u hl ch Hu Hin).
- rewrite lookup_empty in Hu. discriminate.
Qed.
Lemma C_read_out : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q9':'C'D%3221&A'='>&6r1%23871vR@%43:91%63;31&QO&;%13>=5%23?>8%4221&R0&QN+<%2261%4261%B261%C2<1%E11'Q<&Q;&Q?vRFr2%H3NM1%4231%C3Q0O3%7221vRE%8215%:214%Q03<41p0>1pU4Q51").
Proof. intros q. intros Hq. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst q) E_shadow). apply (cell_read_hdr_havoc_out p st (proj2 R_align) C_TK q Hq). Qed.
Lemma C_known_out : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q5':'C'D%3221&A'='>&6r2%23871vR@%43:91%63;31&QO&;%13>=5%23?>8%4221&R0&QN+<%2261%4261%B261%C2<1%E11&Q1vREr3%3321EvRFr4%63214p041p091pV6Q11pU4Q11").
Proof. intros q v. intros Hq K. unfold known, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
Lemma C_unknown_out : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "Q4':'C'D%3221&A'='>&6r1%23871vR@%43:91%63;31&QO&;%13>=5%23?>8%4221&R0&QN+<%2261%4261%B261%C2<1%E11&Q5vREr2%3221vRFr3%6221p041p091pU4Q01").
Proof. intros q. intros Hq K. unfold unknown, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
Lemma C_unknown_hdr : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "J'D'=&QOzr1%3221&R0+<%2241%8241&Q5vRF(9'C&6vR@%233@1&QN&;%136C4r2%4221%:49F61%=2<1p0?1pU0I1").
Proof. intros o.
intros Ho. unfold unknown, SHd. cbn [fst snd]. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst p) E_shadow).
apply (cell_read_hdr_havoc_in p st (proj2 R_align) (fst p, snd p + o)); [reflexivity| cbn; lia|].
cbn [fst snd]. intros v tk H. apply (SH_ghdr (snd p + o) v tk); [clear - Ho; lia| exact H].
Qed.
Lemma hdr0_res : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "H&Q:'D&Q0vREr3r2%43321'>&R1&R3&Q4&K%1298%3218&Q8%6221+@%9221+<%<3B21p0>1pTFD1pV8F1pT>G1").
Proof. intros b x i.
intros Hx. pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG SM]. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
unfold sstart, IB, UNIT in *. rewrite (hosts_gbase _ _ _ IM _ _ Hx).
pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma C_unknown_any : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate ":&Q:&Q5vREr1%3221vRFr2%6221p041pU491").
Proof. intros q.
intros U. destruct (N.eq_dec (fst q) (fst p)) as [E|NE]; [| apply C_unknown_out; [tauto| exact U]].
destruct (Z.lt_ge_cases (snd q) (snd p)) as [L1|G1]; [apply C_unknown_out; [lia| exact U]|].
destruct (Z.lt_ge_cases (snd q) (snd p + 12)) as [L2|G2]; [| apply C_unknown_out; [lia| exact U]].
replace q with (fst p, snd p + (snd q - snd p)) by (destruct q; cbn in *; subst; f_equal; lia). apply C_unknown_hdr. lia.
Qed.
Lemma C_known_res : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "H':'C'D%3221&QO+<&R1&;r2%23871+@%5221%8271&Q1vREr3%33218vRFr4%63214p041p091pV6D1pU4D1").
Proof. intros q v. intros R K. apply C_known_out; [| exact K]. intros [_ H]. exact (res_excl _ _ (proj2 R_align) R H). Qed.
Section SE.
Local Abbreviation SEC_T_blk_clear := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "R;&L&Q:'D&QMr3v2%33621'>'8':%1298%311&RG&Q='RL&RK'C&RN&RO%4432A1&RJ&RH&RI%36762E51%:4G51>&RM%14I73@&Mr4%211&QJvRE%211%E6DG9741(5(9r2%24Q4Q3Q11%42L1%Q03L61&6r5%?11%33KQ91vR@%53MQ;1%Q73N31'B&QO&R3&QN&;r6%J11%33Q6QD1&Q@&K%12J@%311%9251&Q8%<221%;3Q>QLB%?221+<%?231%A2<6%C221%E251p0G1p0O1p0R11pTFR61pV8R81pTJR:1")) (only parsing).
Variable k : ltac:(sec_ty2 constr:(SEC_T_blk_clear) 0%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_blk_clear) 1%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_blk_clear) 2%nat 0%nat).
Lemma blk_clear : ltac:(sec_stmt2 constr:(SEC_T_blk_clear) 3%nat 0%nat).
Proof.
intros Hk Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
destruct SITE as [(Hml & P0 & HO & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hfp & Hip & Ep & _)].
- exfalso. destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx].
rewrite (NG bx) in Hxx; [discriminate|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ a Hxx)) in Es. rewrite Es in Hf. exact Hf.
- destruct Hpm as [aipm Hpm']. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es.
assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
assert (Hf2 : fst bx = fst bpm) by (rewrite Es, Ep in Hf; cbn in Hf; exact Hf).
pose proof (is_part _ _ _ IS _ _ _ i (proj2 (hosts_ok _ _ _ IG _ _ Hx) ) Hi) as P5 || pose proof I as P5.
destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx).
pose proof (is_part _ _ _ IS _ _ _ i Hbx Hi) as Q5. cbn zeta in Q5. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx), <- Es in Q5. unfold one5 in Q5.
assert (U : In (bslot k) (map bslot BL)) by (apply in_map; exact Hk).
assert (NH2 : s_groups st !! (fst bx, sstart (MR st x) i) = None).
{ rewrite <- Es. apply none_of. intros Hh. destruct Q5 as (_ & _ & _ & _ & _ & _ & _ & _ & nCD & _). apply nCD. split; [exact U| exact Hh]. }
assert (NE : x <> pm \/ i <> ip).
{ destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->.
pose proof (is_part _ _ _ IS _ _ _ ip Hpm' Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm')), <- Ep, HP in P.
unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity].
pose proof (hosts_inj _ _ _ IM _ _ _ Hx (ex_intro _ aipm Hpm')) as Ebx. rewrite Ebx in Es. rewrite Ep, <- Es. exact U. }
pose proof (@sep_ext _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi NE NH2) as D.
rewrite !sstart_succ in D. rewrite Es. cbn [snd]. rewrite Ep. cbn [snd].
pose proof (stride_ge _ _ _ IG _ _ (ex_intro _ aipm Hpm')) as [SGp _]. unfold IB, UNIT in *. clear - D SGp. lia.
Qed.
End SE.
Theorem INVL_create : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate "8&JvIvR4vRFvGv2vH%76654321").
Proof.
destruct E_ctx as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
destruct R_masks as (W1 & W2 & W3 & W4 & W5 & W6). destruct R_stride16 as [SP SM]. destruct R_align as [P0 P16].
assert (XO : forall rid, x_orph X' = Some rid -> x_orph X = Some rid /\ m_maplen mr' = 0).
{ intros rid Ho. destruct SITE as [(_ & _ & _ & HO' & _)|(Hml & _ & _ & HO' & _)]; [rewrite HO' in Ho; discriminate| rewrite HO' in Ho; auto]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; rewrite ?E_regions, ?E_next_rid, ?E_reserved, ?F6, ?F7, ?F10, ?F15; try assumption.
+ eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite C_frontier. reflexivity.
+ intros rid r H1 H2. rewrite C_frontier. exact (ir_metalen rid r H1 H2).
+ intros rid r H1 H2. rewrite C_frontier. exact (ir_brkfront rid r H1 H2).
+ intros rid Ho. destruct (XO rid Ho) as [Ho' Hml]. destruct (ir_orph rid Ho') as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
intros b Hb. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [| exact (NG b Hb)]. exfalso.
destruct SITE as [(Hml' & _)|(_ & _ & _ & _ & HO0 & _)]; [exact (Hml' Hml)| rewrite HO0 in Ho'; discriminate].
- destruct IA; constructor; rewrite ?E_regions, ?E_areas, ?E_secret, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14; try assumption.
+ destruct ia_ctx as (_ & C2 & C3 & C4). split; [exact E_mc|]. auto.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite C_frontier. auto.
+ intros x mr Hx. assert (K : s_metas st' !! x <> None) by congruence. apply C_keys in K. destruct (s_metas st !! x) as [mr0|] eqn:E; [| congruence]. exact (ia_metas x mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply C_keys in K. apply K. apply Hk. exact Hk2.
+ intros sc0 Hsc0. rewrite (E_usage sc0 Hsc0), (ia_usage sc0 Hsc0), gcnt_C. rewrite Z.eqb_sym. destruct (sc' =? sc0); lia.
- destruct IM as [Q1 Q2 Q3 Q4 Q5] eqn:EIM; constructor.
+ intros x Hx. destruct (aptr_eq_dec x m) as [E|NE]; [subst x; rewrite C_MR_m, R_mem in Hx; discriminate|]. rewrite (C_MR_other x NE) in Hx |- *. exact (Q1 x Hx).
+ intros x b Hx. rewrite X_zomb. destruct (aptr_eq_dec x m) as [E|NE].
* subst x. rewrite C_MR_m, R_mem in Hx. inversion Hx. subst b. left. apply C_hosts. left. auto.
* rewrite (C_MR_other x NE) in Hx. destruct (Q2 x b Hx) as [H|H]; [left; apply C_hosts_old; exact H| right; exact H].
+ intros b h. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
* intros E. inversion E. subst h. exists m. cbn. rewrite C_MR_m, R_mem. fold last'. auto.
* intros Hb. destruct (Q3 b h Hb) as (x & Ex & Hmem & Hai). exists x.
assert (NEx : x <> m) by (intros ->; rewrite MRm in Hmem; discriminate). rewrite (C_MR_other x NEx). auto.
+ intros x Hx. destruct (X_idle x Hx) as [Hx' NE]. destruct (Q4 x Hx') as [E NI]. split; [| exact NI]. rewrite E_metas, lookup_insert_ne by congruence. exact E.
+ intros z Hz. rewrite X_zomb, X_nozomb in Hz. destruct Hz.
- destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
+ intros h. rewrite C_get_head. apply L1.
+ intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
eapply linked_ext; [| | exact D]; intros x Hx; rewrite C_MR_other; try reflexivity; intros ->; apply (m_unlisted h); rewrite E.
* apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
* apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
+ intros x. destruct (aptr_eqb_spec x m) as [->|NE].
* rewrite C_MR_m, R_next, R_prev. split; [| reflexivity]. split; [intros [h H]; exfalso; exact (m_unlisted h H)| intros H; exfalso; apply H; reflexivity].
* rewrite (C_MR_other x NE). apply L5.
+ intros x Hx. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE). apply L6. exact Hx.
+ intros sc x Hx. destruct (L7 sc x Hx) as (A1 & [b Hb] & A3).
destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE).
split; [exact A1|]. split; [exists b; apply C_hosts_old; exact Hb| exact A3].
- destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
+ intros x b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
*
intros E. inversion E. subst x aix. constructor; rewrite ?C_MR_m, ?E_regions; fold sc' last' stride'.
-- apply C_keys. rewrite m_meta0. discriminate.
-- exact R_li.
-- exact R_ai.
-- destruct R_sc as [A|(A1 & A2 & A3)]; [left; exact A| right]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros [h H]. exact (m_unlisted h H).
-- exact R_freeable.
-- exact R_maplen.
-- exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 W6))))).
-- intros NF Hlt. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)|]. destruct R_sc as [[A _]|(_ & L0 & _)]; unfold sc' in *; lia.
-- intros NF Hsc NI. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
-- intros NF sc Hin Hnh. exfalso. exact (m_unlisted _ Hin).
-- exact R_stride.
-- intros NF Hsc LT. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
-- exact (conj P0 P16).
-- intros Hml. destruct SITE as [(_ & B0 & _ & _ & _ & r & Hr & Hk & Hlen & Hend)|(Hml0 & _)]; [| exfalso; exact (Hml Hml0)].
split; [exact B0|]. exists r. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|].
unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact Hend.
-- intros Hml. destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & FIT & Hsc & Hstr & _)]; [exfalso; exact (Hml1 Hml)|].
exists pm, ip. rewrite (C_MR_hosted _ _ Hpm). split; [rewrite C_slots_old; [exact Hs| exact p_not_new]|].
rewrite (hosts_gbase _ _ _ IM _ _ Hpm). split; [exact Hf|]. split; [| split; [exact Hsc| exact Hstr]].
unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact FIT.
-- exact R_full0.
*
intros Hb. pose proof (G1 x b aix Hb) as GO. assert (Hx : hosts st b x) by (exists aix; exact Hb).
pose proof (C_hosts_old_ne _ _ Hx) as NEx. assert (NF : x_fresh X <> Some x) by (rewrite X_fresh_old; discriminate).
assert (NF' : x_fresh X' <> Some x) by (destruct X_fresh as [XF|[_ XF]]; rewrite XF; [congruence| rewrite X_fresh_old; discriminate]).
destruct GO; constructor; rewrite ?(C_MR_other x NEx), ?E_regions; try assumption.
-- apply C_keys. exact g_present.
-- intros _. exact (g_partial NF).
-- intros _. exact (g_unlisted NF).
-- intros _. exact (g_rest NF).
-- intros _. exact (g_under NF).
-- intros Hml. destruct (g_nest Hml) as (px & ix & Hs & REST). exists px, ix.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
split; [rewrite C_slots_old; [exact Hs| exact (old_slot_not_new _ _ _ Hs)]| exact REST].
+ intros b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb]; [discriminate| exact (G2 b aix)].
+ intros m1 m2 b1 b2 ai1 ai2. rewrite !C_groups.
destruct (aptr_eqb_spec b1 p) as [->|N1]; destruct (aptr_eqb_spec b2 p) as [->|N2].
* intros E1 E2. inversion E1. inversion E2. subst. reflexivity.
* intros E1 H2. inversion E1. subst m1 ai1. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai2 H2)). fold last' sc'. intros P1 P2 Esc.
exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H2) ltac:(rewrite X_fresh_old; discriminate) P2) as IN. rewrite <- Esc, (NOPART P1) in IN. exact IN.
* intros H1 E2. inversion E2. subst m2 ai2. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai1 H1)). fold last' sc'. intros P1 P2 Esc.
exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H1) ltac:(rewrite X_fresh_old; discriminate) P1) as IN. rewrite Esc, (NOPART P2) in IN. exact IN.
* intros H1 H2. rewrite (C_MR_hosted _ _ (ex_intro _ ai1 H1)), (C_MR_hosted _ _ (ex_intro _ ai2 H2)). exact (G3 m1 m2 b1 b2 ai1 ai2 H1 H2).
+ intros rid r Hr Hk Ho. rewrite E_regions in Hr.
destruct (N.eq_dec rid (fst p)) as [->|NE].
* destruct SITE as [(Hml & B0 & HO & _)|(Hml & _ & _ & HO' & HO & _)].
-- exists m. split; [apply C_hosts; left; split; [destruct p; cbn in B0 |- *; subst; reflexivity| reflexivity]|]. rewrite C_MR_m. exact Hml.
-- destruct (G4 (fst p) r Hr Hk ltac:(rewrite HO; discriminate)) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
* assert (Ho0 : x_orph X <> Some rid).
{ destruct SITE as [(_ & _ & HO & _)|(_ & _ & _ & HO' & HO & _)]; [rewrite HO; congruence| rewrite HO; discriminate]. }
destruct (G4 rid r Hr Hk Ho0) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
+ intros b h. rewrite C_groups, E_regions. destruct (aptr_eqb_spec b p) as [->|NEb]; [| exact (G5 b h)]. intros _.
destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & _)]; [exists r; auto|].
destruct Hpm as [a Hpm]. destruct (G5 _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto.
- destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
+ intros s x i Hs. destruct (C_slots s) as [[Es NS]|(j & Hj & -> & Es)].
* rewrite Es in Hs. destruct (S1' s x i Hs) as ([b Hb] & Hi & E). rewrite (C_MR_hosted _ _ Hb). split; [exists b; apply C_hosts_old; exact Hb| auto].
* rewrite Es in Hs. inversion Hs. subst x i. rewrite C_MR_m. fold last'. split; [exists p; apply C_hosts; left; auto|]. split; [lia|]. rewrite slot'. reflexivity.
+ intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
* rewrite C_MR_m in Hi |- *. rewrite slot'. apply C_slots_new. fold last' in Hi. lia.
* rewrite (C_MR_hosted _ _ Hx) in Hi |- *. rewrite C_slots_old; [exact (S2 b x i Hx Hi)|].
apply (old_hosts_not_new_slot b x i Hx Hi) || (intros N; destruct N as (j & Hj & E); exact (old_slot_not_new _ _ _ (S2 b x i Hx Hi) (ex_intro _ j (conj Hj E)))).
+ intros b x aix i. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
* intros E Hi. inversion E. subst x aix. rewrite C_MR_m in Hi |- *. cbn zeta. rewrite slot', C_groups. fold last' in Hi.
pose proof (X_part i Hi) as P5.
eapply one5_iff_create; [exact P5| |]; cbn.
-- intros Hin. apply in_map_iff in Hin as (k & Ek & Hk). apply (blk_not_new k Hk). exists i. split; [clear -Hi; lia| exact Ek].
-- destruct (aptr_eqb_spec (fst p, snd p + UNIT + stride' * i) p) as [Eip|NE]; [exfalso; apply p_not_new; exists i; split; [clear -Hi; lia| symmetry; exact Eip]|].
rewrite (new_not_group i ltac:(clear -Hi; lia)). intros H; apply H; reflexivity.
* intros Hb Hi. assert (Hx : hosts st b x) by (exists aix; exact Hb).
rewrite (C_MR_hosted _ _ Hx) in Hi |- *. cbn zeta. rewrite C_groups.
pose proof (S3 b x aix i Hb Hi) as P5. cbn zeta in P5.
set (s := slot_start' (MR st x) i) in *.
assert (NSs : ~ nslot s) by (apply (old_slot_not_new s x i); exact (S2 b x i Hx Hi)).
destruct (aptr_eqb_spec s p) as [Esp|NEsp].
--
destruct SITE as [(_ & B0 & _ & _ & HPX & _)|(_ & HPX & HPX' & _)].
++ exfalso. rewrite Esp in *. pose proof (S2 b x i Hx Hi) as Hs. fold s in Hs. rewrite Esp in Hs.
destruct (S1' _ _ _ Hs) as ([bb Hbb] & _ & Eps). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hbb) in Eps.
pose proof (sstart0 _ _ _ IM _ _ Hbb). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hbb ltac:(lia)).
destruct (hosts_ok _ _ _ IG _ _ Hbb) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0) as [A00 _].
apply (f_equal snd) in Eps. cbn in Eps. unfold UNIT in *. clear - B0 Eps H H0 A00. lia.
++ rewrite Esp in P5 |- *. rewrite HPX in P5. rewrite HPX'.
revert P5. unfold one5. clear. intros P5.
assert (NN : ~ (@None aptr = Some p)) by discriminate. assert (SS : Some (mkGhdr (Some m) ai) <> None) by discriminate.
tauto.
-- eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P5].
split.
++ intros HPs. exfalso. destruct SITE as [(_ & _ & _ & _ & HPX & _)|(_ & HPX & _)]; rewrite HPX in HPs; [discriminate| inversion HPs; exact (NEsp (eq_sym H0))].
++ intros HPs. exfalso. destruct (X_pend' _ HPs) as (j & Hj & Ej). apply NSs. exists j. split; [fold last' in Hj; lia| exact Ej].
+ intros s Hs. destruct (X_pend' _ Hs) as (j & Hj & ->). rewrite C_slots_new; [discriminate| fold last' in Hj; lia].
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (x & i & Hs & REST). exists x, i.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hbx] & _). rewrite (C_MR_hosted _ _ Hbx).
split; [rewrite C_slots_old; [exact Hs| exact (blk_not_new k Hk)]| exact REST].
- destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
assert (REGp : exists r, s_regions st !! fst p = Some r /\ r_kind r = RKGroup).
{ destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & [a Hpm] & Hf & _)]; [exists r; auto|].
destruct (ig_region _ _ _ IG _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto. }
constructor.
+ intros rid sh. rewrite E_shadow, E_regions. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst p)) as [->|NE].
* intros _. exact REGp.
* rewrite lookup_insert_ne by congruence. exact (D1 rid sh).
+ intros rid sh Hsh. rewrite E_tick. rewrite E_shadow in Hsh. exact (TKS_hdr_havoc st p D2 rid sh Hsh).
+ intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
* rewrite C_MR_m in Hi |- *. rewrite sstart'. apply C_known_out; [| apply SH_hdr0; unfold cnt_of in Hi; fold last' cnt in Hi; exact Hi].
cbn. intros [_ H]. unfold IB, UNIT in H. destruct (Z.eq_dec i 0) as [->|NZ]; [lia|]. unfold cnt_of in Hi. assert (stride' * 1 <= stride' * i) by nia. lia.
* rewrite (C_MR_hosted _ _ Hx) in Hi |- *. apply C_known_res; [cbn; rewrite (hdr0_res _ _ i Hx); lia| exact (D3 b x i Hx Hi)].
+ intros b x o Hx Ho. apply C_hosts in Hx as [[-> ->]|[NEb Hx]]; [apply C_unknown_hdr; exact Ho| apply C_unknown_any; exact (D4 b x o Hx Ho)].
+ intros b x px ix Hx Hml Hs. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
*
rewrite C_MR_m in Hml. rewrite (C_slots_old p p_not_new) in Hs.
destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs0 & Hpm & Hf & Hip & Ep & _ & _ & _ & (v3 & K3 & E3 & R3) & K2 & K1 & Q)]; [exfalso; exact (Hml1 Hml)|].
rewrite Hs0 in Hs. inversion Hs. subst px ix. rewrite (C_MR_hosted _ _ Hpm), (hosts_gbase _ _ _ IM _ _ Hpm). cbn zeta.
split; [exists v3; split; [apply C_known_out; [cbn; lia| exact K3]| auto]|].
split; [apply C_known_out; [cbn; lia| exact K2]|]. split; [apply C_known_out; [cbn; lia| exact K1]| exact Q].
* rewrite (C_MR_hosted _ _ Hx) in Hml. rewrite (C_slots_old b (old_hosts_not_new _ _ Hx)) in Hs.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
destruct (D5 b x px ix Hx Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx). pose proof (g_align _ _ _ _ _ _ GOx) as [A0 A16]. unfold UNIT in A16.
assert (RS : forall d r, 0 <= r < 16 -> d = r - 16 -> 12 <= r -> 12 <= (snd b + d) mod 16).
{ intros d r Hr -> H12. pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as Db. rewrite A16 in Db.
replace (snd b + (r - 16)) with (r + (snd b / 16 - 1) * 16) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. exact H12. }
split; [exists v3; split; [apply C_known_res; [cbn; replace (snd b - 3) with (snd b + (13 - 16)) by lia; apply (RS _ 13); lia| exact K3]| auto]|].
split; [apply C_known_res; [cbn; replace (snd b - 2) with (snd b + (14 - 16)) by lia; apply (RS _ 14); lia| exact K2]|].
split; [apply C_known_res; [cbn; replace (snd b - 1) with (snd b + (15 - 16)) by lia; apply (RS _ 15); lia| exact K1]| exact Q].
+ intros k x i Hk Hs. rewrite (C_slots_old _ (blk_not_new k Hk)) in Hs.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es). rewrite (C_MR_hosted _ _ Hx).
pose proof (D6 k x i Hk Hs) as B. cbn zeta in B |- *. destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (OUT : forall o, snd (bslot k) - IB <= o < snd (bslot k) + get_stride (MR st x) - IB -> ~ (fst (bslot k) = fst p /\ snd p <= o < snd p + 12)).
{ intros o Ho [Hf Hin]. pose proof (blk_clear k x i Hk Hs Hf) as D. unfold IB in *. clear - Ho Hin D. lia. }
destruct (is_blocks _ _ _ IS k Hk) as (x' & i' & Hs' & Hoff & Hn & Hfit). rewrite Hs in Hs'. inversion Hs'. subst x' i'.
pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG _]. unfold IB, UNIT in *.
assert (K : forall o v, snd (bslot k) - 4 <= o < snd (bslot k) + get_stride (MR st x) - 4 -> known st (fst (bslot k), o) v -> known st' (fst (bslot k), o) v).
{ intros o v Ho Ko. apply C_known_out; [apply (OUT o Ho)| exact Ko]. }
split; [apply K; [lia| exact A1]|]. split; [apply K; [lia| exact A2]|]. split; [apply K; [lia| exact A3]|]. split; [apply K; [lia| exact A4]|].
split; [exact A5|]. split.
* intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). split; [apply K; [lia| exact B1]|]. split; [apply K; [lia| exact B2]|]. split; [apply K; [lia| exact B3]|].
split; [apply K; [lia| exact B4]|]. split; [apply K; [lia| exact B5]| exact B6].
* split; [intros Hr; apply K; [lia| apply A7; exact Hr]|]. intros a Ha. apply C_unknown_any. apply A8. exact Ha.
Qed.
End CREATE.
End CEIL_WRAP_1.
