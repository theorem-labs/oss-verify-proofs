(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require KStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_A2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_A2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0A'"; "1Some"; "1fst"; "1length"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3N"; "3Z"; "0L"]; ["0P"; "4asegs"; "5agree_on"; "6area_rep"; "6group_rep"; "6lr_lo"; "6meta_cells"; "6pw"; "6ticks_ok"; "7mem"; "7optr_in"; "7ptrs_in"; "8u64arr"; "8u8arr"; "9cell"; "9cells_size"]; [":mmap_len"; ";bytes_at"; ";wr_at"; "<rw_cells"; "=Known"; "=aptr"; "=area"; "=brkstate"; "=c_active"; "=c_avail_meta"; "=c_avail_meta_areas"; "=c_brk"; "=c_free_meta_head"; "=c_meta_area_head"; "=c_meta_area_tail"; "=cell_read"]; ["=cellval"; "=conc"; "=get_meta_rec"; "=get_shadow"; "=ghdr"; "=hdr_havoc"; "=m_mem"; "=m_next"; "=m_prev"; "=mctx"; "=meta"; "=mstate"; "=optr"; "=put_group"; "=put_meta"; "=r_base"]; ["=r_len"; "=region"; "=round_up_pg"; "=s_areas"; "=s_groups"; "=s_regions"; "=set_slots"; "=set_tick"; "=shadow"; "=shadow0"; "=step_seq"; "=upd_ctx"; ">add"; ">le"; ">modulo"; ">mul"]; [">of_nat"; "0a"; "0ai"; "0ar"; "0b"; "0bs"; "0c"; "0cs"; "0f"; "0g"; "0gh"; "0l"; "0m"; "0m'"; "0mo"; "0mr"]; ["0n"; "0n'"; "0o"; "0off"; "0p"; "0q"; "0r"; "0r0"; "0rid"; "0rq"; "0st"; "0st'"; "?delete"; "?insert"; "?lookup"; "@bv"]; ["AN_countable"; "AZ_countable"; "Aprod_countable"; "Bprod_eq_dec"; "Cmap_delete"; "Cmap_insert"; "Dgmap"; "Dgmap_lookup"; "Dgmap_partial_alter"; "Eeq_dec"; "Feq_dec"; "0t"; "0v"; "0ws"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.
Lemma pw_extP : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "B&QL&Jv@r1%3221':'S?yR0%211&GvS;r2%3221vS:%5213%:3731p0<1pV:A1").
Proof. intros p. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.
Lemma get_meta_rec_extP : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 ";&Q5':'QJ&QBvS;r1%3221vS:%5213%83731pUD:1").
Proof. intros g. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.
Lemma meta_cells_extP : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "?&Q5':'5'N%211&FvS;&QBvS:r1%3221%6251%7242%<3921pUD>1").
Proof. intros g.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !pw_extP by assumption. reflexivity.
Qed.
Lemma area_rep_extP : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q@'S?yR0%211'6y8%511%311p051&Q5'Q6':%812&S>'SF&SC'=&SI'>&SJ%544321&SB&S@&SA%36872651%;4@51?&SG%14B73Ar2&R3vS:%211%C6GF7541(2r1%22I1%I3H41&Cr4r3%34:21<vS;r5%642154p041p091pU8Q41pU4Q61pUJQ81").
Proof. intros m a ar.
intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
destruct (H9 a ar Ha) as [Pa Pn].
unfold area_rep. rewrite (Hconc a Pa). rewrite (pw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
intros k Hk. rewrite get_meta_rec_extP, meta_cells_extP. apply A2. exact Hk.
Qed.
Lemma group_rep_extP : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q@'S?yR0%211'6y8%511%311p051&Q5'QD':%812&S>'SF&SC'=&SI'>&SJ%544321&SB&S@&SA%36872651%;4@51?&SG%14B73Ar2&R4vS:%211%C6GF7541(2r1%22I1%I3H41&Dr4r3%34:21<vS;r5%642154p041p091pUFQ41pU:Q61pUJQ81").
Proof. intros m b gh.
intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (pw_extP _ Pg). auto.
Qed.
End PEXT.
Definition agree_on (m m' : mem) (A n : Z) : Prop :=
forall a, A <= a < A + n -> m' (wa a) = m (wa a).
Lemma bytes_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q1'S?yR0%211'6y8%511%311p051&I'>'5%116&Q1&Ar4r2r1%544321&Br5r3&R@&4%12B8%311%746;51%>4=7<6p021p0;1pU<B1p2E1pULG1pUJI1").
Proof. intros m m' A bs.
intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
Lemma wr_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "K'S?yR0%211'6y8%511%311p051&I'>&Q2&Ar4r2r1%544321&Br5r3%342716%:49382p021p071pV2>1p2?1pULA1pUJC1").
Proof. intros m m' A n.
intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.
Lemma rw_cells_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q2'S?yR0%211'6y8%511%311p051&I'>'5'N%211&Q3&Ar4r2r1%544321&Br5r3&R@&O%118%311%746;51%>4=7<6p021p0;1pU@B1p2F1pULH1pUJJ1").
Proof. intros m m' A cs.
intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_agree; eauto.
Qed.
Lemma u64arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q4'S?yR0%211'6y8%511%311p051&I'>'5%119&L&Ar4r2r1%544321&Br5r3&R?+8&R@&4%12G:%311%6251%:49>81%A4@:?9p021p0>1pWLE1p2H1pULJ1pUJL1").
Proof. intros m m' A ws.
intros [HB HW] AG. split.
- eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply wr_at_agree; [exact HW|]. exact AG.
Qed.
Lemma u8arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q1'S?yR0%211'6y8%511%311p051&I'>'5%116&M&Ar4r2r1%544321&Br5r3&R@&4%12B8%311%746;51%>4=7<6p021p0;1pU<B1p2E1pULG1pUJI1").
Proof. intros m m' A bs. intros [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.
Lemma agree_on_sub : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "J&I'>&Br6r5r4r3%544321&R=%1253&R<%1265%2298%5221r9r8%>421<;p041p091p0<1pV4C1p4D1pV2E1p2F1pULH1pUJI1").
Proof. intros m m' A n A' n'. intros AG H1 H2 a Ha. apply AG. lia. Qed.
Lemma mmap_len_round_up : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "9'>':&Q0r1%211&R2%113%63731pUH81").
Proof. intros l. unfold mmap_len. symmetry. apply KStep.round_up_pg_eq. Qed.
Lemma round_up_pg_mod : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 ";'>':&R>&R2r1%211+TP0%5221z%83921pWN:1").
Proof. intros x. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. Qed.
Lemma cell_read_shadow0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "<'>':'Q@&Q?&R9r1%3221(Q4z%211%93841pV6;1").
Proof. intros o. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.
Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).
Lemma nr_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "E':'SF'=&SI&S@'R1%544321&R5vS;%211&S=&SE&SH%14;:98%34<981vS8vS7vS:%;11%97A>=5431%D3>;1").
Proof. reflexivity. Qed.
Lemma nr_lookup_new : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "E':'6'R1%211&S>'='SF&SI&S@%344217&SG%146439vS8&R5vS;%211%<6;>7541(2vS7%22A1%D3A41").
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
Lemma nr_lookup_old : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "L'=&;':r1vS8%33521%511'6'R1%211&S>'SF&SI&S@%34>216&SG%14@438r2&R5vS;%211%;6E=7541vS:%511%>6H@:871%G3@41p0D1pV<K1").
Proof. intros q. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma nr_lookup_inv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q9'='R1':'6%113&S>'SF&SI&S@%349218&SG%14;43:r2&R5vS;%211%;6@?7541(2r1%22B1%B3@41'<'9r3vS8%G3I21vS7%I3J?1%6231&;%115vS:%C11%L6Q1Q0HF:1%A2Q1F%Q13O21%>261%@291p0B1pV>Q61pV<Q81").
Proof. intros q r.
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite nr_lookup_new in H. inversion H. auto.
- right. rewrite nr_lookup_old in H by exact NE. auto.
Qed.
Lemma nr_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "E'8'='>%3221&;':&3r1%23761vS8%53921%711&QAvS;r2%3221vS:%5213%=3@31p081pV<A1").
Proof. intros q. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.
Lemma nr_conc_new : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "?'>':&QAvS;(7'=vS8r1%443821%7261&R<vSN%2215%<3=41pV8>1").
Proof. intros off. unfold conc, get_region. cbn [fst snd]. rewrite nr_lookup_new. reflexivity. Qed.
Lemma nr_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 ";'=':'R8&QCvS;r1%3221vS:%5213%83731pV<:1").
Proof. intros q. reflexivity. Qed.
Lemma nr_lr_lo_new : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "6&R=vSN&EvS7%211%5241").
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.
Lemma nr_old_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q:'='R1':'6%113&S>'SF&SI&S@%349218&SG%14;43:r2&R5vS:%211%;6@?7541(2r1%22B1%B3@41'<&R=&R<vSNv?%3221&E%11@%7231&QO%11C&R2&R0%11F%311%=251%?21=%A291p0C1pV>Q71pV<Q91").
Proof. intros q r.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.
Lemma ticks_ok_new_region : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "6&HvS:%211vS;%411p031").
Proof. intros H. exact H. Qed.
Lemma ptrs_in_new_region : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "<'=!p021&Kr1vS:%3221r2vS;%6221p041pQ291").
Proof. intros P. intros H. exact H. Qed.
End NEWREGION.
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Lemma dr_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "D':'SF'=&SI&S@'R1%544321&R5vS;%211&S<&SD&SH%14;:98%34<981vS8vS:%:11%85@<431%C3=:1").
Proof. reflexivity. Qed.
Lemma dr_lookup_inv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q4'='R1':'6%113&S>'SF&SI&S@%349218&SG%14;43:r2&R5vS;%211%;6@?7541(2r1%22B1%B3@41'9&;r3vS8%G3I21%411vS:%?11%H6MLDB61%=2MB%M3K21%;261p0=1pVDQ11pV<Q31").
Proof. intros q rq.
intros H. rewrite dr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma dr_lookup_old : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "L'=&;':r1vS8%33521%511'6'R1%211&S>'SF&SI&S@%34>216&SG%14@438r2&R5vS;%211%;6E=7541vS:%511%>6H@:871%G3@41p0D1pV<K1").
Proof. intros q. intros. rewrite dr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma dr_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "E'8'='>%3221&;':&3r1%23761vS8%53921%711&QAvS;r2%3221vS:%5213%=3@31p081pV<A1").
Proof. intros q. intros. unfold conc, get_region. rewrite dr_lookup_old by assumption. reflexivity. Qed.
Lemma dr_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "A'=&;':r1vS8%33521%511'R8&QCvS;r2%3221vS:%5213%<3731p091pV<@1").
Proof. intros q. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma ticks_ok_drop_region : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "6&HvS:%211vS;%411p031").
Proof.
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.
Lemma ptrs_in_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "@'=!p021'QK&Kr3r2%3221r4&R7%1245%7231p051pWH=1pVF;1pQ2=1").
Proof. intros P st t. intros H; exact H. Qed.
Lemma ptrs_in_upd_ctx_scalar : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "RD'=!p021'QK'QIpWN11':&QL&Q<r2r1%211%411%513%83721pU>;1&Q9r3%118%311%41:%?3>21pU>B1&Q=r4%11?%311%41A%F3E21pU>I1&Q>r5%11F%311%41H%M3L21pU>Q01&Q:r6%11M%311%41O%Q43Q321pU>Q71'SF'>&SJ&SA&Q5%544321&Q8r7%11Q:%311%41Q<%QA3621pU>QD1'Q7&Q;r8%11QB%311%41QD%QI3621pU>QL1&Kr:r9%3221r;&R;%1245%7231p051p0:1p0C1p0Q11p0Q91p0QA1p0QI1p0R11pUBR<1pVFR?1pQ2RA1").
Proof. intros P st f.
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E1, E2, E3, E4, E5, E6, E7.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9| exact H10]].
intros g. exact (H8 g).
Qed.
Lemma ptrs_in_step_seq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "?'=!p021'QK&Kr2r1%3221r3&R:%115%7231p051pVF:1pQ2<1").
Proof. intros P st. intros H. unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply ptrs_in_upd_ctx_scalar; [..|exact H]; reflexivity). Qed.
Lemma ptrs_in_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q5'=!p021'QK&Q5'QJ&Jr4&QHr1%211%5241r5&QGr2%211%:241r6&QFr3%211%?241&Kr7%2217r8&QN%13:?4%6231p051p091p0?1p0E1pV0L1pUDN1pVFQ01pQ2Q21").
Proof. intros P st g mr.
intros Q1 Q2 Q3 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
destruct (decide (g' = g)) as [->|NE].
- rewrite lookup_insert_eq. cbn. auto.
- rewrite lookup_insert_ne by congruence. apply H8.
Qed.
Lemma ptrs_in_put_group : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "Q0'=!pWN21'QK'8'>%2261&QLr5&3r3%23;61%411&Jr6%2215&Kr7%2214r8&QMr4%248>15%7241p061p0:1p0>1pU6F1pUNE1pU:G1pVFK1pQ2M1").
Proof. intros P st b mo ai.
intros Q1 Q2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx put_group set_groups s_metas s_areas s_groups get_meta_rec] in *.
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
split; [exact H8|]. split; [exact H9|].
intros b' gh Hb'. destruct (decide (b' = b)) as [->|NE].
- rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. cbn. auto.
- rewrite lookup_insert_ne in Hb' by congruence. exact (H10 b' gh Hb').
Qed.
Lemma ptrs_in_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "A'=!p021'QK&Q5&Kr3r2%3221r4&QE%1245%7231p051pU::1pVF<1pQ2>1").
Proof. intros P st b. intros H; exact H. Qed.
Lemma ptrs_in_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A2 "N'=!p021'QK'SF&Q5&SC&SI'>&SJ%44:321&SB&S@&SA%36>72651'8%12;8%=4<731&Kr3r2%3221r4&R6%1245%7231p051pWJ:1pVFI1pQ2K1").
Proof. intros P st v. intros H; exact H. Qed.
End CEIL_WRAP_1.
