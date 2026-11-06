(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_B () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0C"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["2iff"; "2not"; "3N"; "3Z"; "4AW"; "5amo_aligned"; "0P"; "6sxv"; "7asegs"; "8agree_on"; "8ivs_avoid"; "8ivs_covered"; "9actives"; "9b8"; "9bouncess"; "9meta_cells"]; ["9meta_slot"; "9pw"; "9unmap_seqs"; "9usages"; "9wz"; ":pres_except"; ";u64arr"; ";u8arr"; "<cell"; "<cells_size"; "=ivl"; "=munch"; "=outside"; "=wmono"; ">bytes_at"; ">le4"]; ["?rw_cells"; "@active"; "@aptr"; "@aptr_eqb"; "@area"; "@bounces"; "@conc"; "@ctx"; "@del_slots"; "@get_meta_rec"; "@mctx"; "@meta"; "@mstate"; "@optr"; "@put_meta"; "@s_areas"]; ["@s_slots"; "@set_slots"; "@unmap_seq"; "@upd_meta"; "@usage"; "AIn"; "Anth_error"; "Badd"; "Ble"; "Blor"; "Blt"; "Bmodulo"; "Bmul"; "Bof_nat"; "Bpow"; "Bto_nat"]; ["0W"; "0a"; "0b"; "0bs"; "0c"; "0cs"; "0f"; "0g"; "0hi"; "0i"; "0iv"; "0lo"; "0m"; "0m'"; "0mr"; "0n"]; ["0p"; "0q"; "0r"; "0s"; "0sc"; "0st"; "0st'"; "CZ_to_bv"; "Cbv"; "Cbv_swrap"; "DN_countable"; "DZ_countable"; "Dprod_countable"; "Eprod_eq_dec"; "Fgmap"; "Geq_dec"]; ["Heq_dec"; "0v"; "0ws"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.
Lemma ivs_avoid_nil : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B ";'C!p021&J(9'<%1266%311r1%6221pQ>81").
Proof. intros P lo hi a []. Qed.
Lemma ivs_avoid_cons : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q5'C'7'<%1233%311!pW861'>&R8r5r1%3221&R:r4%2241%8241&Ar3r2%211%411p061pU4F1&J%1276(4(;r6%24LL1C%43J1@%721=p071p0:1pQ>K1pU2N1pUBQ31pUHQ41").
Proof.
intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
- inversion E; subst. apply H1. exact Ha.
- eapply H2; eauto.
Qed.
Lemma avoid_outside : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "D'7'<'C%2211%411!p041&Jr3r2%3221%312&Q<r5%2216p041p061pW8?1pQ><1pU2?1").
Proof.
induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
- intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
- apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
forall a, A <= a < A + n -> m' (wa a) = m (wa a).
Lemma munch_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "QJ'7&Q:%211'S8yR0%211':y8%511%311p051'C!p021&Q;r6r5r4%43321&Jr7%2214'>&R8r1%2291&R:&R7%12<;%3251%8251r2%<11p031pU4G1z%=21D%:2FE&R>+2+R0%3221%C251&Ir:r9%3421JOp051p0<1p0?1p0M1p0Q11pV0Q91p2Q:1pQ>Q91pULQ=1pUJQ>1pU2QG1").
Proof.
intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.
Lemma bytes_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q0'S8yR0%211':y8%511%311p051'C'7%115&Q>&Hr4r2r1%544321&Ir5r3&R=&6%12A8%311%746;51%>4=7<6p021p0;1pU8B1p2E1pULG1pUJH1").
Proof.
intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
Lemma rw_cells_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q5'S8yR0%211':y8%511%311p051'C'7'Q8%211&Q@&Hr4r2r1%544321&Ir5r3&R=&Q9%118%311%746;51&Q=r6%23?19%A4@2:?p021p061p0?1pU<F1p2J1pULL1pUJM1").
Proof.
intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_transport; eauto.
Qed.
Lemma u64arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q7'S8yR0%211':y8%511%311p051'C'7%118&Q6&Hr4r2r1%544321&Ir5r3&R<+8&R=&6%12F:%311%6251%:49>81&Q=r6%23B1<%D4C2=Bp021p061p0B1pW6I1p2L1pULN1pUJO1").
Proof.
intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.
Lemma u8arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q4'S8yR0%211':y8%511%311p051'C'7%115&Q7&Hr4r2r1%544321&Ir5r3&R=&6%12A8%311%746;51&Q=r6%23?19%A4@2:?p021p061p0?1pU8F1p2I1pULK1pUJL1").
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply bytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.
Lemma get_meta_rec_put : forall st g mr g',
get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
Lemma upd_meta_put : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "C'QL&QB'QKp011'?&R3r2r1r3%43321&QN&QI%1246%611%43816%;3?61pU>=1pU@@1pV<B1").
Proof. reflexivity. Qed.
Lemma del_slots_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "C&QB'C'QL'?&QHr4r3r2r1%544321&R1&R0%113%3215%;3<51pV<=1pU:?1pV8@1pV2B1").
Proof. reflexivity. Qed.
Lemma meta_slot_same_areas : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "O'QL&QB'?'S>&S='B&S?'C&S@%544321&S<&S:&S;%36872651'QD%<4>621&QOr2%211r3%411%C3631&Q0r4%2217%3226p021p061pU@K1pV>M1pV<N1").
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.
Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
(i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
rewrite IH by lia. f_equal. f_equal. lia.
Qed.
Lemma actives_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q3'QL'C'>&R8zr1%3221&R:+Q@%2241%8241'?':'S8yR0%211%411&R6&Lr3%211&R?r2%211%73941(2&Q1&QA%1296%32:1%52?1%D3?71p0F1pV:Q01pV<Q21").
Proof.
intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma usages_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q3'QL'C'>&R8zr1%3221&R:+Q@%2241%8241'?':'S8yR0%211%411&R6&Q3r3%211&R?r2%211%73941(2&Q4&R4%1296%311%52?1%D3?71p0F1pV:Q01pV<Q21").
Proof.
intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma bouncess_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q3'QL'C'>&R8zr1%3221&R:+Q0%2241%8241'?':'S8y8%211%411&R6&Nr3%211&R?r2%211%73941(2&M&QE%1296%311%52?1%D3?71p0F1pUDQ01pV<Q21").
Proof.
intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma unmap_seqs_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q3'QL'C'>&R8zr1%3221&R:+Q0%2241%8241'?':'S8y8%211%411&R6&Q2r3%211&R?r2%211%73941(2&M&R2%1296%311%52?1%D3?71p0F1pUDQ01pV<Q21").
Proof.
intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma actives_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B ">'QL'?'8&6'S8yR0%211&Lr1%211%7241uQ@%;3:21pV<=1").
Proof. intros st. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
Lemma usages_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B ">'QL'?'8&6'S8yR0%211&Q3r1%211%7241uQ@%;3:21pV<=1").
Proof. intros st. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bouncess_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B ">'QL'?'8&6'S8y8%211&Nr1%211%7241uQ0%;3:21pV<=1").
Proof. intros st. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
Lemma unmap_seqs_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B ">'QL'?'8&6'S8y8%211&Q2r1%211%7241uQ0%;3:21pV<=1").
Proof. intros st. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bytes_at_cons : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q4'S8yR0%211':y8%511%311p051'C'7%115&@&Q>&Hr4r3(4r2r1%33>21%847651'>(9%11B%83C71%=4<;:1&R7+1%22=1%A4@?1;%9251%D2;1pU8F1pU6L1pU4J1pUJL1").
Proof.
intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app asegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.
Lemma put_meta_put_meta_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "A'QL&QB'QK'?&QNr3r2r1r4%53421%63541%73653%93<21pU6;1pU4<1pU@>1pV<@1").
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.
Lemma aptr_eqb_neq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "@&QB&A'?r2r1%33521%511'3&QCr3%2217(5%:3521p071pU6>1pU4?1").
Proof.
intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.
Lemma aptr_eqb_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B ">&QB&@'?'3&QCr2r1%3221(=%73621%83:54%:221pU6<1pU4=1").
Proof.
intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.
Lemma get_meta_rec_put_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "?'QL&QB'QK'?&QI&QNr2r1r3%43321%6214%83914pUN:1pU@<1pV<>1").
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "G'QL&QB'QK&A'?r1r3%33621%511&QI&QNr4r5%33271r2%6221%7242%=3?21p0:1pV4B1pUNB1pU@D1pV<F1").
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.
Lemma pw_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "F'QL&QB'QK&QM'?'S8yR0%211&Q1&QNr3r2r4%43321r1%7221%8242%=3:21pV2?1pUNA1pU@C1pV<E1"). Proof. reflexivity. Qed.
Lemma conc_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "C'QL&QB'QK'?'C&QF&QNr3r2r4%43321r1%7221%8242%;3:21pV2>1pUN>1pU@@1pV<B1"). Proof. reflexivity. Qed.
Lemma ctx_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "A'QL&QB'QK'?'QJ&QG&QNr2r1r3%43321%611%713%:3921pUN<1pU@>1pV<@1"). Proof. reflexivity. Qed.
Lemma meta_slot_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "B'QL&QB'QK&Q0r4r1%3221&QNr3r5%33621r2%9221p071pV4=1pUN=1pU@?1pV<A1").
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "E'QL&QB'QK'?'7'Q8%211&O&QNr3r2r4%43321r1%7221%8242%=3:21pV6?1pUN@1pU@B1pV<D1"). Proof. reflexivity. Qed.
Definition fm_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.
Definition fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).
Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => fm_link st0 g head
| None => fm_single st0 h g
end.
Lemma queue_eq : forall R h g st0 (k : mstate -> M R) bail,
m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
queue h g st0 k bail = k (queue_st h g st0).
Proof.
intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
unfold queue_st, fm_link, fm_single. destruct (get_head st0 h); reflexivity.
Qed.
Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).
Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
intros. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.
Lemma outside_of_cover : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q6'C!p021'7'<%1255%311&R5(;r2r1%34;;21r4%63821'>&R8%1246&R:r3%2291%6241r8%11=p031pW8H1p0<1pUBJ1pUHK1&A%A1D%211&Q<%12D>p031p071pU4Q31pU2N1p4Q31").
Proof.
induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
- intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
- apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.
Lemma pres_except_of_munch' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "QE'C!pW821'7&Q:%211'S8yR0%211':y8%511%311p051&Q;r3r2r1%43321&Q=&H%23165&R5'<%12HH(;%14JJ:9r7%63421'>&R8r4%221?&R:%12AC%6231r;%11Ep031pW8Q71p0<1pUBQ91pUHQ:1&Q5r5%23B1>p041p0J1p0N1pULQ41pUJQ51pU2Q>1p4QB1").
Proof.
intros C W m m' MU WM HW. eapply pres_except_of_munch; [exact MU | exact WM |].
intros a _ HC. eapply outside_of_cover; eauto.
Qed.
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
end.
Lemma ivs_covered_In : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q1'C!p021'7'<%1255%311&Kr2r1%3221&R5(;%14==54r4%43:21'>&R8%1249&R:r3%22<1%6241r8%11@p031pW8J1p0<1pUBL1pUHM1p0D1pU2I1p4N1").
Proof.
induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.
Lemma pres_except_of_munch_cov : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q5'C!p021'7&Q:%211'S8yR0%211':y8%511%311p051&Q;r3r2r1%43321&Q=&H%23165&Kr6r5%3221&Q5r7r4%33251p051p0:1p0>1pULD1pUJE1pU2N1p4Q21").
Proof. intros. eapply pres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.
Lemma munch_grow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "N&Q:'7%112'S8yR0%211':y8%511%311p051&Q;(4r5r3%33?21r2r1%73321r6r4%93E81%:3F31%<3197p061pUL?1pUJ@1pU2I1pUFL1pU>M1").
Proof.
intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
intros x Hx. cbn in Hx |- *. tauto.
Qed.
End CEIL_WRAP_1.
Ltac munch_grow MU iv :=
lazymatch type of MU with
| munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma amo_aligned_intro : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q0'C'>&R8zr1%3221&R:&R>+2+R0%3221%5271%;271'?&R;r2+4%3221%53B1?'3&E(D&S7yR0r3%3221%6251(=%?3921p0;1p0B1pU4O1").
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
End CEIL_WRAP_2.
Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).
Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Lemma sextw_sxv0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "D'C'?'S8yR0%211&S7&S9yQ0&R7&Gr1%211z%5221%8271%:2<1&Q4%116%A3>31pW4C1").
Proof. intros v. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "A'C'?'S8yR0%211&S7&S9yQ0&Gr1%211%5241%7291&Q4%114%>3;31pW4@1").
Proof. intros v. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.
Lemma le4_lor_sxv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B "Q8'C'>&R8zr2%3221&R:&R>+2+Q0%3221%5271%;271'?'7'S8y8%211%411&Q?&S7yR0&R9&Gr3%211r4%411%6231%9281%;11&Q4%:268%211%?11%F3A51p0H1p0I1pV8Q61pU>Q71").
Proof.
intros f s Hf Hs. apply le4_congr. pose proof (lor_range64 (sxv s) (sxv f) (sxv_range _) (sxv_range _)).
pose proof (Z_lor_range f s ltac:(lia) ltac:(lia)).
rewrite unsigned_lit by lia. rewrite wz_unsigned.
2:{ split; [lia|]. apply (Z.lt_le_trans _ (2^32)); [|lia]. apply Z_bounded_by_bits; [lia|lia|].
intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity. }
rewrite lor_sxv_mod32 by lia. rewrite Z.lor_comm. symmetry. apply Z.mod_small.
split; [lia|]. apply Z_bounded_by_bits; [lia|lia|].
intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity.
Qed.
Definition ntf_mid_post (pc : Z) (R : list cell -> word -> Prop ) : Prop := True.
End CEIL_WRAP_3.
