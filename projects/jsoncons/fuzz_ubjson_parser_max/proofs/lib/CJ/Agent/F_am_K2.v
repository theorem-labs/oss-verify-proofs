(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_am_K2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_K2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."], [["1Some"; "1bool"; "1option"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3N"; "3Z"; "0P"; "4clear_range"; "5ptrs_in"; "6aptr"; "6conc"; "6live_ranges"]; ["6mkRegion"; "6mstate"; "6r_base"; "6r_kind"; "6ranges_free"; "6region"; "6round_up_pg"; "6s_regions"; "6upd_region"; "7add"; "7modulo"; "0lo"; "0n"; "0off"; "0q"; "0r'"]; ["0rg"; "0rid"; "0rq"; "0st"; "0st'"; "8insert"; "8lookup"; "9N_countable"; ":map_insert"; ";gmap"; ";gmap_lookup"; ";gmap_partial_alter"; "<eq_dec"; "0x"]]).
Module A2 := MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition clear_range (st : mstate) (lo n : Z) : Prop :=
forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).
Lemma clear_range_of_ranges_free : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "D'A'9'5'1&D&?r3%211r2r1%63321(3%:3921&;r4%23197p041pQJ@1pQHA1pR8C1").
Proof. intros st lo n.
intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.
Lemma round_up_pg_aligned : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 ">'9'5&Jr1+TP0%3221z%63721&Fr2%211%:3;12p051pRL=1").
Proof. intros x. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.
Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.
Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.
Lemma gr_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "E'5'A&HvQ1'E(@&Cr1%211&B%113&IvM+TP0%3221%:3751qR2<1vQ3%@3?21vQ4%D3C21").
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma gr_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "E'5'Q9'8&Q<&Q7'E%544321&GvQ4%211&Q5&Q8&Q;%14;:98%34<981vQ1vOvQ3%;11%97A>=5431%D3>;1").
Proof. reflexivity. Qed.
Lemma gr_lookup_inv : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "Q9'8'E'5'2%113&Q6'Q9&Q<&Q7%349218&Q:%14;43:r2&GvQ4%211%;6@?7541(0r1%22B1%B3@41'7'4r3vQ1%G3I21vO%I3J?1%6231&6%115vQ3%C11%L6Q1Q0HF:1%A2Q1F%Q13O21%>261%@291p0B1pR6Q61pQNQ81").
Proof. intros q rq.
rewrite gr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma gr_lookup_old : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "L'8&6'5r1vQ1%33521%511'2'E%211&Q6'Q9&Q<&Q7%34>216&Q:%14@438r2&GvQ4%211%;6E=7541vQ3%511%>6H@:871%G3@41p0D1pQNK1").
Proof. intros q. intros. rewrite gr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma gr_lookup_new : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "E'5'2'E%211&Q6'8'Q9&Q<&Q7%344217&Q:%146439vQ1&GvQ4%211%<6;>7541(0vO%22A1%D3A41").
Proof. rewrite gr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma gr_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 ";&='5'9&>vQ4r1%3221vQ3%5213%83731pQN:1").
Proof. intros q.
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, gr_lookup_new, Hr. reflexivity.
- rewrite gr_lookup_old by exact NE. reflexivity.
Qed.
Lemma gr_ru : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 ";'5'9&F&IvM+TP0%3221%511%614%6214%:3931").
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.
Lemma ptrs_in_grow : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_K2 "<'8!p021&<r1vQ3%3221r2vQ4%6221p041pF91").
Proof. intros P. intros H. exact H. Qed.
End GROW.
Lemma impl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
impl asegs (at_node asegs) (enode n dec) (epost P) ms ->
(forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
impl asegs (at_node asegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
intros H HD. unfold enode in *. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec' rsp) as [a|] eqn:E.
- destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
- cbn. apply evt_done. exact I.
Qed.
End CEIL_WRAP_1.
