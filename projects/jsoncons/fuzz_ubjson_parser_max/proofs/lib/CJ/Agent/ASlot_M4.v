(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_M4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W16."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1bool"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3N"; "3Z"; "4mm_cnt_red"; "4mm_final"; "5UNIT"]; ["5aadd"; "5account_bounce"; "5add_slots"; "5aptr"; "5brkstate"; "5c_active"; "5c_avail_meta"; "5c_avail_meta_area_count"; "5c_avail_meta_areas"; "5c_avail_meta_count"; "5c_brk"; "5c_free_meta_head"; "5c_init_done"; "5c_meta_alloc_shift"; "5c_meta_area_head"; "5c_meta_area_tail"]; ["5c_mmap_counter"; "5c_secret"; "5c_usage"; "5mctx"; "5mstate"; "5optr"; "5round_up_pg"; "5s_slots"; "5step_seq"; "5upd_ctx"; "6add"; "6le"; "6lt"; "6modulo"; "6mul"; "0c"]; ["0cnt"; "0f"; "0i"; "0m"; "0nd"; "0nos"; "0p"; "0q"; "0req"; "0sc"; "0size"; "0st"; "0st2"; "7lookup"; "8bv_unsigned"; "9N_countable"]; ["9Z_countable"; "9prod_countable"; ":prod_eq_dec"; ";gmap"; ";gmap_lookup"; "<eq_dec"; "=eq_dec"; "0stride"; "0tp"; "0u1"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section MMEQ.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
let size := UNIT * size_class sc in
let st1 := step_seq (account_bounce sc st2) in
fun r =>
if negb (mmap_answer_ok (live_ranges st1) nd r) then bad_answer bail else
if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
else
let '(st2, rid) := new_region RKGroup r nd st1 in
let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
let ai := (4096 - UNIT) / size - 1 in
let ai := if c - 1 <? ai then c - 1 else ai in
let ai := if ai <? 0 then 0 else ai in
ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).
Lemma ag_mmap_eq st2 m cnt :
ag_mmap sc req k bail st2 m cnt =
(let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
(mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
(is_bouncing sc st2) in
SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.
Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Lemma ag_tail_kq_eq stT mm p c ai :
m_next (get_meta_rec stT mm) = None -> m_prev (get_meta_rec stT mm) = None -> active stT sc = None ->
ag_tail full_lay stT sc mm p c ai (as_kq sc k bail) = k (st_model stT sc c ai mm p) 0.
Proof.
intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
rewrite as_queue_eq.
2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
unfold as_queue_st. cbn [get_head].
match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.
Lemma mm_cnt_red_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4 "I'<'2'6&Q;+1r3%3221+Q0%5231%7231&=r6r5r4r2%55432:1%=2<1%>22:%@221p0:1pS<C1pTDE1pS2F1pSFG1pSDH1").
Proof. intros sc size cnt u1 nos.
intros H. unfold mm_cnt_red.
destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.
Lemma round_up_pg_props : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4 "G'<&Q;zr1%3221'6r2&Q6%112%8231&Q<&Q:+TP0%2271%4261%:261'7&Q=%12:6%33C1A%?251p0A1pTFF1").
Proof. intros x.
intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
Z.div_mod_to_equations. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_mm_final_props := (ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4 "R9'<'2'6&Q;+1r4%3221+Q0%5231%7231+@r8%9221z%;213&Q:r9+4%3221r:%A221'7'5%12GG&>r;r7%3528;@1(4r6r5%34OO21%;3951%N2M7%O28B%Q1221&Q=+TP0%2291%B3Q71J+D%J2@1%Q721=':%G3Q<BQ8&Q6%115%J3Q?B1%Q>241&Q>r<%221I%Q521Q:%QB21H%912%Q23QGJ1%QF231%>291%QH2@1%QI2D1%QJ2I1p0M1p0Q:1p0QA1p0QD1p0QH1pS:R21pS0R31pS<R31pS2R51pTDR61pSBR71pSFR81")) (only parsing).
Variable size : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 0%nat 0%nat).
Variable req : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 1%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 2%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 3%nat 0%nat).
Variable nos : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 5%nat 0%nat).
Variable nd : ltac:(sec_ty2 constr:(SEC_T_mm_final_props) 6%nat 0%nat).
Lemma mm_final_props : ltac:(sec_stmt2 constr:(SEC_T_mm_final_props) 7%nat 0%nat).
Proof.
intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
change (size * cnt + UNIT) with (size * cnt + 16) in E.
destruct (negb nos && (cnt <=? 7)).
- destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
+ inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
+ destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
* inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
* inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
- inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.
End SE.
Lemma pos_iter_slots (m p : aptr) (stride : Z) : forall n tb,
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
Lemma add_slots_first : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4 "RH&C'<'Q4&Q;+1r2%3221&Q<zr4%3221'6'7'3'5%12?>%311&QM'R3&R2';&R5&R6%4432F1&R1&QO&R0%36762J51%:4L51=&R4%14N73?&@r6&?%3221&Q7&Br7r5r3%45382O1%611%I6Q:K><81(1(4%14Q=Q<8Q5%32O1%Q33O51&9r1r8%?51>C=Q:%A11%Q46QEQ6IG41(0%11Q8%Q<3Q831%911':%H1E%Q;6QLQ=Q0NQG1%QA3Q=16%>11'8%QM2QH?%QJ2@L%QG221r9&Q:&Q>%12DE%32Q61%Q9251%QM3R9Q21%QO281qS6R:1%=2R;1%C2?1p0E1pS@R?1%R52Q11p0R71p0R<1pSHRA1pS0RC1pT@RD1pS>RF1pS8RG1").
Proof. intros m p stride c st.
intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
destruct (pos_iter_slots m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.
Lemma stS_shape : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4 "S5'<'Q4'8'Q3p011'6'7&Q8&Ar3r2%3221%511&Q9r1%2215%:3?41'R3&R6&R0&C%44E321&E%=19%211%31;%D3521%:4K98K&Q2%116%21@%I3421'D&J%11;%21E%N3421&Q0%11?%21I%Q23Q821&Q5&K%11D%21N%Q73421&F%11H%21Q2%Q;3821&Q1%11L%21Q6%Q?3QE21&L%11Q0%21Q:%QC3QI21&I%11Q4%21Q>%QG3QM21&G%11Q8%21QB%QK3R121&M%11Q<%21QF%QO3R521&N%11Q@%21QJ%R33Q021&O%11QD%21QN%R73Q421&H%11QH%21R2%R;3Q821%R=251%R>2:1%R?2?1%R@2D1%RA2I1%RB2N1%RC2Q31%RD2Q81%RE2Q=1%RF2QC1%RG2QH1%RH2QN1%RI2R41pS0RL1%RK2R@1qS4RM1%S02RN1pSJS21pSDS41").
Proof. intros sc st2.
assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
{ unfold account_bounce, set_bounce.
destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
destruct AB as (g & EG & HG).
rewrite step_seq_eq. rewrite EG.
destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
- exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
- exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Lemma errno_lit4 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M4 ";'7'<&Q:&QNyR0vR8%3221-U4%6221+SY[L%:3921").
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.
End LEVEL.
End CEIL_WRAP_1.
