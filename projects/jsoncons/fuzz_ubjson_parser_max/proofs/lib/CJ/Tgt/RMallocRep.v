(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Export F_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMallocRep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"]; ["2ex"; "2not"; "2or"; "3N"; "3Z"; "4Segment"; "5find_segment"; "5memory_read"; "5ov_read_bytes"; "5write_to_mem"; "5wview"; "0RUNp"; "6W_high"; "6b8"; "6lr_lo"; "6meta_cells"]; ["6meta_slot"; "6pw"; "6sh_ticks"; "6shadow_le"; "6ticks_ok"; "6wr_in"; "6wz"; "7CB"; "7cell"; "8ivl"; "8munch"; "8wmono"; "9bytes_at"; "9le2"; "9le4"; "9le8"]; ["9mem_inv"; "9mrd"; "9ro_addr"; "9wa"; "9wr_at"; ":alloc_ceiling"; ";ro_cells"; ";rw_cells"; "<AREA_HDR"; "<Known"; "<META_SIZE"; "<NSLOTS"; "<RKBrk"; "<RKGroup"; "<a_check"; "<aadd"]; ["<aptr"; "<area"; "<c_secret"; "<cell_read"; "<cellval"; "<conc"; "<ctx"; "<g_active_idx"; "<g_meta"; "<get_meta_rec"; "<get_shadow"; "<ghdr"; "<havoc"; "<hdr_havoc"; "<m_set_avail"; "<m_set_freed"]; ["<mctx"; "<meta"; "<mstate"; "<optr"; "<r_base"; "<r_kind"; "<r_len"; "<ranges_free"; "<region"; "<rkind"; "<round_up_pg"; "<s_areas"; "<s_groups"; "<s_regions"; "<s_tick"; "<set_active"]; ["<set_tick"; "<shadow"; "<size_class"; "<upd_meta"; "<upd_shadow"; "<wr16"; "<wr8"; "=reservedZ"; ">rsegs"; "?RCTX"; "?RSIZE_CLASSES"; "?rarea_rep"; "?ref_reserved"; "?rgroup_rep"; "?rmrep"; "?rmrep_ctx"]; ["?rmrep_globals"; "?rregions_wf"; "?rshadow_rep"; "?rsize_classes_bytes"; "@seg_rom"; "Aadd"; "Aland"; "Ale"; "Alt"; "Amodulo"; "Amul"; "Aof_N"; "Aof_nat"; "Apow"; "Ato_nat"; "0W"]; ["0a"; "0ar"; "0ar0"; "0b"; "0bs"; "0f"; "0g"; "0gh"; "0k"; "0len"; "0m"; "0m'"; "0n"; "0o"; "0p"; "0r"]; ["0r'"; "0r1"; "0r2"; "0rid"; "0rid'"; "0rid1"; "0rid2"; "0sc"; "0st"; "0st'"; "Blookup"; "Cbv"; "Cbv_unsigned"; "DN_countable"; "DZ_countable"; "Dprod_countable"]; ["Eprod_eq_dec"; "Fgmap"; "Fgmap_lookup"; "Geq_dec"; "Heq_dec"; "0t"; "0v"; "0v0"; "0v1"; "0w8"; "0x"; "0z"]]).
Notation RVMLOCKC := 0xe98a4%Z (only parsing).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition RCTX : Z := 0xe90c0.
Definition RMLOCK : Z := 0xe90b8.
Definition RLIBC : Z := 0xe8f40.
Definition RNEED_LOCKS : Z := 0xe8f43.
Definition RPAGE_SIZE : Z := 0xe8f70.
Definition RAUXV_CELL : Z := 0xe8f48.
Definition RSIZE_CLASSES : Z := 0x1ade0.
Definition RDEBRUIJN : Z := 0x1adc0.
Definition RSMALL_CNT : Z := 0x1ae40.
Definition RMED_CNT : Z := 0x1ae5b.
Definition RGOT_SSP : Z := 0xb5f18.
Definition RSSP_GUARD : Z := 0xe8f20.
Definition RATP : Z := 0xc8cb0.
Definition RERRNO : Z := 0xc8c0c.
Definition rget_meta_entry : Z := 0x9bfb8.
Definition rmalloc_entry : Z := 0x9c778.
Definition rfree_entry : Z := 0x9bdec.
Definition ralloc_meta_entry : Z := 0x9c4a0.
Definition ralloc_slot_entry : Z := 0x9cae8.
Definition renframe_entry : Z := 0x9d38c.
Definition rnontrivial_free_entry : Z := 0x9c0c8.
Definition rmmap_entry : Z := 0x9db1c.
Definition rmunmap_entry : Z := 0x9dd24.
Definition rmprotect_entry : Z := 0x9dc08.
Definition rlock_entry : Z := 0xaae44.
Definition runlock_entry : Z := 0xab0cc.
Definition ref_reserved : list (Z * Z) := [(0x10000, 0x23000); (0x33000, 0x7d000); (0xb0000, 0x6000); (0xb6000, 0x34000)].
Lemma reservedZ_ref : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep ";'?'7';'D%2211%411&S7&S8%211&S<%:3521").
Proof. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_ref_find_segment_none := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "N'D&SG+1r1%3221'B&SEr3r2%3221+RPP0%:221+mXP0%<216%9231'?':'E%211&F&S8r4%3321?(0%117%:3731p0<1p0G1pXJL1pZHM1")) (only parsing).
Variable z : ltac:(sec_ty2 constr:(SEC_T_ref_find_segment_none) 0%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_ref_find_segment_none) 1%nat 0%nat).
Lemma ref_find_segment_none : ltac:(sec_stmt2 constr:(SEC_T_ref_find_segment_none) 2%nat 0%nat).
Proof.
intros Hn Hz.
unfold rsegs, Ubsan.Ubsan_loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Ubsan_segment_000)) with 65536%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_000)) with 143360%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan_segment_001)) with 208896%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_001)) with 512000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan_segment_002)) with 720896%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_002)) with 24576%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan_segment_003)) with 745472%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_003)) with 212992%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + n) (65536 + 143360)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 208896 z); destruct (Z.leb_spec0 (z + n) (208896 + 512000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 720896 z); destruct (Z.leb_spec0 (z + n) (720896 + 24576)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 745472 z); destruct (Z.leb_spec0 (z + n) (745472 + 212992)); cbn [andb]; try lia.
all: reflexivity.
Qed.
End SE.
Lemma ref_ro_addr_false : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "J'TKyR0%211'B&SG&SE&TLr1%2271+1%5221+RPP0%8221+mXP0%:216%<231'?'2&QB&S8r2%3221(4%73621p091pZFG1").
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.
Lemma ref_memory_read_none : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q9'TKyR0%211'C&SG+1&SKr1%211%5241'B&SE&TLr3%22=1r2%:11%6231+RPP0%?221+mXP0%A217%<231'?':'7y8%K11%311%511&G&S8r4%3321D(0%117%=3731p0?1p0M1pXJQ41pZFQ61").
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.
Lemma ref_wview_overlay : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q0'TKyR0%211':y8%511%311p051'B&SG&SE&TLr1%22<1+1%5221+RPP0%8221+mXP0%:216%<231'?&J&S8r3r2%43321%312%73F21p091pZFL1pXFH1").
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.
Lemma ref_seg_rom_none : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "N'TKyR0%211'B&SG&SE&TLr1%2271+1%5221+RPP0%8221+mXP0%:216%<231'?':y8%C11%311&SD&S8r2%3221(0%117%;3731p0=1pZFK1").
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.
Lemma ref_mrd_overlay : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q0'TKyR0%211':y8%511%311p051'B&SG&SE&TLr1%22<1+1%5221+RPP0%8221+mXP0%:216%<231'?&QA&S8r3r2%43321%312%73F21p091pZFL1pXFH1").
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
Section MREP.
Variable st : mstate.
Variable m : word -> option byte.
Definition rmrep_ctx : Prop :=
rw_cells rsegs m RCTX (ctx_head_cells st)
/\ u64arr rsegs m (RCTX + 80) (actives st)
/\ u64arr rsegs m (RCTX + 464) (usages st)
/\ u8arr rsegs m (RCTX + 848) (unmap_seqs st)
/\ u8arr rsegs m (RCTX + 880) (bouncess st)
/\ rw_cells rsegs m (RCTX + 912) (ctx_tail_cells st).
Definition rmrep_globals : Prop :=
rw_cells rsegs m RMLOCK [C4 (wz 0)]
/\ rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)]
/\ rw_cells rsegs m RPAGE_SIZE [C8 (wz 4096)]
/\ rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
/\ rw_cells rsegs m RSSP_GUARD [C8 (wz canary_val)]
/\ rw_cells rsegs m RVMLOCKC [C4 (wz 0)].
Definition rarea_rep (a : aptr) (ar : area) : Prop :=
rw_cells rsegs m (conc st a) [C8 (wz (a_check ar)); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
/\ (forall k, 0 <= k < NSLOTS ->
rw_cells rsegs m (conc st a + AREA_HDR + META_SIZE * k)
(meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
/\ rw_cells rsegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition rmrep_areas : Prop :=
forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.
Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop :=
exists w8 : byte,
rw_cells rsegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
/\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition rmrep_groups : Prop :=
forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.
Definition rshadow_rep (rid : N) (r : region) : Prop :=
wr_at rsegs m (r_base r) (round_up_pg (r_len r))
/\ forall o v, 0 <= o < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) o = Known v ->
bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition rmrep_shadow : Prop :=
forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.
Definition rregions_wf : Prop :=
s_reserved st = ref_reserved
/\ (forall rid r, (s_regions st) !! rid = Some r ->
0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
/\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ ranges_free ref_reserved (r_base r) (round_up_pg (r_len r)) = true)
/\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)
/\ (forall a ar, (s_areas st) !! a = Some ar ->
exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
/\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
/\ (forall b gh, (s_groups st) !! b = Some gh ->
exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).
Definition rmrep : Prop :=
rregions_wf /\ rmrep_ctx /\ rmrep_globals /\ rmrep_areas /\ rmrep_groups /\ rmrep_shadow.
End MREP.
Definition rmrep_W (st : mstate) : list (Z * Z) :=
(RCTX, RCTX + 928)
:: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).
Lemma rmrep_shadow_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "S0'RB'TKyR0%211':y8%511%311p051'C'RH'D&S>r6r5%3221'?%=17&TJ'U1&U3&TM%34=21<&U2%14?43>&RMr7%211%:6CB64>1(1r4%22E1%@3?41'RI&RE%11E(QM%E3421'>&SGz%221K&SH&RJ&RF%11Q0%311%52Q11%:271'R4&R3&R:r:r8%3221%521Q:(QI%11Q;%Q:3931'7%11QF%QI11&H&S8&QC&SE&RD%11>%321Q:%511u1%948C21(3&M%11QM(9%11R6%53R731%QA2B1%QO3B81%Q92Q8R3+X0%Q82R51%Q=231%Q>251p0K1p0Q61p0QB1p0QH1p0R:1pZ>R?1pXLR@1pY0RB1pY8RD1pXFRF1pYBRO1").
Proof.
intros st m rid r o v (WF & _ & _ & _ & _ & SH) Hr Hk Ho Hc.
destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|exact Hv].
rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.
Lemma rmrep_shadow_read2 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "SB'RB'TKyR0%211':y8%511%311p051'C'RH'D&S>r7r6%3221'?%=17&TJ'U1&U3&TM%34=21<&U2%14?43>&RMr8%211%:6CB64>1(1r5%22E1%@3?41'RI&RE%11E(QM%E3421&SGz%221J&SE+2%22N1&RJ&RF%11D%311%:251'R4&R3&R:r<r:%3221%521M(QI%11Q<%Q:3931r=r;%:221r9+1%G221%?241%QB3A19'>'7%11QO%R211&H&S8&QC&RD%11?%Q321G%411u2%847D21(3&M%11D%21QI(9%11R?%63R@31%73RA51%QK2C1%R93C:1%QD2QCL&SH+X0%22O1%K241%QI2QHR5%52R64%N221%O241%Q02:1p0Q21p0Q;1p0QF1p0QO1p0R31p0R91p0RK1pZBS01pZ@S11pXLS21pY0S41pY8S61pXFS81pYBSA1").
Proof.
intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
pose proof MR as (WF & _ & _ & _ & _ & SH).
destruct (SH rid r Hr Hk) as [HW HB].
destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
split; [|split; assumption].
assert (B : bytes_at rsegs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
{ apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. exact B1. }
rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ _ 0 2 B); [lia|cbn; lia].
Qed.
Definition rsize_classes_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RSIZE_CLASSES 96 with Some bs => bs | None => [] end).
Lemma rsize_classes_ro : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "K'TKyR0%211':y8%511%311p051&Q@&S8r1%3221&QFr2&S:(3'Q8(Q7uS0&SC%3221(9%116%83731%<4?;:1p0>1pXFC1").
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RSIZE_CLASSES; lia | unfold RSIZE_CLASSES; cbn; lia]. Qed.
Section SE.
Local Abbreviation SEC_T_rsize_classes_read := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QC'TKyR0%211':y8%511%311p051'D&Q@&S8r2%3221'>&SGz%2215&SH+Q@%2281%7241'?'7%11B%E11&Hr4&QC&SE&S:&SJ+2r3%3221%6251%811u2%<4K;21(1&Q=&Q6&S2%11:%311%511%72F1%I3F91p0K1p0Q41pY@Q91pXFQ;1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rsize_classes_read) 0%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rsize_classes_read) 1%nat 0%nat).
Lemma rsize_classes_read : ltac:(sec_stmt2 constr:(SEC_T_rsize_classes_read) 2%nat 0%nat).
Proof.
intros MI Hsc.
destruct (rsize_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite (bytes_at_read rsegs m RSIZE_CLASSES rsize_classes_bytes (2 * sc) 2 B) by (cbn; lia).
assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed.
End SE.
Lemma rmrep_meta_chunk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q0'RB'TKyR0%211':y8%511%311p051&R0&S>r3r2%3221&Q0r4%2214&QG&S8&R5r5%221:&O&R9%124=%3251%948;51p0;1p0?1pX>D1pXFF1pYBO1").
Proof.
intros st m g MR (a & ar & k & Ha & Hk & ->).
pose proof MR as (WF & _ & _ & AR & _ & _).
destruct (AR a ar Ha) as (_ & SL & _).
destruct WF as (_ & _ & _ & WA & _). destruct (WA a ar Ha) as (r & Hr & _).
rewrite conc_aadd by (rewrite Hr; eauto).
replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. exact Hk.
Qed.
Lemma rmrep_group_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "RO'RB'TKyR0%211':y8%511%311p051&R0'R;&S>r4r3%3221'?%<16&TJ'U1&U0'C&U3'D&U4%544321&TO&TM&TN%36872651%;4D51C&U2%14F73E&RLr5%211%B6JI64F1(1r2%22L1%H3G41'>'7%11Q4%Q711&H&S8&QC&R5r6%221Q5%411u8%847C21&Q?&Q1&R8%11Q;%3291%511%G2A1%Q=3A81'@&SEr7%A21O+8%4221%E11u1%I4HE21(3r1(9%11R3%43R431%Q72Q11%QM3Q171&SF&TL%12R:8+O%4221&R7%11R7%R53QN31%Q=291qZDR@1%J2RA1%Q@2L1p0QB1p0R<1pX@RA1pX8RC1pXFRE1pYBRN1").
Proof.
intros st m b gh MR Hb. pose proof MR as (_ & _ & _ & _ & GR & _).
destruct (GR b gh Hb) as (w8 & RW & Hw8). split.
- rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); reflexivity.
- exists w8. split; [|exact Hw8].
apply (rw_cells_read_at rsegs m _ _ 8 (C1 w8) 1 _ RW); reflexivity.
Qed.
Lemma rmrep_area_check_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "R2'RB'TKyR0%211':y8%511%311p051&R0'R1&S>r4r3%3221'?%<16&TJ'U1&U0'C&U3'D&U4%544321&TO&TM&TN%36872651%;4D51C&U2%14F73E&RKr5%211%B6JI64F1(1r2%22L1%H3G41'7%11Q3%Q611&H&S8&QC&R5r6%221Q4%411u8%847B21&Q?&Q6&QN%11Q:%311%511%F2A1%Q<3A81p0E1p0Q?1pX4QD1pX2QF1pXFQH1pYBR11").
Proof.
intros st m a ar MR Ha. pose proof MR as (_ & _ & _ & AR & _ & _).
destruct (AR a ar Ha) as (HD & _ & _).
rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (wz (a_check ar))) 8 _ HD); reflexivity.
Qed.
Lemma rmrep_ctx_secret_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q7'RB'TKyR0%211':y8%511%311p051&S>r2r1%3221'?'7%119%<11&H&S8&QC&S9%211u8%645=21(1&Q?&Q6&R2&R6r3%211%411%611%811%:2C1%F3C<1p0H1pXFM1pYBQ61").
Proof.
intros st m (_ & (HD & _) & _).
rewrite <- (Z.add_0_r RCTX). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (wz (c_secret (ctx st)))) 8 _ HD); reflexivity.
Qed.
Lemma rreserved_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q7'D'?'2&RG&S<r2r1%43321(=%83721'>'B&SG&SEr3%221:+RPP0%5221+V\P0%7215%9231%9263+fPP0%;219%=231%=2:3+fhP0%?21=%A231%A2>3+mXP0%C21A%E231%G251%H2:1%I2?1p0K1pXJQ51pX8Q61").
Proof.
intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.
Lemma rreserved_disjoint1 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "L'D'?'2&RG&S<r2r1%43321(=%83721&SHz%2217'B&SG&SEr4r3%3221+RPP0%6221+mXP0%8216%:231p0<1p0@1pXJJ1pX8K1").
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.
Lemma rwr_in_image : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q9'RB'C'D&SAr4%211&Q5r5r3r2%443621'>'B&SG&SE%12;7+fPP0%4221+fhP0%621?%8231%8263+mXP0%:21C%<231%>251z%>21G&SM+2+R0%3221%C2A1%F261%G291p0I1p0O1pXDQ31pX2Q41pY8Q61pYBQ81").
Proof.
intros st rid a len (_ & WR & _) (r & Hr & H1 & H2 & H3).
destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). pose_ceil.
destruct (rreserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.
Lemma rwr_in_other : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QK'RB'C'D'RH&SAr6%211&Q5r7r5r4%443621'?':%11;&TJ'U1&U3&TM%34B21@&U2%14D43B&RMr8%211%:6HF64?1(1r3%22I1%A3?41&A%C3NF8%211'B&SG&SE%12=L&N%11M%5231&RD%11Q0&RJ&RF%11Q3%311%;251%=21H%?291p0A1p0E1p0Q81p0Q>1pY2QB1pY:QE1pXDQE1pX2QF1pY8QH1pYBQJ1").
Proof.
intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.
Lemma rarea_lr_lo : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QO'RB';'C'D%3221'R1'RH&SAr4%211'?':%117&TJ'U1&R0&U0&U3&U4%34A2@1&TO&TM&TN%36E62D51%:4951C&U2%14;73E&RKr5%211%A6JI64F1(1r3%22L1%H3F41%H1M%F4Q2C?N%<4Q3D@O&5%13Q5Q4;&RMr6%211%N6Q9Q57641%=2Q6<%Q33:21&SG&N%11Q8&SE&RD%11Q;&<%13QCQB<%5231%9271p0;1p0G1p0QA1pY0QE1pX4QG1pX2QI1pYBQN1").
Proof.
intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.
Lemma rregions_disjoint_full : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "R7'RB'C'RH&SAr5%211'?':%116&TJ'U1&U3&TM%34<21;&U2%14>43=&RMr6%211%:6BA64?1(1r4%22D1%A3?41r7%911%A6IH=;51r3%82J1%G3E31&A%I3N7K%211'RI&RE%11;(QL%O3421%811%51F%Q23714%;11'B&SG&SE&RDr9%211&RJ&RF%114%311%8251%81M%;221%61O%811%=241%?21;%A251p0C1p0G1p0N1p0Q21p0Q91p0QL1pY6R01pY>R21pY4R21pY<R41pYBR61").
Proof.
intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. exact X.
Qed.
Lemma rregions_disjoint_grp : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "R4'RB'C'RH&SAr5%211'?':%116&TJ'U1&U3&TM%34<21;&U2%14>43=&RMr6%211%:6BA64?1(1r4%22D1%A3?41r7%911%A6IH=;51r3%82J1%G3E31&A%I3N7K%211'RI&RE%11;(QM%O3421'B&SG&SE&RDr8%211&RJ&RF%114%311%8251&N%11Q1%<231%;1Q3%81Q4%:11%?231%A21=%C261p0E1p0K1p0O1p0Q61p0QI1pY6QM1pY>QO1pY4QO1pY<R11pYBR31").
Proof.
intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. exact X.
Qed.
Lemma rmrep_ctx_ext : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q4'RB'TKyR0%211':y8%511%311p051'?'R@&R6r2%211r3%411%73631&R0'D&R5r4r1%3221r5%5213%@3731pXN91&S?%125>%2269p021p051p0@1pXFI1pYDQ21pYBQ31").
Proof.
intros st st' m Hc Hconc H.
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
assert (E1 : ctx_head_cells st' = ctx_head_cells st) by (unfold ctx_head_cells; rewrite Hc, !Hpw; reflexivity).
assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.
Lemma rarea_rep_ext : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QL'RB'TKyR0%211':y8%511%311p051&R0'R1'?'D&R5r5r1%3221r6%5213%83731pXN;1'>&SGz%2219&SH&QK%22<1%7241'RA&R9r7&QO&SE&QH&SJ&QJr2%3221%6251%82J1%;2:1r8%=213%Q13?31p0A1pXBQ21&S;r4r3%34CQ421%44DQ2Q53p021p071p0Q21pX4Q=1pX2Q?1pXFQA1pYDQJ1pYBQK1").
Proof.
intros st st' m a ar Hconc Hm (H1 & H2 & H3).
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
unfold rarea_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.
Lemma rgroup_rep_ext : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q2'RB'TKyR0%211':y8%511%311p051&R0'R;'?'D&R5r5r1%3221r6%5213%83731pXN;1&S=r4r3r2%448321%549<43p021p081pX@C1pX8E1pXFG1pYDQ01pYBQ11").
Proof.
intros st st' m b gh Hconc (w8 & H1 & H2).
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
exists w8. rewrite Hconc, Hpw. auto.
Qed.
Lemma rshadow_rep_ext : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q0'RB'TKyR0%211':y8%511%311p051'C'RH'?'S1&R:r4r2%3221r5%5213%83731&SBr6r3%342918%4437:2p021p071pY0A1pY8C1pXFE1pYDN1pYBO1").
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.
Lemma rmrep_ctx_frame : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q;'RB'TKyR0%211':y8%511%311p051'D'7%115'C&SAr5%211&Q5r6r2r4&SL&6r3%22A1%411%948761&S?r7%221;r8&I&QC%11?%3361C%8251p071p0;1p0F1pY8J1pX:L1pX2O1pXFQ11pYBQ:1").
Proof.
intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5 & H6).
destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold rmrep_ctx. unfold RCTX in *. split; [|split; [|split; [|split; [|split]]]].
- apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
- apply u64arr_frame; [exact H2|lia|lia|rewrite L1; cbn; lia].
- apply u64arr_frame; [exact H3|lia|lia|rewrite L2; cbn; lia].
- apply u8arr_frame; [exact H4|lia|lia|rewrite L3; cbn; lia].
- apply u8arr_frame; [exact H5|lia|lia|rewrite L4; cbn; lia].
- apply rw_cells_frame; [exact H6|lia|lia|cbn; lia].
Qed.
Lemma rmrep_globals_frame : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q:'RB'TKyR0%211':y8%511%311p051'D'7%115'C&SAr5%211&Q5r6r2r4&SL&6r3%22A1%411%948761&S@%11:&Ir7&QC%11>%4331B%711p071p0:1p0E1pY8I1pX:K1pX2N1pXFQ01pYBQ91").
Proof.
intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5 & H6).
destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
unfold rmrep_globals. unfold RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split; [|split]]]].
- apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
- apply rw_cells_frame; [exact H2|lia|lia|cbn; lia].
- apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
- apply rw_cells_frame; [exact H4|lia|lia|cbn; lia].
- apply rw_cells_frame; [exact H5|lia|lia|cbn; lia].
- apply rw_cells_frame; [exact H6|lia|lia|cbn; lia].
Qed.
Lemma rarea_rep_frame : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "RK'RB'TKyR0%211':y8%511%311p051'D'7%115&R0'R1&SAr6%211'?%>15&TJ'U1&U0'C&U3&U4%4432@1&TO&TM&TN%36762D51%:4B51A&U2%14D73Cr3&RKr7%211%B6IH7541(1r2%22K1%H3G41&SGz%221M&SE&SL&6%12Q:Q1%311%52?1&SM+2+R0%3221%=251'B&R5r:%221Q<+TP0%@221r8%E221%A2QJM%C11%E241%I218%<251&S;r;%241=Q4QHr<&I&QC%11Ar9%43721%9461@Q;p081p0<1p0J1p0Q61p0Q:1p0R41pX4R81pX6R:1pX:R<1pX2R?1pXFRA1pYBRJ1").
Proof.
intros st m a bs ar0 ar WF Har A0 A1 D (H1 & H2 & H3).
unfold rarea_rep. split; [|split].
- apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
- intros k Hk. apply rw_cells_frame; [apply H2; exact Hk|lia|lia|]. unfold AREA_HDR, META_SIZE, NSLOTS in *. cbn. lia.
- apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
Qed.
Lemma rgroup_rep_frame : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QO'RB'TKyR0%211':y8%511%311p051'D'7%115&R0'R;&SGzr4%3221&SEr5&SL&6%12@6%311%6251&SM+2+R0%3221%?251'B&R5r8%221A+9%A221r6%G221%A2Q0C%C11%F241%K218%<251&S=r9%241=JMr:&I&QC%11Ar7%43721%9461@Q1p081p0<1p0J1p0Q71pX@Q<1pX8Q>1pX:Q@1pX2QC1pXFQE1pYBQN1").
Proof.
intros st m a bs b gh A0 A1 D (w8 & H1 & H2). exists w8. split; [|exact H2].
apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
Qed.
Lemma rshadow_rep_frame : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "R3'RB'TKyR0%211':y8%511%311p051'D'7%115'C'RH&SGzr4%3221&SEr5&SL&6%12@6%311%6251&SM+2+R0%3221%?251'B&RDr3%211&RJ&RF%114%311%D251r6%J221%D2Q3F%F11%I241%N21;%?251&SBr9r8%3421NQ1r:&I&QC%115r7%43821%:461AQ5p081p0=1p0N1p0Q;1pY0Q@1pY8QB1pX:QD1pX2QG1pXFQI1pYBR21").
Proof.
intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; exact HW|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|exact Hv].
apply bytes_at_write_other; [exact Hb|lia|lia|cbn; lia].
Qed.
Lemma rarea_conc : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "S7'RB';'C'D%3221'R1&SAr3%211'?':%116&TJ'U1&R0&U0&U3&U4%34@2?1&TO&TM&TN%36D62C51%:4951B&U2%14;73D&RKr4%211%A6IH64F1(1r2%22K1%H3F41'@'RH'>%K12%I4Q4FB3%?4Q5GC4&5r5%23Q8Q71&RMr6%211%Q26Q<;8741r1%B2=1%Q83<31&R5%127:&SE&RD%117&<%13QFQE?%5231%QA3QG71&SGz%2215+TP0%;271&RJ&RF%11C%311%9251&SI%12>8%QN3R41;&A'RI&RE%11L(QM%R43421%611&SH%12DJ%<2KC%R93R?1F%O2M@&QEvK%211%L241%QD261%QE291%QF2<1%QG2D1%QH2H1%QI2Q01%QJ2Q41%QK2Q>1qY0QM1%QO2QN1p0R11p0RK1pX4RO1pX2S11pYBS61").
Proof.
intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.
Lemma rgroup_conc : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "S2'RB';'C'D%3221'R;&SAr3%211'?':%116&TJ'U1&R0&U0&U3&U4%34@2?1&TO&TM&TN%36D62C51%:4951B&U2%14;73D&RLr4%211%A6IH64F1(1r2%22K1%H3F41'@'RH'>%K12%I4Q4FB3%?4Q5GC4&5r5%23Q8Q71&RMr6%211%Q26Q<;8741r1%B2=1%Q83<31&R5%127:&SE&RD%117&<%13QFQE?%5231%QA3QG71'RI&RE%11>(QM%QF3421&SGz%221:+@%@2<1&RJ&RF%11H%311%9251&SI%12C8%R33R91;&SH%12=H%K2I7&QEvK%211%C241%Q@261%QA291%QB2=1%QC2E1%QD2I1%QE2O1%QF2Q91qY0QH1%QJ2QI1p0QL1p0RF1pX@RJ1pX8RL1pYBS11").
Proof.
intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_wr8 := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "T3'RB'TKyR0%211':y8%511%311p051';'C'D%3221'RH&S>r5r4%3221&Q4r6%211'?%B19&TJ'U1&U3&TM%34A21>&U2%14C43@&5%13ED@&RMr7%211%<6IF8641(1r3%22I1%B3A41'RI&RE%11J(QM%G3421'>&SGz&<%13Q7Q6@%4231&SH&RJ&RF%11Q7%311%5271%<271'R;%QG11&R0&U0&U4%24QEQ6QD1&TO&TN%26QHQ9Q8QG41%Q;47419%Q84852:r2&RLr<%211%QB6QM?6541r1%Q72A1%QG3A31%Q?3R3R2Q8r;%QA3R5R41%QK3R631&A%Q23R8R7R2%Q33R9R8<%Q6221&SE+9%2251%Q5251%Q<251%911p0;1p0@1pX@Q31pX8RB1r8%QB2QA1+X0%Q?231%QF231&S6r:r9%3321Q0&I&QC&RD%11<%QL3S2S17%H221%511(3&M%11;(9%11S=%53S>31%=3Q771%S82?1p0D1p0J1p0R01p0R>1p0RD1p0S81p0S<1pY0SA1pZ>SD1pXNSD1pXFSI1pYBT21")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_wr8) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_wr8) 1%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_rmrep_wr8) 2%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_rmrep_wr8) 3%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rmrep_wr8) 4%nat 0%nat).
Lemma rmrep_wr8 : ltac:(sec_stmt2 constr:(SEC_T_rmrep_wr8) 5%nat 0%nat).
Proof.
intros MR TK Hr Hk Ho Hgrp Hv.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof (lr_lo_group r Hk) as LRr.
assert (WI : wr_in st (fst p) (r_base r + snd p) (Z.of_nat (length [b8 v]))).
{ exists r. cbn. repeat split; auto; lia. }
destruct (rwr_in_image st _ _ _ WF WI) as (D & A0 & A1). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in D, A1.
assert (Hconc : forall q, conc (wr8 p v st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- exact WF.
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
- eapply rmrep_globals_frame; eauto.
- intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
apply rarea_rep_frame; [exact WF|exact Ha|lia|cbn; lia| |exact (AR a ar Ha)]. rewrite Ca. cbn.
destruct (N.eq_dec (fst a) (fst p)) as [E|NE].
+ rewrite E in Hra. rewrite Hr in Hra. inversion Hra; subst ra. congruence.
+ destruct (rwr_in_other st _ _ _ _ ra WF WI Hra NE); cbn in *; lia.
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
apply rgroup_rep_frame; [lia|cbn; lia| |exact (GR b gh Hb)]. rewrite Cb. cbn.
destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
+ rewrite E in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. specialize (Hgrp b gh Hb E). lia.
+ destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
- intros rid r' Hr' Hk'. cbn in Hr'.
destruct (N.eq_dec rid (fst p)) as [E|NE].
+ subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
destruct (SH (fst p) r Hr Hk) as [HW HB]. split; [apply wr_at_write; exact HW|].
intros o v' Ho' Hc.
destruct (Z.eq_dec o (snd p)) as [->|NEo].
* rewrite cell_read_wr8_same in Hc by assumption. inversion Hc; subst v'. split; [|lia].
apply bytes_at_write_same; cbn; lia.
* rewrite cell_read_wr8_other in Hc by exact NEo. destruct (HB o v' Ho' Hc) as [Hb Hv']. split; [|exact Hv'].
apply bytes_at_write_other; [exact Hb|lia|cbn; lia|cbn; lia].
+ eapply rshadow_rep_ext; [apply get_shadow_wr8_other; exact NE|].
pose proof (lr_lo_group r' Hk') as LR'.
apply rshadow_rep_frame; [lia|cbn; lia| |exact (SH rid r' Hr' Hk')].
destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.
End SE.
Lemma rmrep_wr16 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "T5'RB'TKyR0%211':y8%511%311p051';'C'D%3221'RH&S>r5r4%3221&Q4r6%211'?%B19&TJ'U1&U3&TM%34A21>&U2%14C43@&5%13ED@&RMr7%211%<6IF8641(1r3%22I1%B3A41'RI&RE%11J(QM%G3421&SGz&<%13Q6Q5?%4231&SEr8%53Q:Q91+2%4221&RJ&RF%11Q6%311%>251'R;%QI11&R0&U0&U4%24QGQ8QF1&TO&TN%26QJQ;Q:QI41%Q=47419%Q:4852:r2&RLr=%211%QD6QO?6541r1%Q92A1%QI3A31%QA3R5R4Q:r<%QC3R7R61%QM3R831'B%Q53R:R9;%Q321Q0%Q73R<R;R6%Q:221+9%Q7231%Q=216%8241p0:1p0?1pX@Q21pX8RC1'>r9%QE2QD1&SH+RPP0%2241%6241&S5r;r:%3321Q1&I&QC&RD%11=%R03S5S47%QN221%511&Q=&Q6%11;%311%;3Q651%S92=1p0B1p0J1p0QO1p0R:1p0R@1p0RF1p0S:1p0S>1pY0SC1pZ>SF1pXNSF1pXFSK1pYBT41").
Proof.
intros st m p v r MR TK Hr Hk Ho Ho2 Hg Hv.
rewrite le2_split by lia.
change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 (v / 256)])
with (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p) + 1) [b8 (v / 256)]).
rewrite wa_succ. unfold wr16. rewrite (wr8_mod st p v).
replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (unfold aadd; cbn; lia).
replace (Z.shiftr v 8) with (v / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
apply (rmrep_wr8 (wr8 p (v mod 256) st) _ (aadd p 1) (v / 256) r).
- apply rmrep_wr8; auto; [lia|]. intros b gh Hb E. specialize (Hg b gh Hb E). lia.
- apply ticks_ok_wr8. exact TK.
- cbn. exact Hr.
- exact Hk.
- cbn. lia.
- intros b gh Hb E. cbn in Hb, E |- *. specialize (Hg b gh Hb E). lia.
- exact Hd.
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_meta_store4 := (forall st m g (f : meta -> meta) (off : nat) v, rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
(forall mr, cell_at (meta_cells st mr) off = Some (C4 (wz (match off with 24%nat => m_avail mr | _ => m_freed mr end)))) ->
(forall mr, cell_upd (meta_cells st mr) off (C4 (wz v)) = meta_cells st (f mr)) ->
(off = 24%nat \/ off = 28%nat) ->
rmrep (upd_meta g f st) (write_to_mem m (wa (conc st g + Z.of_nat off)) (le4 (wz v)))) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_meta_store4) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_meta_store4) 1%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rmrep_meta_store4) 2%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_rmrep_meta_store4) 3%nat 0%nat).
Variable off : ltac:(sec_ty2 constr:(SEC_T_rmrep_meta_store4) 4%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_rmrep_meta_store4) 5%nat 0%nat).
Lemma rmrep_meta_store4 : ltac:(sec_stmt2 constr:(SEC_T_rmrep_meta_store4) 6%nat 0%nat).
Proof.
intros MR (a & ar & k & Ha & Hk & Eg) Hv Hat Hupd Hoff.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil.
pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
assert (WI : wr_in st (fst a) (conc st g + Z.of_nat off) (Z.of_nat (length (le4 (wz v))))).
{ exists ra. rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat]. split; [exact Hra|]. rewrite HG, Ca. destruct Hoff; subst; cbn; lia. }
assert (Hconc : forall q, conc (upd_meta g f st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- exact WF.
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
- eapply rmrep_globals_frame; eauto.
- intros a' ar' Ha'. cbn in Ha'.
assert (Hpw : forall q, pw (upd_meta g f st) q = pw st q) by (intros [q|]; reflexivity).
assert (Hmc : forall mr, meta_cells (upd_meta g f st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra') as LRa'.
destruct (decide (a' = a)) as [->|NEa].
+
rewrite Ha in Ha'. inversion Ha'; subst ar'.
destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw. rewrite length_le4 in *.
split; [|split].
* apply rw_cells_frame; [exact HD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
* intros k' Hk'. rewrite Hmc, get_meta_rec_upd.
destruct (Z.eq_dec k' k) as [->|NEk].
-- rewrite <- Eg, aptr_eqb_refl.
replace (conc st g + Z.of_nat off) with (conc st a + 24 + 40 * k + Z.of_nat off) by (rewrite HG; lia).
rewrite <- Hupd. unfold le4. change (Z_to_le_bytes 4 (bv_unsigned (wz v))) with (cbytes (C4 (wz v))).
eapply rw_cells_write; [ | apply Hat | reflexivity | exact I].
rewrite Eg. replace (24 + 40 * k) with (AREA_HDR + META_SIZE * k) by reflexivity. apply SL. unfold NSLOTS. lia.
-- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
apply rw_cells_frame; [apply SL; lia|lia|rewrite length_le4; cbn in *; lia|].
rewrite length_le4, HG. cbn [cells_size meta_cells csize Nat.add length]. unfold AREA_HDR, META_SIZE. destruct Hoff; subst; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; nia.
* apply rw_cells_frame; [exact PD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
+
assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. nia. }
eapply rarea_rep_ext; [exact Hconc| |].
{ intros k0 Hk0. rewrite get_meta_rec_upd.
replace (aptr_eqb (aadd a' (AREA_HDR + META_SIZE * k0)) g) with false; [reflexivity|].
symmetry. rewrite Eg. unfold aptr_eqb, aadd, AREA_HDR, META_SIZE. cbn [fst snd].
destruct PG as [NE|[E PG]].
- rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
- rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. unfold NSLOTS in *. lia. }
apply rarea_rep_frame; [exact WF|exact Ha'|lia|rewrite length_le4; cbn in *; lia| |exact (AR a' ar' Ha')].
rewrite length_le4, Ca', HG, Ca. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat].
destruct PG as [NE|[E PG]].
* destruct (rwr_in_other st _ _ _ _ ra' WF WI Hra' NE); rewrite ?HG, ?Ca in *; cbn in *; lia.
* rewrite E, Hra in Hra'. inversion Hra'; subst ra'. destruct Hoff; subst; cbn; lia.
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
apply rgroup_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (GR b gh Hb)]. rewrite Cb, length_le4. cbn.
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
- intros rid r' Hr' Hk'. cbn in Hr'.
eapply rshadow_rep_ext; [reflexivity|]. pose proof (lr_lo_group r' Hk') as LR'.
apply rshadow_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (SH rid r' Hr' Hk')]. rewrite length_le4. cbn.
assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.
End SE.
Lemma rmrep_meta_set_avail : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QH'RB'TKyR0%211':y8%511%311p051&R0'D&S>r4r3%3221&Q0r5%2214'>&SGz%2218&SH&SM+2+Q0%3221%52>1%:271&S3&R>%11Cr7%43A21&Ir6&QC&SE&R5%127G+H%4221%611&Q>&Q6%11Q1%311%=3<51%Q52?1p0E1p0Q11p0Q51pZ>Q:1pX>Q<1pXFQ>1pYBQG1").
Proof.
intros. change 24 with (Z.of_nat 24).
apply (rmrep_meta_store4 st m g (m_set_avail v) 24%nat v); auto; intros; reflexivity.
Qed.
Lemma rmrep_meta_set_freed : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QH'RB'TKyR0%211':y8%511%311p051&R0'D&S>r4r3%3221&Q0r5%2214'>&SGz%2218&SH&SM+2+Q0%3221%52>1%:271&S3&R?%11Cr7%43A21&Ir6&QC&SE&R5%127G+L%4221%611&Q>&Q6%11Q1%311%=3<51%Q52?1p0E1p0Q11p0Q51pZ>Q:1pX>Q<1pXFQ>1pYBQG1").
Proof.
intros. change 28 with (Z.of_nat 28).
apply (rmrep_meta_store4 st m g (m_set_freed v) 28%nat v); auto; intros; reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_set_active := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QB'RB'TKyR0%211':y8%511%311p051'D&RC&S>r4r3%3221'>&SGz%2215&SH+Q@%2281%7241&ROr6%23=<1&Ir5&QC&SE&S9+R@%3221&SJ+8%221G%7241%911&Q?&Q1%12@K%311%@3?51%Q02B1p0F1p0O1pZ>Q41pY@Q61pXFQ81pYBQA1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_active) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_active) 1%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_active) 2%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_active) 3%nat 0%nat).
Lemma rmrep_set_active : ltac:(sec_stmt2 constr:(SEC_T_rmrep_set_active) 4%nat 0%nat).
Proof.
intros MR Hsc.
pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & (G1 & G2 & G3 & G4 & G5 & G6) & AR & GR & SH).
assert (Hconc : forall q, conc (set_active sc v st) q = conc st q) by (intros; reflexivity).
assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
pose proof (length_le8 (pw st v)) as L8.
unfold RCTX in *.
split; [|split; [|split; [|split; [|split]]]].
- exact WF.
- unfold rmrep_ctx.
change (ctx_head_cells (set_active sc v st)) with (ctx_head_cells st).
change (usages (set_active sc v st)) with (usages st).
change (unmap_seqs (set_active sc v st)) with (unmap_seqs st).
change (bouncess (set_active sc v st)) with (bouncess st).
assert (E6 : ctx_tail_cells (set_active sc v st) = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_active upd_ctx c_seq c_brk set_active_map]. destruct (c_brk (s_ctx st)); reflexivity. }
rewrite E6, actives_set_active by lia. unfold RCTX.
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
+ apply rw_cells_frame; [exact C1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ replace (954560 + 80 + 8 * sc) with ((954560 + 80) + 8 * sc) by lia. apply u64arr_write; [exact C2| rewrite L1; lia].
+ apply u64arr_frame; [exact C3|lia|rewrite L8; lia|rewrite L8, L2; lia].
+ apply u8arr_frame; [exact C4|lia|rewrite L8; lia|rewrite L8, L3; lia].
+ apply u8arr_frame; [exact C5|lia|rewrite L8; lia|rewrite L8, L4; lia].
+ apply rw_cells_frame; [exact C6|lia|rewrite L8; lia|rewrite L8; cbn; lia].
- unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split; [|split]]]].
+ apply rw_cells_frame; [exact G1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [exact G2|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [exact G3|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [exact G4|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [exact G5|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [exact G6|lia|rewrite L8; lia|rewrite L8; cbn; lia].
- intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
destruct WF as (_ & WR & _). destruct (WR _ ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
apply rarea_rep_frame; [exact (proj1 MR)|exact Ha|lia|rewrite L8; lia| |exact (AR a ar Ha)].
rewrite L8, Ca. pose proof (round_up_pg_ge (r_len ra)). cbn. lia.
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct WF as (_ & WR & _). destruct (WR _ rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
apply rgroup_rep_frame; [lia|rewrite L8; lia| |exact (GR b gh Hb)]. rewrite L8, Cb. cbn. lia.
- intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
destruct WF as (_ & WR & _). destruct (WR _ r' Hr') as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
apply rshadow_rep_frame; [lia|rewrite L8; lia| |exact (SH rid r' Hr' Hk')]. rewrite L8. cbn. lia.
Qed.
End SE.
Lemma rshadow_rep_le : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "O'RB'TKyR0%211':y8%511%311p051'C'RH&Q3&R:r5r2%3221r4%5213%7231&SBr6r3%342618%443:72p021p071pY0@1pY8B1pXFD1pYDM1pYBN1").
Proof. intros st st' m rid r [_ HL] [HW HB]. split; [exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.
Lemma rmrep_upd_shadow : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q<'RB'TKyR0%211':y8%511%311p051'C'S1pZF11&S>r4r3%3221&Q4r5%211'>&Q3&R:r6%221:%:11%5221&Q2&RN%116%3251%;251&S4r7%23@D1%F21<%C12%A221p071p0D1p0H1pX<M1pY8Q01pXFQ21pYBQ;1").
Proof.
intros st m rid f MR TK [HL HT]. pose proof MR as (WF & CX & GL & AR & GR & SH).
assert (Hconc : forall q, conc (upd_shadow rid f st) q = conc st q) by (intros; reflexivity).
assert (GS : forall rid', get_shadow (upd_shadow rid f st) rid' = if N.eqb rid' rid then f (get_shadow st rid) else get_shadow st rid').
{ intros rid'. rewrite (get_shadow_unfold (upd_shadow rid f st)). unfold upd_shadow, set_shadow. cbn [s_shadow].
destruct (N.eqb_spec rid' rid); [subst; rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
split.
- split; [exact WF|]. split; [eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX]|]. split; [exact GL|].
split; [intros a ar Ha; eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)]|].
split; [intros b gh Hb; eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)]|].
intros rid' r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_le; [|exact (SH rid' r' Hr' Hk')].
rewrite GS. destruct (N.eqb_spec rid' rid); [subst; exact HL| apply shadow_le_refl].
- destruct TK as [T1 T2]. destruct HT as [HT1 HT2]. split.
+ intros rid' sh u hl ch Hs Hu Hin. cbn [s_tick upd_shadow set_shadow] in *.
pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
destruct (N.eqb_spec rid' rid); [subst sh; eapply HT1; eauto|].
unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T1; eauto| subst; rewrite lookup_empty in Hu; discriminate].
+ intros rid' sh pg t Hs Hp. cbn [s_tick upd_shadow set_shadow] in *.
pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
destruct (N.eqb_spec rid' rid); [subst sh; eapply HT2; eauto|].
unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T2; eauto| subst; rewrite lookup_empty in Hp; discriminate].
Qed.
Lemma rmrep_havoc : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "O'RB'TKyR0%211':y8%511%311p051&R0'D&S>r4r3%3221&Q4r5%211'>&R<r6%23981%;216%812%6221p081p0<1pXJA1pXNC1pXFE1pYBN1").
Proof.
intros st m p n MR TK. unfold havoc. destruct (n <=? 0); [auto|].
apply rmrep_upd_shadow; [exact MR|exact TK|].
pose proof (sh_ticks_of_ticks_ok st (fst p) TK) as T0.
set (sh := get_shadow st (fst p)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
destruct ((snd p + 4095) / 4096 <? (snd p + n) / 4096).
- destruct (havoc_pages_le cells hav havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T0) as [L1 T1].
set (hav1 := if snd p <? (snd p + 4095) / 4096 * 4096 then havoc_units (snd p) ((snd p + 4095) / 4096 * 4096) (s_tick st) hav else hav).
assert (S1 : shadow_le (mkShadow cells hav havp) (mkShadow cells hav1 havp) /\ sh_ticks (mkShadow cells hav1 havp) (s_tick st)).
{ subst hav1. destruct (snd p <? _); [apply havoc_units_le; exact T0| split; [apply shadow_le_refl|exact T0]]. }
destruct S1 as [L2 T2].
set (hav2 := if (snd p + n) / 4096 * 4096 <? snd p + n then havoc_units ((snd p + n) / 4096 * 4096) (snd p + n) (s_tick st) hav1 else hav1).
assert (S2 : shadow_le (mkShadow cells hav1 havp) (mkShadow cells hav2 havp) /\ sh_ticks (mkShadow cells hav2 havp) (s_tick st)).
{ subst hav2. destruct (_ <? snd p + n); [apply havoc_units_le; exact T2| split; [apply shadow_le_refl|exact T2]]. }
destruct S2 as [L3 T3].
destruct (havoc_pages_le cells hav2 havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T3) as [L4 T4].
split; [|exact T4]. eapply shadow_le_trans; [exact L2|]. eapply shadow_le_trans; [exact L3|exact L4].
- apply havoc_units_le. exact T0.
Qed.
Lemma rmrep_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "M'RB'TKyR0%211':y8%511%311p051&R0&S>r3r2%3221&Q4r4%211'>&R=r5%2291%;216%812%6221p081p0<1pX8A1pXFC1pYBL1").
Proof.
intros st m b MR TK. unfold hdr_havoc.
apply rmrep_upd_shadow; [exact MR|exact TK|].
pose proof (sh_ticks_of_ticks_ok st (fst b) TK) as T0.
set (sh := get_shadow st (fst b)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
apply hav_unit_step. exact T0.
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_transport_high := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "Q5'RB'TKyR0%211':y8%511%311p051'7&Q9%211&S>r4r3%3221&Q:r2%23154&Q;&S8r5%33219&LvK%221<r8r6%@221p041p081p0=1p0A1pX0F1pXHJ1pXFK1pYBQ41")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_high) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_high) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_high) 2%nat 0%nat).
Variable W : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_high) 3%nat 0%nat).
Lemma rmrep_transport_high : ltac:(sec_stmt2 constr:(SEC_T_rmrep_transport_high) 4%nat 0%nat).
Proof.
intros (WF & CX & GL & AR & GR & SH) MU WM HW.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (D : forall a n, a + n <= alloc_ceiling -> disjoint_from W a n) by (intros; apply W_high_disjoint; assumption).
pose_ceil.
assert (TC : forall A cs, rw_cells rsegs m A cs -> A + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells rsegs m' A cs).
{ intros A cs H HB. eapply rw_cells_transport; eauto. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact C1 | unfold RCTX; cbn; lia].
+ eapply u64arr_transport; eauto. apply D. unfold actives. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
+ eapply u64arr_transport; eauto. apply D. unfold usages. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
+ eapply u8arr_transport; eauto. apply D. unfold unmap_seqs. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
+ eapply u8arr_transport; eauto. apply D. unfold bouncess. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
+ apply TC; [exact C6 | unfold RCTX; cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact G1 | unfold RMLOCK; cbn; lia].
+ apply TC; [exact G2 | unfold RNEED_LOCKS; cbn; lia].
+ apply TC; [exact G3 | unfold RPAGE_SIZE; cbn; lia].
+ apply TC; [exact G4 | unfold RGOT_SSP; cbn; lia].
+ apply TC; [exact G5 | unfold RSSP_GUARD; cbn; lia].
+ apply TC; [exact G6 | cbn; lia].
- intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil.
split; [|split].
+ apply TC; [exact A1 | cbn; lia].
+ intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
+ apply TC; [exact A3 | cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Sb0 & Sb1 & SbL & RB0 & RBAL & RBC). pose_ceil.
apply TC; [exact R | cbn; lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
destruct (WR rid r Hr) as (B0 & BAL & L0 & BC & _). pose_ceil.
split.
+ eapply wr_at_transport; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. apply D. cbn. lia.
Qed.
End SE.
Lemma rmrep_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "F'RB'TKyR0%211':y8%511%311p051'C&S>r3r2%3221&S0r4%2241%7216p051pZ<:1pXF<1pYBE1").
Proof.
intros st m t (WF & CX & GL & AR & GR & SH).
split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
- eapply rmrep_ctx_ext; [reflexivity | intros; reflexivity | exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [intros; reflexivity | intros; reflexivity | exact (AR a ar Ha)].
- intros b gh Hb. eapply rgroup_rep_ext; [intros; reflexivity | exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity | exact (SH rid r Hr Hk)].
Qed.
Section SE.
Local Abbreviation SEC_T_rwr_at_bytes_exist := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocRep "QD'TKyR0%211':y8%511%311p051'D&QD&S8r3r2r1%544321&SGz%2215'B&SEr4%221:+RPP0%8221+mXP0%:215%8231'@'7%11H'>'?'8&6%12ME&SNr5%211%73641&Q<r7r6%34Q021M%=251qX:?1%B2@1p0D1p0N1p0Q21pXJQ91pX2Q:1pXFQ<1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rwr_at_bytes_exist) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rwr_at_bytes_exist) 1%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_rwr_at_bytes_exist) 2%nat 0%nat).
Lemma rwr_at_bytes_exist : ltac:(sec_stmt2 constr:(SEC_T_rwr_at_bytes_exist) 3%nat 0%nat).
Proof.
intros (A0 & An & W) Hn Himg.
assert (G : forall i, 0 <= i < n -> exists b, mrd rsegs m (wa (a + i)) = Some b).
{ intros i Hi. specialize (W i Hi). rewrite ref_wview_overlay in W by (rewrite wa_unsigned by lia; lia).
rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
destruct (m (wa (a + i))) as [b|]; [exists b; reflexivity| exfalso; apply W; reflexivity]. }
assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at rsegs m (a + (n - Z.of_nat k)) bs).
{ induction k as [|k IH]; intros Hk.
- exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- destruct (IH ltac:(lia)) as (bs & L & B). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
exists (b :: bs). split; [cbn; lia|].
change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
+ split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. exact Hb.
+ cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (a + (n - Z.of_nat (S k)) + 1) with (a + (n - Z.of_nat k)) by lia. exact B. }
destruct (REC (Z.to_nat n) ltac:(lia)) as (bs & L & B). exists bs. split; [exact L|].
replace (a + (n - Z.of_nat (Z.to_nat n))) with a in B by lia. exact B.
Qed.
End SE.
End CEIL_WRAP_1.
