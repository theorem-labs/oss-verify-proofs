(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F F_ntf_G F_ntf_H.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocFacts_Bpres.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_ntf () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["1fst"; "1option"; "1prod"; "1snd"; "2eq"; "3N"; "3Z"; "4rdv"; "5oracle_ok"; "6gmeta_ok"; "7mw_ok"; "8mem"; "8pans_mem"; "9Known"; "9aptr"; "9cell_read"]; ["9cellval"; "9get_meta_rec"; "9get_shadow"; "9mstate"; "9region"; "9s_regions"; "9s_shadow"; "9shadow"; "0g"; "0m"; "0o"; "0p"; "0q"; "0st"; "0st'"; ":bv"]; [";N_countable"; "<gmap"; "=eq_dec"; "0v"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma gmeta_mw : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_ntf "@'C&>'9r3r2r1%43321&:&Ar4%2217%411p061pQH<1pQB=1pQL?1").
Proof. intros st g p.
intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
unfold mw_ok. repeat split; lia.
Qed.
Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
nontrivial_free dec (S f) st g i k bail =
let mr := get_meta_rec st g in
let sc := m_sizeclass mr in
if ntf_cond st g i then
match m_next mr with
| Some _ =>
guard 50 (sc <? 48) (
let activate_new := optr_eqb (active st sc) (Some g) in
let st1 := dequeue (LActive sc) g st in
match activate_new, active st1 sc with
| true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
| _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
end) bail
| None => free_group R dec (nontrivial_free dec f) st g k bail
end
else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
guard 51 (sc <? 48) (
if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
else k (aor_st st g i) None) bail
else k (aor_st st g i) None.
Proof. reflexivity. Qed.
Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
free_group R dec rec st g k bail =
let mr := get_meta_rec st g in
let st1 := fg_usage_st st g in
match m_mem mr with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some p =>
let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
if negb (m_maplen mr =? 0) then
free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
else
dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
end.
Proof. reflexivity. Qed.
Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
match mi with
| None => a1v = wz 0
| Some (b, len) =>
a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
/\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
/\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
end.
Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
8 <= (r_base r + q) mod 16 ->
cell_read (get_shadow st rid) q = Unknown h ->
o (wa (r_base r + q)) = m (wa (r_base r + q)).
Lemma oracle_ok_frame : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_ntf "Q9'OyR0%211'1y8%511%311p051'C&8r4r3r2%43321'4'Q1'5&Q2&Q0'D%544321&E%11:%21<%:3421'G%;4:981&F%11A%21C%@3421r7r6%H321Gp041p0;1p0G1pQNM1pQLN1pQDQ01pQFQ11").
Proof. intros o m st st'.
intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.
Lemma rdv_known : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_ntf "Q1&;'C'2'5'6%3221'4'@&?&Br3&0r2%23:91%5241&3%13=<4%9231(=r1%211%?3>41&7&<r5r4%45J321@%E3G1?p071pR8I1pQJI1pQLN1pQFQ01").
Proof. intros o st q v. intros H. unfold rdv. rewrite H. reflexivity. Qed.
Lemma implT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
(m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> implT o (k (queue_st h g st0)) s Q ms) ->
implT o (queue h g st0 k bail) s Q ms.
Proof.
intros H. unfold queue. apply implT_guard. intros G1. apply implT_guard. intros G2.
assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.
End CEIL_WRAP_1.
