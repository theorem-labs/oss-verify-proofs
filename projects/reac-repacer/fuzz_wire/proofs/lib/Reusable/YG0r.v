(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0r.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the empty-depot switch (DepotCfg.depot_has_trace) taken from proofs/libreac/fuzz_knock/lib/Reusable/YG0r.v at 88154566652a, hunk by hunk (provenance evidence/depot: depot-classes.tsv, depot_apply.py): hunks 1 2 3 4 5 6 7 8 9 10; no hunk keeps this file's text. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YG0r.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n DepotCfg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section j.
Variable B : asyms.
Variable ly : alayout.
Variable rd : reader.
Local Notation ev := (aeval B ly).
Lemma le_byte_0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite (Z.shiftr_0_l (8 * Z.of_nat k)). reflexivity. Qed.
Lemma cell_zero_of_range : forall e0 len a w,
range_zero B ly rd (e0, len) -> 0 <= ev a - ev e0 -> ev a - ev e0 + Z.of_nat w <= len ->
cell_holds B ly rd (ACell a w (AV (ANum 0))).
Proof.
intros e0 len a w Hz Hlo Hhi k Hk. cbn [c_val c_at c_w aeval] in Hk |- *. rewrite le_byte_0.
replace (ev a + Z.of_nat k) with (ev e0 + (ev a - ev e0 + Z.of_nat k)); [|lia]. apply (Hz (ev a - ev e0 + Z.of_nat k)). cbn [fst snd]. lia.
Qed.
Lemma range_vis_of_zero : forall r, range_zero B ly rd r -> range_vis B ly rd r.
Proof. intros r Hz i Hi. rewrite (Hz i Hi). discriminate. Qed.
Lemma range_vis_sub : forall e0 len e len', range_vis B ly rd (e0, len) -> 0 <= ev e - ev e0 -> ev e - ev e0 + len' <= len ->
range_vis B ly rd (e, len').
Proof.
intros e0 len e len' Hv Hlo Hhi i Hi. cbn [fst snd] in *.
replace (ev e + i) with (ev e0 + (ev e - ev e0 + i)); [|lia]. apply (Hv (ev e - ev e0 + i)). cbn [fst snd]. lia.
Qed.
Lemma range_zero_sub : forall e0 len e len', range_zero B ly rd (e0, len) -> 0 <= ev e - ev e0 -> ev e - ev e0 + len' <= len ->
range_zero B ly rd (e, len').
Proof.
intros e0 len e len' Hv Hlo Hhi i Hi. cbn [fst snd] in *.
replace (ev e + i) with (ev e0 + (ev e - ev e0 + i)); [|lia]. apply (Hv (ev e - ev e0 + i)). cbn [fst snd]. lia.
Qed.
Record init_facts : Prop := {
if_universe : universe_ok (as_universe B);
if_syms : asyms_ok B;
if_layout : layout_ok ly;
if_const : Forall (cell_holds B ly rd) (as_const B ly);
if_const_owned : Forall (cell_owned B ly) (as_const B ly);
if_rinfo : range_zero B ly rd (ASp kRegionInfoOff, 4096);
if_thread : range_zero B ly rd (AT t_qc, kThreadObjSize - t_qc);
if_thread_vis : range_vis B ly rd (AT 0, kThreadObjSize);
if_fs_hints : range_zero B ly rd (AF 0, 88);
if_fs_flags : range_zero B ly rd (AF 96, kFakeFramesOff - 96);
if_fs_log : cell_holds B ly rd (z8 (AF 88) kStackSizeLog);
if_fs_vis : range_vis B ly rd (AF 0, kFakeStackSize);
if_ialloc : range_zero B ly rd (AIal 0, as_ialloc_hi B - as_ialloc_lo B);
if_ialloc_flag : range_zero B ly rd (ANum (as_ialloc_flag B), 2);
if_inst_sec : range_zero B ly rd (AInst o_sec_reserved, 16);
if_inst_secmutex : range_zero B ly rd (AInst o_sec_mutex, 1);
if_inst_quar : range_zero B ly rd (AInst o_q_cmutex, 2);
if_inst_qcache : range_zero B ly rd (AInst o_q_size, 32);
if_inst_vis : range_vis B ly rd (AInst 0, 3632);
if_oom_vis : range_vis B ly rd (ANum (as_oom_byte B), 1);
if_depot_nuniq : depot_pick (cell_holds B ly rd (z4 (ADepot d_nuniq) 1)) (cell_holds B ly rd (z4 (ADepot d_nuniq) 0));
if_depot_map1 : depot_pick (cell_holds B ly rd (c8 (ADepot d_map1) (ANB 0))) (cell_holds B ly rd (z8 (ADepot d_map1) 0));
if_depot_vis : range_vis B ly rd (ADepot d_nuniq, 32);
if_store_total : depot_pick (cell_holds B ly rd (z8 (AStore s_total) (Z.of_nat (length (ly_tr0 ly)) + 1)))
(cell_holds B ly rd (z8 (AStore s_total) 0));
if_store_block : depot_pick (cell_holds B ly rd (c8 (AStore s_block0) (ASB 0))) (cell_holds B ly rd (z8 (AStore s_block0) 0));
if_store_vis : range_vis B ly rd (AStore 0, 32);
if_nb_vis : depot_pick (range_vis B ly rd (ANB 0, kNodesBlockSize)) (ly_NB ly = 0);
if_sb_vis : depot_pick (range_vis B ly rd (ASB 0, kStoreBlockSize)) (ly_SB ly = 0);
if_tab : depot_pick (exists b1, 0 <= b1 < d_tab_words /\ ((as_dhash B (ly_tr0 ly)) mod 2 ^ 64) mod d_tab_words = b1 /\
rd32 rd (as_depot B + 4 * b1) 1 /\
(forall b, 0 <= b < d_tab_words -> b <> b1 -> rd32 rd (as_depot B + 4 * b) 0))
(forall b, 0 <= b < d_tab_words -> rd32 rd (as_depot B + 4 * b) 0);
(* Without a start-up trace this field carries the words a first StackDepotPut reads before it maps anything, and
   StackStore::allocated_: all 0 at main (.bss, read through the image ROM). *)
if_node1 : depot_pick (rd64 rd (ly_NB ly + 16) ((as_dhash B (ly_tr0 ly)) mod 2 ^ 64) /\ rd32 rd (ly_NB ly + 16 + 8) 0)
(Forall (cell_holds B ly rd) [ z4 (ADepot d_mu) 0; z4 (AStore s_stored0) 0; z4 (AStore s_mtx0) 0; z8 (AStore s_alloc) 0 ]);
if_junk : Forall (range_vis B ly rd) (as_junk B ly);
if_zshadow : zshadow_ok B ly rd;
if_tsd : ly_tsd ly = as_tsd B;
if_fsh_vis : range_vis B ly rd (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8);
if_static_img : Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)
}.
Lemma zseq_In : forall lo n x, In x (zseq lo n) -> lo <= x < lo + Z.max n 0.
Proof.
intros lo n x H. unfold zseq in H. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. lia.
Qed.
Lemma Forall_flat_map {X Y} : forall (P : Y -> Prop) (f : X -> list Y) (l : list X),
(forall x, In x l -> Forall P (f x)) -> Forall P (flat_map f l).
Proof.
intros P f l H. induction l as [|a t IH]; cbn; [constructor|].
apply Forall_app. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx].
Qed.
Lemma aoff_ok : forall o d, aeval B ly (aoff (ASp o) d) = aeval B ly (ASp o) + d.
Proof. intros. cbn. lia. Qed.
Lemma Forall_app2 {X} : forall (P : X -> Prop) l1 l2, Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros P l1 l2 H1 H2. apply (proj2 (Forall_app P l1 l2)). split; assumption. Qed.
Hypothesis IF : init_facts.
Ltac uoffs := unfold o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex,
o_comb_stats, o_quar, o_q_max, o_q_min, o_q_maxcache, o_q_cmutex, o_q_rmutex, o_q_size, o_q_first, o_q_last, o_q_bytes,
t_qc, t_cache, t_cache_stats, t_stats, t_unwinding, d_nuniq, d_map1, s_total, s_block0,
kThreadObjSize, kFakeFlagsOff, kFakeFramesOff in *.
Ltac cbnk := cbn -[kRegionInfoOff kFakeStackSize kNodesBlockSize kStoreBlockSize kPrimResvSize kSpaceSize d_tab_words Z.pow].
Ltac zc Z0 := eapply cell_zero_of_range; [exact Z0 | cbnk; uoffs; lia | cbnk; uoffs; lia].
Lemma region_cells_init : forall c, 1 <= c <= 31 -> Forall (cell_holds B ly rd) (region_cells init_state c).
Proof.
intros c Hc. unfold region_cells. rewrite reg_init. cbn [rg_free fa_len rg_mapped_fa rg_alloc_user rg_mapped_user region0].
pose proof (if_rinfo IF) as Z0.
repeat apply Forall_cons; try apply Forall_nil; zc Z0.
Qed.
Lemma cache_cells_init : forall c, 1 <= c <= 31 -> Forall (cell_holds B ly rd) (cache_cells init_state c).
Proof.
intros c Hc. unfold cache_cells. cbn [st_cache_inited init_state].
pose proof (if_thread IF) as Z0.
repeat apply Forall_cons; try apply Forall_nil; zc Z0.
Qed.
Lemma sec_cells_init : Forall (cell_holds B ly rd) (sec_cells init_state).
Proof.
unfold sec_cells. cbn [st_sec_reserved st_sec_arr st_chunks init_state length seq combine map flat_map app].
pose proof (if_inst_sec IF) as Z0. pose proof (if_inst_secmutex IF) as Z1.
constructor; [|constructor; [|constructor; [|constructor]]].
- zc Z0.
- change (Z.of_nat 0) with 0. zc Z0.
- zc Z1.
Qed.
Lemma quar_cells_init : Forall (cell_holds B ly rd) (quar_cells init_state).
Proof.
unfold quar_cells, qc_cells. cbn [st_qthread st_qglobal init_state qc_list qc_bytes qc0 length rev batch_cells app].
pose proof (if_inst_quar IF) as Z0. pose proof (if_inst_qcache IF) as Z1. pose proof (if_thread IF) as Z2.
change (Z.of_nat 0) with 0.
repeat apply Forall_cons; try apply Forall_nil.
- zc Z0.
- zc Z0.
- zc Z2.
- zc Z2.
- zc Z2.
- zc Z2.
- zc Z1.
- zc Z1.
- zc Z1.
- zc Z1.
Qed.
Lemma fs_cells_init : Forall (cell_holds B ly rd) (fs_cells init_state).
Proof.
unfold fs_cells. cbn [st_fs init_state fs_hint repeat seq combine map].
pose proof (if_fs_hints IF) as Z0. pose proof (if_fs_flags IF) as Z1.
apply Forall_cons; [exact (if_fs_log IF)|]. apply Forall_cons.
- zc Z1.
- repeat apply Forall_cons; try apply Forall_nil;
(zc Z0).
Qed.
Lemma depot_cells_init : Forall (cell_holds B ly rd) (depot_cells ly init_state).
Proof.
unfold depot_cells. cbn [depot_ids depot_frames st_depot init_state length fold_right].
lazymatch eval cbv in depot_has_trace with true => rewrite Z.add_0_r | false => idtac end.
apply Forall_cons; [exact (if_depot_nuniq IF)|]. apply Forall_cons; [exact (if_depot_map1 IF)|].
apply Forall_cons; [exact (if_store_total IF)|]. apply Forall_cons; [exact (if_store_block IF)|].
lazymatch eval cbv in depot_has_trace with
| true => apply Forall_nil
| false => exact (if_node1 IF)
end.
Qed.
Lemma ialloc_cells_init : Forall (cell_holds B ly rd) (ialloc_cells B init_state).
Proof.
unfold ialloc_cells. cbn [st_internal_inited init_state].
pose proof (if_ialloc IF) as Z0. pose proof (if_ialloc_flag IF) as Z1. pose proof (aso_ialloc _ (if_syms IF)) as [W1 W2].
repeat apply Forall_cons; try apply Forall_nil.
- zc Z1.
- zc Z1.
- zc Z0.
- zc Z0.
Qed.
Lemma acells_init : Forall (cell_holds B ly rd) (acells B ly init_state).
Proof.
unfold acells.
apply Forall_app2; [apply Forall_flat_map; intros c Hc; apply zseq_In in Hc; apply region_cells_init; lia|].
apply Forall_app2; [apply Forall_flat_map; intros c Hc; apply zseq_In in Hc; apply cache_cells_init; lia|].
apply Forall_app2; [cbn; apply Forall_nil|].
apply Forall_app2; [apply sec_cells_init|].
apply Forall_app2; [apply quar_cells_init|].
apply Forall_app2; [apply fs_cells_init|].
apply Forall_app2; [apply depot_cells_init|].
apply Forall_app2; [apply ialloc_cells_init|].
unfold thread_cells. pose proof (if_thread IF) as Z2. apply Forall_cons; [zc Z2 | apply Forall_nil].
Qed.
Lemma fs_flags_fit : forall cid pos, 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
0 <= fs_flags_off cid /\ fs_flags_off cid + pos < 32768.
Proof.
assert (H : zall (Z.to_nat (10 - 0 + 1)) 0 (fun c => (0 <=? fs_flags_off c) && (fs_flags_off c + fs_frames c <=? 32768)) = true)
by (vm_compute; reflexivity).
intros cid pos Hc Hp. pose proof (zall_range 0 10 _ H cid Hc) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma fs_flags_init : fs_flags_ok ly rd init_state.
Proof.
intros cid pos Hc Hp. cbn [frames init_state st_fs fs_live mem_pos].
pose proof (fs_flags_fit cid pos Hc Hp) as [F1 F2]. pose proof (if_fs_flags IF) as Z1.
unfold flag_addr, fs_flag_off. specialize (Z1 (kFakeFlagsOff + fs_flags_off cid + pos - 96)).
cbn [fst snd aeval] in Z1. unfold kFakeFlagsOff, kFakeFramesOff in *.
replace (ly_F ly + (4096 + fs_flags_off cid + pos)) with (ly_F ly + 96 + (4096 + fs_flags_off cid + pos - 96)); [|lia].
apply Z1. lia.
Qed.
Lemma fa_entries_init : fa_entries_ok ly rd init_state.
Proof. intros c i v Hc Hi. rewrite reg_init in Hi. cbn in Hi. lia. Qed.
Lemma depot_init : depot_ok B ly rd init_state.
Proof.
lazymatch eval cbv in depot_has_trace with
| true =>
destruct (if_tab IF) as (b1 & Hb1 & Hh & T1 & T0); destruct (if_node1 IF) as [N1 N2];
exists (fun b => if b =? b1 then 1 else 0), (fun _ => 0);
unfold depot_ids, depot_traces; cbn [st_depot init_state length Z.of_nat Z.add Pos.add];
split; [|split];
[ intros b Hb; destruct (b =? b1) eqn:E;
  [ apply Z.eqb_eq in E; subst b; split; [lia | exact T1]
  | apply Z.eqb_neq in E; split; [lia | exact (T0 b Hb E)] ]
| intros id Hid; assert (id = 1) by lia; subst id; cbn [Z.to_nat Z.sub nth Pos.to_nat Z.mul Pos.mul];
  split; [lia|]; split; [exact N1 | ]; replace (ly_NB ly + (16 * 1 + 8)) with (ly_NB ly + 16 + 8); [exact N2 | lia]
| intros id Hid; assert (id = 1) by lia; subst id; change (Z.to_nat (1 - 1)) with 0%nat;
  cbn [nth chain_has Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Hh, Z.eqb_refl; split; [lia | left; reflexivity] ]
| false =>
unfold depot_ok; cbn [st_depot st_chunks init_state];
split; [reflexivity |]; split; [exact (if_tab IF) |];
split; [split; [intros _; split; [exact (if_nb_vis IF) | exact (if_sb_vis IF)] | intros _; reflexivity] |];
intros (k & Hk); destruct Hk
end.
Qed.
Lemma ashadow_init : forall g, ashadow B ly init_state g = None.
Proof.
intros g. unfold ashadow. cbn [st_chunks init_state find_chunk_at].
assert (E : in_rangesb g (fa_poison_ranges ly init_state) = false); [|rewrite E; reflexivity].
unfold fa_poison_ranges. cbn [st_chunks init_state flat_map app]. rewrite app_nil_r.
assert (G : forall l, in_rangesb g (flat_map (fun c => [(region_base ly c, rg_mapped_user (reg init_state c)); (fa_base ly c, rg_mapped_fa (reg init_state c))]) l) = false).
{ induction l as [|c t IH]; [reflexivity|]. cbn [flat_map app in_rangesb]. rewrite reg_init. cbn [rg_mapped_user rg_mapped_fa region0].
rewrite IH. rewrite !Z.add_0_r.
destruct (Z.leb_spec (region_base ly c) g); destruct (Z.ltb_spec g (region_base ly c)); try lia; cbn;
destruct (Z.leb_spec (fa_base ly c) g); destruct (Z.ltb_spec g (fa_base ly c)); try lia; reflexivity. }
apply G.
Qed.
Lemma range_vis_nil : forall e, range_vis B ly rd (e, 0).
Proof. intros e i Hi. cbn in Hi. lia. Qed.
Lemma ajunk_init : Forall (range_vis B ly rd) (ajunk B ly init_state).
Proof.
pose proof (range_vis_of_zero _ (if_rinfo IF)) as V0. pose proof (if_thread_vis IF) as VT.
pose proof (if_inst_vis IF) as VI.
unfold ajunk. apply Forall_cons; [eapply range_vis_sub; [exact V0 | cbnk; lia | cbnk; lia]|].
apply Forall_cons; [apply range_vis_nil|].
apply Forall_app2.
{ apply Forall_flat_map. intros c Hc. apply zseq_In in Hc. unfold region_junk.
repeat apply Forall_cons; try apply Forall_nil; (eapply range_vis_sub; [exact V0 | cbnk; lia | cbnk; lia]). }
apply Forall_app2.
{ apply Forall_flat_map. intros c Hc. apply zseq_In in Hc. unfold cache_junk. cbn [st_cache_inited init_state].
apply Forall_cons; [|apply Forall_nil]. eapply range_vis_sub; [exact VT | cbnk; uoffs; lia | cbnk; uoffs; lia]. }
apply Forall_app2; [cbn; apply Forall_nil|].
apply Forall_app2.
{ unfold sec_junk. cbn [st_sec_arr st_sec_reserved st_chunks init_state length flat_map app].
apply Forall_cons; [eapply range_vis_sub; [exact VI | cbnk; uoffs; lia | cbnk; uoffs; lia]|].
apply Forall_cons; [eapply range_vis_sub; [exact VI | cbnk; uoffs; lia | cbnk; uoffs; lia]|].
apply Forall_cons; [apply range_vis_nil | apply Forall_nil]. }
apply Forall_app2; [cbn; apply Forall_nil|].
apply Forall_app2.
{ unfold thread_junk. repeat apply Forall_cons; try apply Forall_nil; (eapply range_vis_sub; [exact VT | cbnk; uoffs; lia | cbnk; uoffs; lia]). }
apply Forall_app2; [|exact (if_junk IF)].
apply Forall_cons; [exact (if_oom_vis IF)|].
apply Forall_cons; [eapply range_vis_sub; [exact (if_depot_vis IF) | cbnk; uoffs; lia | cbnk; uoffs; lia]|].
apply Forall_cons; [eapply range_vis_sub; [exact (if_store_vis IF) | cbnk; uoffs; lia | cbnk; uoffs; lia]|].
apply Forall_cons; [eapply range_vis_sub; [exact (if_store_vis IF) | cbnk; uoffs; lia | cbnk; uoffs; lia]|].
apply Forall_nil.
Qed.
Lemma aareas_init : Forall (range_vis B ly rd) (aareas init_state).
Proof.
unfold aareas. cbn [st_sec_reserved st_chunks init_state flat_map].
apply Forall_app2.
{ apply Forall_flat_map. intros c Hc. rewrite reg_init. cbn [rg_mapped_user rg_mapped_fa region0].
apply Forall_cons; [apply range_vis_nil|]. apply Forall_cons; [apply range_vis_nil | apply Forall_nil]. }
apply Forall_app2; [apply Forall_cons; [apply range_vis_nil | apply Forall_nil]|].
apply Forall_app2; [cbn; apply Forall_nil|].
apply Forall_cons; [exact (if_fs_vis IF)|].
apply Forall_cons; [lazymatch eval cbv in depot_has_trace with true => exact (if_nb_vis IF) | false => cbn [st_depot]; apply range_vis_nil end|].
apply Forall_cons; [lazymatch eval cbv in depot_has_trace with true => exact (if_sb_vis IF) | false => cbn [st_depot]; apply range_vis_nil end|].
apply Forall_cons; [exact (if_thread_vis IF)|].
apply Forall_cons; [exact (range_vis_of_zero _ (if_rinfo IF)) |]. apply Forall_cons; [exact (if_fsh_vis IF) | apply Forall_nil].
Qed.
Lemma azero_init : Forall (range_zero B ly rd) (ialloc_zero B).
Proof.
pose proof (if_ialloc IF) as Z0. pose proof (aso_ialloc _ (if_syms IF)) as [W1 W2]. unfold ialloc_zero.
apply Forall_cons; [eapply range_zero_sub; [exact Z0 | cbnk; lia | cbnk; lia]|].
apply Forall_cons; [eapply range_zero_sub; [exact Z0 | cbnk; lia | cbnk; lia] | apply Forall_nil].
Qed.
Theorem ARm_init_intro : ARm B ly init_state rd.
Proof.
constructor.
- apply wf_init.
- exact (if_universe IF).
- exact (if_syms IF).
- exact (if_layout IF).
- split; [cbn; apply Forall_nil|]. cbn [sec_extents st_chunks init_state flat_map app]. exact (lo_disj _ (if_layout IF)).
- exact (if_const IF).
- exact (if_const_owned IF).
- apply acells_init.
- apply fa_entries_init.
- apply fs_flags_init.
- apply depot_init.
- intros g v Hg Hv. rewrite ashadow_init in Hv. discriminate.
- exact (if_zshadow IF).
- apply ajunk_init.
- apply aareas_init.
- cbn. apply Forall_nil.
- apply azero_init.
- exact (if_tsd IF).
- exact (if_static_img IF).
Qed.
End j.
End h.
