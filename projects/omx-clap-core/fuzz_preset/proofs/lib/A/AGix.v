(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: the depot bound in the P'' form (depot_fits / depot_len_bound, YG01.v), as fuzz_preset's YFix / YFjb / YFju do at commit 116f6c4dab1; the call's trace premise stays In-form here and is converted to the released contract's `admits` with admits_fix (YG01.v:184). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGix.v (a working branch 84ee52cd012, file sha256 759e0b2b69bc) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 5 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; 2 hand maps (the internal file agreloc-resolve-A.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at d1f93c50c87) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc 0474699fc83547e0 (a working branch 83209f9d9cd8), --assume-source, --resolve the internal file resolve-102.txt (0 lines name this file); 3 numerals changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's P'' delta to proofs/cgif/cgif_file_fuzzer/lib/AGix.v (84ee52cd012 -> a working branch a9d93b8c304 = cf layer ae2fa80b0325 + lanes H / M, file sha256 b2a59546fe07) applied at A' by a 3-way merge: base = the 84ee52cd012 text relocated cgif -> A', theirs = the a9d93b8c304 text relocated the same way, ours = this file; 5 lines changed, no numeral in the delta. *)
(* cgif_file's frame-free facts for the hit-g arm of Allocate, ported from YFix.v (the same scripts without the walk's
   frame):
   - section c: the constant cells' zone (AGImgA.CZONE), the depot's memory facts and the depot callee (YFix.D1W_ok
     made generic in the stack pointer and the trace buffer);
   - section o: the model facts of the pop (the final state's parts) and the allocator memory the walk writes
     (YFix.WR_owned without its stack window). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import EVroom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFhy AGhy AGis AFi3 AGImgA AGiy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
(* A one-frame trace: AGis's range lemmas take the walk's trace (and its length bound) as arguments their
   statements do not use. *)
Lemma dtrlen : (1 <= length [0] <= 30)%nat.
Proof. cbn. lia. Qed.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order. *)
Set Default Proof Using "All".
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Definition abs_cell_ok (c : acell) : bool :=
match c_at c with
| ANum a => (0x10000 <=? a) && ((a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x600000) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x800b8000)))
| _ => false
end.
Lemma abs_cells_ok : forallb abs_cell_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof using. vm_compute. reflexivity. Qed.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* Section c: the constant cells and the depot.                                                                     *)
Section c.
Variables (B : asyms) (ly : alayout).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Local Abbreviation DZONE := (@AGis.DZONE ly).
Local Abbreviation blocks_facts := (@AGis.blocks_facts _ ly LY IMG).
Lemma const_cells_zone : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> CZONE ly (aeval B ly (c_at c) + k).
Proof.
intros c k Hin Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. unfold CZONE.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD;
unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, kStackSpan in *; zlia |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_ok c Hin) as Hc. unfold abs_cell_ok in Hc.
destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval].
apply andb_prop in Hc as [Hz Hc]. apply Z.leb_le in Hz.
apply Bool.orb_prop in Hc. unfold CZONE. destruct Hc as [Hc|Hc]; [apply Z.leb_le in Hc; zlia|].
apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. zlia.
Qed.
Lemma CZONE_range : forall a, CZONE ly a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof (lo_app ly LY) as HA. pose proof ASAN_CEIL_range as [CR _].
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth' _ _ 6 _ HA eq_refl) as IC. pose proof (Forall_nth' _ _ 7 _ HA eq_refl) as ID.
cbn beta in IT, IC, ID. cbn [fst snd] in IT, IC, ID. unfold in_app, CZONE, TFIB_TSD, kThreadObjSize, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma DZONE_range : forall a, DZONE a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _). unfold DZONE in Ha.
clear - Ha NBhi SBhi. numconst. zlia.
Qed.
Lemma cell_holds_agree : forall (rd rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by zlia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by zlia. rewrite Z.add_0_r. exact Hb.
Qed.
Lemma cell_holds_agree2 : forall (rd1 rd2 rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd' c.
Proof.
intros rd1 rd2 rd' c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(zlia)) as [E|E]; rewrite E; [exact (H1 k Hk) | exact (H2 k Hk)].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
destruct (He 0 ltac:(zlia)) as [E|E]; rewrite Z.add_0_r in E; rewrite E; [exists b1 | exists b2]; tauto.
Qed.
Lemma aview_agree : forall (W : world tfibsegs) (mem mem' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a.
Proof using. intros W mem mem' a Ha He. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) mem mem' a He). reflexivity. Qed.
Lemma const_kept : forall (W : world tfibsegs) mem1 mem2, Forall (cell_holds B ly (aview tfibsegs (w_H W) mem1)) (as_const B ly) ->
(forall x : word, CZONE ly (bv_unsigned x) -> mem2 x = mem1 x) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem2)) (as_const B ly).
Proof.
intros W mem1 mem2 HC He. apply Forall_forall. intros c Hc.
apply (cell_holds_agree (aview tfibsegs (w_H W) mem1)); [| exact (proj1 (Forall_forall _ _) HC c Hc)].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (CZONE_range _ Z1) as R.
apply aview_agree; [exact R|]. apply He. rewrite unsigned_lit_small by exact R. exact Z1.
Qed.
Lemma depot_ids_bound : forall S', depot_fits (as_universe B) (st_depot S') -> depot_ids S' <= 4097.
Proof.
intros S' HD. pose proof (depot_len_bound _ _ (ts_universe B TS) HD) as DLEN. unfold depot_ids, DEPOT_MAX in *. zlia.
Qed.
Lemma depot_mem_ok_agree : forall S' (rd rd' : reader), depot_ids S' <= 4098 ->
(forall a, DZONE a -> rd' a = rd a) -> depot_mem_ok B ly S' rd -> depot_mem_ok B ly S' rd'.
Proof.
intros S' rd rd' HID He (D1' & D2 & D3). pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + d_map1 + 8) \/ (TFIB_STORE <= a < TFIB_STORE + 32) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. apply He. unfold DZONE, TFIB_DEPOT, TFIB_STORE, d_map1 in *. zlia. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (cell_holds_agree rd); [| exact (proj1 (Forall_forall _ _) D1' c Hc)].
intros k Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk; rewrite ?ED, ?ES; unfold d_nuniq, d_map1, s_total, s_block0 in *; zlia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
+ intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|].
rewrite ED. unfold d_tab_words, d_map1 in *. zlia.
+ intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
* intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. unfold kNodesBlockSize. zlia.
* intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. unfold kNodesBlockSize. zlia.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; rewrite ?ED, ?ES; unfold d_nuniq, d_map1 in *; zlia.
Qed.
Lemma depot_ok_ext : forall S1 S2 (rd : reader), st_depot S1 = st_depot S2 -> depot_ok B ly rd S1 -> depot_ok B ly rd S2.
Proof. intros S1 S2 rd E. unfold depot_ok, depot_ids, depot_traces. rewrite E. exact (fun H => H). Qed.
(* The depot's memory facts read the model only through its depot. *)
Lemma depot_mem_ok_ext : forall S1 S2 (rd : reader), st_depot S1 = st_depot S2 -> depot_mem_ok B ly S1 rd -> depot_mem_ok B ly S2 rd.
Proof.
intros S1 S2 rd E (D1 & D2 & D3). split; [|split; [exact (depot_ok_ext S1 S2 rd E D2) | exact D3]].
replace (depot_cells ly S2) with (depot_cells ly S1) by (unfold depot_cells, depot_ids, depot_frames; rewrite E; reflexivity). exact D1.
Qed.
Lemma depot_at0 : forall S (W : world tfibsegs) mem0, ARm B ly S (aview tfibsegs (w_H W) mem0) -> depot_mem_ok B ly S (aview tfibsegs (w_H W) mem0).
Proof.
intros S W mem0 HARm. set (rd0 := aview tfibsegs (w_H W) mem0) in *.
split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm)).
unfold acells. do 6 (apply in_or_app; right). apply in_or_app. left. exact Hc.
- exact (am_depot B ly S rd0 HARm).
- apply Forall_forall. intros r Hr. cbn in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
1-3: apply (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm)); unfold ajunk; right; right; do 6 (apply in_or_app; right); apply in_or_app; left; cbn; tauto.
all: apply (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm)); unfold aareas; do 3 (apply in_or_app; right); cbn; tauto.
Qed.
Lemma footprint_DZONE : forall a, depot_footprint B ly a -> DZONE a.
Proof.
intros a FP. unfold depot_footprint, DZONE in *. rewrite (ts_depot B TS), (ts_store B TS) in FP.
unfold TFIB_DEPOT, TFIB_STORE, d_map1 in FP. zlia.
Qed.
(* The depot callee (YFix.D1W_ok for any stack pointer and trace buffer): entered with the depot and the constant
   cells as at mem0, it returns the depot's answer, the depot's memory facts after the put and the constant cells. *)
Lemma depot_call : tfib_depot_spec B ->
forall (W : world tfibsegs) S mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
AR tfibsegs B ly S W mem0 md0 -> In tr (as_universe B) ->
(forall x : word, DZONE (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(aok S (KDepot tr) z /\ depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs (w_H W) mem') /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly))).
Proof.
intros HD1 W S mem0 md0 tr regs mem md buf HAR Htr MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
pose proof (proj1 HAR) as HARm. pose proof (am_wf _ _ _ _ HARm) as WF.
assert (CST : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)).
{ apply (const_kept W mem0); [exact (am_const B ly S _ HARm)|]. intros x Hx. apply MEQ. right. exact Hx. }
assert (DEP : depot_mem_ok B ly S (aview tfibsegs (w_H W) mem)).
{ apply (depot_mem_ok_agree S (aview tfibsegs (w_H W) mem0)).
- pose proof (depot_ids_bound S (wf_depot _ _ _ _ _ WF)). zlia.
- intros a Ha. pose proof (DZONE_range a Ha) as Ra.
apply aview_agree; [exact Ra|]. apply MEQ. left. rewrite unsigned_lit_small by exact Ra. exact Ha.
- exact (depot_at0 S W mem0 HARm). }
eapply SRr_mono.
{ exact (HD1 W ly S regs mem md buf tr LY IMG WF (admits_fix _ _ S (ts_universe B TS) Htr) CST DEP R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES). }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [reflexivity|]. split; [exact RP|]. split; [|split; [exact PR'| exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [exact N1|]. intros FP. apply N2. exact (footprint_DZONE _ FP).
Qed.
End c.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* Section o: the pop's model facts and the memory the hit-g walk writes, for the cached chunk at class-region offset *)
(* off = 16 * v of class cl, size n with redzone class kz, depot trace tr.                                          *)
Section o.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v kz : Z) (S : astate) (l : list Z) (off : Z) (tr : list Z).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Let T : Z := ly_T ly.
Local Abbreviation RZ := (@AGis.RZ kz).
Local Abbreviation R8v := (@AGis.R8v n).
Local Abbreviation N8D := (@AGis.N8D n).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation SHBv := (@AGis.SHBv).
Local Abbreviation SKv := (@AGis.SKv ly cl v).
Local Abbreviation PBv := (@AGis.PBv ly n cl v kz).
Local Abbreviation SUv := (@AGis.SUv ly cl v kz).
Local Abbreviation WINT := (@AGis.WINT ly cl).
Local Abbreviation PBW := (@AGis.PBW ly n cl v kz).
Local Abbreviation DZONE := (@AGis.DZONE ly).
Local Abbreviation casek_sizes := (@AGis.casek_sizes n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AGis.RZ_num n kz Hkz Nrange).
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Lemma Hn0 : 0 <= n. Proof. pose proof RZ_num as (_ & _ & _ & N & _). lia. Qed.
Lemma FPn : from_primary n = true. Proof. pose proof casek_sizes as (_ & _ & _ & _ & F & _). exact F. Qed.
Local Abbreviation cl_range := (AGiy.cl_range B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation off_facts := (AGiy.off_facts B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_geom := (AGiy.Kv_geom B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (AGiy.cached_vs_chunk B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow_present := (AGiy.shadow_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hcl := (AGiy.Hcl' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv := (AGiy.Hv' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hcnt := (AGiy.Hcnt' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv2 := (AGiy.Hv2' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
(* AGis's range lemmas also take the walk's regs0, trace and depot post, which their statements do not use. *)
Local Abbreviation derived_ranges := (@AGis.derived_ranges _ ly (bvmap_empty : bvmap 5 word) mem0 n [0] cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG dtrlen
(fun (_ : Z) (_ : word -> option byte) => True) Hkz Nrange).
Local Abbreviation high_facts := (@AGis.high_facts _ ly (bvmap_empty : bvmap 5 word) mem0 n [0] v kz Hv LY IMG dtrlen
(fun (_ : Z) (_ : word -> option byte) => True)).
Lemma cls_geom :
0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16 /\
RZ + n <= class_size cl /\ RZ + R8v <= class_size cl.
Proof.
pose proof RZ_num as (RZr & RZ8 & RZ88 & Nlo & NRZ).
pose proof casek_sizes as (_ & RS & R8 & NP & FP & NS & RQ).
pose proof (primary_geometry n ltac:(zlia) FP) as (G1 & G2 & G3 & G4 & G5). rewrite <- Hcl_class in *.
pose proof (class_ok cl ltac:(zlia)) as (K1 & K2 & K3 & K4 & K5 & K6).
rewrite RS, RQ, NS in G2. repeat split; try zlia.
Qed.
(* The redzone part of the chunk's shadow is present (the walk's HSKpres). *)
Lemma SKPRES : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Proof.
intros a Ha. pose proof cls_geom as (K1 & _ & _ & _ & _ & K6).
apply shadow_present. pose proof (Z.div_le_mono (RZ + R8v) (class_size cl) 8 ltac:(lia) K6). lia.
Qed.
Let Kc : chunk := new_chunk cl off n.
Let SF (z : Z) : astate := st_final S cl l off n tr z.
Lemma Kc_fresh : forall k, In k (st_chunks S) -> sptr_eqb (ck_beg k) (ck_beg Kc) = false.
Proof.
intros k Hk. pose proof off_facts as (_ & _ & _ & _ & _ & NI & _).
destruct (sptr_eqb (ck_beg k) (ck_beg Kc)) eqn:E; [|reflexivity]. exfalso.
unfold Kc, new_chunk in E. cbn [ck_beg] in E. destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; cbn in E; try discriminate.
apply Z.eqb_eq in E. apply NI. apply in_or_app. right. apply in_or_app. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. rewrite E in IN.
replace (prim_class (region_off cl + off)) with cl in IN.
2:{ pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof cls_geom as (K1 & _). pose proof cl_range.
unfold prim_class. rewrite region_off_eq by zlia. symmetry. rewrite Z.shiftr_div_pow2 by zlia.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S cl WF ltac:(zlia)). pose proof ev_user_room. unfold kUserMapSize, kFreeArrayOffset in *.
rewrite Z.div_add_l by zlia. rewrite Z.div_small by zlia. zlia. }
rewrite region_off_eq in IN by (pose proof cl_range; zlia). replace (cl * 2 ^ 32 + off - cl * 2 ^ 32) with off in IN by zlia. exact IN.
Qed.
Lemma upd_chunk_fresh : forall lst, (forall k, In k lst -> sptr_eqb (ck_beg k) (ck_beg Kc) = false) -> upd_chunk lst Kc = lst ++ [Kc].
Proof.
induction lst as [|k t IH]; intros H; [reflexivity|]. cbn [upd_chunk app]. rewrite (H k (or_introl eq_refl)). f_equal. apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.
Lemma SF_chunks : forall z, st_chunks (SF z) = st_chunks S ++ [Kc].
Proof.
intros z. unfold SF, st_final. cbn [st_chunks set_chunks]. replace (st_chunks (depot_after z tr (st_popped S cl l))) with (st_chunks S).
- apply upd_chunk_fresh. exact Kc_fresh.
- unfold depot_after, st_popped. destruct (z =? 0); reflexivity.
Qed.
Lemma SF_same : forall z,
st_regions (SF z) = st_regions S /\ st_cache_inited (SF z) = st_cache_inited S /\ st_secs (SF z) = st_secs S /\
st_sec_arr (SF z) = st_sec_arr S /\ st_sec_reserved (SF z) = st_sec_reserved S /\ st_qthread (SF z) = st_qthread S /\
st_qglobal (SF z) = st_qglobal S /\ st_fs (SF z) = st_fs S /\ st_internal_inited (SF z) = st_internal_inited S /\
st_nev (SF z) = st_nev S /\ st_cache (SF z) = zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S) /\
st_depot (SF z) = (if z =? 0 then st_depot S else st_depot S ++ [tr]).
Proof.
intros z. unfold SF, st_final, depot_after, st_popped. destruct (z =? 0); cbn; repeat split; reflexivity.
Qed.
Lemma SF_sec_extents : forall z, sec_extents ly (SF z) = sec_extents ly S.
Proof.
intros z. unfold sec_extents. rewrite SF_chunks. rewrite flat_map_app. cbn. rewrite app_nil_r. reflexivity.
Qed.
Lemma SF_sec_live : forall z, sec_live_bytes (SF z) = sec_live_bytes S.
Proof.
intros z. unfold sec_live_bytes. rewrite SF_chunks. rewrite fold_right_app. cbn. reflexivity.
Qed.
Lemma SF_ledger : forall z md, ALedger tfibsegs ly S md -> ALedger tfibsegs ly (SF z) md.
Proof.
intros z md L. pose proof (SF_same z) as (R1 & _ & _ & _ & Rres & _ & _ & _ & _ & Rnev & _).
destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
constructor; try assumption.
- destruct L3 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
destruct P1 as (Q1 & Q2 & Q3). unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in *. rewrite R1. exact (conj Q1 (conj Q2 Q3)).
- rewrite SF_sec_extents. exact L6.
- rewrite SF_sec_extents. exact L7.
-   rewrite SF_sec_extents, Rres. unfold prim_committed in *. rewrite R1. exact L8.
-   rewrite SF_sec_extents. exact L11.
Qed.
(* (d) The allocator memory the hit-g walk writes (AGImgA.hit_writes) is owned (YFix.WR_owned without the stack). *)
Lemma hit_owned : forall odd a, 0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
hit_writes ly n cl v kz odd a -> aowned B ly S a.
Proof.
intros odd a Ra Hodd Hw. pose proof derived_ranges as DR. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5). pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
pose proof high_facts as (F1 & F2 & _).
assert (OWN_SH : forall g, Kv <= g < Kv + class_size cl -> aowned B ly S (shadow_addr g)).
{ intros g Hg. apply (own_shadow_prim B ly S rd0 g HARm). zlia. }
assert (OWN_K : forall b, Kv <= b < Kv + RZ -> aowned B ly S b).
{ intros b Hb. apply (own_prim_nonuser B ly S rd0 b HARm); [zlia|]. intros k Hk _.
pose proof (cached_vs_chunk k Hk) as D. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). zlia. }
pose proof RZ_num as (RZr & RZ8 & RZ88 & Nlo & NRZ).
unfold hit_writes, WINT, PBW in Hw. destruct Hw as [Hw|[[Hw|Hw]|[[Ho Hw]|[Hw|Hw]]]].
- apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto|]. cbn [fst snd].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, t_unwinding in *. unfold T in Hw. zlia.
- apply OWN_K. clear - Hw RZr; zlia.
- apply OWN_K. clear - Hw RZr DR; zlia.
- replace a with (shadow_addr (Kv + RZ + N8D)) by (unfold shadow_addr, PBv, SHBv, SHADOW_OFF in *; zlia). apply OWN_SH.
pose proof (Hodd Ho) as E8. pose proof (Z.div_mod n 8 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as MB. clear - E8 DM MB K5 RZr Nlo. unfold N8D in *. zlia.
- unfold DZONE in Hw. destruct Hw as [Hw|[Hw|Hw]].
+ apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xaa710, 0x5cd510 - 0xaa710). split; [cbn; tauto|]. unfold in_zr; cbn. zlia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a HARm); [unfold core_extents; cbn; tauto| cbn [fst snd]; exact Hw].
+ apply (own_core B ly S rd0 (ly_SB ly, kStoreBlockSize) a HARm); [unfold core_extents; cbn; tauto| cbn [fst snd]; exact Hw].
- replace a with (shadow_addr (Kv + 8 * (a - SKv))).
2:{ unfold shadow_addr, SKv, SHBv, SHADOW_OFF in *. rewrite (Z.mul_comm 8 (a - (2147450880 + Kv / 8))), Z.div_add by zlia. zlia. }
apply OWN_SH. unfold SKv, SHBv in *. pose proof (Z.div_mod Kv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound Kv 8 ltac:(zlia)).
pose proof (div8_bounds n ltac:(zlia)). unfold N8D in *. rewrite Z.div_mul in Hw by zlia. clear - Hw H H0 H1 K5 RZr RZ8 Nlo DR V3. zlia.
Qed.
End o.
End d.
