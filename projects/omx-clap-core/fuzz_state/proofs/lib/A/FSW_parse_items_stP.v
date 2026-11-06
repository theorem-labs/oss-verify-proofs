(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the parse_items member step (P), from the
   parse_string call at 0x84c4c (invariant pi_IP) to the __asan_memset call at 0x84d78 (invariant pi_IM). Route:
   FSW_parse_items_calls.pic_call_ps_84c4c (m := 1 - k, Qk := |kk|, cs := pi_csL; the key facts from pi_mem_facts,
   pim_spieces_plain and pim_key_run); at the resume the kit turns the call's state into the start state of segment
   S2: the three block regions dropped AND v's write window closed (pik_st_ok_setm, a YP06 subregion: the S2 code never
   writes v, and an open window would lose v's num / str bytes, which no chunk covers), the env extended by the slots
   keys + 8 n / kids + 56 n (xatom 22 / 23, pik_st_ok_extra), a0 := the key (pik_st_ok_setr), the `:` window and the
   keys[n] window (st_ok_add_region'), the slot facts, the `:` guards and the two aliases (pik_st_ok_addf). That state,
   pip_ss_s2, is pi_ss_s2 with v's region narrowed, measured here (pip_run_s2, closed vm_compute). Run it
   (FSW_K.fsw_run_tok_AJU, shadow entries pi_SH_s2); at the stop keys[n] = a is written and in->p is past `:`; the
   object with FSW_parse_items_obj.pio_key; then pi_IM.
   Rule 24: proves function parse_items (lookup: proof-index by name, 03:15Z, exit 0, full output
   (internal path); a Theorem Labs lane's CONFIRM, no ASan donor,
   (internal path)). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rd
FSW_pj FSH_Fn_reader
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_grow FSW_parse_items_calls FSW_parse_items_kit
FSW_parse_items_seg FSW_parse_items_mem FSW_parse_items_mdl FSW_parse_items_loop
FSW_parse_items_obj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs FSW_grow_holds FSW_pj_set_heads.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ---- parse_items_spec k's entry (the same Section variables and hypotheses as FSW_parse_items_loop.v's Section M) ---- *)
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let xr : list word := map (YK11.getr regs) pi_saved.
Variable ch : list (Z * Z * Z).
Hypothesis Hk : (k <= 1)%nat.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HPRE : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch.
Hypothesis HHEADS : FSupoisonU.fs_heads B ly S U.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HQ16 : spZ regs + 16 <= q.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HIN0 : PjIn.pj_in_ok tfibsegs (rdW W mem) q text len p dd tb.
Hypothesis HVTX : v + 56 <= text - HEAD \/ text + tcap <= v.
Hypothesis HPO0 : pobj tfibsegs B ly S W mem v.
Hypothesis HQT : quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))).
Hypothesis HSZ : rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)).
Hypothesis HLIVE : live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64.
Hypothesis HEV : st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX.
Hypothesis HBB : blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1).
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis H11 : YK11.getr regs 11 = w64 v.
Hypothesis H12 : YK11.getr regs 12 = w64 1.
Hypothesis HCH0 : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Hypothesis HREST : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest.
Hypothesis HDV : FSDocStrs.fs_doc_values (PjTree.JObj ms).
Hypothesis HDS : FSDocStrs.fs_doc_strings (PjTree.JObj ms).
Hypothesis HWF : PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms).
Hypothesis HDEP : (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat.
Hypothesis HZERO : PjStruct.pj_zero tfibsegs (rdW W mem) v.
Hypothesis HVSP : v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
#[local] Abbreviation IG := (pi_IG B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IP := (pi_IP B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IK := (pi_IK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IM := (pi_IM B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IV := (pi_IV B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation Q := (pi_Q B k ly S U W regs mem md q ot v text len p tcap tb ms pr live peak cnt fail).

(* callee: parse_string (S0, lib/A/FSW_parse_string.v parse_string_proof) *)
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.

(* ================= S2 with v's write window closed, measured here ================= *)
Definition pip_vR : YP09.region := YP09.mkRegion (Some 20%nat) 0 56 0 0 (YP09.r_chunks pig_v_region).
Definition pip_rs : list YP09.region := [pig_q_region; pip_vR].
Definition pip_ss_s2 : sstate :=
  pik_addf (pik_addr (pik_setr (fss_retT 0x84c50 144 pi_csL pip_rs pic_gf_ps) ((10%bv, SOff (xatom 20) 0) :: pi_RL))
    [pik_treg (xatom 0) 0 [58]; pi_kaR]) (pi_gf_ka ++ pi_gf_vk) (pi_wsc 0 0) [pi_al_ka; pi_al_vk].
Definition pip_st_s2 : shst := fst (pi_tok_run pi_SH_s2 pip_ss_s2).
Lemma pip_static_s2 :
  sh_static_ok (run_K 0 fs_Bx pi_SH_s2 pip_ss_s2) fs_Bx fs_Bspan pi_SH_s2 (ss_facts pip_ss_s2) (ss_mem pip_ss_s2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pip_run_s2 : pi_tok_run pi_SH_s2 pip_ss_s2 = (pip_st_s2, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pip_K : run_K 0 fs_Bx pi_SH_s2 pip_ss_s2 = 57%nat.
Proof. vm_compute. reflexivity. Qed.
(* at the memset: a0 = the kid (xatom 23), a1 = 0, a2 = 56; keys[n] holds the key (xatom 20); in->p past `:` *)
Lemma pip_fin_s2 :
  let s := sh_ss pip_st_s2 in
  ss_pc s = PC_memset /\ sh_obls pip_st_s2 = [] /\ ss_resv s = None /\ sh_j pip_st_s2 = 4%nat /\
  pi_regs_are s ([(1%bv, SLit 0x84d7c); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0);
                  (10%bv, SOff (xatom 23) 0); (11%bv, SLit 0); (12%bv, SLit 56); (20%bv, SOff 20 0)] ++ pi_RL) = true /\
  nth_error (ss_mem s) 1 = Some (YP09.mkRegion (Some (xatom 22)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff (xatom 20) 0))]) /\
  nth_error (ss_mem s) 2 = Some (fstk_ret 144 pi_csL) /\
  nth_error (ss_mem s) 5 = Some (YP09.mkRegion (Some 8%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))]).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pip_mem_eq : ss_mem pip_ss_s2 =
  [pik_treg (xatom 0) 0 [58]; pi_kaR; fstk_ret 144 pi_csL; fs_got_region; fs_bcell_region 32; pig_q_region; pip_vR].
Proof. reflexivity. Qed.
(* the write windows of the start state: keys[n], the frame, q *)
Lemma pip_wr : forall E x, in_wrange E (ss_mem pip_ss_s2) x ->
  (bv_unsigned (ew E (xatom 22)) <= x < bv_unsigned (ew E (xatom 22)) + 8) \/
  (bv_unsigned (ew E 2) <= x < bv_unsigned (ew E 2) + 144) \/
  (bv_unsigned (ew E 8) <= x < bv_unsigned (ew E 8) + 24).
Proof.
intros E x (r & Hin & Hr). rewrite pip_mem_eq in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
  cbn [pik_treg pi_kaR fstk_ret fs_got_region fs_bcell_region pig_q_region pip_vR YP09.r_base YP09.r_wlo YP09.r_whi
       base_val] in Hr; lia.
Qed.
(* the call's resume regions narrow to the start state's: frame, cells and q kept, v's window closed, blocks dropped *)
Lemma pip_subregion_refl : forall r, subregion r r.
Proof.
intros r. unfold subregion. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [|tauto].
destruct (Z.le_gt_cases (YP09.r_whi r) (YP09.r_wlo r)); [left; lia | right; lia].
Qed.
Lemma pip_submem : forall cap' kl,
  submem (fsT_ret_regions 144 pi_csL pip_rs) (fsT_ret_regions 144 pi_csL (pic_rs_ps cap' kl)).
Proof.
intros cap' kl. unfold fsT_ret_regions, pip_rs, pic_rs_ps, pic_rs. cbn [app].
do 4 (apply submem_keep; [apply pip_subregion_refl|]).
apply submem_keep; [|apply submem_nil].
unfold subregion, pip_vR, pig_v_region. cbn. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [left; lia | tauto].
Qed.
Lemma pip_wf : regions_wf (fsT_ret_regions 144 pi_csL pip_rs) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================= small facts ================= *)
Lemma pip_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
assert (Hp : 0xa1000 <= fst r) by (repeat (destruct Hr as [<-|Hr]; [cbn; lia|]); destruct Hr).
destruct Hro as [(sg & Hsg & Hw & Hr2) | Hr2].
- assert (HB : forallb (fun s => seg_writable s ||
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)) tfibsegs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB sg Hsg) as H. cbv beta in H. rewrite Hw in H. cbn [orb] in H.
  apply Z.leb_le in H. cbn [fst snd] in Ha, Hp. lia.
- unfold FS_RLO, FS_RHI in Hr2. cbn [fst snd] in Ha, Hp. lia.
Qed.
Lemma pip_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.
Lemma pip_apart_of : forall a n b m, 0 < n -> 0 < m -> (forall x, a <= x < a + n -> ~ (b <= x < b + m)) ->
  a + n <= b \/ b + m <= a.
Proof.
intros a n b m Hn Hm H. destruct (Z_lt_le_dec b (a + n)) as [H1|H1]; [|left; exact H1].
destruct (Z_lt_le_dec a (b + m)) as [H2|H2]; [|right; exact H2]. exfalso. apply (H (Z.max a b)); lia.
Qed.
Lemma pip_den : forall E n z c, ew E n = Z_to_bv 64 z -> 0 <= z -> 0 <= c -> z + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (z + c).
Proof.
intros E n z c Hn Hz Hc Hzc. apply bv_eq. rewrite denot_SOff, Hn, (unsigned_lit_small z) by lia.
rewrite (unsigned_lit_small (z + c)) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pip_mod8 : forall b n, b mod 16 = 0 -> (b + 8 * n) mod 8 = 0 /\ (b + 56 * n) mod 8 = 0.
Proof.
intros b n H. pose proof (Z.div_mod b 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd. split.
- replace (b + 8 * n) with ((2 * (b / 16) + n) * 8) by lia. apply Z.mod_mul. lia.
- replace (b + 56 * n) with ((2 * (b / 16) + 7 * n) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma pip_bytes_at_eq : forall (m m' : word -> option byte) a bs,
  (forall j, (j < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  Mem.bytes_at tfibsegs m a bs -> Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. unfold Mem.mrd, Mem.wa. rewrite (H j Hj). exact (H3 j Hj).
Qed.
Lemma pip_glob_eq : forall (W' : world tfibsegs) m m' lv pk cn fl,
  fs_glob tfibsegs W' m lv pk cn fl ->
  (forall x, inFP FS_PSTAT_FP x -> mrestrict (w_H W') m' (Z_to_bv 64 x) = mrestrict (w_H W') m (Z_to_bv 64 x)) ->
  fs_glob tfibsegs W' m' lv pk cn fl.
Proof.
intros W' m m' lv pk cn fl (G1 & G2 & G3 & G4 & GR) H.
assert (K : forall g z, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W') m) g 8 z ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 z).
{ intros g z Hg Hv j Hj. unfold mbyte. rewrite H; [exact (Hv j Hj)|].
  exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
refine (conj (K _ _ _ G1) (conj (K _ _ _ G2) (conj (K _ _ _ G3) (conj (K _ _ _ G4) GR))));
  unfold FS_PSTAT_FP, G_LIVE, G_PEAK, G_COUNT, G_FAIL; cbn; auto 10.
Qed.
(* the callee-saved list pi_RL restated over the stop's own registers *)
Lemma pip_RL_restate : forall E' (r2 : bvmap 5 word),
  Forall (fun r => YK11.getr r2 (fst r) = sv_denot E' (snd r)) pi_RL -> ed E' = ed (Ereg r2 fs_extraT) ->
  ew E' 8 = YK11.getr r2 8 -> ew E' 20 = YK11.getr r2 20 -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (fun r => YK11.getr r2 (fst r) = sv_denot (Ereg r2 fs_extraT) (snd r)) pi_RL.
Proof.
intros E' r2 HF Hed H8 H20 H32. pose proof pi_RL_ok as Hok. unfold pi_R_ok in Hok. rewrite forallb_forall in Hok.
rewrite Forall_forall in HF |- *. intros [r e] Hin. pose proof (HF _ Hin) as Hre. cbn [fst snd] in Hre |- *.
rewrite Hre. apply pik_sv_denot_agree; [exact Hed|]. intros n Hn.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat]. rewrite forallb_forall in Hat.
pose proof (Hat n Hn) as Hn'. apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|];
  apply Nat.eqb_eq in Hn'; subst n.
- rewrite H8. symmetry. exact (ew_Ereg_nat r2 _ 8 8%bv eq_refl).
- rewrite H20. symmetry. exact (ew_Ereg_nat r2 _ 20 20%bv eq_refl).
- rewrite H32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ================= the start state's two new regions, and its write permissions ================= *)
Lemma pip_disj : forall E pt ks,
  bv_unsigned (ew E (xatom 0)) = pt -> bv_unsigned (ew E (xatom 22)) = ks ->
  bv_unsigned (ew E 2) = spZ regs - 144 -> bv_unsigned (ew E 8) = q -> bv_unsigned (ew E 20) = v ->
  text <= pt -> pt + 1 <= text + len -> len < tcap -> 4096 + HEAD <= text -> text + tcap <= alloc_ceiling ->
  (text - HEAD + (tcap + HEAD) <= 65536 \/ FS_IMG_END <= text - HEAD) ->
  4096 <= ks -> ks + 8 <= alloc_ceiling -> (ks + 8 <= 65536 \/ FS_IMG_END <= ks) ->
  (pt + 1 <= ks \/ ks + 8 <= pt) -> (ks + 8 <= v \/ v + 56 <= ks) ->
  all_disjoint E pi_kaR (fsT_ret_regions 144 pi_csL pip_rs) /\
  all_disjoint E (pik_treg (xatom 0) 0 [58]) (pi_kaR :: fsT_ret_regions 144 pi_csL pip_rs).
Proof.
intros E pt ks E0 E22 E2 E8 E20 H1 H2 H3 H4 H5 Himg Hk1 Hk2 Hkimg Htk Hkv.
pose proof (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (_ & _ & _ & Hqc & Hq47).
pose proof (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (_ & HceilS & _).
pose proof (pi_stk144 k S regs ot ms Hk HDEP) as Hst.
pose proof (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof asan_consts as (C1 & _).
split; apply all_disjoint_of_extents;
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pip_rs, pig_q_region, pip_vR, pik_treg, pi_kaR,
    extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat];
  rewrite ?E0, ?E22, ?E2, ?E8, ?E20;
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
    HEAD in *;
  cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
  repeat match goal with |- _ /\ _ => split end; try exact I; destruct HVTX; lia.
Qed.
Lemma pip_awr : forall E lyc' Sc' ks,
  bv_unsigned (ew E 2) = spZ regs - 144 -> bv_unsigned (ew E 8) = q -> bv_unsigned (ew E (xatom 22)) = ks ->
  (forall a, ks <= a < ks + 8 -> in_tmp_block (ablocks B ly S) (ablocks B lyc' Sc') a) ->
  awr_ok tfibsegs B E (ss_mem pip_ss_s2) (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
    (ablocks B ly S) (ablocks B lyc' Sc') lyc' [] (frames S).
Proof.
intros E lyc' Sc' ks E2 E8 E22 Htmp.
pose proof (pi_stk144 k S regs ot ms Hk HDEP) as Hst. pose proof HWIN as (Hsq & Hq24 & _ & _ & _).
rewrite pip_mem_eq.
apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen with (k := xatom 22) (b := ks); [reflexivity | exact E22 | |].
{ intros a Ha. cbn [pi_kaR YP09.r_wlo YP09.r_whi] in Ha. left. right. right. left. apply Htmp. lia. }
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 144 - ot);
  [reflexivity | cbn [fstk_ret YP09.r_base]; rewrite E2; lia | cbn [fstk_ret YP09.r_wlo]; lia
  | cbn [fstk_ret YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
eapply awr_ok_cons_stack_off with (n := 8%nat) (d := q - ot);
  [reflexivity | cbn [pig_q_region YP09.r_base]; rewrite E8; lia | cbn [pig_q_region YP09.r_wlo]; lia
  | cbn [pig_q_region YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [pip_vR YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.

(* a disjunction kept out of lia's sight (lia case-splits every disjunction in the context) *)
Ltac pip_hide H := let T := type of H in change (pghide T) in H.

(* ================= (P) the parse_string call to the memset call ================= *)
Lemma pi_step_P : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
    (Qc : world tfibsegs -> config -> Prop),
  IP dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' Da' peak1' a,
     IM dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids keys cap Di Da' peak1' a ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs PC_memset regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_string regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc HIP K.
assert (HEADv : HEAD = 16) by reflexivity.
assert (HFIE : FS_IMG_END = 6279168) by reflexivity.
pose proof HIP as (Hms & Htr & Hi & Hc54 & HJC & R1 & R10 & HRP & HFL & HST & HRST & HBL & HOB).
(* ---- the entry's facts ---- *)
pose proof (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & HspC & Hsp47).
pose proof (pi_stk144 k S regs ot ms Hk HDEP) as Hstk.
pose proof (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (_ & _ & _ & _ & _ & Hstk2 & _).
pose proof Hstk2 as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
pose proof asan_consts as (C1 & _).
pose proof (pi_mem_facts k S regs ot ms Hk HDV HDS HWF HDEP dn kk x rm Hms) as (Hplain & _).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R8 & R20 & R3 & R4 & RL).
pose proof HST as (HCH & HCHF & Htop & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HBK1 & HPERM1 & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOB as (HHDR1 & HOPEN1).
pose proof HARU as (HAR & _ & _).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & Ht0 & (Hpc1 & Hpc2) & Hte & _ & Htblen & _ & _).
pip_hide HVTX. pip_hide HVSP.
pose proof (pi_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc
  (Z.of_nat k + 1) HAR HTX1 HIN) as (Htx1 & _ & Htx3 & Htx4 & Hac47).
pose proof HTX1 as (_ & HRBT1 & _). pose proof HRBT1 as (HinT1 & _ & Htc0 & _).
pose proof HTX as (_ & HRBT0 & _). pose proof HRBT0 as (HinT0 & _).
assert (Hxl : length xr = 13%nat) by exact (pi_xr_len regs).
assert (Hcap0 : 0 < cap) by lia.
(* ---- the kids / keys blocks ---- *)
destruct (pi_slots_of B k ly S U regs ot v text len tcap ms live peak cnt fail Hk HDEP lyc Sc Uc W1 memC mdC Da T peak1
  (Z.of_nat (length dn)) kids keys cap dn Di HARU HBL HOB ltac:(lia)) as (_ & HBKd & HAPd & _ & HNEd & _).
assert (ED : ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. reflexivity. }
pose proof HBKd as HBKd'. rewrite ED in HBKd'.
pose proof (HBKd' kids (56 * cap) (or_introl eq_refl)) as HRBK1.
pose proof (HBKd' keys (8 * cap) (or_intror (or_introl eq_refl))) as HRBY1.
pose proof HRBK1 as (HinK1 & HK16 & _ & _). pose proof HRBY1 as (HinY1 & HY16 & _ & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids (56 * cap) HAR HRBK1) as (HKlo & HKhi).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys (8 * cap) HAR HRBY1) as (HYlo & HYhi).
assert (HnY0 : ~ In (keys - HEAD, 8 * cap + HEAD) (ablocks B ly S)).
{ apply HNEd. unfold rd_hblocks. rewrite ED. right. left. reflexivity. }
pose proof (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HAR HinY1) as HYimg.
pose proof (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HAR HinT1) as HTimg.
rewrite (pio_req_hb (8 * cap)) in HYimg by lia. rewrite (pio_req_hb tcap) in HTimg by lia.
assert (HTY : text - HEAD + (tcap + HEAD) <= keys - HEAD \/ keys - HEAD + (8 * cap + HEAD) <= text - HEAD).
{ assert (Hne : (text - HEAD, tcap + HEAD) <> (keys - HEAD, 8 * cap + HEAD)).
  { intros Heq. apply HnY0. rewrite <- Heq. exact HinT0. }
  pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) lyc Sc W1 (unpoison Uc memC) mdC _ _ _ _ HAR HinT1 HinY1 Hne)
    as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite !pio_req_hb in Hz by lia. exact Hz. }
assert (HYV : keys + 8 * Z.of_nat (length dn) + 8 <= v \/ v + 56 <= keys + 8 * Z.of_nat (length dn)).
{ apply pip_apart_of; [lia | lia |]. intros z Hz Hzv. apply (HAPd (keys, 8 * cap) z); [rewrite ED; right; left; reflexivity | |exact Hzv].
  unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
assert (Hi' : Z.of_nat (length dn) + 1 <= cap) by lia.
pip_hide HTimg. pip_hide HYimg. pip_hide HTY. pip_hide HYV.
(* ---- the text: the key, `:`, then the value ---- *)
rewrite (pim_spieces_plain kk Hplain), (pim_wsep pr) in HRST.
match type of HRST with _ = _ ++ _ ++ ?R => set (R0 := R) in HRST end.
set (ws := if pr then [32] else []) in HRST.
assert (HRlen : forall p', text <= p' -> Z.of_nat (length (ReaderRes.rest_at tb text p')) = Z.max 0 (text + len - p')).
{ intros p' Hp'. unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn. lia. }
assert (HR1 : ReaderRes.rest_at tb text pc = 34 :: kk ++ 34 :: 58 :: ws ++ R0).
{ rewrite HRST. cbn [app]. rewrite <- app_assoc. reflexivity. }
destruct (pim_key_run tb text len pc kk (58 :: ws ++ R0) Hpc1 ltac:(rewrite HRlen by lia; lia) HR1 Hplain)
  as (Hrun & Hrunat & Hq34 & Hpclt).
assert (HRc : ReaderRes.rest_at tb text (pc + Z.of_nat (length kk) + 2) = 58 :: ws ++ R0).
{ replace (pc + Z.of_nat (length kk) + 2) with (pc + Z.of_nat (length (34 :: kk ++ [34])))
    by (cbn [length]; rewrite length_app; cbn [length]; lia).
  apply pim_rest_skip; [lia|]. rewrite HR1. cbn [app]. rewrite <- app_assoc. reflexivity. }
assert (HRd : ReaderRes.rest_at tb text (pc + Z.of_nat (length kk) + 3) = ws ++ R0).
{ replace (pc + Z.of_nat (length kk) + 3) with (pc + Z.of_nat (length kk) + 2 + Z.of_nat (length [58])) by (cbn; lia).
  apply pim_rest_skip; [lia|]. rewrite HRc. reflexivity. }
assert (Hcolon : pc + Z.of_nat (length kk) + 2 < text + len).
{ pose proof (HRlen (pc + Z.of_nat (length kk) + 2) ltac:(lia)) as HL. rewrite HRc in HL. cbn [length] in HL. lia. }
(* ---- the trace and the budget of parse_string's one allocation ---- *)
assert (Hech : length (flat_map PjRoundTrip.ech kk) = length kk) by (rewrite (pim_ech_plain kk Hplain); reflexivity).
assert (HTR2 : PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))] ++
  (PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S (length dn)) (Z.to_nat cap) rm)).
{ rewrite Htr, Hech. reflexivity. }
pose proof HJ as (_ & _ & _ & _ & _ & Hfr1 & Hnev1 & _).
destruct (pi_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc _ T _ _ HTR2 Hnev1 HPERM1
  HSUM HLEN) as (HQ1 & HLV1 & HEV1 & HBB1 & HSZ1).
unfold rd_live in HLV1, HBB1. cbn [fold_right PjGrammar.esize] in HLV1, HBB1.
rewrite pim_rd_ev_alloc in HEV1.
unfold rd_sizes_ok in HSZ1. apply Forall_inv in HSZ1. cbn [PjGrammar.esize] in HSZ1.
(* ---- the call ---- *)
refine (pic_call_ps_84c4c B HSS HPS (1 - k)%nat (spZ regs) ot ly S U W mem md [] lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq
  q text len pc (Z.of_nat k + 1) tb tcap xr v 0 0 kids keys (Z.of_nat (length dn)) cap (Z.of_nat (length kk))
  (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail pi_csL Qc HJ HARU HRO HHD R1 Rsp Hsp16 ltac:(lia)
  R8 R20 R10 R3 R4 (achain_lower _ _ _ (spZ regsC) _ _ HCH ltac:(lia)) Hsq ltac:(lia) HIN ltac:(lia) HTX1 Hpclt Hq34 Hrun
  Hxl HPO1 HHDR1 ltac:(lia) HBKd HAPd HG1 HQ1 ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) HEV1
  ltac:(unfold HEAD in *; lia) pi_wf_csL _ _).
{ (* the frame's chunks at the resume *)
  intros regs0 a0 HP0.
  destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs0 (pic_xs_ps (pc + Z.of_nat (length kk) + 2) (text + len)
    (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap a0 (Z.of_nat (length kk))) pi_RL HRP HP0)
    as (E8 & E20 & E32 & _).
  apply (pi_csL_ok _ _ (spZ regs) xr q v Hxl); [| exact E8 | exact E20 | exact E32 | lia | lia | lia | lia | exact HFL].
  intros j Hj. apply pi_ps_xs_saved; [exact Hxl | exact Hj]. }
(* ---- the resume at 0x84c50 ---- *)
intros a ly' S' W' regs' mem' md' HJ' HJps HARU' HP' R10' HS' Ha16 HAB' HRB' HCB' HIN' HWK' HTX' HG' HHDR' HV' HBK' HKY'.
pose proof HARU' as (HAR' & HUOK' & HUP').
destruct (fsw_rblock_low B ly' S' W' (unpoison (Uc ++ [(a - HEAD, HEAD)]) mem') md' mem' a _ HAR' HRB') as (Ha1 & Ha2).
pose proof HJ' as (_ & Hly' & _). pose proof Hly' as (_ & _ & _ & _ & _ & _ & _ & _ & Htop' & Hslo' & Hshi' & _).
(* ---- the resume env and the extended one ---- *)
set (xs0 := pic_xs_ps (pc + Z.of_nat (length kk) + 2) (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn))
  cap a (Z.of_nat (length kk))) in *.
set (E0 := Ereg regs' (fs_extraT ++ xs0)) in *.
set (E := Ereg regs' (fs_extraT ++ (xs0 ++ [Z_to_bv 64 (keys + 8 * Z.of_nat (length dn));
  Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))]))).
assert (EXa : forall j, (j < 22)%nat -> ew E (xatom j) = ew E0 (xatom j)).
{ intros j Hj. unfold E, E0. rewrite !fsw_ew_xatom. apply app_nth1.
  unfold xs0, pic_xs_ps, pig_xs. rewrite !length_app, Hxl. cbn [length]. lia. }
assert (Ex0 : ew E (xatom 0) = Z_to_bv 64 (pc + Z.of_nat (length kk) + 2))
  by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
assert (Ex1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
assert (Ex16 : ew E (xatom 16) = Z_to_bv 64 kids) by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
assert (Ex17 : ew E (xatom 17) = Z_to_bv 64 keys) by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
assert (Ex18 : ew E (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn)))
  by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
assert (Ex20 : ew E (xatom 20) = Z_to_bv 64 a) by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
assert (Ex22 : ew E (xatom 22) = Z_to_bv 64 (keys + 8 * Z.of_nat (length dn))) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (Ex23 : ew E (xatom 23) = Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
pose proof (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs' (xs0 ++ [Z_to_bv 64 (keys + 8 * Z.of_nat (length dn));
  Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))]) pi_RL HRP HP') as HEnv.
fold E in HEnv. destruct HEnv as (E8 & E20 & E32 & E2u & E3 & E4).
assert (E8u : bv_unsigned (ew E 8) = q) by (rewrite E8; apply wz; lia).
assert (E20u : bv_unsigned (ew E 20) = v) by (rewrite E20; apply wz; lia).
assert (Ex0u : bv_unsigned (ew E (xatom 0)) = pc + Z.of_nat (length kk) + 2) by (rewrite Ex0; apply wz; lia).
assert (Ex22u : bv_unsigned (ew E (xatom 22)) = keys + 8 * Z.of_nat (length dn)) by (rewrite Ex22; apply wz; lia).
assert (UBx : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
(* ---- the heads and v after the call ---- *)
assert (HH' : FSupoisonU.fs_heads B ly' S' (Uc ++ [(a - HEAD, HEAD)])).
{ intros r Hr. apply in_app_or in Hr as [Hr | [<- | []]].
  - destruct (HHD r Hr) as (H16 & m0 & Hm & Hrq). split; [exact H16|]. exists m0.
    split; [rewrite HAB'; apply in_or_app; left; exact Hm | exact Hrq].
  - split; [reflexivity|]. exists (Z.of_nat (length kk) + 1 + HEAD).
    split; [rewrite HAB'; apply in_or_app; right; left; reflexivity|].
    rewrite pio_req_hb by lia. unfold HEAD. lia. }
assert (HPO' : pobj tfibsegs B ly' S' W' mem' v).
{ apply (pobj_kept_call B _ _ FS_PSTAT_FP lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' EV_fuzz_malloc v HJps HARU HUOK' HUP');
    [| exact pio_pstat_off_shadow | exact HH' | exact HPO1].
  intros z Hz. apply pio_pstat_off. pose proof (fsw_pobj_off_img B lyc Sc W1 _ mdC memC v HAR HPO1). lia. }
pose proof HTX' as (_ & HRBT' & _). pose proof HRBT' as (HinT' & _).
pose proof HBK' as HBK''. rewrite ED in HBK''.
pose proof (HBK'' keys (8 * cap) (or_intror (or_introl eq_refl))) as HRBY'. pose proof HRBY' as (HinY' & _).
(* ---- the start state pip_ss_s2 ---- *)
assert (Hlx : length (fs_extraT ++ xs0) = 23%nat)
  by (unfold xs0, pic_xs_ps, pig_xs; rewrite !length_app, Hxl; reflexivity).
pose proof (pik_st_ok_setm _ _ _ (fsT_ret_regions 144 pi_csL pip_rs) HS' (pip_submem cap (Z.of_nat (length kk))) pip_wf)
  as HS1.
assert (HS1' : st_ok tfibsegs E0 (fss_retT 0x84c50 144 pi_csL pip_rs pic_gf_ps)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84c50) mem' (seg_rom tfibsegs)))) by exact HS1.
pose proof (pik_st_ok_extra regs' (fs_extraT ++ xs0) [Z_to_bv 64 (keys + 8 * Z.of_nat (length dn));
  Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))] _ _ HS1' ltac:(rewrite Hlx; vm_compute; reflexivity)) as HS2.
rewrite <- app_assoc in HS2. fold E in HS2.
assert (Ha0 : YK11.getr regs' 10 = sv_denot E (SOff (xatom 20) 0)) by (rewrite fsw_SOff0, Ex20; exact R10').
pose proof (pik_st_ok_setr E _ _ _ HS2 (pi_setr_ok B k S regs q ot v ms Hk HDEP regsC regs' _ pi_RL (SOff (xatom 20) 0)
  HRP HP' pi_RL_ok Ha0)) as HS3.
assert (RKA : region_ok tfibsegs E (mrestrict (w_H W') mem') pi_kaR).
{ apply (pic_blk_ok E _ (xatom 22) (keys + 8 * Z.of_nat (length dn)) 8 Ex22u ltac:(lia) ltac:(lia)).
  intros i0 Hi0. apply (pic_block_writable B ly' S' _ W' mem' md' (keys - HEAD) (8 * cap + HEAD) _ HARU' HinY').
  rewrite pio_req_hb by lia. unfold HEAD. lia. }
destruct (pi_txt_bytes k S regs ot text len tb ms Hk HDEP _ q (pc + Z.of_nat (length kk) + 2) (Z.of_nat k + 1) [58]
  (ws ++ R0) HIN' HRc) as (Hbs & Hbm).
assert (RTR : region_ok tfibsegs E (mrestrict (w_H W') mem') (pik_treg (xatom 0) 0 [58])).
{ apply (pik_treg_ok E _ (xatom 0) (pc + Z.of_nat (length kk) + 2) 0 [58] Ex0u ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hbs).
  intros i0 Hi0. rewrite Z.add_0_r. exact (Hbm i0 Hi0). }
destruct (pip_disj E (pc + Z.of_nat (length kk) + 2) (keys + 8 * Z.of_nat (length dn)) Ex0u Ex22u E2u E8u E20u
  ltac:(lia) ltac:(lia) ltac:(lia) Htx1 Htx4 HTimg ltac:(lia) ltac:(lia) ltac:(pic_pd) ltac:(pic_pd) HYV) as (DJ1 & DJ2).
pose proof (st_ok_add_region' tfibsegs E _ _ pi_kaR HS3 ltac:(vm_compute; reflexivity) RKA DJ1) as HS4.
pose proof (st_ok_add_region' tfibsegs E _ _ (pik_treg (xatom 0) 0 [58]) HS4 (pik_treg_wf (xatom 0) 0 [58] ltac:(lia)) RTR DJ2)
  as HS5.
assert (HAT : atoms_ok E (pi_gf_ka ++ pi_gf_vk)).
{ cbn [pi_gf_ka pi_gf_vk app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Ex22, Ex23, !wz by lia. change (2 ^ 3) with 8.
  split; [split; [lia | split; [|lia]] | split; [split; [lia | split; [|lia]] | exact I]].
  - exact (proj1 (pip_mod8 keys (Z.of_nat (length dn)) HY16)).
  - exact (proj2 (pip_mod8 kids (Z.of_nat (length dn)) HK16)). }
assert (HCD : conds_ok E (pi_wsc 0 0))
  by exact (pi_conds_ws k S regs ot ms Hk HDEP E 0 0 _ _ Ex0 Ex1 ltac:(lia) ltac:(lia) ltac:(lia) Hte).
assert (HAL : alias_ok E [pi_al_ka; pi_al_vk]).
{ destruct (pik_alias_ok_lin E (xatom 17) (xatom 18) (xatom 22) keys (Z.of_nat (length dn)) Ex17 Ex18 ltac:(lia) ltac:(lia))
    as (AL1 & _).
  destruct (pik_alias_ok_lin E (xatom 16) (xatom 18) (xatom 23) kids (Z.of_nat (length dn)) Ex16 Ex18 ltac:(lia) ltac:(lia))
    as (_ & AL2).
  exact (pik_alias_ok_app E [pi_al_ka] [pi_al_vk] (AL1 ltac:(lia) Ex22) (AL2 ltac:(lia) Ex23)). }
pose proof (pik_st_ok_addf E _ _ (pi_gf_ka ++ pi_gf_vk) (pi_wsc 0 0) [pi_al_ka; pi_al_vk] HS5 HAT HCD HAL) as HS6.
assert (HS : st_ok tfibsegs E pip_ss_s2 (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84c50) mem' (seg_rom tfibsegs))))
  by exact HS6.
(* ---- the shadow entries and the write permissions of the run ---- *)
assert (SHOK : sh_ok tfibsegs fs_Bx pi_SH_s2 E (mrestrict (w_H W') mem')).
{ unfold sh_ok, pi_SH_s2, pi_SHm. repeat apply Forall_cons; try apply Forall_nil.
  - apply (pi_sh_blk B k S regs ot ms Hk HDEP ly' S' _ W' mem' md' E (xatom 0) (text - HEAD) (tcap + HEAD)
      (pc + Z.of_nat (length kk) + 2) 0 1 HARU' HH' HinT' ltac:(lia) ltac:(lia) ltac:(lia) UBx).
    apply U_atom; [exact Ex0 | lia].
  - apply (pi_sh_blk B k S regs ot ms Hk HDEP ly' S' _ W' mem' md' E (xatom 22) (keys - HEAD) (8 * cap + HEAD)
      (keys + 8 * Z.of_nat (length dn)) 0 8 HARU' HH' HinY' ltac:(lia) ltac:(lia) ltac:(lia) UBx).
    apply U_atom; [exact Ex22 | lia].
  - apply (pi_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' _ W' mem' md' E 8
      HARU' Hslo' Hshi' UBx).
    apply U_atom; [exact E8 | lia].
  - apply (pi_sh_v B k S regs ot v ms Hk HDEP ly' S' _ W' mem' md' E 20 HARU' HPO' UBx).
    apply U_atom; [exact E20 | lia]. }
assert (HAWR := pip_awr E ly' S' (keys + 8 * Z.of_nat (length dn)) E2u E8u Ex22u).
assert (HAWR' : awr_ok tfibsegs B E (ss_mem pip_ss_s2) (STK_parse_items (1 - k) + (ot - spZ regs)) ot
  ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B ly' S') ly' [] (frames S)).
{ apply HAWR. intros a0 Ha0'. exists (keys - HEAD), (8 * cap + HEAD). split; [exact HinY'|]. split; [exact HnY0|].
  rewrite pio_req_hb by lia. lia. }
(* ---- the run of S2 ---- *)
eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pi_SH_s2 pip_ss_s2) fs_Bx fs_Bspan pi_SH_s2
  pip_ss_s2 pip_st_s2 (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 0x84c50) mem' (seg_rom tfibsegs))
  (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md [] ly' S'
  (Uc ++ [(a - HEAD, HEAD)]) md' (rd_ev T + EV_fuzz_malloc) Qc HS SHOK pip_static_s2 pip_run_s2 I HARU' HJ'
  ltac:(destruct pip_fin_s2 as (_ & Hob & _); rewrite Hob; constructor) HAWR').
intros wsr ms2 mat2 Hlen2 HS2r SHOK2 HJ2 HARU2 HF2 HFr2 HG2.
destruct pip_fin_s2 as (Hpcs & _ & Hres2 & _ & Hregs2 & Hn1 & Hn2 & Hn5).
rewrite pip_K in HS2r.
assert (E2n : forall n, (n < 57)%nat -> ew (extK E 57 wsr) n = ew E n)
  by (intros n Hn; exact (pi_ew_extK k S regs ot ms Hk HDEP wsr E 57 n Hn)).
set (E2 := extK E 57 wsr) in *.
(* ---- the bytes the run kept: all but keys[n], the frame and q ---- *)
assert (HRAW : forall z, 0 <= z < 2 ^ 64 ->
  ~ (keys + 8 * Z.of_nat (length dn) <= z < keys + 8 * Z.of_nat (length dn) + 8) ->
  ~ (spZ regs - 144 <= z < spZ regs) -> ~ (q <= z < q + 24) ->
  mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z) = mrestrict (w_H W') mem' (Z_to_bv 64 z)).
{ intros z Hz H1 H2 H3. apply HFr2. rewrite wz by lia. intros Hw. apply pip_wr in Hw.
  rewrite Ex22u, E2u, E8u in Hw. lia. }
(* ---- keys[n] = a at the stop ---- *)
assert (RKA2 : region_ok tfibsegs E2 (mrestrict (w_H W') (ms_mem ms2))
  (YP09.mkRegion (Some (xatom 22)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff (xatom 20) 0))]))
  by exact (fsw_region_nth E2 _ _ 1 _ HS2r Hn1).
assert (E2_22 : bv_unsigned (ew E2 (xatom 22)) = keys + 8 * Z.of_nat (length dn))
  by (rewrite E2n by (unfold xatom; lia); exact Ex22u).
pose proof (fsw_field E2 _ (xatom 22) _ _ 0 8 0 8 0 8 (SOff (xatom 20) 0) a RKA2 E2_22 ltac:(left; reflexivity)
  ltac:(rewrite fsw_SOff0, E2n by (unfold xatom; lia); exact Ex20) ltac:(cbn; lia) ltac:(cbn; lia)) as HVAL.
rewrite Z.add_0_r in HVAL.
destruct RKA2 as (_ & _ & RKW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RKW. rewrite E2_22 in RKW.
assert (HCB2 : PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a kk) by (rewrite <- Hrunat; exact HCB').
(* ---- the object and its blocks (FSW_parse_items_obj.pio_key) ---- *)
destruct (pio_key B ly S U lyc Sc Uc W1 memC mdC ly' S' W' mem' md' (ms_mem ms2) (STK_parse_string + (ot - spZ regsC)) ot
  v text len tcap (length dn) dn kids keys cap Di Da T a kk eq_refl ltac:(lia) Hc54 HARU HHD HHEADS HTX1 HinT0 HPO1 HBK1
  HPERM1 HUc HDa HSUM HLEN HHDR1 HOPEN1 HJps HARU' Ha16 HAB' HRB' HCB2 HTX' HHDR' HV' HBK' HKY' HVAL
  ltac:(intros z Hz Hns; apply HRAW; lia)
  ltac:(intros z Hz; replace z with (keys + 8 * Z.of_nat (length dn) + (z - (keys + 8 * Z.of_nat (length dn)))) by lia;
        apply RKW; lia))
  as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & _).
assert (Hheld : PjGrammar.held (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) =
  PjGrammar.held T + (Z.of_nat (length kk) + 1)).
{ rewrite <- K5, pim_rd_sum_app, HSUM. unfold rd_sum. cbn [fold_right fst snd]. lia. }
rewrite <- app_assoc in K1, K2, K4, K5, K6, K11, K13.
(* ---- the stop's registers ---- *)
pose proof (pi_regs_of_stop E2 (sh_ss pip_st_s2) ms2 (w_H W') _ HS2r Hregs2) as RG.
assert (RGf : forall r e, In (r, e) ([(1%bv, SLit 0x84d7c); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0);
  (8%bv, SOff 8 0); (10%bv, SOff (xatom 23) 0); (11%bv, SLit 0); (12%bv, SLit 56); (20%bv, SOff 20 0)] ++ pi_RL) ->
  YK11.getr (ms_regs ms2) r = sv_denot E2 e) by (intros r e Hin; exact (proj1 (Forall_forall _ _) RG _ Hin)).
pose proof (RGf 1%bv (SLit 0x84d7c) ltac:(cbn; auto 20)) as G1.
pose proof (RGf 2%bv (SOff 2 0) ltac:(cbn; auto 20)) as G2.
pose proof (RGf 3%bv (SOff 3 0) ltac:(cbn; auto 20)) as G3.
pose proof (RGf 4%bv (SOff 4 0) ltac:(cbn; auto 20)) as G4.
pose proof (RGf 8%bv (SOff 8 0) ltac:(cbn; auto 20)) as G8.
pose proof (RGf 10%bv (SOff (xatom 23) 0) ltac:(cbn; auto 20)) as G10.
pose proof (RGf 11%bv (SLit 0) ltac:(cbn; auto 20)) as G11.
pose proof (RGf 12%bv (SLit 56) ltac:(cbn; auto 20)) as G12.
pose proof (RGf 20%bv (SOff 20 0) ltac:(cbn; auto 20)) as G20.
rewrite fsw_SOff0, E2n in G2, G3, G4, G8, G20 by lia.
rewrite fsw_SOff0, E2n in G10 by (unfold xatom; lia).
assert (HRP2 : pi_regsP B regs q v (ms_regs ms2) pi_RL).
{ split; [unfold spZ; rewrite G2; exact E2u|]. split; [rewrite G8; exact E8|]. split; [rewrite G20; exact E20|].
  split; [rewrite G3; exact E3|]. split; [rewrite G4; exact E4|].
  apply (pip_RL_restate E2 (ms_regs ms2)).
  - apply Forall_forall. intros r Hr. exact (proj1 (Forall_forall _ _) RG r (in_or_app _ _ _ (or_intror Hr))).
  - unfold E2. rewrite pi_ed_extK. reflexivity.
  - rewrite G8, E2n by lia. reflexivity.
  - rewrite G20, E2n by lia. reflexivity.
  - rewrite E2n by lia. exact E32. }
(* ---- the frame ---- *)
assert (HFL2 : pi_frameL (rdW W' (ms_mem ms2)) (spZ regs) xr q v).
{ apply (pi_frameL_of B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTX HPO0 HDEP HVSP
    E2 _ pi_csL Hxl).
  - rewrite E2n by lia. exact E2u.
  - rewrite E2n by lia. exact E8.
  - rewrite E2n by lia. exact E20.
  - rewrite E2n by lia. exact E32.
  - intros j Hj. rewrite E2n by (unfold xatom; lia). rewrite EXa by lia. unfold E0, xs0.
    apply pi_ps_xs_saved; [exact Hxl | exact Hj].
  - exact (fsw_region_nth E2 _ _ 2 _ HS2r Hn2).
  - apply incl_refl. }
(* ---- the frame chain at q, struct pj_in past `:`, the caller's window ---- *)
assert (HCH2 : achain ly' (aview tfibsegs (w_H W') (unpoison (Uc ++ [(a - HEAD, HEAD)]) (ms_mem ms2))) (spZ regs) q chq).
{ apply (pi_chain_kept lyc ly' _ _ (spZ regs) q (ly_top ly) chq HCH HCHF Htop Htop').
  intros z Hz Hzq.
  assert (Hz64 : 0 <= z < 2 ^ 64) by lia.
  assert (NS : ~ (SHADOW_OFF <= z < SHADOW_OFF + 2 ^ 44)) by (unfold SHADOW_OFF; lia).
  assert (Hraw : mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z) = mrestrict (w_H W') mem' (Z_to_bv 64 z))
    by (apply HRAW; lia).
  rewrite (aview_at tfibsegs (w_H W') _ (ms_mem ms2) z (fsw_unpoison_app B ly' S' _ W' (ms_mem ms2) _ z HARU2 Hz64 NS)).
  rewrite (aview_at tfibsegs (w_H W1) _ memC z (fsw_unpoison_app B lyc Sc Uc W1 memC mdC z HARU Hz64 NS)).
  rewrite (pio_aview_raw (w_H W') mem' (ms_mem ms2) z Hraw).
  destruct (Z_lt_le_dec z ot) as [Hzo | Hzo].
  - destruct (HWK' z ltac:(lia) Hzq) as (Hm & _). unfold aview. rewrite Hm. reflexivity.
  - pose proof HJps as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
    pose proof (J9 z ltac:(lia) ltac:(lia)) as Hj9.
    rewrite (aview_at tfibsegs (w_H W') _ mem' z (fsw_unpoison_app B ly' S' _ W' mem' md' z HARU' Hz64 NS)) in Hj9.
    rewrite (aview_at tfibsegs (w_H W1) _ memC z (fsw_unpoison_app B lyc Sc Uc W1 memC mdC z HARU Hz64 NS)) in Hj9.
    exact Hj9. }
assert (RQ2 : region_ok tfibsegs E2 (rdW W' (ms_mem ms2)) (YP09.mkRegion (Some 8%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))])) by exact (fsw_region_nth E2 _ _ 5 _ HS2r Hn5).
assert (E2_8u : bv_unsigned (ew E2 8) = q) by (rewrite E2n by lia; exact E8u).
assert (Ex2 : ew E (xatom 2) = Z_to_bv 64 (Z.of_nat k + 1))
  by (rewrite EXa by lia; unfold E0; rewrite fsw_ew_xatom; reflexivity).
pose proof (fsw_field E2 _ 8 q _ 0 24 0 24 0 8 (SOff (xatom 0) 1) (pc + Z.of_nat (length kk) + 2 + 1) RQ2 E2_8u
  ltac:(cbn; tauto) ltac:(apply pip_den; [rewrite E2n by (unfold xatom; lia); exact Ex0 | lia | lia | lia])
  ltac:(cbn; lia) ltac:(cbn; lia)) as F0.
pose proof (fsw_field E2 _ 8 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len) RQ2 E2_8u
  ltac:(cbn; tauto) ltac:(rewrite fsw_SOff0, E2n by (unfold xatom; lia); exact Ex1) ltac:(cbn; lia) ltac:(cbn; lia)) as F8.
pose proof (fsw_field E2 _ 8 q _ 0 24 0 24 16 4 (SOff (xatom 2) 0) (Z.of_nat k + 1) RQ2 E2_8u
  ltac:(cbn; tauto) ltac:(rewrite fsw_SOff0, E2n by (unfold xatom; lia); exact Ex2) ltac:(cbn; lia) ltac:(cbn; lia)) as F16.
rewrite Z.add_0_r in F0.
destruct RQ2 as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E2_8u in RQW.
pose proof HIN' as (_ & _ & _ & _ & I5 & I6 & I7 & _ & I9 & I10 & I11 & I12).
assert (HIN2 : PjIn.pj_in_ok tfibsegs (rdW W' (ms_mem ms2)) q text len (pc + Z.of_nat (length kk) + 3)
  (Z.of_nat k + 1) tb).
{ refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
  - replace (pc + Z.of_nat (length kk) + 3) with (pc + Z.of_nat (length kk) + 2 + 1) by lia.
    exact (proj2 (fsw_val_pj_u64 _ _ q _ F0 ltac:(lia) ltac:(lia) ltac:(lia))).
  - exact (proj2 (fsw_val_pj_u64 _ _ (q + 8) _ F8 ltac:(lia) ltac:(lia) ltac:(lia))).
  - exact (proj1 (fsw_pj_word4_iff tfibsegs _ (q + 16) (Z.of_nat k + 1) ltac:(lia) ltac:(lia)) F16).
  - split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
  - lia.
  - apply (pip_bytes_at_eq (rdW W' mem')); [|exact I10]. intros j Hj. apply HRAW; [lia | pic_pd | lia | lia]. }
assert (HWK2 : wkeep tfibsegs W W' mem (ms_mem ms2) (spZ regs) ot q 24).
{ apply (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W' W' mem' (ms_mem ms2) (spZ regs)); [| |lia].
  - exact (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W' memC mem' (spZ regsC) HWK HWK' ltac:(lia)).
  - intros z Hz Hzq.
    assert (Hr : mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z) = mrestrict (w_H W') mem' (Z_to_bv 64 z))
      by (apply HRAW; lia).
    split; [exact (pio_mbyte_raw _ _ z Hr)|].
    split; intros Hw; [exact (writable_at_eq tfibsegs _ _ z Hr Hw) | exact (writable_at_eq tfibsegs _ _ z (eq_sym Hr) Hw)]. }
(* ---- the read-only data and fuzz/alloc.c's statics ---- *)
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem'))
  by exact (arodata_kept B _ _ FS_PSTAT_FP lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' EV_fuzz_malloc HJps HARU HUOK' HUP'
     pip_pstat_closed pip_ro_not_pstat HRO).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') (ms_mem ms2))).
{ intros z Hz Ho He. rewrite <- (HRO' z Hz Ho He). apply pio_aview_raw.
  pose proof (pic_img_lo z (fsw_roP_img z Hz)) as Hl. apply HRAW; [lia | pic_pd | lia | lia]. }
assert (HG2' : fs_glob tfibsegs W' (ms_mem ms2) (live + PjGrammar.held (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]))
  (Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1))
  (cnt + Z.of_nat (length (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]))) fail).
{ rewrite Hheld, length_app. cbn [length].
  replace (live + (PjGrammar.held T + (Z.of_nat (length kk) + 1))) with (live + PjGrammar.held T + Z.of_nat (length kk) + 1)
    by lia.
  replace (cnt + Z.of_nat (length T + 1)) with (cnt + Z.of_nat (length T) + 1) by lia.
  apply (pip_glob_eq W' mem'); [exact HG'|].
  intros z Hz. assert (Hzr : 670880 <= z < 6137352).
  { destruct Hz as (r & Hr & Hzr). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hzr; lia. }
  apply HRAW; [lia | pic_pd | lia | lia]. }
assert (HevT : rd_ev (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) = rd_ev T + EV_fuzz_malloc)
  by (rewrite pim_rd_ev_app, pim_rd_ev_alloc; reflexivity).
(* ---- the memset call configuration, and pi_IM there ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W') E2 _ ms2 HS2r Hres2), Hpcs.
refine (K (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' (ms_mem ms2)
  (with_vm_backing (m_vm_lazy md') mat2 md') (ms_regs ms2) chq (pc + Z.of_nat (length kk) + 3)
  (Da ++ [(a, Z.of_nat (length kk) + 1)]) (Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1)) a _).
unfold pi_IM, pi_IK. cbv zeta.
split; [|split; [exact G1 | split; [rewrite G10; exact Ex23 | split; [exact G11 | exact G12]]]].
refine (conj Hms (conj _ (conj Hi (conj Hc54 (conj _ (conj HRP2 (conj HFL2 (conj _ (conj HRd (conj _ (conj _
  (conj K12 K13)))))))))))).
- rewrite Htr, Hech, <- app_assoc. reflexivity.
- refine (conj _ (conj HARU2 (conj HRO2 K7))). rewrite HevT. exact HJ2.
- exact (conj HCH2 (conj HCHF (conj Htop' (conj HIN2 HWK2)))).
- assert (Hpk' : peak <= Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1)) by lia.
  exact (conj K8 (conj K9 (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj HG2' Hpk'))))))))).
- exact (conj K10 K11).
Qed.

End X.
