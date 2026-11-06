(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the ENTRY step of parse_items' member path, pi_entry:
   for ms = (kk, x) :: rm, the configuration at A_parse_items reaches grow #1 (A_grow, ra 0x84b6c) in the call-site
   invariant pi_IG [] kk x rm (T = [], kids = keys = cap = 0, Di = Da = [], peak1 = peak). Route, as
   FSW_pitems_dev.v pitems_nil's start: the entry run to 0x84ad0 (FSW_parse_items.pitems_entry_run), the branch
   SRr_sym_branch there (in->p + 1 < in->end; the other arm refuted from the text length), then the measured segment E
   of FSW_parse_items_seg.v: the start state pi_ss_e pr k is pi_ss_ws0 with the literal window
   pik_treg (xatom 0) 1 (pi_wsb pr (k + 1) ++ [34]) (the white space after `{` and the key's quote, read from HREST and
   pi_obj_cons / pi_spieces_head) and the conditions pi_wsc |ws| 1 added; pi_run_e runs it (shadow entries pi_SH_e) to
   the grow call; pi_fin_e's registers, frame region (the prologue's 13 saved registers), q region (in->p past the
   white space, in->depth = k + 1) and v region (type 6, the rest zero) give pi_IG. The bytes the two runs did not write
   (frame_of of both runs: only the frame below sp0, q's 24 bytes and v's 56 bytes are write windows) keep the text, the
   text block's head, the globals, the rodata, the caller's window and the frame chain at q.
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
FSW_parse_items_seg FSW_parse_items_mem FSW_parse_items_mdl FSW_parse_items_loop.
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

(* ================= helpers (FSW_pitems_dev.v's shapes; that file is not imported here) ================= *)
(* a run only edits chunks: the write windows of a region list with the same skeleton are the same *)
Lemma pie_wr_skel : forall E (rs rs' : list YP09.region),
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs =
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs' ->
  forall a, in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' H a (r & Hin & Ha).
assert (Hm : In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)
               (map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs'))
  by (rewrite <- H; apply (in_map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r))); exact Hin).
apply in_map_iff in Hm as (r' & Er & Hin').
injection Er as E1 E2 E3. exists r'. split; [exact Hin'|].
first [rewrite E1, E2, E3; exact Ha | rewrite <- E1, <- E2, <- E3; exact Ha].
Qed.
Lemma pie_skel_ws0 :
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem pi_ss_ws0) =
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem pi_ss0).
Proof. vm_compute. reflexivity. Qed.
(* the same for the regions' extents: disjointness from the entry state's regions carries *)
Lemma pie_ext_skel : forall E r (rs rs' : list YP09.region),
  map (fun y => (YP09.r_base y, YP09.r_lo y, YP09.r_hi y)) rs =
  map (fun y => (YP09.r_base y, YP09.r_lo y, YP09.r_hi y)) rs' ->
  all_disjoint E r rs' -> all_disjoint E r rs.
Proof.
intros E r rs. induction rs as [|y rs IH]; intros [|z rs'] Hm Hd; cbn [map] in Hm; try discriminate; [exact I|].
injection Hm as E1 E2 E3 Hm. cbn [all_disjoint] in *. destruct Hd as (Hyz & Hd).
split; [|exact (IH rs' Hm Hd)].
unfold extent_disjoint in *.
first [rewrite E1, E2, E3; exact Hyz | rewrite <- E1, <- E2, <- E3; exact Hyz].
Qed.
Lemma pie_skel3_ws0 :
  map (fun y => (YP09.r_base y, YP09.r_lo y, YP09.r_hi y)) (ss_mem pi_ss_ws0) =
  map (fun y => (YP09.r_base y, YP09.r_lo y, YP09.r_hi y)) (ss_mem pi_ss0).
Proof. vm_compute. reflexivity. Qed.
(* MEASURED: segment E's run bound K (run_K) is 36 at every (pr, k) *)
Lemma pie_K36 : forall (pr0 : bool) (k0 : nat), (k0 <= 1)%nat ->
  run_K 0 fs_Bx (pi_SH_e pr0 k0) (pi_ss_e pr0 k0) = 36%nat.
Proof. intros [|] [|[|k0]] H0; try lia; vm_compute; reflexivity. Qed.
(* segment E's run (FSW_parse_items_seg.v pi_run_e) in the engine's own form. The cast is written so that the kernel
   compares sym_runN_tok against pi_tok_run with pi_tok_run on the side it unfolds first; checked the other way round it
   unfolds the symbolic run instead (about a minute per use) *)
Lemma pie_run_e : forall (pr0 : bool) (k0 : nat), (k0 <= 1)%nat ->
  sym_runN_tok tfibsegs pitems_tbl (run_K 0 fs_Bx (pi_SH_e pr0 k0) (pi_ss_e pr0 k0)) fs_Bx fs_Bspan (pi_SH_e pr0 k0) FUEL
    (pi_ss_e pr0 k0) = (pi_st_e pr0 k0, TS_stopped SR_fetch).
Proof.
intros pr0 k0 H0.
exact (eq_rect (pi_tok_run (pi_SH_e pr0 k0) (pi_ss_e pr0 k0) = (pi_st_e pr0 k0, TS_stopped SR_fetch)) (fun X : Prop => X)
  (pi_run_e pr0 k0 H0)
  (sym_runN_tok tfibsegs pitems_tbl (run_K 0 fs_Bx (pi_SH_e pr0 k0) (pi_ss_e pr0 k0)) fs_Bx fs_Bspan (pi_SH_e pr0 k0) FUEL
     (pi_ss_e pr0 k0) = (pi_st_e pr0 k0, TS_stopped SR_fetch))
  (@eq_refl Prop (sym_runN_tok tfibsegs pitems_tbl (run_K 0 fs_Bx (pi_SH_e pr0 k0) (pi_ss_e pr0 k0)) fs_Bx fs_Bspan
     (pi_SH_e pr0 k0) FUEL (pi_ss_e pr0 k0) = (pi_st_e pr0 k0, TS_stopped SR_fetch)))).
Qed.
(* MEASURED: every loaded segment of fs.asan starts at or above 0x10000 *)
Lemma pie_segs_lo : forall a, in_img tfibsegs a -> 65536 <= a.
Proof.
intros a (sg & Hin & Hr).
assert (Hb : forallb (fun s => 65536 <=? Z.of_N (seg_base s)) tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
(* a byte that is defined stays defined as the memory grows *)
Lemma pie_mrd_grows : forall (m m' : word -> option byte) y, mem_grows m m' ->
  (exists b, Mem.mrd tfibsegs m y = Some b) -> exists b, Mem.mrd tfibsegs m' y = Some b.
Proof.
intros m m' y HG (b & Hb). unfold Mem.mrd in *.
destruct (m y) as [c|] eqn:E1; destruct (m' y) as [c'|] eqn:E2; try (eexists; reflexivity).
- exfalso. apply (HG y); [rewrite E1; discriminate | exact E2].
- exists b. exact Hb.
Qed.
(* one byte's value, writability, a field, a byte list, the ASan view: the same where the raw memories agree *)
Lemma pie_mbyte_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma pie_wr_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.
Lemma pie_val_eq : forall (m m' : word -> option byte) a n z,
  (forall j, (j < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  val_mem tfibsegs m a n z -> val_mem tfibsegs m' a n z.
Proof. intros m m' a n z H Hv j Hj. unfold mbyte. rewrite (H j Hj). exact (Hv j Hj). Qed.
Lemma pie_bytes_at_eq : forall (m m' : word -> option byte) a bs,
  (forall j, (j < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  Mem.bytes_at tfibsegs m a bs -> Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (H i Hi). exact (H3 i Hi).
Qed.
Lemma pie_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
(* an atom plus an offset, as a word *)
Lemma pie_off : forall E n y c, ew E n = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 -> 0 <= y + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (y + c).
Proof.
intros E n y c H Hy Hyc. apply bv_eq. rewrite denot_SOff, H, !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* the text at in->p, regrouped *)
Lemma pie_txt1 : forall (a : Z) (w s sep vx mg cl r : list Z),
  (a :: w ++ s ++ sep ++ vx ++ mg ++ cl ++ [125]) ++ r = (a :: w) ++ (s ++ sep ++ vx ++ mg ++ cl ++ [125] ++ r).
Proof. intros. cbn [app]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma pie_txt2 : forall (a b : Z) (w y r : list Z), (a :: w) ++ ((b :: y) ++ r) = (a :: w ++ [b]) ++ (y ++ r).
Proof. intros. cbn [app]. rewrite <- !app_assoc. reflexivity. Qed.
(* a field chunk's range side conditions *)
Local Ltac pie_rng :=
  lazymatch goal with
  | |- 0 <= _ < 2 ^ (8 * Z.of_N ?w) => let z := eval vm_compute in (8 * Z.of_N w) in change (8 * Z.of_N w) with z; lia
  | |- Z.of_N ?w <= 8 => let z := eval vm_compute in (Z.of_N w) in change (Z.of_N w) with z; lia
  end.
Local Ltac pie_in := repeat (first [left; reflexivity | right]).
(* a disjunction kept out of lia's sight (lia splits every disjunctive hypothesis in the context) *)
Definition pie_box (P : Prop) : Prop := P.
Lemma pie_unbox : forall P, pie_box P -> P.
Proof. intros P H. exact H. Qed.
Local Ltac pie_boxit H := let P := type of H in let B := fresh "B" H in assert (B : pie_box P) by exact H; clear H.

(* ================= (E) the entry: A_parse_items to grow #1 in pi_IG [] ================= *)
Lemma pi_entry : forall kk x rm, ms = (kk, x) :: rm ->
  (forall T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
     IG [] kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
     SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros kk x rm Ems HK.
(* ---- the measured stop of segment E ---- *)
pose proof (pi_fin_e pr k Hk) as FE. cbv zeta in FE.
destruct FE as (Hpc & Hob & Hrv & HjE & Hregs & Hm1 & Hm4 & Hm5).
set (ws := pi_wsb pr (Z.of_nat k + 1)) in *.
(* ---- the entry's facts ---- *)
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAPRE & _ & _).
pose proof HAPRE as (HAR & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & Htop & Htop2).
pose proof asan_consts as (C1 & _).
pose proof (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
pose proof (pi_stk144 k S regs ot ms Hk HDEP) as HST.
pose proof (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv0 & Hv1).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
pose proof (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (Hq0 & Hq64 & Ht0 & (Hp1 & Hp2) & Hend & _ & Hlen & _ & Hd).
pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO0) as Hvimg.
pose proof Htxblk as (HinT & _).
pose proof (fsw_ablock_low B ly S W (unpoison U mem) md _ _ HAR HinT) as (Hb4096 & Hbceil & Hbreq).
pose proof (fsw_ablock_off_img B ly S W (unpoison U mem) md _ _ HAR HinT) as Himg.
assert (Hv8 : v mod 8 = 0) by (pose proof HPO0 as [[(_ & Hm8 & _)|(_ & Hm8 & _)] _]; exact Hm8).
destruct HCH0 as (chq & HCH & HCHF).
pie_boxit HVTX. pie_boxit Hvimg. pie_boxit Himg.
(* ---- the text at in->p: `{`, the white space ws, the key's quote, ... ---- *)
assert (HRIG : ReaderRes.rest_at tb text p = (123 :: ws) ++
  (concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++ concat (WriterValue.wvpieces x pr (Z.of_nat k + 1)) ++
   concat (pi_mgo pr (Z.of_nat k) 1 rm) ++ pi_wsb pr (Z.of_nat k) ++ [125] ++ rest)).
{ rewrite HREST, Ems, pi_obj_cons. apply pie_txt1. }
assert (HB : ReaderRes.rest_at tb text p = (123 :: ws ++ [34]) ++
  ((concat (WriterSpec.spieces_run [] kk) ++ [34]) ++ (WriterValue.wsep pr ++
   concat (WriterValue.wvpieces x pr (Z.of_nat k + 1)) ++ concat (pi_mgo pr (Z.of_nat k) 1 rm) ++
   pi_wsb pr (Z.of_nat k) ++ [125] ++ rest))).
{ rewrite HRIG, pi_spieces_head. apply pie_txt2. }
assert (HLW : p + Z.of_nat (length ws) + 2 <= text + len).
{ pose proof (pi_rest_len _ q text len p dd tb HIN0) as HRL. rewrite HB in HRL.
  rewrite !length_app in HRL. cbn [length] in HRL. rewrite ?length_app in HRL. cbn [length] in HRL. lia. }
assert (HLB : Z.of_nat (length (ws ++ [34])) = Z.of_nat (length ws) + 1)
  by (rewrite length_app; cbn [length]; lia).
assert (F_text : ReaderRes.rest_at tb text (p + 1 + Z.of_nat (length ws)) =
  concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++ concat (WriterValue.wvpieces x pr (Z.of_nat k + 1)) ++
  concat (pi_mgo pr (Z.of_nat k) 1 rm) ++ pi_wsb pr (Z.of_nat k) ++ [125] ++ rest).
{ replace (p + 1 + Z.of_nat (length ws)) with (p + Z.of_nat (length (123 :: ws))) by (cbn [length]; lia).
  exact (pim_rest_skip tb text p (123 :: ws) _ Hp1 HRIG). }
destruct (pi_txt_bytes k S regs ot text len tb ms Hk HDEP _ q p dd _ _ HIN0 HB) as (TBF & TBB).
(* ---- the entry run to 0x84ad0 ---- *)
assert (HFRM : FRAME_parse_items <= STK_parse_items (1 - k)) by (rewrite pi_frame_val; exact HST).
assert (Hd01 : 0 <= dd <= 1) by (unfold dd; lia).
assert (HFP : forall a, v <= a < v + 56 -> inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a).
{ intros a Ha. exists (v, v + 56). split; [left; reflexivity|]. cbn [fst snd]. lia. }
eapply (pitems_entry_run B (proj1 HSS) (proj2 HSS) ly S U W regs mem md ch q ot v text len p tb tcap dd
  (STK_parse_items (1 - k)) ([(v, v + 56)] ++ FS_PSTAT_FP)).
all: try eassumption.
intros ws1 ms1 mat1 Hln1 HS SHOK HJ HARU HF HFr HG.
pose proof pi_run_entry as Hre. cbv zeta in Hre. destruct Hre as (_ & _ & _ & Hj0 & _).
assert (Hj84 : sh_j pi_st_84ad0 = 0%nat) by exact Hj0.
rewrite Hj84 in Hln1. destruct ws1 as [|w ws1]; [clear Hln1 | discriminate Hln1].
cbn [extK] in HS, SHOK. cbn [ms_mem mkst] in HF, HFr, HG. clear HVSP.
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) dd)) in *.
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 (Z.of_nat k)) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (ER : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros r n Hn; unfold E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%bv 2%nat eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = q) by (rewrite (ER 10%bv 10%nat eq_refl), H10; apply unsigned_lit_small; lia).
assert (E11 : bv_unsigned (ew E 11) = v) by (rewrite (ER 11%bv 11%nat eq_refl), H11; apply unsigned_lit_small; lia).
(* ---- the branch at 0x84ad0: in->p + 1 < in->end ---- *)
assert (U1 : YP0e.U E (SOff (xatom 0) 1) = p + 1) by (apply U_atom_off; [exact EX0 | lia | lia]).
assert (U2 : YP0e.U E (SOff (xatom 1) 0) = text + len)
  by (rewrite (U_atom_off E (xatom 1) (text + len) 0 EX1) by lia; lia).
apply (SRr_sym_branch tfibsegs W E (sh_ss pi_st_84ad0) ms1 _ _ BC_LTU (SOff (xatom 0) 1) (SOff (xatom 1) 0) HS).
2: { intros Hb _. exfalso. rewrite branch_ltu_U, U1, U2 in Hb. apply Z.ltb_ge in Hb. lia. }
intros _ HS2.
(* ---- the write windows of the entry state: the frame below sp0, q's 24 bytes, v's 56 bytes ---- *)
assert (WR0 : forall y, in_wrange E (ss_mem pi_ss0) y ->
  (spZ regs - 144 <= y < spZ regs) \/ (q <= y < q + 24) \/ (v <= y < v + 56)).
{ intros y (r & Hin & Hr).
  unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs in Hin. cbn [ss_mem app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [fstk fs_got_region fs_bcell_region pi_q_region pi_v_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?pi_frame_val in Hr; lia. }
assert (WRe : forall y, in_wrange E (ss_mem (pi_ss_e pr k)) y -> in_wrange E (ss_mem pi_ss0) y).
{ intros y (r & Hin & Hr). unfold pi_ss_e, pik_addf, pik_addr in Hin. cbn [ss_mem app In] in Hin.
  destruct Hin as [<- | Hin].
  - unfold pik_treg in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
  - exact (pie_wr_skel E _ _ pie_skel_ws0 y (ex_intro _ r (conj Hin Hr))). }
assert (KEEP1 : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 144 <= y < spZ regs) -> ~ (q <= y < q + 24) ->
  ~ (v <= y < v + 56) -> ms_mem ms1 (Z_to_bv 64 y) = mem (Z_to_bv 64 y)).
{ intros y Hy H1 H2 H3. apply HF. rewrite unsigned_lit_small by lia.
  intros Hw. destruct (WR0 y Hw) as [Hx|[Hx|Hx]]; contradiction. }
(* ---- segment E's start state: the literal window at in->p + 1 and the white-space conditions ---- *)
assert (RTREG : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms1)) (pik_treg (xatom 0) 1 (ws ++ [34]))).
{ apply (pik_treg_ok E _ (xatom 0) p 1 (ws ++ [34])).
  - rewrite EX0. apply unsigned_lit_small. lia.
  - lia.
  - lia.
  - lia.
  - exact (Forall_inv_tail TBF).
  - intros i Hi.
    pose proof (TBB (Datatypes.S i) ltac:(cbn [length]; lia)) as Hx. cbn [nth] in Hx.
    replace (p + Z.of_nat (Datatypes.S i)) with (p + 1 + Z.of_nat i) in Hx by lia.
    rewrite <- Hx. unfold mbyte, mrestrict.
    rewrite (KEEP1 (p + 1 + Z.of_nat i)); [reflexivity | lia | lia | lia |].
    destruct (pie_unbox _ BHVTX); unfold HEAD in *; lia. }
assert (DJ0 : all_disjoint E (pik_treg (xatom 0) 1 (ws ++ [34])) (ss_mem pi_ss0)).
{ apply all_disjoint_of_extents.
  unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, pi_rs,
    pi_q_region, pi_v_region, pik_treg, extent_of_region.
  cbn [ss_mem app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EX0, (unsigned_lit_small p) by lia. rewrite E2, E10, E11, HLB.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
    FRAME_parse_items, HEAD in *.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct (pie_unbox _ BHVTX); destruct (pie_unbox _ BHimg);
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (DJ : all_disjoint E (pik_treg (xatom 0) 1 (ws ++ [34])) (ss_mem pi_ss_ws0))
  by exact (pie_ext_skel E _ _ _ pie_skel3_ws0 DJ0).
assert (RT' : region_ok tfibsegs E (ms_mem (restrict (w_H W) ms1)) (pik_treg (xatom 0) 1 (ws ++ [34])))
  by (rewrite restrict_mem; exact RTREG).
assert (HS3a : st_ok tfibsegs E (pik_addr pi_ss_ws0 [pik_treg (xatom 0) 1 (ws ++ [34])]) (restrict (w_H W) ms1))
  by exact (st_ok_add_region' tfibsegs E pi_ss_ws0 (restrict (w_H W) ms1) (pik_treg (xatom 0) 1 (ws ++ [34])) HS2
       (pik_treg_wf (xatom 0) 1 (ws ++ [34]) ltac:(lia)) RT' DJ).
assert (HC : conds_ok E (pi_wsc (length ws) 1))
  by (apply (pi_conds_ws k S regs ot ms Hk HDEP E (length ws) 1 p (text + len) EX0 EX1); lia).
assert (HS3 : st_ok tfibsegs E (pi_ss_e pr k) (restrict (w_H W) ms1))
  by exact (pik_st_ok_addf E _ _ [] (pi_wsc (length ws) 1) [] HS3a I HC I).
assert (SHOK3 : sh_ok tfibsegs fs_Bx (pi_SH_e pr k) E (mrestrict (w_H W) (ms_mem ms1))).
{ unfold sh_ok, pi_SH_e. constructor; [|exact SHOK]. fold ws.
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms1) E fs_Bx (xatom 0) (p + 1) (1 + Z.of_nat (length ws)) p 1
    (2 + Z.of_nat (length ws))).
  - apply (fsw_block_body_addressable B ly S U W (ms_mem ms1) _ _ _ (p + 1) (1 + Z.of_nat (length ws)) HARU HHEADS HinT);
      unfold HEAD in *; lia.
  - unfold fs_Bx. apply U_atom; [exact E32 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact EX0 | lia].
  - lia.
  - lia.
  - intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia.
    exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR HinT y ltac:(unfold HEAD in *; lia)). }
assert (HAWR : awr_ok tfibsegs B E (ss_mem (pi_ss_e pr k)) (STK_parse_items (1 - k) + (ot - spZ regs)) ot
  ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B ly S) ly [] (frames S)).
{ intros a Ha.
  apply (pi_awr_ok B ly S W mem regs q ot v text len p dd (STK_parse_items (1 - k)) ([(v, v + 56)] ++ FS_PSTAT_FP)
    Hsq Hq24 Hsp1 HFRM H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPO0 HFP).
  exact (WRe a Ha). }
(* ---- segment E: the run to grow #1 ---- *)
apply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W FUEL E (run_K 0 fs_Bx (pi_SH_e pr k) (pi_ss_e pr k)) fs_Bx
  fs_Bspan (pi_SH_e pr k) (pi_ss_e pr k) (pi_st_e pr k) (TS_stopped SR_fetch) ms1
  (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md [] ly S U
  (with_vm_backing (m_vm_lazy md) mat1 md) 0).
- exact HS3.
- exact SHOK3.
- exact (pi_static_e pr k Hk).
- exact (pie_run_e pr k Hk).
- exact I.
- exact HARU.
- exact HJ.
- rewrite Hob. constructor.
- exact HAWR.
- intros ws2 ms2 mat2 Hlen2 HS4 SHOK2 HJ2 HARU2 HF2 HFr2 HG2.
  rewrite (pie_K36 pr k Hk) in HS4, SHOK2.
  set (E4 := extK E 36 ws2) in *.
  assert (EA : forall n, (n < 36)%nat -> ew E4 n = ew E n)
    by (intros n Hn; exact (pi_ew_extK k S regs ot ms Hk HDEP ws2 E 36 n Hn)).
  (* the bytes neither run wrote *)
  assert (KEEP : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 144 <= y < spZ regs) -> ~ (q <= y < q + 24) ->
    ~ (v <= y < v + 56) -> ms_mem ms2 (Z_to_bv 64 y) = mem (Z_to_bv 64 y)).
  { intros y Hy H1 H2 H3. rewrite <- (KEEP1 y Hy H1 H2 H3). apply HF2.
    rewrite unsigned_lit_small by lia. intros Hw. destruct (WR0 y (WRe y Hw)) as [Hx|[Hx|Hx]]; contradiction. }
  assert (KEEPr : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 144 <= y < spZ regs) -> ~ (q <= y < q + 24) ->
    ~ (v <= y < v + 56) -> mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 y) = mrestrict (w_H W) mem (Z_to_bv 64 y)).
  { intros y Hy H1 H2 H3. unfold mrestrict. rewrite (KEEP y Hy H1 H2 H3). reflexivity. }
  (* the stop's atoms *)
  assert (E4r : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E4 n = YK11.getr regs r).
  { intros r n Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 5) with 32 in Hr. rewrite (EA n) by lia. exact (ER r n Hn). }
  assert (E4_2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite (E4r 2%bv 2%nat eq_refl); reflexivity).
  assert (E4_10 : ew E4 10 = Z_to_bv 64 q) by (rewrite (E4r 10%bv 10%nat eq_refl); exact H10).
  assert (E4_11 : ew E4 11 = Z_to_bv 64 v) by (rewrite (E4r 11%bv 11%nat eq_refl); exact H11).
  assert (E4_12 : ew E4 12 = Z_to_bv 64 1) by (rewrite (E4r 12%bv 12%nat eq_refl); exact H12).
  assert (E4_32 : ew E4 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 32%nat) by lia; exact E32).
  assert (E4_X0 : ew E4 (xatom 0) = Z_to_bv 64 p) by (rewrite (EA (xatom 0)) by (unfold xatom; lia); exact EX0).
  assert (E4_X1 : ew E4 (xatom 1) = Z_to_bv 64 (text + len))
    by (rewrite (EA (xatom 1)) by (unfold xatom; lia); exact EX1).
  assert (E4_X2 : ew E4 (xatom 2) = Z_to_bv 64 (Z.of_nat k))
    by (rewrite (EA (xatom 2)) by (unfold xatom; lia); exact EX2).
  assert (E4_10' : bv_unsigned (ew E4 10) = q) by (rewrite E4_10; apply unsigned_lit_small; lia).
  assert (E4_11' : bv_unsigned (ew E4 11) = v) by (rewrite E4_11; apply unsigned_lit_small; lia).
  (* the stop's registers *)
  pose proof (pi_regs_of_stop E4 (sh_ss (pi_st_e pr k)) ms2 (w_H W) _ HS4 Hregs) as RG.
  rewrite Forall_forall in RG.
  set (regsC := ms_regs ms2) in *.
  pose proof (RG (1%bv, SLit 0x84b6c) ltac:(pie_in)) as R1. cbn [fst snd] in R1.
  pose proof (RG (2%bv, SOff 2 (-144)) ltac:(pie_in)) as R2'. cbn [fst snd] in R2'.
  pose proof (RG (3%bv, SOff 3 0) ltac:(pie_in)) as R3'. cbn [fst snd] in R3'.
  pose proof (RG (4%bv, SOff 4 0) ltac:(pie_in)) as R4'. cbn [fst snd] in R4'.
  pose proof (RG (8%bv, SOff 10 0) ltac:(pie_in)) as R8'. cbn [fst snd] in R8'.
  pose proof (RG (10%bv, SOff 11 0) ltac:(pie_in)) as R10'. cbn [fst snd] in R10'.
  pose proof (RG (20%bv, SOff 11 0) ltac:(pie_in)) as R20'. cbn [fst snd] in R20'.
  pose proof (RG (9%bv, SOff 10 16) ltac:(pie_in)) as R9'. cbn [fst snd] in R9'.
  pose proof (RG (19%bv, SOff 12 0) ltac:(pie_in)) as R19'. cbn [fst snd] in R19'.
  pose proof (RG (21%bv, pi_shv 10 16) ltac:(pie_in)) as R21'. cbn [fst snd] in R21'.
  pose proof (RG (22%bv, SOff 10 8) ltac:(pie_in)) as R22'. cbn [fst snd] in R22'.
  pose proof (RG (23%bv, pi_shv 10 8) ltac:(pie_in)) as R23'. cbn [fst snd] in R23'.
  pose proof (RG (26%bv, SOff 32 0) ltac:(pie_in)) as R26'. cbn [fst snd] in R26'.
  pose proof (RG (27%bv, pi_shv 10 0) ltac:(pie_in)) as R27'. cbn [fst snd] in R27'.
  assert (R2 : spZ regsC = spZ regs - 144).
  { unfold spZ at 1. transitivity (bv_unsigned (sv_denot E4 (SOff 2 (-144)))); [f_equal; exact R2'|].
    rewrite denot_SOff, E4_2. apply zcanon_id. unfold M64. lia. }
  assert (R3 : YK11.getr regsC 3 = w64 (as_gp B)) by (rewrite R3', fsw_SOff0, (E4r 3%bv 3%nat eq_refl); exact Hgp).
  assert (R4 : YK11.getr regsC 4 = w64 (as_tp B)) by (rewrite R4', fsw_SOff0, (E4r 4%bv 4%nat eq_refl); exact Htp).
  assert (R8 : YK11.getr regsC 8 = w64 q) by (rewrite R8', fsw_SOff0; exact E4_10).
  assert (R10 : YK11.getr regsC 10 = w64 v) by (rewrite R10', fsw_SOff0; exact E4_11).
  assert (R20 : YK11.getr regsC 20 = w64 v) by (rewrite R20', fsw_SOff0; exact E4_11).
  assert (R9 : YK11.getr regsC 9 = Z_to_bv 64 (q + 16)) by (rewrite R9'; apply pie_off; [exact E4_10 | lia | lia]).
  assert (R19 : YK11.getr regsC 19 = Z_to_bv 64 1) by (rewrite R19', fsw_SOff0; exact E4_12).
  assert (R21 : YK11.getr regsC 21 = Z_to_bv 64 (pi_sh (q + 16)))
    by (rewrite R21'; apply pi_shv_denot; [exact E4_10 | exact E4_32 | lia | lia | lia]).
  assert (R22 : YK11.getr regsC 22 = Z_to_bv 64 (q + 8)) by (rewrite R22'; apply pie_off; [exact E4_10 | lia | lia]).
  assert (R23 : YK11.getr regsC 23 = Z_to_bv 64 (pi_sh (q + 8)))
    by (rewrite R23'; apply pi_shv_denot; [exact E4_10 | exact E4_32 | lia | lia | lia]).
  assert (R26 : YK11.getr regsC 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite R26', fsw_SOff0; exact E4_32).
  assert (R27 : YK11.getr regsC 27 = Z_to_bv 64 (pi_sh (q + 0)))
    by (rewrite R27'; apply pi_shv_denot; [exact E4_10 | exact E4_32 | lia | lia | lia]).
  assert (ERC : ew (Ereg regsC fs_extraT) 8 = Z_to_bv 64 q)
    by (rewrite (ew_Ereg_nat regsC fs_extraT 8 8%bv eq_refl); exact R8).
  assert (ERC32 : ew (Ereg regsC fs_extraT) 32 = Z_to_bv 64 SHADOW_OFF)
    by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  (* the frame: the prologue's 13 saved registers *)
  pose proof (fsw_region_nth E4 _ _ 1 _ HS4 Hm1) as RF1. rewrite restrict_mem in RF1.
  assert (F_frame : pi_frame0 (mrestrict (w_H W) (ms_mem ms2)) (spZ regs) (map (YK11.getr regs) pi_saved)).
  { unfold pi_frame0. apply Forall_forall. intros j Hjj. apply in_seq in Hjj. cbv beta.
    pose proof (bv_unsigned_in_range 5 (nth j pi_saved 0%bv)) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 5) with 32 in Hr.
    assert (Hxr : nth j (map (YK11.getr regs) pi_saved) (Z_to_bv 64 0) = YK11.getr regs (nth j pi_saved 0%bv)).
    { rewrite (nth_indep (map (YK11.getr regs) pi_saved) (Z_to_bv 64 0) (YK11.getr regs 0%bv))
        by (rewrite pi_xr_len; lia).
      apply map_nth. }
    rewrite Hxr.
    replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
    apply (fsw_field E4 _ 2 (spZ regs) _ (-144) 0 (-144) 0 (-8 - 8 * Z.of_nat j) 8
      (SOff (Z.to_nat (bv_unsigned (nth j pi_saved 0%bv))) 0) (bv_unsigned (YK11.getr regs (nth j pi_saved 0%bv)))
      RF1 E4_2).
    - apply (proj1 (in_rev _ _)).
      apply (in_map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j)
        (CVal 8 (SOff (Z.to_nat (bv_unsigned (nth j pi_saved 0%bv))) 0)))).
      apply in_seq. lia.
    - rewrite fsw_SOff0, (E4r (nth j pi_saved 0%bv)) by (rewrite Z2Nat.id by lia; reflexivity).
      symmetry. apply Z_to_bv_bv_unsigned.
    - apply u64_range.
    - pie_rng. }
  (* q's struct pj_in: in->p past the white space, in->end, in->depth = k + 1 *)
  pose proof (fsw_region_nth E4 _ _ 4 _ HS4 Hm4) as RQ. rewrite restrict_mem in RQ.
  pose proof (fsw_field E4 _ 10 q _ _ _ _ _ 0 8 (SOff (xatom 0) (1 + Z.of_nat (length ws)))
    (p + (1 + Z.of_nat (length ws))) RQ E4_10' ltac:(pie_in)
    (pie_off E4 (xatom 0) p (1 + Z.of_nat (length ws)) E4_X0 ltac:(lia) ltac:(lia))
    ltac:(pie_rng) ltac:(pie_rng)) as HPV0.
  pose proof (fsw_field E4 _ 10 q _ _ _ _ _ 16 4 (SOff (xatom 2) 1) (Z.of_nat k + 1) RQ E4_10' ltac:(pie_in)
    (pie_off E4 (xatom 2) (Z.of_nat k) 1 E4_X2 ltac:(lia) ltac:(lia)) ltac:(pie_rng) ltac:(pie_rng)) as HPV16.
  pose proof (fsw_field E4 _ 10 q _ _ _ _ _ 8 8 (SOff (xatom 1) 0) (text + len + 0) RQ E4_10' ltac:(pie_in)
    (pie_off E4 (xatom 1) (text + len) 0 E4_X1 ltac:(lia) ltac:(lia)) ltac:(pie_rng) ltac:(pie_rng)) as HPV8.
  rewrite Z.add_0_r in HPV0, HPV8.
  replace (p + (1 + Z.of_nat (length ws))) with (p + 1 + Z.of_nat (length ws)) in HPV0 by lia.
  destruct RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E4_10' in RQW.
  assert (F_pin : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem ms2)) q text len (p + 1 + Z.of_nat (length ws))
    (Z.of_nat k + 1) tb).
  { pose proof HIN0 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
    refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 _))))))))))).
    - exact (proj2 (fsw_val_pj_u64 tfibsegs _ q _ HPV0 ltac:(lia) ltac:(lia) ltac:(lia))).
    - exact (proj2 (fsw_val_pj_u64 tfibsegs _ (q + 8) _ HPV8 ltac:(lia) ltac:(lia) ltac:(lia))).
    - exact (proj1 (fsw_pj_word4_iff tfibsegs _ (q + 16) (Z.of_nat k + 1) ltac:(lia) ltac:(lia)) HPV16).
    - split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
    - lia.
    - apply (pie_bytes_at_eq (mrestrict (w_H W) mem)); [|exact I10].
      intros j Hj. apply KEEPr; destruct (pie_unbox _ BHVTX); unfold HEAD in *; lia.
    - lia. }
  (* the caller's window [sp0, ot) but q's 24 bytes *)
  assert (F_wk : wkeep tfibsegs W W mem (ms_mem ms2) (spZ regs) ot q 24).
  { intros a Ha Hnq.
    assert (Em : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEPr; [lia | lia | exact Hnq | lia]).
    split; [exact (pie_mbyte_eq _ _ a Em) | exact (pie_wr_eq _ _ a Em)]. }
  (* the frame chain at q: it reads only in [sp0, ly_top), where nothing but q's bytes changed *)
  assert (HCH2 : achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms2))) (spZ regs) q chq).
  { apply (pi_chain_kept ly ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) q (ly_top ly) chq HCH HCHF
      eq_refl eq_refl).
    intros a Ha Hq.
    apply pie_aview_eq. unfold unpoison. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
    apply KEEP; [lia | lia | exact Hq | lia]. }
  (* the text block, v, the globals, the rodata at the stop *)
  assert (F_rdt : rd_text tfibsegs B ly S W (ms_mem ms2) text len tcap).
  { split; [exact Htx4096|]. split; [|exact Htxlen].
    pose proof Htxblk as (TB1 & TB2 & TB3 & TB4). split; [exact TB1|]. split; [exact TB2|]. split; [exact TB3|].
    apply (pie_val_eq (mrestrict (w_H W) mem)); [|exact TB4].
    intros j Hj. apply KEEPr; destruct (pie_unbox _ BHVTX); unfold HEAD in *; lia. }
  pose proof (fsw_region_nth E4 _ _ 5 _ HS4 Hm5) as RV. rewrite restrict_mem in RV.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 0 4 (SLit 6) 6 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV0.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 8 8 (SLit 0) 0 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV8.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 16 8 (SLit 0) 0 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV16.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 24 8 (SLit 0) 0 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV24.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 32 8 (SLit 0) 0 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV32.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 40 8 (SLit 0) 0 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV40.
  pose proof (fsw_field E4 _ 11 v _ _ _ _ _ 48 8 (SLit 0) 0 RV E4_11' ltac:(pie_in) eq_refl ltac:(pie_rng)
    ltac:(pie_rng)) as HV48.
  rewrite Z.add_0_r in HV0.
  destruct RV as (_ & _ & RVW & _). unfold pi_v_region6 in RVW.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RVW. rewrite E4_11' in RVW.
  assert (UBx : YP0e.U E4 fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E4_32 | unfold SHADOW_OFF; lia]).
  assert (UV : YP0e.U E4 (SOff 11 0) = v) by (apply U_atom; [exact E4_11 | lia]).
  assert (RA2 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF v 56).
  { pose proof SHOK2 as SH2. unfold sh_ok, pi_SH_e, pi_SH in SH2.
    apply Forall_inv_tail, Forall_inv_tail, Forall_inv in SH2.
    destruct SH2 as (RA & _). cbn [she_m she_lo she_hi] in RA.
    rewrite UBx, UV, Z.add_0_r in RA. rewrite aview_rd_of. exact RA. }
  assert (VDEF : forall a, v <= a < v + 56 ->
    exists b, Mem.mrd tfibsegs (mrestrict (w_H W) (ms_mem ms2)) (Mem.wa a) = Some b).
  { intros a Ha. apply (pie_mrd_grows (mrestrict (w_H W) (ms_mem ms1))); [exact HG2|].
    apply (pie_mrd_grows (mrestrict (w_H W) mem)); [exact HG|].
    pose proof HZERO as (_ & (_ & _ & HZB)).
    pose proof (HZB (Z.to_nat (a - v)) ltac:(rewrite repeat_length; lia)) as Hx.
    rewrite pi_nth_repeat in Hx by lia.
    rewrite Z2Nat.id in Hx by lia. replace (v + (a - v)) with a in Hx by lia.
    eexists. exact Hx. }
  assert (F_pobj : pobj tfibsegs B ly S W (ms_mem ms2) v).
  { split.
    - pose proof HPO0 as [[HFo | HHo] _].
      + left. destruct HFo as (PF1 & PF2 & _). split; [exact PF1|]. split; [exact PF2 | exact RA2].
      + right. destruct HHo as (PH1 & PH2 & _). split; [exact PH1|]. split; [exact PH2 | exact RA2].
    - intros i Hi. exact (RVW i Hi). }
  assert (F_hdr : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) (ms_mem ms2)) v 6 0 0 0 0 0 0).
  { unfold PjStruct.pj_hdr.
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - unfold PjStruct.pj_rw. split; [exact Hv8|]. split; [lia|]. split; [lia|].
      intros a Ha. split; [|exact (VDEF a Ha)].
      pose proof (RVW (a - v) ltac:(lia)) as HW. replace (v + (a - v)) with a in HW by lia. exact HW.
    - apply fsw_val_pj_u32; [exact HV0 | lia | lia | lia].
    - apply fsw_val_pj_u64; [exact HV8 | lia | lia | lia].
    - apply fsw_val_pj_u64; [exact HV16 | lia | lia | lia].
    - apply fsw_val_pj_u64; [exact HV24 | lia | lia | lia].
    - apply fsw_val_pj_u64; [exact HV32 | lia | lia | lia].
    - apply fsw_val_pj_u64; [exact HV40 | lia | lia | lia].
    - apply fsw_val_pj_u64; [exact HV48 | lia | lia | lia]. }
  assert (F_glob : fs_glob tfibsegs W (ms_mem ms2) live peak cnt fail).
  { assert (GK : forall g z, 0xa3ca0 <= g -> g + 8 <= 0x5da608 ->
      val_mem tfibsegs (mrestrict (w_H W) mem) g 8 z -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) g 8 z).
    { intros g z Hg1 Hg2 Hv. apply (pie_val_eq (mrestrict (w_H W) mem)); [|exact Hv].
      intros j Hj. apply KEEPr; destruct (pie_unbox _ BHvimg); unfold FS_IMG_END in *; lia. }
    pose proof HGLOB as (G1 & G2 & G3 & G4 & GR).
    split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
    split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
    split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
    split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
    exact GR. }
  assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms2))).
  { intros a Ha Ho He.
    assert (Hb : 65536 <= a < FS_IMG_END).
    { destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI, FS_IMG_END in *; lia].
      assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
      pose proof (fs_segs_img a Hi). pose proof (pie_segs_lo a Hi). lia. }
    rewrite (pie_aview_eq (w_H W) mem (ms_mem ms2) a); [exact (HRO a Ha Ho He)|].
    apply KEEP; destruct (pie_unbox _ BHvimg); unfold FS_IMG_END in *; lia. }
  (* the open object: no member yet, cap 0 *)
  assert (HL0 : parse_items_shape.pis_slots true 0 0 0 ++ [] = []) by reflexivity.
  assert (F_open : parse_items_shape.pis_open tfibsegs (mrestrict (w_H W) (ms_mem ms2))
    (ReaderRes.lin (parse_items_shape.pis_slots true 0 0 0 ++ [])) v true 0 0 0 0
    (Z.of_nat (length (@nil (list Z * PjTree.jv)))) (map snd (@nil (list Z * PjTree.jv)))
    (map fst (@nil (list Z * PjTree.jv))) []).
  { unfold parse_items_shape.pis_open. rewrite HL0.
    split; [constructor|].
    split; [intros b y Hb; destruct Hb|].
    split; [exact F_hdr|].
    split.
    { unfold PjStruct.pj_slots_at, parse_items_shape.pis_oz.
      split; [right; reflexivity|]. split; [cbn [length Z.of_nat]; lia|].
      split; [intros _; split; [reflexivity | intros _; reflexivity] | intros Hc; exfalso; lia]. }
    split; [intros _; reflexivity|].
    unfold parse_items_shape.pis_items. split; exact eq_refl. }
  (* ---- the call configuration at grow #1, and pi_IG [] there ---- *)
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E4 (sh_ss (pi_st_e pr k)) ms2 HS4 Hrv) as Hshape.
  rewrite Hshape, Hpc.
  refine (HK [] ly S U W (ms_mem ms2) _ regsC chq (p + 1 + Z.of_nat (length ws)) 0 0 0 [] [] peak _).
  unfold pi_IG. cbv zeta.
  refine (conj Ems (conj _ (conj _ (conj _ (conj _ (conj R1 (conj R10 (conj _ (conj F_frame (conj _
    (conj F_text (conj _ _)))))))))))).
  + rewrite Ems, pim_ttrace_obj. reflexivity.
  + cbn [length Z.to_nat]. lia.
  + lia.
  + split; [exact HJ2|]. split; [exact HARU2|]. split; [exact HRO2 | exact HHEADS].
  + unfold pi_regsP. cbn [length Nat.eqb].
    split; [exact R2|]. split; [exact R8|]. split; [exact R20|]. split; [exact R3|]. split; [exact R4|].
    unfold pi_R0. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    * transitivity (Z_to_bv 64 (q + 16)); [exact R9 | symmetry; apply pie_off; [exact ERC | lia | lia]].
    * transitivity (Z_to_bv 64 1); [exact R19 | reflexivity].
    * transitivity (Z_to_bv 64 (pi_sh (q + 16))); [exact R21|].
      symmetry. apply pi_shv_denot; [exact ERC | exact ERC32 | lia | lia | lia].
    * transitivity (Z_to_bv 64 (q + 8)); [exact R22 | symmetry; apply pie_off; [exact ERC | lia | lia]].
    * transitivity (Z_to_bv 64 (pi_sh (q + 8))); [exact R23|].
      symmetry. apply pi_shv_denot; [exact ERC | exact ERC32 | lia | lia | lia].
    * transitivity (Z_to_bv 64 SHADOW_OFF); [exact R26 | rewrite fsw_SOff0; symmetry; exact ERC32].
    * transitivity (Z_to_bv 64 (pi_sh (q + 0))); [exact R27|].
      symmetry. apply pi_shv_denot; [exact ERC | exact ERC32 | lia | lia | lia].
  + split; [exact HCH2|]. split; [exact HCHF|]. split; [reflexivity|]. split; [exact F_pin | exact F_wk].
  + rewrite HL0. unfold pi_blocks.
    split; [exact F_rdt|]. split; [exact F_pobj|]. split; [intros a kk' Hin; destruct Hin|].
    split; [unfold rd_hblocks; cbn [map]; rewrite app_nil_r; apply Permutation_refl|].
    split; [unfold rd_heads; cbn [map]; rewrite app_nil_r; reflexivity|].
    split; [apply Permutation_refl|].
    split; [reflexivity|].
    split; [cbn [length]; lia|].
    split; [|lia].
    cbn [PjGrammar.held length Z.of_nat]. rewrite !Z.add_0_r. exact F_glob.
  + split; [exact F_hdr | exact F_open].
Qed.

End X.
