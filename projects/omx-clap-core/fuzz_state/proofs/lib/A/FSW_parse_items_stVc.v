(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the step pi_step_Vc of parse_items' member loop, from
   the call-site invariant pi_IV at parse_value (0x84d98, level k + 1, on q and the kid kids + 56 n) to pi_IG at grow
   #2 (0x84e60) for the next member, the `,` arm. Route: FSW_parse_items_calls.pic_call_pv_84d98 (u := x, ws := the
   separator's white space, cs := pi_csL; the frame chunks by FSW_parse_items_mem.pi_csL_ok); in its continuation
   FSW_parse_items_obj.pio_value joins parse_value's blocks to the live list (the key block apart from v by
   pio_new_apart); the resume state fss_retT 0x84d9c 144 pi_csL (pic_rs cap) pic_gf becomes
   FSW_parse_items_seg.pi_ss_s4c by the kit (pik_st_ok_setm to pig_rs, then FSW_parse_items_loop.pi_start_T over
   pig_rs: a0 := 0, the text window [44], the conditions pi_wsc 0 0), and then pvc_ss: pi_ss_s4c with v's write
   window narrowed to v->n ([v + 40, v + 48), pik_st_ok_setm), measured here by vm_compute (pvc_static / pvc_run /
   pvc_fin, SH pi_SH_s4c), so the run's frame keeps every byte below alloc_ceiling but v->n. At the stop (grow #2, ra
   0x84e64, a0 = v, v->n = n + 1, in->p past `,`) pio_snoc closes the member and pi_IG (dn ++ [(kk, x)]) is read off
   the stop (the text by pim_mgo_cons, T' := T ++ ttrace x, Di' := Di ++ [(a, |kk| + 1)] ++ D).
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
FSW_parse_items_seg FSW_parse_items_mem FSW_parse_items_mdl FSW_parse_items_loop FSW_parse_items_obj.
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
Hypothesis HPV : @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k).
(* (the callee: parse_value at level k + 1) *)

(* ================= S4c from a start state with v's write window narrowed to v->n (measured) ================= *)
(* pig_v_region with the write window [40, 48): S4c writes only v->n, so the run's frame keeps the rest of v *)
Definition pvc_vR : YP09.region := YP09.mkRegion (Some 20%nat) 0 56 40 48 (YP09.r_chunks pig_v_region).
Definition pvc_mem : list YP09.region :=
  [pik_treg (xatom 0) 0 [44]; fstk_ret 144 pi_csL; fs_got_region; fs_bcell_region 32; pig_q_region; pvc_vR].
Definition pvc_ss : sstate := pik_setm pi_ss_s4c pvc_mem.
Definition pvc_st : shst := fst (pi_tok_run pi_SH_s4c pvc_ss).
Lemma pvc_mem_eq : ss_mem pi_ss_s4c =
  [pik_treg (xatom 0) 0 [44]; fstk_ret 144 pi_csL; fs_got_region; fs_bcell_region 32; pig_q_region; pig_v_region].
Proof. reflexivity. Qed.
Lemma pvc_wf : regions_wf pvc_mem = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pvc_sub : submem pvc_mem (ss_mem pi_ss_s4c).
Proof.
rewrite pvc_mem_eq. unfold pvc_mem.
do 5 (apply submem_keep; [apply subregion_refl|]). apply submem_keep; [|apply submem_nil].
unfold subregion, pvc_vR, pig_v_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros c Hc. exact Hc.
Qed.
Lemma pvc_K : run_K 0 fs_Bx pi_SH_s4c pvc_ss = 53%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma pvc_static :
  sh_static_ok (run_K 0 fs_Bx pi_SH_s4c pvc_ss) fs_Bx fs_Bspan pi_SH_s4c (ss_facts pvc_ss) (ss_mem pvc_ss) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pvc_run : pi_tok_run pi_SH_s4c pvc_ss = (pvc_st, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
(* at grow #2: ra 0x84e64, a0 = v; v->n = n + 1 (the only byte window the run may write); in->p past `,` *)
Definition pvc_regs : list (bv 5 * sv) :=
  [(1%bv, SLit 0x84e64); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0);
   (10%bv, SOff 20 0); (20%bv, SOff 20 0)] ++ pi_RL.
Lemma pvc_fin :
  let s := sh_ss pvc_st in
  ss_pc s = A_grow /\ sh_obls pvc_st = [] /\ ss_resv s = None /\ sh_j pvc_st = 4%nat /\
  pi_regs_are s pvc_regs = true /\
  nth_error (ss_mem s) 1 = Some (fstk_ret 144 pi_csL) /\
  nth_error (ss_mem s) 4 = Some (YP09.mkRegion (Some 8%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))]) /\
  nth_error (ss_mem s) 5 = Some (YP09.mkRegion (Some 20%nat) 0 56 40 48
    [YP09.mkChunk 40 (CVal 8 (SOff (xatom 18) 1)); YP09.mkChunk 0 (CVal 4 (SLit 6));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 16) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 17) 0));
     YP09.mkChunk 48 (CVal 8 (SOff (xatom 19) 0))]).
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the write windows of the start state: the frame, q's 24 bytes, v->n *)
Lemma pvc_wr : forall E a, in_wrange E pvc_mem a ->
  bv_unsigned (ew E 2) <= a < bv_unsigned (ew E 2) + 144 \/ bv_unsigned (ew E 8) <= a < bv_unsigned (ew E 8) + 24 \/
  bv_unsigned (ew E 20) + 40 <= a < bv_unsigned (ew E 20) + 48.
Proof.
intros E a (r & Hin & Hr). unfold pvc_mem in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fstk_ret fs_got_region fs_bcell_region pig_q_region pvc_vR YP09.r_base YP09.r_wlo YP09.r_whi
    base_val] in Hr; lia.
Qed.
Lemma pvc_wr_ret : forall E a, in_wrange E pvc_mem a -> in_wrange E (fsT_ret_regions 144 pi_csL pig_rs) a.
Proof.
intros E a Ha. pose proof (pvc_wr E a Ha) as [H|[H|H]].
- exists (fstk_ret 144 pi_csL). split; [left; reflexivity|]. cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val]. lia.
- exists pig_q_region. split; [right; right; right; left; reflexivity|].
  cbn [pig_q_region YP09.r_base YP09.r_wlo YP09.r_whi base_val]. lia.
- exists pig_v_region. split; [right; right; right; right; left; reflexivity|].
  cbn [pig_v_region YP09.r_base YP09.r_wlo YP09.r_whi base_val]. lia.
Qed.

(* ================= small facts ================= *)
Lemma pvc_RL_atoms : forall r e, In (r, e) pi_RL -> forall n, In n (pik_sv_atoms e) ->
  n = 8%nat \/ n = 20%nat \/ n = 32%nat.
Proof.
intros r e Hin n Hn. pose proof pi_RL_ok as Hok. unfold pi_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'. cbv beta in Hn'. revert Hn'.
destruct (Nat.eqb_spec n 8); [intros _; left; assumption|].
destruct (Nat.eqb_spec n 20); [intros _; right; left; assumption|].
destruct (Nat.eqb_spec n 32); [intros _; right; right; assumption|].
cbn. discriminate.
Qed.
(* the stop's callee-saved list restated over the stop's own registers *)
Lemma pvc_RL_restate : forall E regs2,
  (forall r e, In (r, e) pi_RL -> YK11.getr regs2 r = sv_denot E e) -> ed E = ed (Ereg regs2 fs_extraT) ->
  ew E 8 = YK11.getr regs2 8%bv -> ew E 20 = YK11.getr regs2 20%bv -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (fun r => YK11.getr regs2 (fst r) = sv_denot (Ereg regs2 fs_extraT) (snd r)) pi_RL.
Proof.
intros E regs2 HG Hed E8 E20 E32. apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (HG r e Hin). apply pik_sv_denot_agree; [exact Hed|].
intros n Hn. destruct (pvc_RL_atoms r e Hin n Hn) as [ -> | [ -> | -> ] ].
- rewrite (ew_Ereg_nat regs2 fs_extraT 8 8%bv eq_refl). exact E8.
- rewrite (ew_Ereg_nat regs2 fs_extraT 20 20%bv eq_refl). exact E20.
- change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. exact E32.
Qed.
(* a byte's view, and the view of an unpoisoned memory, from the raw restricted byte *)
Lemma pvc_av : forall (H : word -> bool) (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte. cbv beta. rewrite E. reflexivity. Qed.
Lemma pvc_av_unp : forall (H : word -> bool) U0 (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
  aview tfibsegs H (unpoison U0 m') a = aview tfibsegs H (unpoison U0 m) a.
Proof.
intros H U0 m m' a E. unfold aview, mbyte. cbv beta. unfold mrestrict, unpoison in *.
destruct (H (Z_to_bv 64 a)); [reflexivity|]. destruct (in_ush U0 (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
rewrite E. reflexivity.
Qed.
Lemma pvc_mbyte : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof. intros m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma pvc_val_eq : forall (m m' : word -> option byte) a n z,
  (forall j, (j < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  val_mem tfibsegs m a n z -> val_mem tfibsegs m' a n z.
Proof. intros m m' a n z H Hv j Hj. rewrite (pvc_mbyte m m' _ (H j Hj)). exact (Hv j Hj). Qed.
Lemma pvc_bytes_at_eq : forall (m m' : word -> option byte) a bs,
  (forall j, (j < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  Mem.bytes_at tfibsegs m a bs -> Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (H i Hi). exact (H3 i Hi).
Qed.
(* fs's statics are no read-only bytes (FSW_pj_free.v pjf_pstat_not_roP, restated: that file is not imported) *)
Lemma pvc_pstat_not_roP : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
assert (Hlo : 0xa3ca0 <= a) by (destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia).
destruct Hro as [(s & Hs & Hw & Hsr) | Hr2]; [|unfold FS_RLO, FS_RHI in Hr2; lia].
assert (Hall : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa3ca0)) tfibsegs
  = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall s Hs). rewrite Hw in Hall. cbn [orb] in Hall.
apply Z.leb_le in Hall. lia.
Qed.
(* the bytes left after the text at in->p are as many as in->end - in->p *)
Lemma pvc_rest_lt : forall (tb0 : list byte) t0 p0 c r, t0 <= p0 -> ReaderRes.rest_at tb0 t0 p0 = c :: r ->
  p0 - t0 < Z.of_nat (length tb0).
Proof.
intros tb0 t0 p0 c r Hp H. destruct (pim_rest_byte tb0 t0 p0 c r Hp H) as (Hn & _).
assert (Hl : (Z.to_nat (p0 - t0) < length tb0)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia.
Qed.

(* ================= the step ================= *)
Lemma pi_step_Vc : forall dn kk x kk' x' rm' T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da
    peak1 a (Qc : world tfibsegs -> config -> Prop),
  IV dn kk x ((kk', x') :: rm') T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' Di' Da' peak1',
     IG (dn ++ [(kk, x)]) kk' x' rm' T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids keys cap Di' Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_grow regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_value regsC memC mdC) Qc.
Proof.
intros dn kk x kk' x' rm' T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a Qc HIV KC.
unfold pi_IV, pi_IK in HIV. cbv zeta in HIV.
destruct HIV as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HSTK & HTXT & HBL & HOBJ & Hu64 & Hcstr) &
  R1 & R10 & R11 & HZK & HPK).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R8 & R20 & R3 & R4 & RL).
pose proof HSTK as (HCH & HFW & Htop & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HRB & HPERM & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOBJ as (HHDR & HOP).
pose proof HARU as (HAR & _ & _).
(* ---- the numbers ---- *)
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
pose proof (pi_stk144 k S regs ot ms Hk HDEP) as H144.
pose proof (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & Hnev & _).
pose proof HTX as (_ & (TIN0 & _) & _).
assert (HH : HEAD = 16) by reflexivity.
assert (Hxr : length (map (YK11.getr regs) pi_saved) = 13%nat) by exact (pi_xr_len regs).
assert (Hn : Z.of_nat (length dn) < cap) by lia.
assert (Hvimg0 : pghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v))
  by exact (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR0 HPO0).
(* the disjunctions lia would case-split on, kept out of its sight *)
assert (HVTXh : pghide (v + 56 <= text - HEAD \/ text + tcap <= v)) by exact HVTX.
assert (HVSPh : pghide (v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v)) by exact HVSP.
clear HVTX HVSP.
(* ---- the member's own facts, the budgets ---- *)
destruct (pi_mem_facts k S regs ot ms Hk HDV HDS HWF HDEP dn kk x ((kk', x') :: rm') Hms)
  as (Hplain & Hsoo & Hstr & Hwf & Hdep).
destruct (pi_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]) T
  (PjRoundTrip.ttrace x) (PjRoundTrip.tgo_obj (Datatypes.S (length dn)) (Z.to_nat cap) ((kk', x') :: rm'))
  Htr Hnev HPERM HSUM HLEN) as (B1 & B2 & B3 & B4 & B5).
assert (HFRL1 : Z.of_nat (length (frames Sc)) <= FRL_parse_value (Z.of_nat (Datatypes.S k))).
{ rewrite (pi_frames B k ly S U W regs mem md ot v lyc Sc Uc W1 memC mdC (rd_ev T) HJC).
  replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1) by lia. exact HFRL. }
(* ---- the key block is apart from v (v placed at the entry, the key block live since) ---- *)
assert (HAPa : PjStruct.pj_apart [(a, Z.of_nat (length kk) + 1)] v).
{ intros b0 z [<-|[]] Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz.
  assert (HinL : In (a, Z.of_nat (length kk) + 1)
    (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
    by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  pose proof (HRB _ _ HinL) as (HinA & _ & HKa & _).
  destruct (pio_jr_frames B _ _ _ ly S W (unpoison U mem) md lyc Sc W1 (unpoison Uc memC) mdC _ HJ HAR0)
    as (Hfr & Hfa).
  apply (pio_new_apart B ly S W mem v lyc Sc W1 (unpoison Uc memC) mdC (a - HEAD) (Z.of_nat (length kk) + 1 + HEAD)
    HAR HPO0 Hfr Hfa).
  - intros b mm Hb _ _. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hb.
  - exact HinA.
  - apply (pi_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
    unfold rd_hblocks. apply (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ _ HinL).
  - rewrite pio_req_hb by lia. lia. }
(* ---- the call of parse_value (k + 1) on q and the kid ---- *)
eapply (pic_call_pv_84d98 B HSS k HPV (spZ regs) ot ly S U W mem md [] lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq q
  text len pc tb tcap (map (YK11.getr regs) pi_saved) v 0 0 kids keys (Z.of_nat (length dn)) cap x pr
  (if pr then [32] else [])
  (concat (pi_mgo pr (Z.of_nat k) (Datatypes.S (length dn)) ((kk', x') :: rm')) ++ pi_wsb pr (Z.of_nat k) ++ [125] ++ rest)
  (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail pi_csL Qc).
- exact Hk.
- exact HJ.
- exact HARU.
- exact HRO.
- exact HHD.
- exact HFRL1.
- exact R1.
- exact Rsp.
- exact Hsp16.
- lia.
- exact R8.
- exact R20.
- exact R10.
- exact R11.
- exact R3.
- exact R4.
- apply (achain_lower lyc _ (spZ regs) (spZ regsC) q chq HCH). lia.
- rewrite Htop. exact HFW.
- exact Hsq.
- exact Hq24.
- replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1) by lia. exact HIN.
- exact HTX1.
- exact TIN0.
- replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1) by lia. exact HTXT.
- exact (pim_wsep_ws pr).
- exact Hsoo.
- exact Hstr.
- exact Hwf.
- exact Hdep.
- exact Hxr.
- exact HPO1.
- exact HHDR.
- exact Hn.
- intros a0 k0 Hin. apply HRB. apply in_or_app. left. exact Hin.
- destruct HOP as (_ & HAPs & _). intros b0 z Hb Hz. apply (HAPs b0 z); [apply in_or_app; left; exact Hb | exact Hz].
- intros b0 Hb. apply (pi_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks in *. apply in_map_iff in Hb as (b1 & <- & Hb1).
  apply (in_map (fun b => (fst b - HEAD, snd b + HEAD))). apply in_or_app. left. exact Hb1.
- exact HPK.
- exact HZK.
- exact HG1.
- exact B1.
- exact B5.
- exact B2.
- exact B3.
- exact B4.
- exact pi_wf_csL.
- intros regs' HP.
  lazymatch goal with |- Forall (YP09.chunk_ok _ (Ereg _ (fs_extraT ++ ?xs)) _ _) _ =>
    destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pi_RL HRP HP) as (E8 & E20 & E32 & _) end.
  apply (pi_csL_ok _ _ (spZ regs) (map (YK11.getr regs) pi_saved) q v Hxr); [| exact E8 | exact E20 | exact E32
    | lia | lia | lia | lia | exact HFL].
  intros j Hj. apply pi_pig_xs_saved; [exact Hxr | exact Hj].
- intros D Da' ly' S' W' regs' mem' md' HPm HJ2 HJc HARU' HP A0 HS0 HIN' HWK' HPERM' HRT HSUMx HLENx HPOk HTX' HG'
    HHDR' VBm BLK' KBm.
  pose proof HARU' as (HAR' & HUOK' & HUPS').
  pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfr2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlytop' & Hlylo' & Hlyhi' & _).
  destruct HG' as (peak' & Hpk' & HG'').
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Bpc & _).
  pose proof (fsw_pobj_low B lyc Sc W1 (unpoison Uc memC) mdC memC _ HAR HPK) as (Hvk1 & Hvk2).
  assert (Hvkimg : pghide (kids + 56 * Z.of_nat (length dn) + 56 <= 0x10000 \/ FS_IMG_END <= kids + 56 * Z.of_nat (length dn)))
    by exact (fsw_pobj_off_img B lyc Sc W1 (unpoison Uc memC) mdC memC _ HAR HPK).
  remember (pc + Z.of_nat (length (if pr then [32] else [])) +
    Z.of_nat (length (concat (WriterValue.wvpieces x pr (Z.of_nat (Datatypes.S k)))))) as p' eqn:Ep'.
  set (xs := pig_xs p' (text + len) (Z.of_nat (Datatypes.S k)) (map (YK11.getr regs) pi_saved) kids keys
    (Z.of_nat (length dn)) cap) in *.
  set (U' := Uc ++ rd_heads Da') in *.
  destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pi_RL HRP HP) as (E8 & E20 & E32 & E2 & Egp & Etp).
  destruct (pig_xs_nth p' (text + len) (Z.of_nat (Datatypes.S k)) (map (YK11.getr regs) pi_saved) kids keys
    (Z.of_nat (length dn)) cap Hxr) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
  set (E := Ereg regs' (fs_extraT ++ xs)) in *.
  assert (Y0 : ew E (xatom 0) = Z_to_bv 64 p') by (unfold E; rewrite fsw_ew_xatom; exact X0).
  assert (Y1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E; rewrite fsw_ew_xatom; exact X1).
  assert (Y2 : ew E (xatom 2) = Z_to_bv 64 (Z.of_nat (Datatypes.S k))) by (unfold E; rewrite fsw_ew_xatom; exact X2).
  assert (Y18 : ew E (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn))) by (unfold E; rewrite fsw_ew_xatom; exact X18).
  assert (E8u : bv_unsigned (ew E 8) = q) by (rewrite E8; apply wz; lia).
  assert (E20u : bv_unsigned (ew E 20) = v) by (rewrite E20; apply wz; lia).
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN') as (_ & _ & _ & Bp' & Bend & _).
  pose proof HIN' as (_ & _ & _ & _ & _ & _ & _ & _ & HL9 & _).
  (* ---- the text: `,` at in->p, the next member after it ---- *)
  rewrite pim_mgo_cons in HTXT. cbn [Nat.eqb] in HTXT.
  assert (Hrv : ReaderRes.rest_at tb text p' = [44] ++
    (concat (WriterValue.wind pr (Z.of_nat k + 1)) ++ concat (WriterSpec.spieces kk') ++ WriterValue.wsep pr ++
     concat (WriterValue.wvpieces x' pr (Z.of_nat k + 1)) ++
     concat (pi_mgo pr (Z.of_nat k) (Datatypes.S (Datatypes.S (length dn))) rm') ++ pi_wsb pr (Z.of_nat k) ++ [125] ++
     rest)).
  { rewrite Ep'. replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1) by lia.
    rewrite <- Z.add_assoc, <- Nat2Z.inj_add, <- length_app.
    apply pim_rest_skip; [lia|]. rewrite HTXT. rewrite <- !app_assoc. reflexivity. }
  pose proof (pvc_rest_lt tb text p' 44 _ ltac:(lia) Hrv) as Hp'lt.
  pose proof (pim_rest_skip tb text p' [44] _ ltac:(lia) Hrv) as Hrv1. change (Z.of_nat (length [44])) with 1 in Hrv1.
  destruct (pi_txt_bytes k S regs ot text len tb ms Hk HDEP _ q p' (Z.of_nat (Datatypes.S k)) [44] _ HIN' Hrv)
    as (Hbr & Hbyte).
  (* ---- the object across parse_value ---- *)
  assert (EL : parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)] =
    (parse_items_shape.pis_slots true kids keys cap ++ Di) ++ [(a, Z.of_nat (length kk) + 1)]) by apply app_assoc.
  pose proof (pio_value B ly S U lyc Sc Uc W1 memC mdC ly' S' W' mem' md' _ _ _ v text len tcap (length dn) dn kids keys
    cap Di Da T a kk x D Da' eq_refl Hn HARU ltac:(rewrite <- EL; exact HPERM) HUc ltac:(rewrite <- EL; exact HDa)
    ltac:(rewrite <- EL; exact HSUM) ltac:(rewrite <- EL; exact HLEN) HHD ltac:(rewrite <- EL; exact HRB) HPO1
    ltac:(rewrite <- EL; exact HOP) Hu64 ltac:(rewrite <- EL; exact Hcstr) HAPa HPm HJc HARU' HPERM' HRT HSUMx HLENx
    HTX' HHDR' VBm BLK' KBm) as PV.
  cbv zeta in PV.
  destruct PV as (RB6 & PERM6 & U6 & DA6 & SUM6 & LEN6 & HD6 & TX6 & PO6 & HDR6 & OP6 & U646 & CS6 & ND6 & NODUP6 & AP6).
  rewrite <- !app_assoc in RB6, PERM6, DA6, SUM6, LEN6, OP6, CS6, ND6, NODUP6.
  (* ---- the start state: pi_ss_s4c, then v's write window narrowed ---- *)
  assert (SUB0 : submem (fsT_ret_regions 144 pi_csL pig_rs) (ss_mem (fss_retT 544156 144 pi_csL (pic_rs cap) pic_gf))).
  { cbn [ss_mem fss_retT fsT_ret_regions pic_rs pig_rs app].
    repeat (apply submem_keep; [apply subregion_refl|]). apply submem_nil. }
  pose proof (pik_st_ok_setm _ _ _ _ HS0 SUB0 pi_wf_csL_g) as HS1.
  change (pik_setm (fss_retT 544156 144 pi_csL (pic_rs cap) pic_gf) (fsT_ret_regions 144 pi_csL pig_rs)) with
    (fss_retT 544156 144 pi_csL pig_rs pic_gf) in HS1.
  pose proof (pi_text_rng B k S regs q ot text len tcap tb ms Hk HDEP ly' S' W' _ md' mem' p' (Z.of_nat (Datatypes.S k))
    HAR' HTX' HIN') as (T1 & T2 & T3 & T4 & T5).
  pose proof HTX' as (_ & (TIN' & _ & Htc & _) & Htl').
  assert (Himg : pghide (text + tcap <= 65536 \/ FS_IMG_END <= text - HEAD)).
  { pose proof (fsw_ablock_off_img B ly' S' W' _ md' _ _ HAR' TIN') as Himg0.
    rewrite pio_req_hb in Himg0 by lia. unfold pghide. destruct Himg0; [left|right]; lia. }
  assert (RT : region_ok tfibsegs E (mrestrict (w_H W') mem') (pik_treg (xatom 0) 0 [44])).
  { apply (pik_treg_ok E _ (xatom 0) p' 0 [44]); [rewrite Y0; apply wz; lia | lia | lia | cbn [length Z.of_nat]; lia
      | exact Hbr |].
    intros i0 Hi0. rewrite Z.add_0_r. exact (Hbyte i0 Hi0). }
  assert (DJ : all_disjoint E (pik_treg (xatom 0) 0 [44]) (fsT_ret_regions 144 pi_csL pig_rs)).
  { apply (pi_treg_disj B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTXh HPO0 HDEP
      E [44] pi_csL p'); [rewrite Y0; apply wz; lia | exact E2 | exact E8u | exact E20u | lia | cbn [length Z.of_nat]; lia
      | lia | lia | lia | exact Himg]. }
  assert (HC : conds_ok E (pi_wsc 0 0))
    by exact (pi_conds_ws k S regs ot ms Hk HDEP E 0 0 p' (text + len) Y0 Y1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (Ha0 : YK11.getr regs' 10 = sv_denot E (SLit 0)) by (rewrite A0; reflexivity).
  pose proof (pi_start_T B k S regs q ot v ms Hk HDEP regsC regs' xs W' mem' 544156 pi_csL pig_rs pic_gf pi_RL (SLit 0)
    [44] (pi_wsc 0 0) HS1 HRP HP pi_RL_ok Ha0 RT DJ HC) as HS2.
  pose proof (pik_st_ok_setm _ pi_ss_s4c _ pvc_mem HS2 pvc_sub pvc_wf) as HS3.
  change (pik_setm pi_ss_s4c pvc_mem) with pvc_ss in HS3.
  (* ---- the shadow entries: the text window, q, v ---- *)
  assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  assert (U0 : YP0e.U E (SOff (xatom 0) 0) = p') by (apply U_atom; [exact Y0 | lia]).
  assert (Uq : YP0e.U E (SOff 8 0) = q) by (apply U_atom; [exact E8 | lia]).
  assert (Uv : YP0e.U E (SOff 20 0) = v) by (apply U_atom; [exact E20 | lia]).
  assert (SHOK : sh_ok tfibsegs fs_Bx pi_SH_s4c E (mrestrict (w_H W') mem')).
  { unfold sh_ok, pi_SH_s4c, pi_SHm. constructor; [|constructor; [|constructor; [|constructor]]].
    - exact (pi_sh_blk B k S regs ot ms Hk HDEP ly' S' U' W' mem' md' E (xatom 0) (text - HEAD) (tcap + HEAD) p' 0 1
        HARU' HD6 TIN' ltac:(lia) ltac:(lia) ltac:(lia) UB U0).
    - exact (pi_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' U' W' mem' md'
        E 8 HARU' Hlylo' Hlyhi' UB Uq).
    - exact (pi_sh_v B k S regs ot v ms Hk HDEP ly' S' U' W' mem' md' E 20 HARU' PO6 UB Uv). }
  assert (AWR : awr_ok tfibsegs B E (ss_mem pvc_ss) (STK_parse_items (1 - k) + (ot - spZ regs)) ot
    ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B ly' S') ly' [] (frames S)).
  { intros a0 Ha0'.
    exact (pi_awr_ret B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E ly' S' W' _ md' mem' pi_csL HAR' PO6
      Hfr2 E2 E8u E20u a0 (pvc_wr_ret E a0 Ha0')). }
  (* ---- the read-only view after the call ---- *)
  assert (HROc : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem')).
  { apply (arodata_kept B _ _ _ lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' _ HJc HARU HUOK' HUPS'); [| |exact HRO].
    - apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia.
    - intros a0 Ha0' Hf. apply inFP_app in Hf as [Hf|Hf].
      + apply inFP_cons in Hf as [Hf|Hf]; [|exact (inFP_nil _ Hf)].
        pose proof (pic_img_lo a0 (fsw_roP_img a0 Ha0')). destruct Hvkimg; lia.
      + exact (pvc_pstat_not_roP a0 Ha0' Hf). }
  (* ---- the run S4c ---- *)
  eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' _ E _ fs_Bx fs_Bspan pi_SH_s4c pvc_ss pvc_st
    (TS_stopped SR_fetch) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS3 SHOK pvc_static pvc_run I HARU' HJ2).
  { destruct pvc_fin as (_ & Hob & _). rewrite Hob. constructor. }
  { exact AWR. }
  intros ws ms2 mat2 Hlen HS4 SHOK4 HJ4 HARU4 HFr HFr' HG4.
  destruct pvc_fin as (Fpc & Fob & Fresv & Fj & Fregs & Ffr & Fq & Fv).
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms2 HS4 Fresv) as Hms2.
  rewrite Hms2, Fpc.
  set (E4 := extK E (run_K 0 fs_Bx pi_SH_s4c pvc_ss) ws) in *.
  assert (EK : forall n, (n < 53)%nat -> ew E4 n = ew E n).
  { intros n Hn53. unfold E4. apply (pi_ew_extK k S regs ot ms Hk HDEP). rewrite pvc_K. exact Hn53. }
  set (mem7 := ms_mem ms2) in *.
  set (md7 := with_vm_backing (m_vm_lazy md') mat2 md') in *.
  cbn [ms_mem mkst] in HFr'.
  (* what the run kept: every byte but the frame, q's 24 bytes and v->n *)
  assert (KEEP7 : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 144 <= y < spZ regs) -> ~ (q <= y < q + 24) ->
    ~ (v + 40 <= y < v + 48) -> mrestrict (w_H W') mem7 (Z_to_bv 64 y) = mrestrict (w_H W') mem' (Z_to_bv 64 y)).
  { intros y Hy H1 H2 H3. apply HFr'. rewrite wz by lia. intros Hw. apply (pvc_wr E y) in Hw.
    rewrite E2, E8u, E20u in Hw. lia. }
  (* the stop's registers *)
  pose proof (pi_regs_of_stop _ _ ms2 (w_H W') _ HS4 Fregs) as RG. rewrite Forall_forall in RG.
  assert (G : forall r e, In (r, e) pvc_regs -> YK11.getr (ms_regs ms2) r = sv_denot E4 e)
    by (intros r e Hin; exact (RG (r, e) Hin)).
  pose proof (G 1%bv (SLit 0x84e64) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G1.
  pose proof (G 2%bv (SOff 2 0) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G2.
  pose proof (G 3%bv (SOff 3 0) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G3.
  pose proof (G 4%bv (SOff 4 0) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G4.
  pose proof (G 8%bv (SOff 8 0) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G8.
  pose proof (G 10%bv (SOff 20 0) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G10.
  pose proof (G 20%bv (SOff 20 0) ltac:(unfold pvc_regs; apply in_or_app; left; cbn; tauto)) as G20.
  rewrite fsw_SOff0 in G2, G3, G4, G8, G10, G20.
  (* the stop's q and v regions, and the frame *)
  pose proof (fsw_region_nth _ _ _ 4 _ HS4 Fq) as RQ. rewrite restrict_mem in RQ.
  pose proof (fsw_region_nth _ _ _ 5 _ HS4 Fv) as RV. rewrite restrict_mem in RV.
  pose proof (fsw_region_nth _ _ _ 1 _ HS4 Ffr) as RF. rewrite restrict_mem in RF.
  assert (E4_8 : bv_unsigned (ew E4 8) = q) by (rewrite EK by lia; exact E8u).
  assert (E4_20 : bv_unsigned (ew E4 20) = v) by (rewrite EK by lia; exact E20u).
  assert (DS : forall n z c, ew E n = Z_to_bv 64 z -> 0 <= z -> 0 <= c -> z + c < 2 ^ 64 -> (n < 53)%nat ->
    sv_denot E4 (SOff n c) = Z_to_bv 64 (z + c)).
  { intros n z c Hn0 Hz Hc Hzc Hn53. apply bv_eq. rewrite denot_SOff. rewrite (EK n Hn53), Hn0, (wz z) by lia.
    rewrite (wz (z + c)) by lia. apply zcanon_id. unfold M64. lia. }
  (* ---- v->n := n + 1, the member closed ---- *)
  assert (V40 : val_mem tfibsegs (mrestrict (w_H W') mem7) (v + 40) 8 (Z.of_nat (length dn) + 1)).
  { exact (fsw_field E4 _ 20 v _ 0 56 40 48 40 8 (SOff (xatom 18) 1) (Z.of_nat (length dn) + 1) RV E4_20
      ltac:(cbn; tauto) (DS (xatom 18) (Z.of_nat (length dn)) 1 Y18 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold xatom; lia))
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (WRz : forall z, v + 40 <= z < v + 48 -> writable_at tfibsegs (mrestrict (w_H W') mem7) z).
  { intros z Hz. pose proof RV as (_ & _ & RVW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RVW.
    rewrite E4_20 in RVW. replace z with (v + (z - v)) by lia. apply RVW. lia. }
  assert (KEEPz : forall z, 0 <= z < alloc_ceiling -> ~ (v + 40 <= z < v + 48) ->
    mrestrict (w_H W') mem7 (Z_to_bv 64 z) = mrestrict (w_H W') mem' (Z_to_bv 64 z))
    by (intros z Hz Hnv; apply KEEP7; lia).
  pose proof (pio_snoc B ly' S' U' W' mem' md' mem7 v text len tcap kids keys cap (length dn) dn kk x Di a D eq_refl Hn
    HARU' RB6 TX6 PO6 OP6 U646 CS6 ND6 NODUP6 AP6 V40 KEEPz WRz) as SN.
  cbv zeta in SN. destruct SN as (HDR7 & OP7 & RB7 & TX7 & PO7).
  (* ---- struct pj_in: in->p past `,` ---- *)
  assert (PIN7 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem7) q text len (p' + 1) (Z.of_nat k + 1) tb).
  { pose proof HIN' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
    pose proof (fsw_field E4 _ 8 q _ 0 24 0 24 0 8 (SOff (xatom 0) 1) (p' + 1) RQ E4_8 ltac:(cbn; tauto)
      (DS (xatom 0) p' 1 Y0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold xatom; lia)) ltac:(cbn; lia) ltac:(cbn; lia))
      as Q0.
    pose proof (fsw_field E4 _ 8 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len + 0) RQ E4_8 ltac:(cbn; tauto)
      (DS (xatom 1) (text + len) 0 Y1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold xatom; lia)) ltac:(cbn; lia)
      ltac:(cbn; lia)) as Q8.
    pose proof (fsw_field E4 _ 8 q _ 0 24 0 24 16 4 (SOff (xatom 2) 0) (Z.of_nat (Datatypes.S k) + 0) RQ E4_8
      ltac:(cbn; tauto) (DS (xatom 2) (Z.of_nat (Datatypes.S k)) 0 Y2 ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold xatom; lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Q16.
    rewrite Z.add_0_r in Q0, Q8, Q16.
    pose proof RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E4_8 in RQW.
    refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 _))))))))))).
    - apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Q0 | lia | lia | lia].
    - apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Q8 | lia | lia | lia].
    - apply (proj1 (fsw_pj_word4_iff _ _ (q + 16) (Z.of_nat k + 1) ltac:(lia) ltac:(lia))).
      replace (Z.of_nat k + 1) with (Z.of_nat (Datatypes.S k)) by lia. exact Q16.
    - split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
    - lia.
    - apply (pvc_bytes_at_eq (mrestrict (w_H W') mem')); [|exact I10].
      intros j Hj. apply KEEP7; destruct HVTXh; lia.
    - lia. }
  (* ---- the caller's window and the frame chain at q ---- *)
  assert (WK7 : wkeep tfibsegs W1 W' memC mem7 (spZ regs) ot q 24).
  { intros a0 Ha0' Hq0'. destruct (HWK' a0 ltac:(lia) Hq0') as (Hb & Hw).
    assert (E7 : mrestrict (w_H W') mem7 (Z_to_bv 64 a0) = mrestrict (w_H W') mem' (Z_to_bv 64 a0))
      by (apply KEEP7; lia).
    split; [rewrite (pvc_mbyte _ _ a0 E7); exact Hb|].
    split; intros Hw'.
    - exact (writable_at_eq tfibsegs _ _ a0 E7 (proj1 Hw Hw')).
    - exact (proj2 Hw (writable_at_eq tfibsegs _ _ a0 (eq_sym E7) Hw')). }
  assert (WK : wkeep tfibsegs W W' mem mem7 (spZ regs) ot q 24)
    by exact (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W' memC mem7 (spZ regs) HWK WK7 (Z.le_refl _)).
  assert (CH7 : achain ly' (aview tfibsegs (w_H W') (unpoison U' mem7)) (spZ regs) q chq).
  { apply (pi_chain_kept lyc ly' (aview tfibsegs (w_H W1) (unpoison Uc memC)) _ (spZ regs) q (ly_top ly) chq HCH HFW
      Htop Hlytop').
    intros a0 Ha0' Hq0'.
    assert (Hsh0 : ~ (SHADOW_OFF <= a0 < SHADOW_OFF + 2 ^ 44)) by (unfold SHADOW_OFF; lia).
    rewrite (pvc_av_unp (w_H W') U' mem' mem7 a0 (KEEP7 a0 ltac:(lia) ltac:(lia) Hq0' ltac:(lia))).
    destruct (Z_lt_le_dec a0 ot) as [Hlt|Hge].
    - rewrite (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' a0
        (fsw_unpoison_app B ly' S' U' W' mem' md' a0 HARU' ltac:(lia) Hsh0)).
      rewrite (aview_at tfibsegs (w_H W1) (unpoison Uc memC) memC a0
        (fsw_unpoison_app B lyc Sc Uc W1 memC mdC a0 HARU ltac:(lia) Hsh0)).
      destruct (HWK' a0 ltac:(lia) Hq0') as (Hb & _). unfold aview. cbv beta. rewrite Hb. reflexivity.
    - pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & HJ9 & _). apply HJ9; lia. }
  (* ---- the read-only view and the statics after the run ---- *)
  assert (RO7 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem7)).
  { apply (FSW_pj_parse.pjp_arodata_keep B W' mem' mem7); [|exact HROc].
    intros y Hy. pose proof (fs_segs_img y Hy) as Hy'. pose proof (pic_img_lo y Hy) as Hy''.
    apply pvc_av. apply KEEP7; unfold FS_IMG_END in *; destruct Hvimg0; lia. }
  assert (HG7 : fs_glob tfibsegs W' mem7 (live + PjGrammar.held (T ++ PjRoundTrip.ttrace x)) peak'
    (cnt + Z.of_nat (length (T ++ PjRoundTrip.ttrace x))) fail).
  { rewrite PjGrammar.held_app, length_app, Nat2Z.inj_add, !Z.add_assoc.
    assert (GK : forall g z, 0xa3ca0 <= g -> g + 8 <= 0x5da608 ->
      val_mem tfibsegs (mrestrict (w_H W') mem') g 8 z -> val_mem tfibsegs (mrestrict (w_H W') mem7) g 8 z).
    { intros g z Hg1 Hg2 Hv. apply (pvc_val_eq (mrestrict (w_H W') mem')); [|exact Hv].
      intros j Hj. apply KEEP7; unfold FS_IMG_END in *; destruct Hvimg0; lia. }
    destruct HG'' as (G1' & G2' & G3' & G4' & GR).
    split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1']|].
    split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2']|].
    split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3']|].
    split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4']|].
    exact GR. }
  (* ---- pi_IG for the next member (kk', x') ---- *)
  apply (KC (T ++ PjRoundTrip.ttrace x) ly' S' U' W' mem7 md7 (ms_regs ms2) chq (p' + 1)
    (Di ++ [(a, Z.of_nat (length kk) + 1)] ++ D) (Da ++ Da') peak').
  unfold pi_IG. cbv zeta.
  replace (length (dn ++ [(kk, x)])) with (Datatypes.S (length dn)) by (rewrite length_app; cbn [length]; lia).
  cbn [Nat.eqb].
  split; [rewrite <- app_assoc; exact Hms|].
  split; [rewrite <- app_assoc; exact Htr|].
  split; [exact Hcap|].
  split; [lia|].
  split; [split; [rewrite pim_rd_ev_app; exact HJ4|]; split; [exact HARU4|]; split; [exact RO7 | exact HD6]|].
  split; [rewrite G1; reflexivity|].
  split; [rewrite G10, EK by lia; exact E20|].
  split.
  { split; [unfold spZ at 1; rewrite G2, EK by lia; exact E2|].
    split; [rewrite G8, EK by lia; exact E8|]. split; [rewrite G20, EK by lia; exact E20|].
    split; [rewrite G3, EK by lia; exact Egp|]. split; [rewrite G4, EK by lia; exact Etp|].
    apply (pvc_RL_restate E4 (ms_regs ms2)).
    - intros r e Hin. apply G. unfold pvc_regs. apply in_or_app. right. exact Hin.
    - unfold E4. rewrite pi_ed_extK. reflexivity.
    - rewrite G8. reflexivity.
    - rewrite G20. reflexivity.
    - rewrite EK by lia. exact E32. }
  split.
  { apply (pi_frameL_of B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTXh HPO0 HDEP
      HVSPh E4 _ pi_csL Hxr); [rewrite EK by lia; exact E2 | rewrite EK by lia; exact E8 | rewrite EK by lia; exact E20
      | rewrite EK by lia; exact E32 | | exact RF | apply incl_refl].
    intros j Hj. rewrite EK by (unfold xatom; lia). unfold E. apply pi_pig_xs_saved; [exact Hxr | exact Hj]. }
  split; [split; [exact CH7|]; split; [exact HFW|]; split; [exact Hlytop'|]; split; [exact PIN7 | exact WK]|].
  split; [exact Hrv1|].
  split.
  { split; [exact TX7|]. split; [exact PO7|]. split; [exact RB7|]. split; [exact PERM6|]. split; [exact U6|].
    split; [exact DA6|]. split; [exact SUM6|]. split; [exact LEN6|]. split; [exact HG7 | lia]. }
  split; [|exact OP7].
  replace (Z.of_nat (Datatypes.S (length dn))) with (Z.of_nat (length dn) + 1) by lia. exact HDR7.
Qed.

End X.
