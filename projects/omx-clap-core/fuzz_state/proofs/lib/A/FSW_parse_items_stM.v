(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the step pi_step_M of parse_items' member loop, from
   the call-site invariant pi_IM at __asan_memset (0x84d78, the kid kids + 56 n) to pi_IV at parse_value (0x84d98).
   Route: FSW_parse_items_calls.pic_call_ms_84d78 (m := 1 - k, cs := pi_csL; the frame chunks by pi_csL_ok); in its
   continuation FSW_parse_items_obj.pio_zero carries the open object, the key and the blocks to the memset's memory;
   the resume state fss_retT 0x84d7c 144 pi_csL (pic_rs cap) pic_gf becomes the segment's start state by the kit
   (pik_st_ok_setm to the five ret regions with every write window narrowed to [0, 0) (pim_ro: S3 writes nothing, so
   the run's frame keeps the whole memory), pik_st_ok_extra with four words so that xatom 23 = kids + 56 n,
   pik_st_ok_setr pi_RL, pik_st_ok_addf pi_gf_vk / pi_al_vk): that is pim_ss_s3 = FSW_parse_items_seg.pi_ss_s3 with
   read-only regions (pim_ss_s3_is), measured here by vm_compute (pim_static_s3 / pim_run_s3 / pim_fin_s3, SH pi_SHm).
   The stop is the parse_value call (a0 = q, a1 = the kid, ra 0x84d9c); its memory is the memset's (functional
   extensionality over the empty write frame), and pi_IV is read off the memset's facts and the stop registers.
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

(* callee: FsRt's fr_memset, FSupoisonU's ARU form of the donor's __asan_memset contract at PC_memset 0x521bc *)
Hypothesis MS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* ================= S3 from a read-only start state (measured) ================= *)
(* a region with its write window narrowed to [0, 0) *)
Definition pim_ro (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).
Definition pim_rs3 : list YP09.region := map pim_ro (fsT_ret_regions 144 pi_csL pig_rs).
Definition pim_ss_s3 : sstate :=
  pik_addf (pik_setr (pik_setm (fss_retT 0x84d7c 144 pi_csL pig_rs pic_gf) pim_rs3) pi_RL) pi_gf_vk [] [pi_al_vk].
Lemma pim_ss_s3_is : pim_ss_s3 = pik_setm pi_ss_s3 (map pim_ro (ss_mem pi_ss_s3)).
Proof. reflexivity. Qed.
Definition pim_st_s3 : shst := fst (pi_tok_run pi_SHm pim_ss_s3).
Lemma pim_static_s3 :
  sh_static_ok (run_K 0 fs_Bx pi_SHm pim_ss_s3) fs_Bx fs_Bspan pi_SHm (ss_facts pim_ss_s3) (ss_mem pim_ss_s3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pim_run_s3 : pi_tok_run pi_SHm pim_ss_s3 = (pim_st_s3, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
(* at parse_value: ra 0x84d9c, a0 = q, a1 = the kid (xatom 23), the member loop's registers; no obligation *)
Lemma pim_fin_s3 :
  ss_pc (sh_ss pim_st_s3) = A_parse_value /\ sh_obls pim_st_s3 = [] /\ ss_resv (sh_ss pim_st_s3) = None /\
  sh_j pim_st_s3 = 0%nat /\
  pi_regs_are (sh_ss pim_st_s3)
    ([(1%bv, SLit 0x84d9c); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0);
      (10%bv, SOff 8 0); (11%bv, SOff (xatom 23) 0); (20%bv, SOff 20 0)] ++ pi_RL) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pim_wf_s3 : regions_wf pim_rs3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pim_atoms_s3 : ss_atoms_lt 53 (pik_setm (fss_retT 0x84d7c 144 pi_csL pig_rs pic_gf) pim_rs3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pim_ro_sub : forall r, subregion (pim_ro r) r.
Proof.
intros r. unfold subregion, pim_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc.
Qed.
Lemma pim_no_wr : forall E a, ~ in_wrange E pim_rs3 a.
Proof.
intros E a (r & Hin & Hr). unfold pim_rs3 in Hin. apply in_map_iff in Hin as (r0 & <- & _).
unfold pim_ro in Hr. cbn [YP09.r_wlo YP09.r_whi YP09.r_base] in Hr. lia.
Qed.

(* ================= the stop's callee-saved list, restated over the stop's own registers ================= *)
Lemma pim_RL_atoms : forall r e, In (r, e) pi_RL -> forall n, In n (pik_sv_atoms e) ->
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
Lemma pim_RL_restate : forall regs2 xs regs',
  (forall r e, In (r, e) pi_RL -> YK11.getr regs' r = sv_denot (Ereg regs2 (fs_extraT ++ xs)) e) ->
  ew (Ereg regs2 (fs_extraT ++ xs)) 8 = YK11.getr regs' 8%bv ->
  ew (Ereg regs2 (fs_extraT ++ xs)) 20 = YK11.getr regs' 20%bv ->
  Forall (fun r => YK11.getr regs' (fst r) = sv_denot (Ereg regs' fs_extraT) (snd r)) pi_RL.
Proof.
intros regs2 xs regs' HG E8 E20. apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (HG r e Hin). apply pik_sv_denot_agree; [reflexivity|].
intros n Hn. destruct (pim_RL_atoms r e Hin n Hn) as [ -> | [ -> | -> ] ].
- rewrite (ew_Ereg_nat regs' fs_extraT 8 8%bv eq_refl). exact E8.
- rewrite (ew_Ereg_nat regs' fs_extraT 20 20%bv eq_refl). exact E20.
- change 32%nat with (32 + 0)%nat. rewrite !ew_Ereg_extra. reflexivity.
Qed.

(* ================= the step ================= *)
Lemma pi_step_M : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1 a
    (Qc : world tfibsegs -> config -> Prop),
  IM dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ->
  (forall mem' md' regs' chq',
     IV dn kk x rm T lyc Sc Uc W1 mem' md' regs' chq' pc kids keys cap Di Da peak1 a ->
     SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_value regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs PC_memset regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a Qc HIM K.
unfold pi_IM, pi_IK in HIM. cbv zeta in HIM.
destruct HIM as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HSTK & HRS & HBL & HOBJ & HU64 & HCSTR) &
  R1 & R10 & R11 & R12).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R8 & R20 & R3 & R4 & RL).
pose proof HSTK as (HCH & HCHF & Htop & HINc & HWK).
pose proof HBL as (HTXc & HPOc & HBLKc & HPERM & HUc & HDa & HSUM & HLEN & HGL & Hpk).
pose proof HOBJ as (HHDR & HOPEN).
(* ---- the numbers ---- *)
pose proof asan_consts as (C1 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HARU as (HAR & _ & _).
pose proof (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
assert (HSTK2 : ESTACK + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items, STK_RT_INTRIN; cbn [fold_right]; lia).
pose proof (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Hlytop & Hlylo & Hlyhi & _).
pose proof HTX as (_ & (TIN0 & _) & _).
assert (HH : HEAD = 16) by reflexivity.
assert (HE : ESTACK = 4096) by reflexivity.
assert (Hxr : length xr = 13%nat) by (unfold xr; rewrite length_map; reflexivity).
assert (Hn : Z.of_nat (length dn) < cap) by lia.
assert (ES : parse_items_shape.pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. reflexivity. }
assert (HinK : In (kids, 56 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite ES; left; reflexivity).
pose proof (HBLKc _ _ HinK) as KRB. pose proof KRB as (KIN & Kal & Kpos & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids (56 * cap) HAR KRB) as (K1 & K2).
assert (Hreq : req_size (56 * cap + HEAD) = 56 * cap + HEAD) by (apply FSW_grow_holds.grow_req; lia).
assert (Hdk8 : (kids + 56 * Z.of_nat (length dn)) mod 8 = 0) by (clear - Kal; Z.div_mod_to_equations; lia).
(* ---- the call's premises ---- *)
assert (HCS : forall regs', aregs_preserved regsC regs' ->
  Forall (YP09.chunk_ok tfibsegs
    (Ereg regs' (fs_extraT ++ pig_xs pc (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap))
    (mrestrict (w_H W1) memC) ((spZ regs) - 144)) pi_csL).
{ intros regs' HP'.
  destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs'
    (pig_xs pc (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap) pi_RL HRP HP') as (E8 & E20 & E32 & _).
  exact (pi_csL_ok _ _ (spZ regs) xr q v Hxr
    (fun j Hj => pi_pig_xs_saved regs' pc (text + len) (Z.of_nat k + 1) xr kids keys _ cap j Hxr Hj)
    E8 E20 E32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HFL). }
assert (HBLKk : rd_blocks_ok tfibsegs B lyc Sc W1 memC (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap))
  by (intros a0 k0 H0; apply HBLKc; apply in_or_app; left; exact H0).
assert (HAPk : PjStruct.pj_apart (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) v).
{ pose proof HOPEN as (_ & HAP0 & _). intros b0 x0 Hb Hh.
  apply (HAP0 b0 x0); [apply in_or_app; left; exact Hb | exact Hh]. }
assert (HTMP : forall b, In b (rd_hblocks (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)) ->
  ~ In b (ablocks B ly S)).
{ intros b Hb. apply (pi_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM b).
  unfold rd_hblocks in *. apply in_map_iff in Hb as (b0 & <- & Hb0).
  apply (in_map (fun b1 => (fst b1 - HEAD, snd b1 + HEAD))). apply in_or_app. left. exact Hb0. }
(* ---- the call of __asan_memset (kids + 56 n, 0, 56) ---- *)
apply (pic_call_ms_84d78 B HSS MS (1 - k)%nat (spZ regs) ot ly S U W mem md [] lyc Sc Uc W1 memC mdC (rd_ev T) regsC q text len pc
  (Z.of_nat k + 1) tb tcap xr v 0 0 kids keys (Z.of_nat (length dn)) cap (live + PjGrammar.held T) peak1
  (cnt + Z.of_nat (length T)) fail pi_csL Qc HJ HARU HHD R1 Rsp Hsp16 ltac:(lia) R8 R20 R10 R11 R12 R3 R4
  ltac:(lia) ltac:(lia) HINc ltac:(lia) HTXc TIN0 Hxr HPOc HHDR Hn HBLKk HAPk HTMP HGL pi_wf_csL HCS).
intros regs2 mem2 md2 HJ2 HARU2 HP H10' HST HKEEP HZ2 HPK2 HIN2 HHDR2 HPO2 MBq BLK2 HTX2 HG2.
(* ---- the object across the memset ---- *)
assert (HPERM' : Permutation (ablocks B lyc Sc)
  (ablocks B ly S ++ rd_hblocks ((parse_items_shape.pis_slots true kids keys cap ++ Di) ++
     [(a, Z.of_nat (length kk) + 1)])))
  by (rewrite <- app_assoc; exact HPERM).
pose proof (pio_zero B ly S lyc Sc Uc W1 memC mem2 md2 (spZ regsC) v text len tcap (length dn) dn kids keys cap Di a kk
  eq_refl Hn ltac:(rewrite Rsp; lia) HARU2 HPERM' ltac:(rewrite <- app_assoc; exact HBLKc) HTXc HPOc HHDR
  ltac:(rewrite <- app_assoc; exact HOPEN) HU64 ltac:(rewrite <- app_assoc; exact HCSTR) HKEEP) as Z0.
cbv zeta in Z0. rewrite <- app_assoc in Z0.
destruct Z0 as (BL5 & TX5 & PO5 & HDR5 & OP5 & U5 & C5).
(* ---- the resume env, extended by four words: xatom 23 = the kid ---- *)
set (xs := pig_xs pc (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap) in *.
set (ys := [Z_to_bv 64 a; Z_to_bv 64 (Z.of_nat (length kk)); Z_to_bv 64 (keys + 8 * Z.of_nat (length dn));
            Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))]).
assert (Lxs : length xs = 20%nat) by (unfold xs, pig_xs; rewrite !length_app, Hxr; reflexivity).
destruct (pig_xs_nth pc (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap Hxr)
  as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
assert (EXs : forall j, (j < 20)%nat ->
  ew (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (xatom j) = nth j xs (Z_to_bv 64 0)).
{ intros j Hj. rewrite fsw_ew_xatom. apply app_nth1. lia. }
assert (EX23 : ew (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (xatom 23) = Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))).
{ rewrite fsw_ew_xatom, app_nth2 by lia. rewrite Lxs. reflexivity. }
assert (E16 : ew (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (xatom 16) = Z_to_bv 64 kids)
  by (rewrite EXs by lia; exact X16).
assert (E18 : ew (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn)))
  by (rewrite EXs by lia; exact X18).
destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs2 (xs ++ ys) pi_RL HRP HP) as (F8 & F20 & F32 & F2 & F3 & F4).
destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs2 xs pi_RL HRP HP) as (D8 & D20 & D32 & D2 & _ & _).
(* ---- the start state pim_ss_s3 ---- *)
assert (S1 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (pik_setm (fss_retT 0x84d7c 144 pi_csL pig_rs pic_gf) pim_rs3)
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x84d7c) mem2 (seg_rom tfibsegs)))).
{ assert (SUB : submem pim_rs3 (ss_mem (fss_retT 0x84d7c 144 pi_csL (pic_rs cap) pic_gf))).
  { unfold pim_rs3. cbn [ss_mem fss_retT fsT_ret_regions pic_rs pig_rs app map].
    repeat (apply submem_keep; [apply pim_ro_sub|]). apply submem_nil. }
  exact (pik_st_ok_setm _ _ _ pim_rs3 HST SUB pim_wf_s3). }
assert (S2 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ (xs ++ ys)))
  (pik_setm (fss_retT 0x84d7c 144 pi_csL pig_rs pic_gf) pim_rs3)
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x84d7c) mem2 (seg_rom tfibsegs)))).
{ rewrite app_assoc. apply pik_st_ok_extra; [exact S1|].
  replace (32 + length (fs_extraT ++ xs))%nat with 53%nat by (rewrite length_app, Lxs; reflexivity).
  exact pim_atoms_s3. }
assert (Ha0 : YK11.getr regs2 10 = sv_denot (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (SOff (xatom 23) 0))
  by (rewrite fsw_SOff0, EX23, H10'; reflexivity).
pose proof (pi_setr_ok B k S regs q ot v ms Hk HDEP regsC regs2 (xs ++ ys) pi_RL (SOff (xatom 23) 0) HRP HP pi_RL_ok Ha0)
  as FRL.
apply Forall_inv_tail in FRL.
assert (S3 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ (xs ++ ys)))
  (pik_setr (pik_setm (fss_retT 0x84d7c 144 pi_csL pig_rs pic_gf) pim_rs3) pi_RL)
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x84d7c) mem2 (seg_rom tfibsegs))))
  by (apply pik_st_ok_setr; [exact S2 | exact FRL]).
assert (HAT : atoms_ok (Ereg regs2 (fs_extraT ++ (xs ++ ys))) pi_gf_vk).
{ unfold pi_gf_vk. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite EX23, wz by lia. split; [lia|]. split; [exact Hdk8 | lia]. }
assert (HAL : alias_ok (Ereg regs2 (fs_extraT ++ (xs ++ ys))) [pi_al_vk])
  by exact (proj2 (pik_alias_ok_lin _ (xatom 16) (xatom 18) (xatom 23) kids (Z.of_nat (length dn)) E16 E18
    ltac:(lia) ltac:(lia)) ltac:(lia) EX23).
assert (HSm : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ (xs ++ ys))) pim_ss_s3
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x84d7c) mem2 (seg_rom tfibsegs))))
  by exact (pik_st_ok_addf _ _ _ pi_gf_vk [] [pi_al_vk] S3 HAT I HAL).
(* ---- the shadow entries: q and v ---- *)
assert (UB : YP0e.U (Ereg regs2 (fs_extraT ++ (xs ++ ys))) fs_Bx = SHADOW_OFF)
  by (unfold fs_Bx; apply U_atom; [exact F32 | unfold SHADOW_OFF; lia]).
assert (Uq : YP0e.U (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (SOff 8 0) = q) by (apply U_atom; [exact F8 | lia]).
assert (Uv : YP0e.U (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (SOff 20 0) = v) by (apply U_atom; [exact F20 | lia]).
assert (SHOK : sh_ok tfibsegs fs_Bx pi_SHm (Ereg regs2 (fs_extraT ++ (xs ++ ys))) (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, pi_SHm. constructor; [|constructor; [|constructor]].
  - exact (pi_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP lyc Sc Uc W1 mem2 md2
      _ 8 HARU2 Hlylo Hlyhi UB Uq).
  - exact (pi_sh_v B k S regs ot v ms Hk HDEP lyc Sc Uc W1 mem2 md2 _ 20 HARU2 HPO2 UB Uv). }
(* ---- what the memset kept, at the caller's own bytes ---- *)
assert (CH2 : achain lyc (aview tfibsegs (w_H W1) (unpoison Uc mem2)) (spZ regs) q chq).
{ apply (pi_chain_kept lyc lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) _ (spZ regs) q (ly_top ly) chq HCH HCHF Htop Htop).
  intros a0 Ha0' _. apply FSW_pj_parse.pjp_aview_unpoison. apply HKEEP; [lia | lia | rewrite Rsp; lia]. }
assert (WK2 : wkeep tfibsegs W1 W1 memC mem2 (spZ regs) ot q 24).
{ intros a0 Ha0' Hq0'.
  assert (Hav : aview tfibsegs (w_H W1) mem2 a0 = aview tfibsegs (w_H W1) memC a0)
    by (apply HKEEP; [lia | lia | rewrite Rsp; lia]).
  assert (Hraw : mrestrict (w_H W1) mem2 (Z_to_bv 64 a0) = mrestrict (w_H W1) memC (Z_to_bv 64 a0)).
  { apply fsw_restrict_of_aview; [lia | | exact Hav].
    intros Hi. pose proof (fs_segs_img a0 Hi). unfold FS_IMG_END in *. lia. }
  split; [exact (mbyte_of_aview tfibsegs _ _ _ _ a0 Hav)|].
  split; intros Hw; [exact (writable_at_eq tfibsegs _ _ a0 Hraw Hw) | exact (writable_at_eq tfibsegs _ _ a0 (eq_sym Hraw) Hw)]. }
assert (WK : wkeep tfibsegs W W1 mem mem2 (spZ regs) ot q 24)
  by exact (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W1 memC mem2 (spZ regs) HWK WK2 (Z.le_refl _)).
assert (RO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) mem2)).
{ apply (FSW_pj_parse.pjp_arodata_keep B W1 memC mem2); [|exact HRO].
  intros y Hy. pose proof (fs_segs_img y Hy) as Hy'.
  apply HKEEP; [unfold FS_IMG_END in *; lia | | rewrite Rsp; unfold FS_IMG_END in *; lia].
  intros Hd. exact (blk_img tfibsegs B LAWS lyc Sc W1 _ mdC (kids - HEAD) (56 * cap + HEAD) y HAR KIN
    ltac:(rewrite Hreq; lia) Hy). }
assert (HR0 : region_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W1) mem2) (fstk_ret 144 pi_csL)).
{ pose proof (fsw_region_nth _ _ _ 0 (fstk_ret 144 pi_csL) HST eq_refl) as HR. rewrite restrict_mem in HR. exact HR. }
assert (FL2 : pi_frameL (mrestrict (w_H W1) mem2) (spZ regs) xr q v)
  by exact (pi_frameL_of B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTX HPO0
    HDEP HVSP _ _ pi_csL Hxr D2 D8 D20 D32
    (fun j Hj => pi_pig_xs_saved regs2 pc (text + len) (Z.of_nat k + 1) xr kids keys _ cap j Hxr Hj) HR0 (incl_refl _)).
(* ---- the run S3 ---- *)
eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W1 FUEL _ (run_K 0 fs_Bx pi_SHm pim_ss_s3) fs_Bx fs_Bspan pi_SHm
  pim_ss_s3 pim_st_s3 (TS_stopped SR_fetch) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSm SHOK pim_static_s3 pim_run_s3 I
  HARU2 HJ2).
- destruct pim_fin_s3 as (_ & Hob & _). rewrite Hob. constructor.
- intros a0 Ha0'. exfalso. exact (pim_no_wr _ a0 Ha0').
- intros ws ms' mat' Hlen HS' SHOK' HJ' HARU' HFr HFr' HG'.
  destruct pim_fin_s3 as (Hpc & Hob & Hresv & Hj & Hregs).
  rewrite Hj in Hlen. destruct ws as [|w ws]; [clear Hlen | discriminate Hlen].
  cbn [extK] in HS', SHOK'.
  assert (Emem : ms_mem ms' = mem2).
  { apply FunctionalExtensionality.functional_extensionality. intros y. apply HFr. exact (pim_no_wr _ (bv_unsigned y)). }
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W1) _ _ ms' HS' Hresv) as Hms'.
  pose proof (pi_regs_of_stop _ _ ms' (w_H W1) _ HS' Hregs) as RG. rewrite Forall_forall in RG.
  assert (G : forall r e, In (r, e)
    ([(1%bv, SLit 0x84d9c); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0);
      (10%bv, SOff 8 0); (11%bv, SOff (xatom 23) 0); (20%bv, SOff 20 0)] ++ pi_RL) ->
    YK11.getr (ms_regs ms') r = sv_denot (Ereg regs2 (fs_extraT ++ (xs ++ ys))) e)
    by (intros r e Hin; exact (RG (r, e) Hin)).
  pose proof (G 1%bv (SLit 0x84d9c) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G1.
  pose proof (G 2%bv (SOff 2 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G2.
  pose proof (G 3%bv (SOff 3 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G3.
  pose proof (G 4%bv (SOff 4 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G4.
  pose proof (G 8%bv (SOff 8 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G8.
  pose proof (G 10%bv (SOff 8 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G10.
  pose proof (G 11%bv (SOff (xatom 23) 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G11.
  pose proof (G 20%bv (SOff 20 0) ltac:(apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right]))) as G20.
  rewrite fsw_SOff0 in G2, G3, G4, G8, G10, G11, G20.
  rewrite Hms', Emem, Hpc. rewrite Emem in HJ', HARU'.
  apply (K mem2 (with_vm_backing (m_vm_lazy md2) mat' md2) (ms_regs ms') chq).
  unfold pi_IV, pi_IK. cbv zeta.
  split; [|split; [rewrite G1; reflexivity|split; [rewrite G10; exact F8|split; [rewrite G11; exact EX23|
    split; [exact HZ2 | exact HPK2]]]]].
  split; [exact Hms|]. split; [exact Htr|]. split; [exact Hcap|]. split; [exact Hcap54|].
  split; [split; [exact HJ'|]; split; [exact HARU'|]; split; [exact RO2 | exact HHD]|].
  split.
  { split; [unfold spZ; rewrite G2; exact F2|].
    split; [rewrite G8; exact F8|]. split; [rewrite G20; exact F20|].
    split; [rewrite G3; exact F3|]. split; [rewrite G4; exact F4|].
    apply (pim_RL_restate regs2 (xs ++ ys) (ms_regs ms'));
      [intros r e Hin; apply G; apply in_or_app; right; exact Hin | exact (eq_sym G8) | exact (eq_sym G20)]. }
  split; [exact FL2|].
  split; [split; [exact CH2|]; split; [exact HCHF|]; split; [exact Htop|]; split; [exact HIN2 | exact WK]|].
  split; [exact HRS|].
  split.
  { split; [exact TX5|]. split; [exact PO5|]. split; [exact BL5|]. split; [exact HPERM|]. split; [exact HUc|].
    split; [exact HDa|]. split; [exact HSUM|]. split; [exact HLEN|]. split; [exact HG2 | exact Hpk]. }
  split; [split; [exact HDR5 | exact OP5]|].
  split; [exact U5 | exact C5].
Qed.

End X.
