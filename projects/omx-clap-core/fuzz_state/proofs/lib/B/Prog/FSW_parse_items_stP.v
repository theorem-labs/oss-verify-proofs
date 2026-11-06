(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) parse_items' parse_string call step on image B (the key,
   0x85044 -> 0x85048): from the call-site invariant at parse_string (pib_IP) through parse_string_spec to the resume
   interface pib_IE (FSW_parse_items_loop.v) at 0x85048, where the segment 0x85048 .. 0x851d0 starts (its walk is
   FSW_parse_items_val.v). The call half of the A walk's pi_step_P (a working branch 4480a5df1ae
   lib/A/FSW_parse_items_stP.v) with the call step of its pic_call_ps_84c4c (lib/A/FSW_parse_items_calls.v), re-read on
   B: the chain parse_string's fpreU reads is at s0 = q + 16 (FSW_parse_items_mem.pim_chain_q16), its own chain premise
   at q from parse_string's frame (pib_stack's chain, lowered), and the resume is FSW_parse_items_calls.pic_after_callT
   into fss_retT 0x85048 144 pib_csL pib_rs pib_gfP under pib_xsK.
   rule 24: proves no function (kind: call-step lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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
FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_calls FSW_parse_items_kit FSW_parse_items_mdl FSW_parse_items_seg
FSW_parse_items_loop FSW_parse_items_mem FSW_parse_items_sw FSW_parse_items_obj FSW_parse_items_lh
FSW_parse_items_sws FSW_parse_items_grow FSW_parse_items_stG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.


(* the resume env's extra words with the key (pib_xsK), by index *)
Lemma pib_xsK_nth : forall p0 e d xr0 k' y' n cap' a kl, length xr0 = 13%nat ->
  let xs := pib_xsK p0 e d xr0 k' y' n cap' a kl in
  nth 0 xs (Z_to_bv 64 0) = Z_to_bv 64 p0 /\ nth 1 xs (Z_to_bv 64 0) = Z_to_bv 64 e /\
  nth 2 xs (Z_to_bv 64 0) = Z_to_bv 64 d /\
  (forall j, (j < 13)%nat -> nth (3 + j) xs (Z_to_bv 64 0) = nth j xr0 (Z_to_bv 64 0)) /\
  nth 16 xs (Z_to_bv 64 0) = Z_to_bv 64 k' /\ nth 17 xs (Z_to_bv 64 0) = Z_to_bv 64 y' /\
  nth 18 xs (Z_to_bv 64 0) = Z_to_bv 64 n /\ nth 19 xs (Z_to_bv 64 0) = Z_to_bv 64 cap' /\
  nth 20 xs (Z_to_bv 64 0) = Z_to_bv 64 a /\ nth 21 xs (Z_to_bv 64 0) = Z_to_bv 64 kl.
Proof.
intros p0 e d xr0 k' y' n cap' a kl Hl xs. subst xs. unfold pib_xsK.
assert (L20 : length (pib_xs p0 e d xr0 k' y' n cap') = 20%nat) by (unfold pib_xs; rewrite !length_app, Hl; reflexivity).
destruct (pib_xs_nth p0 e d xr0 k' y' n cap' Hl) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
split; [rewrite app_nth1 by lia; exact X0|]. split; [rewrite app_nth1 by lia; exact X1|].
split; [rewrite app_nth1 by lia; exact X2|].
split; [intros j Hj; rewrite app_nth1 by lia; exact (pib_xs_saved_nth p0 e d xr0 k' y' n cap' j Hl Hj)|].
split; [rewrite app_nth1 by lia; exact X16|]. split; [rewrite app_nth1 by lia; exact X17|].
split; [rewrite app_nth1 by lia; exact X18|]. split; [rewrite app_nth1 by lia; exact X19|].
rewrite !app_nth2 by lia. rewrite L20. split; reflexivity.
Qed.

Local Ltac pps_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; unfold acallee_saved; lia.
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved_regs.
#[local] Abbreviation JC := (pib_jc B k ly S U W regs mem md ot v).
#[local] Abbreviation RP := (pib_regsP B regs q v).
#[local] Abbreviation STKP := (pib_stack k ly W regs mem q ot text len tb).
#[local] Abbreviation BLK := (pib_blocks B ly S U v text len tcap live peak cnt fail).
#[local] Abbreviation OBJ := (pib_obj v).
#[local] Abbreviation IG := (pib_IG B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IP := (pib_IP B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).

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
(* callee: parse_string (a Theorem Labs lane's B walk) *)
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.
#[local] Abbreviation IE := (pib_IE B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).

Lemma P_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof. exact (pil_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP). Qed.
Lemma P_qs : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof. exact (pil_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP). Qed.
Lemma P_vrng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof. exact (pil_v_rng B k ly S U W regs mem md v ch HPRE HPO0). Qed.
Lemma P_v8 : v mod 8 = 0.
Proof. destruct HPO0 as [[(_ & Hm & _)|(_ & Hm & _)] _]. exact Hm. exact Hm. Qed.
Lemma P_text : 4096 + HEAD <= text /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP ly S W (unpoison U mem) md mem p dd HAR HTX HIN0)
  as (H1 & _ & H3 & H4 & H5). lia.
Qed.
Lemma P_q46 : 2 ^ 46 <= q.
Proof. pose proof P_qs as (_ & _ & _ & Hqc & _). pose proof asan_consts as (C1 & _). lia. Qed.

(* the atom facts pib_gfP under the resume env after parse_string *)
Lemma P_atoms : forall regs' p' kids keys n cap a kl, YK11.getr regs' 9 = w64 q -> YK11.getr regs' 19 = w64 v ->
  4096 <= p' <= 2 ^ 47 - 2 ^ 23 -> 4096 <= kids <= 2 ^ 47 - 2 ^ 23 -> kids mod 16 = 0 ->
  4096 <= keys <= 2 ^ 47 - 2 ^ 23 -> keys mod 16 = 0 -> 0 <= n <= 2 ^ 54 -> 0 <= cap <= 2 ^ 54 ->
  4096 <= a <= 2 ^ 47 - 2 ^ 23 -> 0 <= kl <= 2 ^ 54 ->
  atoms_ok (Ereg regs' (fs_extraT ++ pib_xsK p' (text + len) (dd + 1) xr kids keys n cap a kl)) pib_gfP.
Proof.
intros regs' p' kids keys n cap a kl G9 G19 Hp Hk1 Hk2 Hy1 Hy2 Hn Hc Ha Hkl.
pose proof P_qs as (_ & _ & Hq8 & Hqc & Hq47). pose proof P_q46 as Hq46. pose proof P_vrng as (Hv1 & Hv2).
pose proof P_v8 as Hv8. pose proof P_text as (Ht1 & Ht2 & Ht3 & Ht4). unfold HEAD in Ht1.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & Hpb & _).
destruct (pib_xsK_nth p' (text + len) (dd + 1) xr kids keys n cap a kl (pil_xr_len regs))
  as (X0 & X1 & X2 & _ & X16 & X17 & X18 & X19 & X20 & X21).
set (xs := pib_xsK p' (text + len) (dd + 1) xr kids keys n cap a kl) in *.
assert (XA : forall j, ew (Ereg regs' (fs_extraT ++ xs)) (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; apply fsw_ew_xatom).
assert (E9 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 9) = q)
  by (rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), G9; unfold w64; apply unsigned_lit_small; lia).
assert (E19 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 19) = v)
  by (rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19; unfold w64; apply unsigned_lit_small; lia).
unfold pib_gfP, pib_gf. cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E19, !XA, X0, X1, X2, X16, X17, X18, X19, X20, X21.
unfold dd.
rewrite (unsigned_lit_small p'), (unsigned_lit_small (text + len)), (unsigned_lit_small (Z.of_nat k + 1)),
  (unsigned_lit_small kids), (unsigned_lit_small keys), (unsigned_lit_small n), (unsigned_lit_small cap),
  (unsigned_lit_small a), (unsigned_lit_small kl) by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
repeat split; try lia; try apply Z.mod_1_r; try exact Hq8; try exact Hv8; try exact Hk2; try exact Hy2.
Qed.

(* ================= (P) the parse_string call: pib_IP -> pib_IE ================= *)
Lemma pi_step_P : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
    (Qc : world tfibsegs -> config -> Prop),
  IP dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  (forall a ly' S' (W' : world tfibsegs) regs' mem' md',
     IE dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_string regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc HIP K.
pose proof HIP as HIP0.
unfold pib_IP in HIP. cbv zeta in HIP.
destruct HIP as (Hms & Htr & Hicap & Hcap54 & HJC & R1 & R10 & HRP & HFR & HSTK & HRST & HBL & HOBJ).
set (i := length dn) in *.
set (L := parse_items_shape.pis_slots true kids keys cap ++ Di) in *.
set (Qk := Z.of_nat (length kk)).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof P_sp0 as (Hal16 & Hsp1 & Hsp2).
pose proof P_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof P_vrng as (Hv1 & Hv2). pose proof P_v8 as Hv8.
pose proof P_text as (Gt1 & Gt2 & Gt3 & Gt4).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof (pil_mem_facts k S regs ot ms Hk HDV HDS HWF HDEP dn kk x rm Hms) as (Hplain & _).
pose proof HJC as (HJ & HARU & HRO & HHD). pose proof HARU as (HAR & OKc & POc).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev1 & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16o & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
assert (R8 : YK11.getr regsC 8 = w64 (q + 16)).
{ rewrite Forall_forall in RL. pose proof (RL (8%bv, SOff 9 16) ltac:(cbn; tauto)) as R8'. cbn [fst snd] in R8'.
  rewrite R8'. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regsC _ 9 9%bv eq_refl), R9.
  unfold w64. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
pose proof HSTK as (HCH & HCHF & HTOP & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HBK1 & HPERM1 & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOBJ as (HHDR1 & HOPEN1).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Ht0 & (Hpc1 & Hpc2) & Hte & _ & Htblen & _ & Hd).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc
  (dd + 1) HAR HTX1 HIN) as (Htx1 & _ & Htx3 & Htx4 & Hac47).
unfold HEAD in Htx1.
assert (Hcap0 : 0 < cap) by lia.
(* ---- the kids / keys blocks ---- *)
destruct (pil_slots_of B k ly S U regs ot v text len tcap ms live peak cnt fail Hk HDEP lyc Sc Uc W1 memC mdC Da T peak1
  (Z.of_nat i) kids keys cap dn Di HARU HBL HOBJ ltac:(lia)) as (_ & HBKd & HAPd & _ & HNEd & _).
assert (ED : ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. reflexivity. }
pose proof HBKd as HBKd'. rewrite ED in HBKd'.
pose proof (HBKd' kids (56 * cap) (or_introl eq_refl)) as HRBK1.
pose proof (HBKd' keys (8 * cap) (or_intror (or_introl eq_refl))) as HRBY1.
pose proof HRBK1 as (HinK1 & HK16 & _ & _). pose proof HRBY1 as (HinY1 & HY16 & _ & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids (56 * cap) HAR HRBK1) as (HKlo & HKhi).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys (8 * cap) HAR HRBY1) as (HYlo & HYhi).
unfold HEAD in HKlo, HYlo.
(* ---- the text: the key's run ---- *)
rewrite (pim_spieces_plain kk Hplain), (pim_wsep pr) in HRST.
match type of HRST with _ = _ ++ _ ++ ?R => set (R0 := R) in HRST end.
set (wsp := if pr then [32] else []) in HRST.
assert (HRlen : Z.of_nat (length (ReaderRes.rest_at tb text pc)) = text + len - pc).
{ unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn. lia. }
assert (HR1 : ReaderRes.rest_at tb text pc = 34 :: kk ++ 34 :: 58 :: wsp ++ R0).
{ rewrite HRST. cbn [app]. rewrite <- app_assoc. reflexivity. }
destruct (pim_key_run tb text len pc kk (58 :: wsp ++ R0) Hpc1 HRlen HR1 Hplain) as (Hrun & Hrunat & Hq34 & Hpclt).
(* ---- the trace and the budget of parse_string's one allocation ---- *)
assert (Hech : length (flat_map PjRoundTrip.ech kk) = length kk) by (rewrite (pim_ech_plain kk Hplain); reflexivity).
assert (HTR2 : PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))] ++
  (PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S i) (Z.to_nat cap) rm)).
{ rewrite Htr, Hech. reflexivity. }
destruct (pil_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc _ T _ _ HTR2 Hnev1 HPERM1
  HSUM HLEN) as (HQ1 & HLV1 & HEV1 & HBB1 & HSZ1).
unfold rd_live in HLV1, HBB1. cbn [fold_right PjGrammar.esize] in HLV1, HBB1.
rewrite pim_rd_ev_alloc in HEV1.
unfold rd_sizes_ok in HSZ1. apply Forall_inv in HSZ1. cbn [PjGrammar.esize] in HSZ1.
(* ---- parse_string's fpreU: the chain at s0 = q + 16 ---- *)
assert (HSTK2 : STK_parse_string + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
assert (HSTK0 : 0 <= STK_parse_string) by (unfold STK_parse_string, zmaxl, FRAME_parse_string; cbn [fold_right]; lia).
assert (HCH16 : exists ch1, achain lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) (spZ regsC) (s0Z regsC) ch1).
{ assert (Es0 : s0Z regsC = q + 16) by (unfold s0Z; rewrite R8; unfold w64; apply wz; lia). rewrite Es0.
  destruct (pis_in_vals _ q text len pc (dd + 1) tb HIN) as (Vp & Ve).
  apply (pim_chain_q16 lyc _ (spZ regsC) q (text + len) pc).
  - rewrite (pim_rdword_U B lyc Sc Uc W1 memC mdC (q + 8) HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W1) memC (q + 8) (text + len) ltac:(lia) Ve).
  - rewrite (pim_rdword_U B lyc Sc Uc W1 memC mdC q HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W1) memC q pc ltac:(lia) Vp).
  - lia.
  - lia.
  - exact Hq8.
  - rewrite Rsp. lia. }
destruct HCH16 as [ch1 HCH16].
assert (Hmod : (spZ regsC - ot) mod 16 = 0).
{ rewrite Rsp. change (spZ regs) with sp0. clear - Hal16 Hal16o. Z.div_mod_to_equations. lia. }
assert (PRE : fpreU tfibsegs B STK_parse_string lyc Sc Uc W1 regsC memC mdC ch1).
{ apply (fsw_fpreU_atFP B STKt ot FP ly S Uc W (unpoison U mem) md [] lyc Sc W1 memC mdC (rd_ev T) regsC STK_parse_string
    (spZ regsC - ot) ch1 HJ HARU HRO).
  - lia.
  - exact Hmod.
  - rewrite Rsp. lia.
  - exact HSTK0.
  - rewrite Rsp. unfold STKt. lia.
  - rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - exact HCH16. }
assert (HWIN1 : rd_win tfibsegs regsC lyc W1 memC q ot).
{ unfold rd_win. rewrite Rsp. split; [lia|]. split; [lia|]. split; [exact Hal16o|]. split; [rewrite Etop; exact Htop|].
  intros a0 Ha0. apply (fsw_apresent_unpoison B lyc Sc Uc W1 memC mdC a0 HARU); [lia|]. apply Hpres. lia. }
(* ---- the call ---- *)
eapply SRr_bind.
{ apply (HPS lyc Sc Uc W1 regsC memC mdC ch1 q ot text len pc (dd + 1) tb tcap Qk (live + PjGrammar.held T) peak1
    (cnt + Z.of_nat (length T)) fail PRE HHD).
  - exists chq. apply (achain_lower _ _ sp0); [exact HCH | rewrite Rsp; unfold FRAME_parse_string; lia].
  - rewrite Rsp. lia.
  - exact R10.
  - exact HIN.
  - exact HWIN1.
  - exact HTX1.
  - exact Hpclt.
  - exact Hq34.
  - exact Hrun.
  - exact HG1.
  - exact HQ1.
  - unfold MALLOC_MAX, HEAD in *. unfold Qk. lia.
  - unfold Qk, HEAD in *. lia.
  - exact HEV1.
  - unfold Qk, HEAD in *. lia. }
intros W' c' _ (a & ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP &
  (A10 & Ha16 & Hab & HRB & HCB & HIN' & HWK' & HTX' & HG')).
set (U' := Uc ++ [(a - HEAD, HEAD)]) in *.
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
pose proof HARU' as (HAR' & _).
destruct (fsw_rblock_low B ly' S' W' (unpoison U' mem') md' mem' a _ HAR' HRB) as (A1 & A2).
unfold HEAD in A1.
(* ---- what parse_string kept: every block / frame byte of the call (its footprint is image bytes) ---- *)
assert (NFP : forall y, ~ in_img tfibsegs y -> ~ inFP FS_PSTAT_FP y) by (intros y Hy Hf; exact (Hy (pim_pstat_img y Hf))).
assert (KB : forall y, ((exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= y < p0 + req_size n0) \/
      (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= y < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
   rdW W' mem' (Z_to_bv 64 y) = rdW W1 memC (Z_to_bv 64 y)).
{ intros y Hy. refine (proj2 (fsw_journal_kept_byte B _ _ _ lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' _ y HJc HARU OK' PO' Hy _)).
  apply NFP. destruct Hy as [(p0 & n0 & Hin & Hr0)|(cid & pos & Hin & Hr0)].
  - exact (blk_img tfibsegs B LAWS lyc Sc W1 (unpoison Uc memC) mdC p0 n0 y HAR Hin Hr0).
  - exact (frm_img tfibsegs B LAWS lyc Sc W1 (unpoison Uc memC) mdC cid pos y HAR Hin Hr0). }
assert (VB : forall y, v <= y < v + 56 -> rdW W' mem' (Z_to_bv 64 y) = rdW W1 memC (Z_to_bv 64 y)).
{ intros y Hy. apply KB.
  destruct HPO1 as [[((cid & pos & Hin & Hcid & H8 & X1' & X2') & _)|((b & m & Hb & X1' & X2') & _)] _].
  - right. exists cid, pos. split; [exact Hin | lia].
  - left. exists b, m. split; [exact Hb | unfold HEAD in X1'; lia]. }
assert (VBm : forall y, v <= y < v + 56 -> mbyte tfibsegs (rdW W' mem') y = mbyte tfibsegs (rdW W1 memC) y)
  by (intros y Hy; unfold mbyte; rewrite (VB y Hy); reflexivity).
assert (HHDR' : PjStruct.pj_hdr tfibsegs (rdW W' mem') v 6 0 0 kids keys (Z.of_nat i) cap)
  by exact (parse_items_shape.pis_hdr_frame tfibsegs _ _ v 6 0 0 kids keys (Z.of_nat i) cap HHDR1
    (fun y Hy => pio_same_raw _ _ y (VB y Hy))).
assert (VW' : forall j, 0 <= j < 56 -> writable_at tfibsegs (rdW W' mem') (v + j))
  by (intros j Hj; apply (proj1 (pim_wr_keep (rdW W1 memC) (rdW W' mem') (v + j) (VB (v + j) ltac:(lia))));
      exact (proj2 HPO1 j Hj)).
assert (BLK' : rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)).
{ apply (rd_blocks_ok_kept_call B _ _ _ lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' _ _ HJc HARU OK' PO'); [|exact HBKd].
  intros a0 k0 y Hak Hy. apply NFP. pose proof (HBKd a0 k0 Hak) as (Hin & _ & Hk0 & _).
  apply (blk_img tfibsegs B LAWS lyc Sc W1 (unpoison Uc memC) mdC _ _ y HAR Hin).
  rewrite pio_req_hb by lia. unfold HEAD in *. lia. }
assert (KBm : forall y, kids <= y < kids + 56 * cap \/ keys <= y < keys + 8 * cap ->
   mbyte tfibsegs (rdW W' mem') y = mbyte tfibsegs (rdW W1 memC) y).
{ intros y Hy. unfold mbyte. rewrite KB; [reflexivity|]. left.
  destruct Hy as [Hy|Hy]; [exists (kids - HEAD), (56 * cap + HEAD) | exists (keys - HEAD), (8 * cap + HEAD)].
  - split; [exact HinK1 | rewrite pio_req_hb by lia; unfold HEAD; lia].
  - split; [exact HinY1 | rewrite pio_req_hb by lia; unfold HEAD; lia]. }
(* ---- the resume env ---- *)
set (P' := pc + Qk + 2) in *.
set (xs := pib_xsK P' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a Qk).
set (E := Ereg regs' (fs_extraT ++ xs)).
destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
fold E in E9, E19, E32, E2, E3, E4.
assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (G9 : YK11.getr regs' 9 = w64 q)
  by (rewrite (pil_kept regsC regs' 9%bv HP ltac:(pps_acs)); exact R9).
assert (G19 : YK11.getr regs' 19 = w64 v)
  by (rewrite (pil_kept regsC regs' 19%bv HP ltac:(pps_acs)); exact R19).
destruct (pib_xsK_nth P' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a Qk (pil_xr_len regs))
  as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21).
assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN') as (_ & _ & _ & HPp & _).
(* ---- the resume ---- *)
assert (HFR' : pib_frameL (rdW W' mem') sp0 xr q v).
{ apply (pis_frameL_mb (rdW W1 memC)); [|exact HFR].
  intros y Hy. rewrite Rsp in HWK'. exact (proj1 (HWK' y ltac:(lia) ltac:(lia))). }
assert (HCS : Forall (YP09.chunk_ok tfibsegs E (rdW W' mem') (sp0 - 144)) pib_csL)
  by (apply (pil_csL_ok E _ sp0 xr q v (pil_xr_len regs)); [intros j Hj; rewrite EXn; exact (XR j Hj)
      | exact E19 | exact E32 | lia | lia | exact HFR']).
assert (HRS : Forall (region_ok tfibsegs E (rdW W' mem')) pib_rs).
{ constructor; [|constructor; [|constructor]].
  - apply (pis_q_ok E _ q text len P' (dd + 1) tb E9u);
      [rewrite EXn; exact X0 | rewrite EXn; exact X1 | rewrite EXn; exact X2 | exact HIN'].
  - pose proof HHDR' as (_ & Hty' & _ & _ & Hkids' & Hkeys' & Hn' & Hcap').
    unfold pib_vR, pib_vch. apply (fsw_pj_part_okW tfibsegs _ _ 19 v v 0 56 0 56);
      [lia | lia | exact VW' | exact E19u | lia | lia | right; lia |].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    + apply (fsw_pj_chunk4 tfibsegs _ _ v 0 (SLit 6) 6); [rewrite Z.add_0_r; exact Hty' | reflexivity].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff (xatom 16) 0) kids); [exact Hkids' | rewrite fsw_SOff0, EXn; exact X16].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff (xatom 17) 0) keys); [exact Hkeys' | rewrite fsw_SOff0, EXn; exact X17].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SOff (xatom 18) 0) (Z.of_nat i)); [exact Hn' | rewrite fsw_SOff0, EXn; exact X18].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 48 (SOff (xatom 19) 0) cap); [exact Hcap' | rewrite fsw_SOff0, EXn; exact X19]. }
pose proof (fsw_pobj_off_img B lyc Sc W1 (unpoison Uc memC) mdC memC v HAR HPO1) as Hvimg.
assert (HPD : pairwise_disjoint E (fsT_ret_regions 144 pib_csL pib_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, E9u, E19u.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (HGF : atoms_ok E pib_gfP).
{ apply (P_atoms regs' P' kids keys (Z.of_nat i) cap a Qk G9 G19); unfold MALLOC_MAX, HEAD, Qk in *; lia. }
assert (HFPS : fsw_fp_sub B ly S lyc Sc [] FP FS_PSTAT_FP).
{ intros a0 Ha0. right; right; left. split; [unfold FP; apply inFP_app; right; exact Ha0 | exact (pim_pstat_img a0 Ha0)]. }
destruct (pic_after_callT B STKt ot FP [] ly S U W1 mem md W lyc Sc Uc memC mdC (rd_ev T) STK_parse_string FS_PSTAT_FP sp0
  144 regsC ly' S' U' W' regs' mem' md' EV_fuzz_malloc xs pib_csL pib_rs pib_gfP 0x85048 (proj1 HSS) (proj2 HSS) HJ HARU
  HJc HFPS OK' PO' HP Rsp ltac:(lia) HSTK0 ltac:(rewrite Rsp; change (spZ regs) with sp0; clear - Hal16; Z.div_mod_to_equations; lia)
  ltac:(lia) ltac:(rewrite Rsp; unfold STKt; lia) ltac:(vm_compute; reflexivity) HCS HRS HPD HGF) as (HJ2 & HARU2 & HST).
rewrite R1. change (w64 0x85048) with (Z_to_bv 64 0x85048).
apply (K a ly' S' W' regs' mem' md').
unfold pib_IE. cbv zeta. fold Qk i P' xs U'.
split; [exact HIP0|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HARU2|]. split; [exact HP|].
split; [exact A10|]. split; [exact HST|]. split; [unfold HEAD; lia|]. split; [exact Hab|]. split; [exact HRB|].
split; [exact HCB|]. split; [exact HIN'|]. split; [exact HWK'|]. split; [exact HTX'|]. split; [exact HG'|].
split; [exact HHDR'|]. split; [exact VBm|]. split; [exact BLK' | exact KBm].
Qed.
End P.
