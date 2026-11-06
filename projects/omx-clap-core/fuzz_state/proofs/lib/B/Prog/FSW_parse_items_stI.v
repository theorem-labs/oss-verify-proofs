(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the end of a member in parse_items' loop on image B: from the
   call-site state at skip_ws #4 (pib_IW4, FSW_parse_items_stH.v) through skip_ws #4 (FSW_parse_items_sws.pis_loop_sw)
   and the segment at 0x851f4, two arms on the byte after the white space:
     pi_step_Ic : `,` - segment Ic (FSW_parse_items_seg.pib_run_Ic: in->p + 1 at 0x85244, stop at grow, ra 0x85250)
                  -> the call-site invariant at grow for the next member (pib_IG);
     pi_step_Ie : `}` - segment Ie (pib_run_Ie: in->p + 1, in->depth - 1, the epilogue, the ret 0x852fc) and
                  FSW_ret.fsw_retU -> parse_items_spec k's post (pib_Q) for the object of all members
                  (FSW_parse_items_obj.pio_close).
   The B form of the post-run halves of the A walk's pi_step_Vc / pi_step_Ve (a working branch
   4480a5df1ae lib/A/FSW_parse_items_stVc.v, stVe.v); pib_expect / pib_cs_eq / pib_expect_saved copy its pve_expect /
   pve_cs_eq / pve_expect_saved over B's saved registers.
   rule 24: proves no function (kind: step lemmas). *)
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
FSW_parse_items_sws FSW_parse_items_grow FSW_parse_items_stG FSW_parse_items_stP FSW_parse_items_stH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.


(* ================= segments Ic / Ie: their stops (measured; vm_compute) ================= *)
Definition pib_RIc : list (bv 5 * sv) :=
  [(1%bv, SLit 0x85250); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (9%bv, SOff 9 0); (10%bv, SOff 19 0);
   (19%bv, SOff 19 0)] ++ pib_RL.
Definition pib_qIc : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))].
Definition pib_qIe : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 24 0 24
    [YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) (-1))); YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1));
     YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))].
Definition pib_vRO : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch.
Lemma pib_fin_Ic :
  ss_pc (sh_ss pib_st_Ic) = A_grow /\ sh_obls pib_st_Ic = [] /\ ss_resv (sh_ss pib_st_Ic) = None /\
  pib_regs_are (sh_ss pib_st_Ic) pib_RIc = true /\
  nth_error (ss_mem (sh_ss pib_st_Ic)) 1 = Some (YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL) /\
  nth_error (ss_mem (sh_ss pib_st_Ic)) 4 = Some pib_qIc /\
  nth_error (ss_mem (sh_ss pib_st_Ic)) 5 = Some pib_vRO.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the callee-saved registers at the ret: sp = the entry sp, gp, tp, s0 .. s11 = xatom 4 .. 15 *)
Definition pib_expect (r : bv 5) : sv :=
  if Z.eqb (bv_unsigned r) 2 then SOff 2 144
  else if Z.eqb (bv_unsigned r) 3 then SOff 3 0
  else if Z.eqb (bv_unsigned r) 4 then SOff 4 0
  else if Z.eqb (bv_unsigned r) 8 then SOff (xatom 4) 0
  else if Z.eqb (bv_unsigned r) 9 then SOff (xatom 5) 0
  else SOff (xatom (Z.to_nat (bv_unsigned r) - 12)) 0.
Definition pib_RIe : list (bv 5 * sv) := [(10%bv, SLit 0); (1%bv, SOff (xatom 3) 0)].
Lemma pib_fin_Ie :
  ss_pc (sh_ss pib_st_Ie) = 0x852fc /\ sh_obls pib_st_Ie = [] /\ ss_resv (sh_ss pib_st_Ie) = None /\
  pib_regs_are (sh_ss pib_st_Ie) pib_RIe = true /\
  forallb (fun r => sv_eqb (sr_get (ss_regs (sh_ss pib_st_Ie)) r) (pib_expect r)) CALLEE_SAVED = true /\
  nth_error (ss_mem (sh_ss pib_st_Ie)) 4 = Some pib_qIe /\
  nth_error (ss_mem (sh_ss pib_st_Ie)) 5 = Some pib_vRO.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pib_K_Ic : (xatom 22 <= run_K 0 fs_Bx pib_SHc pib_ss_Ic)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma pib_K_Ie : (xatom 22 <= run_K 0 fs_Bx pib_SHc pib_ss_Ie)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma pib_cs_eq : CALLEE_SAVED = [2; 3; 4]%bv ++ map (fun j => nth j pi_saved_regs 0%bv) (seq 1 12).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_expect_saved : forall j, (1 <= j < 13)%nat ->
  pib_expect (nth j pi_saved_regs 0%bv) = SOff (xatom (3 + j)) 0.
Proof. intros j Hj. do 13 (destruct j as [|j]; [try lia; vm_compute; reflexivity|]). lia. Qed.
(* segments Ic / Ie write struct pj_in only *)
Lemma pib_wr_Ic : forall E qq a, bv_unsigned (ew E 9) = qq -> in_wrange E (ss_mem pib_ss_Ic) a -> qq <= a < qq + 24.
Proof.
intros E qq a E9 (rg & Hin & Ha).
unfold pib_ss_Ic, pib_start, pik_addf, pik_addr, pik_setr, pik_setm, pib_rgs, pib_RO in Hin. cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val fst snd] in Ha;
  rewrite ?E9 in Ha; lia.
Qed.
Lemma pib_wr_Ie : forall E qq a, bv_unsigned (ew E 9) = qq -> in_wrange E (ss_mem pib_ss_Ie) a -> qq <= a < qq + 24.
Proof.
intros E qq a E9 (rg & Hin & Ha).
unfold pib_ss_Ie, pib_start, pik_addf, pik_addr, pik_setr, pik_setm, pib_rgs, pib_RO in Hin. cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val fst snd] in Ha;
  rewrite ?E9 in Ha; lia.
Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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
(* callee: skip_ws (a Theorem Labs lane's B walk) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.
#[local] Abbreviation IW4 := (pib_IW4 B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation Q := (pib_Q B k ly S U W regs mem md q ot v text len p tcap tb ms pr live peak cnt fail).

(* ---- the entry's facts these steps read (FSW_parse_items_lh.v) ---- *)
Lemma I_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof. exact (pil_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP). Qed.
Lemma I_stk144 : 144 <= STK_parse_items (1 - k).
Proof. exact (pil_stk144 k S regs ot ms Hk HDEP). Qed.
Lemma I_qs : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof. exact (pil_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP). Qed.
Lemma I_vrng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof. exact (pil_v_rng B k ly S U W regs mem md v ch HPRE HPO0). Qed.
Lemma I_text : 4096 + HEAD <= text /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP ly S W (unpoison U mem) md mem p dd HAR HTX HIN0)
  as (H1 & _ & H3 & H4 & H5). lia.
Qed.

(* the registers at the grow stop of segment Ic, as pib_IG states them *)
Lemma I_regsP_stopIc : forall E' (regs2 : bvmap 5 word),
  Forall (fun r => YK11.getr regs2 (fst r) = sv_denot E' (snd r)) pib_RIc ->
  ew E' 9 = Z_to_bv 64 q -> ew E' 19 = Z_to_bv 64 v -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E' 2) = sp0 - 144 -> ew E' 3 = Z_to_bv 64 (as_gp B) -> ew E' 4 = Z_to_bv 64 (as_tp B) ->
  ed E' = (fun _ => []) ->
  RP regs2 pib_RL /\ YK11.getr regs2 1 = w64 0x85250 /\ YK11.getr regs2 10 = w64 v.
Proof.
intros E' regs2 HR E9 E19 E32 E2 E3 E4 Hed. rewrite Forall_forall in HR.
assert (G : forall r e, In (r, e) pib_RIc -> YK11.getr regs2 r = sv_denot E' e) by (intros r e H; exact (HR (r, e) H)).
assert (G9 : YK11.getr regs2 9 = Z_to_bv 64 q) by (rewrite (G 9%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9).
assert (G19 : YK11.getr regs2 19 = Z_to_bv 64 v)
  by (rewrite (G 19%bv (SOff 19 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E19).
split; [|split; [rewrite (G 1%bv (SLit 0x85250)) by (cbn; tauto); reflexivity |
  rewrite (G 10%bv (SOff 19 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E19]].
split; [unfold spZ; rewrite (G 2%bv (SOff 2 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E2|].
split; [exact G9|]. split; [exact G19|].
split; [rewrite (G 3%bv (SOff 3 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E3|].
split; [rewrite (G 4%bv (SOff 4 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E4|].
apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (G r e) by (unfold pib_RIc; apply in_or_app; right; exact Hin).
pose proof (pil_RL_ok) as Hok. unfold pil_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
apply pik_sv_denot_agree; [rewrite Hed; reflexivity|].
intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
- rewrite E9, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). symmetry. exact G9.
- rewrite E19, (ew_Ereg_nat regs2 _ 19 19%bv eq_refl). symmetry. exact G19.
- rewrite E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ================= (Ic) `,`: skip_ws #4, segment Ic, to the next member's grow ================= *)
Lemma pi_step_Ic : forall dn kk' x' rm' T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
    (Qc : world tfibsegs -> config -> Prop),
  IW4 dn ((kk', x') :: rm') T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' Di' Da' peak1',
     IG dn kk' x' rm' T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids keys cap Di' Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_grow regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_skip_ws regsC memC mdC) Qc.
Proof.
intros dn kk' x' rm' T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc HIW KIG.
unfold pib_IW4 in HIW. cbv zeta in HIW.
destruct HIW as (Hms & Hi1 & Htr & Hicap & Hcap54 & HJC & R1 & R10 & HRP & HFR & HSTK & HRST & HBL & HOBJ).
set (i := length dn) in *.
set (L := parse_items_shape.pis_slots true kids keys cap ++ Di) in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof I_sp0 as (Hal16 & Hsp1 & Hsp2). pose proof I_stk144 as H144.
pose proof I_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof I_vrng as (Hv1 & Hv2).
pose proof I_text as (Gt1 & Gt2 & Gt3 & Gt4).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HJC as (HJ & HARU & HRO & HHD). pose proof HARU as (HAR & _).
pose proof HBL as (HTXc & HPOc & HBLc & _).
pose proof HSTK as (_ & _ & _ & HIN & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc (dd + 1)
  HAR HTXc HIN) as (Ht0 & Hpc & Htl & Htc & Hac).
unfold HEAD in Ht0.
(* the text at in->p: `,` (no white space before it), then the next member *)
rewrite pim_mgo_cons in HRST. rewrite (proj2 (Nat.eqb_neq i 0) ltac:(lia)) in HRST.
set (more := concat (WriterValue.wind pr (dd + 1)) ++ concat (WriterSpec.spieces kk') ++ WriterValue.wsep pr ++
  concat (WriterValue.wvpieces x' pr (dd + 1)) ++ concat (pi_mgo pr dd (Datatypes.S i) rm') ++ pib_wsb pr dd ++
  [125] ++ rest).
assert (HRw : ReaderRes.rest_at tb text pc = [] ++ 44 :: more) by (rewrite HRST, <- !app_assoc; reflexivity).
(* v's arrays *)
assert (Hcap0 : 0 < cap) by lia.
assert (KIN : In (kids, 56 * cap) L /\ In (keys, 8 * cap) L).
{ unfold L, parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  destruct (Z.eqb_spec cap 0) as [|_]; [lia|].
  split; apply in_or_app; left; [left; reflexivity | right; left; reflexivity]. }
destruct KIN as (KIN & YIN).
pose proof (HBLc _ _ KIN) as KRB. pose proof (HBLc _ _ YIN) as YRB.
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids _ HAR KRB) as (K1 & K2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys _ HAR YRB) as (Y1 & Y2).
pose proof KRB as (_ & Kal & _ & _). pose proof YRB as (_ & Yal & _ & _).
unfold HEAD in K1, Y1.
set (pc0 := pc + Z.of_nat (length (@nil Z))) in *.
assert (Hpc0 : pc0 = pc) by (unfold pc0; cbn [length Z.of_nat]; lia).
destruct (pib_xsK_nth pc0 (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0 (pil_xr_len regs))
  as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21).
(* ---- skip_ws #4 and the resume at 0x851f4 ---- *)
apply (pis_loop_sw B k ly S U W regs mem md q ot v text len p tcap tb ms live peak cnt fail ch Hk HSS HPRE
  HWIN HQ16 HIN0 HVTX HPO0 HDEP HVSP HSW 0x851f4 (pib_xsK pc0 (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0)
  pib_gfP pib_RO (0, 24) pib_RO 44 lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq pc [] more T Da peak1 kids keys cap dn Di
  Qc HJC R1 ltac:(unfold YK0s.ret_ok; vm_compute; reflexivity) ltac:(lia) R10 HRP HFR HSTK HRw (Forall_nil _)
  ltac:(reflexivity) HBL HOBJ ltac:(lia) X0 X1 X2 XR X16 X17 X18 X19).
- intros regs' G9 G19.
  apply (P_atoms B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HTX HIN0 HPO0 HDEP regs'
    pc0 kids keys (Z.of_nat i) cap text 0 G9 G19); lia.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. cbn. lia.
- right. cbn. lia.
- left. cbn. lia.
- intros ly' S' W' regs' mem' md' HJC' HP HRP' HFR' HSTK' HBL' HOBJ' QAB HSS0.
  change (pib_start 0x851f4 pib_csL pib_gfP (pib_rgs pib_csL pib_RO (0, 24) pib_RO) pib_RL [pik_treg (xatom 0) 0 [44]] []
    pib_wsc0 []) with pib_ss_Ic in HSS0.
  set (xs := pib_xsK pc0 (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0) in *.
  set (E := Ereg regs' (fs_extraT ++ xs)) in *.
  destruct HJC' as (HJ2 & HARU2 & HRO2 & HHD2). pose proof HARU2 as (HAR2 & _).
  destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
  fold E in E9, E19, E32, E2, E3, E4.
  assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
  assert (EX0 : ew E (xatom 0) = Z_to_bv 64 pc) by (rewrite EXn, X0, Hpc0; reflexivity).
  assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite EXn; exact X1).
  assert (EX2 : ew E (xatom 2) = Z_to_bv 64 (dd + 1)) by (rewrite EXn; exact X2).
  assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  assert (UX0 : YP0e.U E (SOff (xatom 0) 0) = pc) by (apply U_atom; [exact EX0 | lia]).
  assert (U9 : YP0e.U E (SOff 9 0) = q) by (apply U_atom; [exact E9 | lia]).
  assert (U19 : YP0e.U E (SOff 19 0) = v) by (apply U_atom; [exact E19 | lia]).
  pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
  destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop' & Hslo' & Hshi' & _).
  pose proof HBL' as (HTX' & HPO' & HRB' & HPERM' & HU' & HDa' & HSUM' & HLEN' & HG' & Hpk').
  pose proof HTX' as (Ht4' & HRBt' & Hlt'). pose proof HRBt' as (HinT' & _).
  pose proof HSTK' as (HCH' & HCHF' & HTOP' & HIN' & HWK').
  assert (Epc : pc + Z.of_nat (length (@nil Z)) = pc) by (cbn [length Z.of_nat]; lia).
  rewrite Epc in HIN', HSTK'.
  (* ---- the shadow entries ---- *)
  assert (HSH : sh_ok tfibsegs fs_Bx pib_SHc E (rdW W' mem')).
  { unfold sh_ok, pib_SHc, pib_SHm. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (pil_sh_blk B k S regs ot ms Hk HDEP ly' S' Uc W' mem' md' E (xatom 0) (text - HEAD) (tcap + HEAD) pc 0 1
        HARU2 HHD2 HinT'); [unfold HEAD; lia | lia | unfold HEAD; lia | exact UB | exact UX0].
    - exact (pil_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' Uc W' mem' md'
        E 9 HARU2 ltac:(congruence) ltac:(congruence) UB U9).
    - exact (pil_sh_v B k S regs ot v ms Hk HDEP ly' S' Uc W' mem' md' E 19 HARU2 HPO' UB U19). }
  (* ---- the write windows: struct pj_in ---- *)
  assert (AWR : awr_ok tfibsegs B E (ss_mem pib_ss_Ic) STKt ot FP (ablocks B ly S) (ablocks B ly' S') ly' []
    (frames S))
    by exact (pil_awr_rgs B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E ly' S' W' (unpoison Uc mem') md'
      mem' [pik_treg (xatom 0) 0 [44]] pib_csL pib_RO (0, 24) pib_RO HAR2 HPO' Hfr2 E2 E9u E19u
      ltac:(constructor; [cbn; lia | constructor]) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)).
  (* ---- segment Ic: to grow ---- *)
  destruct pib_fin_Ic as (Fpc & Fob & Fresv & Fregs & Fnth1 & Fnth4 & Fnth5).
  refine (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pib_SHc pib_ss_Ic) fs_Bx fs_Bspan
    pib_SHc pib_ss_Ic pib_st_Ic (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 0x851f4) mem' (seg_rom tfibsegs))
    STKt ot FP ly S W (unpoison U mem) md [] ly' S' Uc md' (rd_ev T) Qc HSS0 HSH pib_static_Ic pib_run_Ic I HARU2 HJ2 _
    AWR _).
  { rewrite Fob. constructor. }
  intros ws2 ms2 mat2 Hlen2 HS2 SHOK2 HJ3 HARU3 HFra HFrr HG2.
  set (K := run_K 0 fs_Bx pib_SHc pib_ss_Ic) in *.
  set (E' := extK E K ws2) in *.
  pose proof pib_K_Ic as HKb. fold K in HKb.
  assert (HK : forall n, (n <= 54)%nat -> ew E' n = ew E n)
    by (intros n Hn; apply (pil_ew_extK k S regs ot ms Hk HDEP); unfold xatom in HKb; lia).
  assert (E'9 : ew E' 9 = Z_to_bv 64 q) by (rewrite HK by lia; exact E9).
  assert (E'19 : ew E' 19 = Z_to_bv 64 v) by (rewrite HK by lia; exact E19).
  assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite HK by lia; exact E32).
  assert (E'2 : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite HK by lia; exact E2).
  assert (E'3 : ew E' 3 = Z_to_bv 64 (as_gp B)) by (rewrite HK by lia; exact E3).
  assert (E'4 : ew E' 4 = Z_to_bv 64 (as_tp B)) by (rewrite HK by lia; exact E4).
  assert (E'9u : bv_unsigned (ew E' 9) = q) by (rewrite E'9; apply unsigned_lit_small; lia).
  assert (Hed : ed E' = (fun _ => [])) by (unfold E'; rewrite pil_ed_extK; reflexivity).
  assert (D9 : forall n0 z c, (n0 <= 54)%nat -> ew E n0 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
    sv_denot E' (SOff n0 c) = Z_to_bv 64 (z + c)).
  { intros n0 z c Hn0 Hz Hz0 Hzc. apply bv_eq. rewrite denot_SOff, HK, Hz by exact Hn0.
    rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
  set (M2 := ms_mem ms2) in *.
  set (md2 := with_vm_backing (m_vm_lazy md') mat2 md') in *.
  (* ---- what the run kept: every byte but struct pj_in ---- *)
  assert (KR : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 24) -> M2 (Z_to_bv 64 z) = mem' (Z_to_bv 64 z)).
  { intros z Hz H1. apply HFra. rewrite wz by lia. intros Hw. pose proof (pib_wr_Ic E q z E9u Hw). lia. }
  assert (KRr : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 24) -> rdW W' M2 (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
    by (intros z Hz H1; unfold mrestrict; rewrite (KR z Hz H1); reflexivity).
  assert (SB : same_below mem' M2 alloc_ceiling) by (intros z Hz; apply KR; lia).
  assert (SBm : forall z, 0 <= z < alloc_ceiling -> rdW W' M2 (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
    by (intros z Hz; unfold mrestrict; rewrite (SB z Hz); reflexivity).
  (* ---- the grow configuration ---- *)
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E' (sh_ss pib_st_Ic) ms2 HS2 Fresv) as Ems2. rewrite Fpc in Ems2.
  rewrite Ems2.
  change (SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_grow (ms_regs ms2) M2 md2) Qc).
  pose proof (pil_regs_of_stop E' (sh_ss pib_st_Ic) ms2 (w_H W') pib_RIc HS2 Fregs) as RG.
  destruct (I_regsP_stopIc E' (ms_regs ms2) RG E'9 E'19 E'32 E'2 E'3 E'4 Hed) as (RP2 & R1' & R10').
  pose proof (fsw_region_nth E' (sh_ss pib_st_Ic) (restrict (w_H W') ms2) 1 _ HS2 Fnth1) as RF. rewrite restrict_mem in RF.
  pose proof (fsw_region_nth E' (sh_ss pib_st_Ic) (restrict (w_H W') ms2) 4 _ HS2 Fnth4) as RQ. rewrite restrict_mem in RQ.
  unfold pib_qIc in RQ.
  (* ---- struct pj_in: in->p past `,` ---- *)
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN') as (Bq0 & Bq24 & Bt0 & (Bp1 & Bp2) & Bte & _ & Btb & _ & Bd).
  assert (Hpc1 : pc + 1 <= text + len).
  { pose proof (pi_rest_len _ q text len pc (dd + 1) tb HIN') as HRL. rewrite HRw in HRL. cbn [length app] in HRL. lia. }
  assert (PIN : PjIn.pj_in_ok tfibsegs (rdW W' M2) q text len (pc + 1) (dd + 1) tb).
  { pose proof HIN' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
    pose proof (fsw_field E' _ 9 q _ 0 24 0 24 0 8 (SOff (xatom 0) 1) (pc + 1) RQ E'9u ltac:(cbn; tauto)
      (D9 (xatom 0) pc 1 ltac:(unfold xatom; lia) EX0 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Q0.
    pose proof (fsw_field E' _ 9 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len + 0) RQ E'9u ltac:(cbn; tauto)
      (D9 (xatom 1) (text + len) 0 ltac:(unfold xatom; lia) EX1 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Q8.
    pose proof (fsw_field E' _ 9 q _ 0 24 0 24 16 4 (SOff (xatom 2) 0) (dd + 1 + 0) RQ E'9u ltac:(cbn; tauto)
      (D9 (xatom 2) (dd + 1) 0 ltac:(unfold xatom; lia) EX2 ltac:(unfold dd; lia) ltac:(unfold dd; lia)) ltac:(cbn; lia)
      ltac:(cbn; lia)) as Q16.
    rewrite Z.add_0_r in Q0, Q8, Q16.
    pose proof RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E'9u in RQW.
    refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
    - apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Q0 | lia | lia | lia].
    - apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Q8 | lia | lia | lia].
    - exact (proj1 (fsw_pj_word4_iff tfibsegs _ (q + 16) (dd + 1) ltac:(lia) ltac:(lia)) Q16).
    - split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
    - lia.
    - destruct I10 as (A0' & A1' & A2'). split; [exact A0'|]. split; [exact A1'|]. intros j Hj.
      pose proof (A2' j Hj) as Hb. pose proof (SBm (text + Z.of_nat j) ltac:(lia)) as Ej.
      unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd,
        OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa in *. rewrite Ej. exact Hb. }
  (* ---- the frame chain and the caller's window ---- *)
  pose proof HPRE as ((HAP0 & _ & _) & _). pose proof HAP0 as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & _ & _ & _ & H47l & _ & Htopl & Htopl2).
  assert (AV : forall z, sp0 <= z < ly_top ly -> ~ (q <= z < q + 24) ->
    aview tfibsegs (w_H W') (unpoison Uc M2) z = aview tfibsegs (w_H W') (unpoison Uc mem') z)
    by (intros z Hz Hq; apply pih_av_unp; apply KRr; lia).
  apply (KIG T ly' S' Uc W' M2 md2 (ms_regs ms2) chq (pc + 1) Di Da peak1).
  unfold pib_IG. cbv zeta. fold i. rewrite (proj2 (Nat.eqb_neq i 0) ltac:(lia)).
  split; [exact Hms|]. split; [exact Htr|]. split; [exact Hicap|]. split; [lia|].
  split.
  { split; [exact HJ3|]. split; [exact HARU3|]. split; [exact (arodata_below B W' mem' M2 SB HRO2)|]. exact HHD2. }
  split; [exact R1'|]. split; [exact R10'|]. split; [exact RP2|].
  split.
  { apply (pil_frameL_of B k ly S U W regs mem md q ot v text tcap ms ch Hk HPRE HVTX HPO0 HDEP HVSP E' _ 0 0 pib_csL
      E'2 E'19 E'32); [| exact RF | apply incl_refl].
    intros j Hj. rewrite HK by (unfold xatom; lia). unfold E.
    exact (pil_xsK_saved regs' pc0 (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0 j (pil_xr_len regs) Hj). }
  split.
  { split.
    { apply (pis_chain_kept ly' ly' _ _ sp0 q (ly_top ly) chq HCH' HCHF' HTOP' HTOP').
      intros z Hz Hq. exact (AV z Hz Hq). }
    split; [exact HCHF'|]. split; [exact HTOP'|]. split; [exact PIN|].
    apply (pil_wkeep_trans k S W regs mem q ot ms Hk HDEP W' W' mem' M2 sp0 HWK'); [|lia].
    intros z Hz Hq. pose proof (KRr z ltac:(lia) Hq) as Ez.
    split; [unfold mbyte; rewrite Ez; reflexivity|].
    split; intros Hw; [exact (writable_at_eq tfibsegs _ _ z Ez Hw) | exact (writable_at_eq tfibsegs _ _ z (eq_sym Ez) Hw)]. }
  split.
  { change (pc + 1) with (pc + Z.of_nat (length [44])).
    rewrite (pim_rest_skip tb text pc [44] more ltac:(lia) HRw). unfold more, pib_wsb. reflexivity. }
  split.
  { split; [split; [exact Ht4'|]; split;
      [exact (fs_rblock_below B ly' S' W' (unpoison Uc mem') md' mem' M2 text tcap HAR2 SB HRBt') | exact Hlt']|].
    split; [exact (pobj_below B ly' S' W' (unpoison Uc mem') md' mem' M2 v HAR2 SB HPO')|].
    split; [exact (rd_blocks_ok_below B ly' S' W' (unpoison Uc mem') md' mem' M2 _ HAR2 SB HRB')|].
    split; [exact HPERM'|]. split; [exact HU'|]. split; [exact HDa'|]. split; [exact HSUM'|]. split; [exact HLEN'|].
    split; [exact (fs_glob_below W' mem' M2 _ _ _ _ SB HG') | exact Hpk']. }
  destruct HOBJ' as (HH' & HOP').
  assert (SV : forall z, 0 <= z < alloc_ceiling -> parse_items_shape.pis_same tfibsegs (rdW W' mem') (rdW W' M2) z)
    by (intros z Hz; apply pio_same_raw; apply SBm; exact Hz).
  assert (HH2 : PjStruct.pj_hdr tfibsegs (rdW W' M2) v 6 0 0 kids keys (Z.of_nat i) cap)
    by exact (parse_items_shape.pis_hdr_frame tfibsegs _ _ v 6 0 0 kids keys (Z.of_nat i) cap HH' (fun z Hz => SV z ltac:(lia))).
  split; [exact HH2|].
  apply (parse_items_shape.pis_frame tfibsegs _ _ _ _ v true 0 kids keys cap (Z.of_nat i) (map snd dn) (map fst dn) Di 0
    (Z.of_nat i) HOP' HH2 ltac:(lia) (fun a0 k0 H => H)).
  intros z Hz. rewrite length_map in Hz.
  destruct (pio_ifoot_in kids keys cap (Z.of_nat i) Di z ltac:(lia) Hz) as ((a0 & k0) & Hin0 & Hh0).
  destruct (fsw_rblock_low B ly' S' W' (unpoison Uc mem') md' mem' a0 k0 HAR2 (HRB' a0 k0 Hin0)) as (L1 & L2).
  unfold PjStruct.pj_holds in Hh0. cbn [fst snd] in Hh0.
  apply SV. unfold HEAD in *. lia.
Qed.
(* ================= (Ie) `}`: skip_ws #4, segment Ie, the ret ================= *)
Lemma pi_step_Ie : forall dn T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
  IW4 dn [] T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_skip_ws regsC memC mdC) Q.
Proof.
intros dn T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HIW.
unfold pib_IW4 in HIW. cbv zeta in HIW.
destruct HIW as (Hms & Hi1 & Htr & Hicap & Hcap54 & HJC & R1 & R10 & HRP & HFR & HSTK & HRST & HBL & HOBJ).
set (i := length dn) in *.
set (L := parse_items_shape.pis_slots true kids keys cap ++ Di) in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof I_sp0 as (Hal16 & Hsp1 & Hsp2). pose proof I_stk144 as H144.
pose proof I_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof I_vrng as (Hv1 & Hv2).
pose proof I_text as (Gt1 & Gt2 & Gt3 & Gt4).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HPRE as ((HAP0 & _ & _) & _). pose proof HAP0 as (HAR0 & Hra0 & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & H47l & _ & Htopl & Htopl2).
pose proof HJC as (HJ & HARU & HRO & HHD). pose proof HARU as (HAR & _).
pose proof HBL as (HTXc & HPOc & HBLc & _).
pose proof HSTK as (_ & _ & _ & HIN & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc (dd + 1)
  HAR HTXc HIN) as (Ht0 & Hpc & Htl & Htc & Hac).
unfold HEAD in Ht0.
(* the text at in->p: the white space of the indent, then `}` *)
assert (HRw : ReaderRes.rest_at tb text pc = pib_wsb pr dd ++ 125 :: rest)
  by (rewrite HRST; reflexivity).
assert (Hws : Forall (fun c0 => PjGrammar.ws c0 = true) (pib_wsb pr dd)) by apply pi_wind_ws.
assert (HRL : Z.of_nat (length (ReaderRes.rest_at tb text pc)) = text + len - pc)
  by exact (pi_rest_len _ q text len pc (dd + 1) tb HIN).
assert (Hwsl : pc + Z.of_nat (length (pib_wsb pr dd)) < text + len)
  by (rewrite HRw, length_app in HRL; cbn [length] in HRL; lia).
(* the trace: all members done *)
assert (ETR : PjRoundTrip.ttrace (PjTree.JObj ms) = T)
  by (rewrite Htr; cbn [PjRoundTrip.tgo_obj]; apply app_nil_r).
(* in->p after `}` is in->p + the object's text *)
assert (EPOS : pc + Z.of_nat (length (pib_wsb pr dd)) + 1 =
  p + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))))).
{ pose proof (pi_rest_len _ q text len p dd tb HIN0) as HRL0. rewrite HREST, length_app in HRL0.
  rewrite HRw, length_app in HRL. cbn [length] in HRL. lia. }
(* v's arrays *)
assert (Hcap0 : 0 < cap) by lia.
assert (KIN : In (kids, 56 * cap) L /\ In (keys, 8 * cap) L).
{ unfold L, parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  destruct (Z.eqb_spec cap 0) as [|_]; [lia|].
  split; apply in_or_app; left; [left; reflexivity | right; left; reflexivity]. }
destruct KIN as (KIN & YIN).
pose proof (HBLc _ _ KIN) as KRB. pose proof (HBLc _ _ YIN) as YRB.
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids _ HAR KRB) as (K1 & K2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys _ HAR YRB) as (Y1 & Y2).
pose proof KRB as (_ & Kal & _ & _). pose proof YRB as (_ & Yal & _ & _).
unfold HEAD in K1, Y1.
destruct (pib_xsK_nth (pc + Z.of_nat (length (pib_wsb pr dd))) (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0
  (pil_xr_len regs)) as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21).
(* ---- skip_ws #4 and the resume at 0x851f4 ---- *)
apply (pis_loop_sw B k ly S U W regs mem md q ot v text len p tcap tb ms live peak cnt fail ch Hk HSS HPRE
  HWIN HQ16 HIN0 HVTX HPO0 HDEP HVSP HSW 0x851f4
  (pib_xsK (pc + Z.of_nat (length (pib_wsb pr dd))) (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0)
  pib_gfP pib_RO (0, 24) pib_RO 125 lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq pc (pib_wsb pr dd) rest T Da peak1 kids
  keys cap dn Di Q HJC R1 ltac:(unfold YK0s.ret_ok; vm_compute; reflexivity) ltac:(lia) R10 HRP HFR HSTK HRw Hws
  ltac:(reflexivity) HBL HOBJ ltac:(lia) X0 X1 X2 XR X16 X17 X18 X19).
- intros regs' G9 G19.
  apply (P_atoms B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HTX HIN0 HPO0 HDEP regs'
    _ kids keys (Z.of_nat i) cap text 0 G9 G19); lia.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. cbn. lia.
- right. cbn. lia.
- left. cbn. lia.
- intros ly' S' W' regs' mem' md' HJC' HP HRP' HFR' HSTK' HBL' HOBJ' QAB HSS0.
  change (pib_start 0x851f4 pib_csL pib_gfP (pib_rgs pib_csL pib_RO (0, 24) pib_RO) pib_RL [pik_treg (xatom 0) 0 [125]] []
    pib_wsc0 []) with pib_ss_Ie in HSS0.
  set (pc' := pc + Z.of_nat (length (pib_wsb pr dd))) in *.
  set (xs := pib_xsK pc' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap text 0) in *.
  set (E := Ereg regs' (fs_extraT ++ xs)) in *.
  destruct HJC' as (HJ2 & HARU2 & HRO2 & HHD2). pose proof HARU2 as (HAR2 & _).
  destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
  fold E in E9, E19, E32, E2, E3, E4.
  assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
  assert (EX0 : ew E (xatom 0) = Z_to_bv 64 pc') by (rewrite EXn; exact X0).
  assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite EXn; exact X1).
  assert (EX2 : ew E (xatom 2) = Z_to_bv 64 (dd + 1)) by (rewrite EXn; exact X2).
  assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  assert (UX0 : YP0e.U E (SOff (xatom 0) 0) = pc') by (apply U_atom; [exact EX0 | lia]).
  assert (U9 : YP0e.U E (SOff 9 0) = q) by (apply U_atom; [exact E9 | lia]).
  assert (U19 : YP0e.U E (SOff 19 0) = v) by (apply U_atom; [exact E19 | lia]).
  pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
  destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop' & Hslo' & Hshi' & _).
  pose proof HBL' as (HTX' & HPO' & HRB' & HPERM' & HU' & HDa' & HSUM' & HLEN' & HG' & Hpk').
  pose proof HTX' as (Ht4' & HRBt' & Hlt'). pose proof HRBt' as (HinT' & _).
  pose proof HSTK' as (HCH' & HCHF' & HTOP' & HIN' & HWK').
  (* ---- the shadow entries ---- *)
  assert (HSH : sh_ok tfibsegs fs_Bx pib_SHc E (rdW W' mem')).
  { unfold sh_ok, pib_SHc, pib_SHm. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (pil_sh_blk B k S regs ot ms Hk HDEP ly' S' Uc W' mem' md' E (xatom 0) (text - HEAD) (tcap + HEAD) pc' 0 1
        HARU2 HHD2 HinT'); [unfold HEAD; lia | lia | unfold HEAD; lia | exact UB | exact UX0].
    - exact (pil_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' Uc W' mem' md'
        E 9 HARU2 ltac:(congruence) ltac:(congruence) UB U9).
    - exact (pil_sh_v B k S regs ot v ms Hk HDEP ly' S' Uc W' mem' md' E 19 HARU2 HPO' UB U19). }
  (* ---- the write windows: struct pj_in ---- *)
  assert (AWR : awr_ok tfibsegs B E (ss_mem pib_ss_Ie) STKt ot FP (ablocks B ly S) (ablocks B ly' S') ly' []
    (frames S))
    by exact (pil_awr_rgs B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E ly' S' W' (unpoison Uc mem') md'
      mem' [pik_treg (xatom 0) 0 [125]] pib_csL pib_RO (0, 24) pib_RO HAR2 HPO' Hfr2 E2 E9u E19u
      ltac:(constructor; [cbn; lia | constructor]) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)).
  (* ---- segment Ie: to the ret ---- *)
  destruct pib_fin_Ie as (Fpc & Fob & Fresv & Fregs & Fcs & Fnth4 & Fnth5).
  refine (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pib_SHc pib_ss_Ie) fs_Bx fs_Bspan
    pib_SHc pib_ss_Ie pib_st_Ie (TS_stopped (SR_jalr (SOff (xatom 3) 0)))
    (mkst regs' (Z_to_bv 64 0x851f4) mem' (seg_rom tfibsegs))
    STKt ot FP ly S W (unpoison U mem) md [] ly' S' Uc md' (rd_ev T) Q HSS0 HSH pib_static_Ie pib_run_Ie I HARU2 HJ2 _
    AWR _).
  { rewrite Fob. constructor. }
  intros ws2 ms2 mat2 Hlen2 HS2 SHOK2 HJ3 HARU3 HFra HFrr HG2.
  set (K := run_K 0 fs_Bx pib_SHc pib_ss_Ie) in *.
  set (E' := extK E K ws2) in *.
  pose proof pib_K_Ie as HKb. fold K in HKb.
  assert (HK : forall n, (n <= 54)%nat -> ew E' n = ew E n)
    by (intros n Hn; apply (pil_ew_extK k S regs ot ms Hk HDEP); unfold xatom in HKb; lia).
  assert (E'2 : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite HK by lia; exact E2).
  assert (E'3 : ew E' 3 = Z_to_bv 64 (as_gp B)) by (rewrite HK by lia; exact E3).
  assert (E'4 : ew E' 4 = Z_to_bv 64 (as_tp B)) by (rewrite HK by lia; exact E4).
  assert (E'9u : bv_unsigned (ew E' 9) = q) by (rewrite HK by lia; exact E9u).
  assert (D9 : forall n0 z c, (n0 <= 54)%nat -> ew E n0 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
    sv_denot E' (SOff n0 c) = Z_to_bv 64 (z + c)).
  { intros n0 z c Hn0 Hz Hz0 Hzc. apply bv_eq. rewrite denot_SOff, HK, Hz by exact Hn0.
    rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
  set (M2 := ms_mem ms2) in *.
  set (md2 := with_vm_backing (m_vm_lazy md') mat2 md') in *.
  (* ---- what the run kept: every byte but struct pj_in ---- *)
  assert (KR : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 24) -> M2 (Z_to_bv 64 z) = mem' (Z_to_bv 64 z)).
  { intros z Hz H1. apply HFra. rewrite wz by lia. intros Hw. pose proof (pib_wr_Ie E q z E9u Hw). lia. }
  assert (KRr : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 24) -> rdW W' M2 (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
    by (intros z Hz H1; unfold mrestrict; rewrite (KR z Hz H1); reflexivity).
  assert (SB : same_below mem' M2 alloc_ceiling) by (intros z Hz; apply KR; lia).
  assert (SBm : forall z, 0 <= z < alloc_ceiling -> rdW W' M2 (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
    by (intros z Hz; unfold mrestrict; rewrite (SB z Hz); reflexivity).
  pose proof (pil_regs_of_stop E' (sh_ss pib_st_Ie) ms2 (w_H W') pib_RIe HS2 Fregs) as RG.
  rewrite Forall_forall in RG.
  assert (G10 : YK11.getr (ms_regs ms2) 10%bv = sv_denot E' (SLit 0)) by exact (RG (10%bv, SLit 0) ltac:(left; reflexivity)).
  assert (G1 : YK11.getr (ms_regs ms2) 1%bv = sv_denot E' (SOff (xatom 3) 0))
    by exact (RG (1%bv, SOff (xatom 3) 0) ltac:(right; left; reflexivity)).
  (* ---- parse_items_spec k's post: D := L, Da ---- *)
  eapply SRr_mono.
  2: { intros W'' c' _ HF. cbv beta delta [pib_Q]. exists L, Da. split; [exact HDa' | exact HF]. }
  refine (fsw_retU B pitems_tbl pitems_tbl_ok W' E' (sh_ss pib_st_Ie) ms2 md2 STKt ot FP regs ly S U W mem md ly' S'
    (U ++ rd_heads Da) (rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms))) _ HS2 Fresv _ _ _ _ _ _).
  + rewrite Fpc. vm_compute. reflexivity.
  + rewrite G1, fsw_SOff0, (HK (xatom 3)) by (unfold xatom; lia).
    change (xatom 3) with (xatom (3 + 0)). rewrite EXn, (XR 0%nat) by lia. exact Hra0.
  + rewrite ETR, <- HU'. exact HJ3.
  + rewrite <- HU'. exact HARU3.
  + apply (fsw_preserved (w_H W') E' (sh_ss pib_st_Ie) ms2 regs pib_expect HS2 Fcs).
    intros r Hr. rewrite pib_cs_eq in Hr. apply in_app_or in Hr as [Hr|Hr].
    * destruct Hr as [<-|[<-|[<-|[]]]].
      -- change (pib_expect 2%bv) with (SOff 2 144). apply bv_eq. rewrite denot_SOff, E'2.
         change sp0 with (spZ regs). unfold spZ. rewrite Z.sub_add. apply zcanon_id.
         pose proof (u64_range (YK11.getr regs 2)). unfold M64. lia.
      -- change (pib_expect 3%bv) with (SOff 3 0). rewrite fsw_SOff0, E'3. symmetry. exact Hgp0.
      -- change (pib_expect 4%bv) with (SOff 4 0). rewrite fsw_SOff0, E'4. symmetry. exact Htp0.
    * apply in_map_iff in Hr as (j & <- & Hj). apply in_seq in Hj.
      rewrite pib_expect_saved by lia. rewrite fsw_SOff0, (HK (xatom (3 + j))) by (unfold xatom; lia).
      rewrite EXn, (XR j) by lia.
      unfold xr. rewrite (nth_indep _ (Z_to_bv 64 0) (YK11.getr regs 0%bv)) by (rewrite length_map; cbn [length pi_saved_regs]; lia).
      apply map_nth.
  + intros mat. cbv beta.
    pose proof (fsw_region_nth E' (sh_ss pib_st_Ie) (restrict (w_H W') ms2) 4 _ HS2 Fnth4) as RQ.
    rewrite restrict_mem in RQ. unfold pib_qIe in RQ.
    (* ---- struct pj_in at the ret: in->p past `}`, in->depth = k ---- *)
    pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN') as (Bq0 & Bq24 & Bt0 & (Bp1 & Bp2) & Bte & _ & Btb & _ & Bd).
    pose proof (fsw_field E' _ 9 q _ 0 24 0 24 0 8 (SOff (xatom 0) 1) (pc' + 1) RQ E'9u ltac:(cbn; tauto)
      (D9 (xatom 0) pc' 1 ltac:(unfold xatom; lia) EX0 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Q0.
    pose proof (fsw_field E' _ 9 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len + 0) RQ E'9u ltac:(cbn; tauto)
      (D9 (xatom 1) (text + len) 0 ltac:(unfold xatom; lia) EX1 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Q8.
    pose proof (fsw_field E' _ 9 q _ 0 24 0 24 16 4 (SOff (xatom 2) (-1)) (dd + 1 + -1) RQ E'9u ltac:(cbn; tauto)
      (D9 (xatom 2) (dd + 1) (-1) ltac:(unfold xatom; lia) EX2 ltac:(unfold dd; lia) ltac:(unfold dd; lia)) ltac:(cbn; lia)
      ltac:(cbn; lia)) as Q16.
    rewrite Z.add_0_r in Q0, Q8. replace (dd + 1 + -1) with dd in Q16 by lia. rewrite EPOS in Q0.
    pose proof RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E'9u in RQW.
    pose proof HIN' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
    assert (PIN : PjIn.pj_in_ok tfibsegs (rdW W' M2) q text len
      (p + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))))) (Z.of_nat k) tb).
    { refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 _))))))))))).
      - apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Q0 | lia | lia | lia].
      - apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Q8 | lia | lia | lia].
      - exact (proj1 (fsw_pj_word4_iff tfibsegs _ (q + 16) dd ltac:(unfold dd; lia) ltac:(unfold dd; lia)) Q16).
      - split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
      - lia.
      - destruct I10 as (A0' & A1' & A2'). split; [exact A0'|]. split; [exact A1'|]. intros j Hj.
        pose proof (A2' j Hj) as Hb. pose proof (SBm (text + Z.of_nat j) ltac:(lia)) as Ej.
        unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd,
          OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa in *. rewrite Ej. exact Hb.
      - unfold dd. lia. }
    assert (WK : wkeep tfibsegs W W' mem M2 (spZ regs) ot q 24).
    { apply (pil_wkeep_trans k S W regs mem q ot ms Hk HDEP W' W' mem' M2 sp0 HWK'); [|lia].
      intros z Hz Hq. pose proof (KRr z ltac:(lia) Hq) as Ez.
      split; [unfold mbyte; rewrite Ez; reflexivity|].
      split; intros Hw; [exact (writable_at_eq tfibsegs _ _ z Ez Hw) | exact (writable_at_eq tfibsegs _ _ z (eq_sym Ez) Hw)]. }
    destruct HOBJ' as (HH' & HOP').
    assert (SV : forall z, 0 <= z < alloc_ceiling -> parse_items_shape.pis_same tfibsegs (rdW W' mem') (rdW W' M2) z)
      by (intros z Hz; apply pio_same_raw; apply SBm; exact Hz).
    assert (HH2 : PjStruct.pj_hdr tfibsegs (rdW W' M2) v 6 0 0 kids keys (Z.of_nat i) cap)
      by exact (parse_items_shape.pis_hdr_frame tfibsegs _ _ v 6 0 0 kids keys (Z.of_nat i) cap HH' (fun z Hz => SV z ltac:(lia))).
    assert (HOP2 : parse_items_shape.pis_open tfibsegs (rdW W' M2) (ReaderRes.lin L) v true 0 kids keys cap (Z.of_nat i)
      (map snd dn) (map fst dn) Di).
    { apply (parse_items_shape.pis_frame tfibsegs _ _ _ _ v true 0 kids keys cap (Z.of_nat i) (map snd dn) (map fst dn) Di 0
        (Z.of_nat i) HOP' HH2 ltac:(lia) (fun a0 k0 H => H)).
      intros z Hz. rewrite length_map in Hz.
      destruct (pio_ifoot_in kids keys cap (Z.of_nat i) Di z ltac:(lia) Hz) as ((a0 & k0) & Hin0 & Hh0).
      destruct (fsw_rblock_low B ly' S' W' (unpoison Uc mem') md' mem' a0 k0 HAR2 (HRB' a0 k0 Hin0)) as (L1 & L2).
      unfold PjStruct.pj_holds in Hh0. cbn [fst snd] in Hh0.
      apply SV. unfold HEAD in *. lia. }
    assert (HRB2 : rd_blocks_ok tfibsegs B ly' S' W' M2 L)
      by exact (rd_blocks_ok_below B ly' S' W' (unpoison Uc mem') md' mem' M2 _ HAR2 SB HRB').
    split; [rewrite G10; reflexivity|].
    split; [exact PIN|].
    split; [exact WK|].
    split; [exact HPERM'|].
    split; [rewrite Hms, app_nil_r; exact (pio_close B ly' S' W' M2 v kids keys cap dn Di HOP2 HRB2)|].
    split; [rewrite ETR; exact HSUM'|].
    split; [rewrite ETR; exact HLEN'|].
    split; [exact (pobj_below B ly' S' W' (unpoison Uc mem') md' mem' M2 v HAR2 SB HPO')|].
    split; [split; [exact Ht4'|]; split;
      [exact (fs_rblock_below B ly' S' W' (unpoison Uc mem') md' mem' M2 text tcap HAR2 SB HRBt') | exact Hlt']|].
    exists peak1. split; [exact Hpk'|]. rewrite ETR. exact (fs_glob_below W' mem' M2 _ _ _ _ SB HG').
Qed.
End I.
