(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the member's close in parse_items' loop on image B, from the
   resume after parse_value (pib_IH at 0x851d0, the end of the segment FSW_parse_items_val.v walks) to the call of
   skip_ws #4 (0x851f0, ra 0x851f4), whose call-site state is pib_IW4 (this file):
     pi_step_H1 : the object across parse_value (pio_value), the start state of segment H (pil_start, v's window
                  narrowed to n), segment H's run (FSW_parse_items_seg.pib_run_H: v->n := n + 1 at 0x851e0, stop at
                  skip_ws), the member closed (pio_snoc) -> pib_IW4.
   The B form of the post-call half of the A walk's pi_step_Vc / pi_step_Ve (a working branch
   4480a5df1ae lib/A/FSW_parse_items_stVc.v, stVe.v), up to where B calls skip_ws; pih_av / pih_av_unp copy its
   pvc_av / pvc_av_unp.
   rule 24: proves no function (kind: step lemma). *)
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
FSW_parse_items_sws FSW_parse_items_grow FSW_parse_items_stG FSW_parse_items_stP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.


(* ================= segment H's stop (measured; vm_compute) ================= *)
Definition pib_RH : list (bv 5 * sv) :=
  [(1%bv, SLit 0x851f4); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (9%bv, SOff 9 0); (10%bv, SOff 9 0);
   (19%bv, SOff 19 0)] ++ pib_RL.
(* v at H's stop: v->n = n + 1 written at 40 *)
Definition pib_vH : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 56 40 48
    [YP09.mkChunk 40 (CVal 8 (SOff (xatom 18) 1)); YP09.mkChunk 0 (CVal 4 (SLit 6));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 16) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 17) 0));
     YP09.mkChunk 48 (CVal 8 (SOff (xatom 19) 0))].
Lemma pib_fin_H :
  ss_pc (sh_ss pib_st_H) = A_skip_ws /\ sh_obls pib_st_H = [] /\ ss_resv (sh_ss pib_st_H) = None /\
  pib_regs_are (sh_ss pib_st_H) pib_RH = true /\
  nth_error (ss_mem (sh_ss pib_st_H)) 0 = Some (YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL) /\
  nth_error (ss_mem (sh_ss pib_st_H)) 3 = Some (YP09.mkRegion (Some 9%nat) 0 24 0 0 (YP09.r_chunks pi_qR)) /\
  nth_error (ss_mem (sh_ss pib_st_H)) 4 = Some pib_vH.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pib_K_H : (xatom 22 <= run_K 0 fs_Bx pib_SHm pib_ss_H)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
(* segment H writes v->n only *)
Lemma pib_wr_H : forall E vv a, bv_unsigned (ew E 19) = vv -> in_wrange E (ss_mem pib_ss_H) a -> vv + 40 <= a < vv + 48.
Proof.
intros E vv a E19 (rg & Hin & Ha).
unfold pib_ss_H, pib_start, pik_addf, pik_addr, pik_setr, pik_setm, pib_rgs, pib_RO in Hin. cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val fst snd] in Ha; rewrite ?E19 in Ha; lia.
Qed.

Section A. Context {fx : YK11.FPState}.
(* fs.asan's image bytes lie in [0x10000, FS_IMG_END) (the A walk's pic_img_lo, lib/A/FSW_parse_items_calls.v
   4480a5df1ae, copied) *)
Lemma pih_img_lo : forall x, in_img tfibsegs x -> 0x10000 <= x < FS_IMG_END.
Proof.
intros x Hx. pose proof (fs_segs_img x Hx) as Hu. split; [|lia].
destruct Hx as (s & Hs & Hr).
assert (HB : forallb (fun s => 0x10000 <=? Z.of_N (seg_base s)) tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB s Hs) as Hc. cbv beta in Hc. apply Z.leb_le in Hc. lia.
Qed.
(* a byte's view, and the view of an unpoisoned memory, from the raw restricted byte (copied, see the header) *)
Lemma pih_av : forall (H : word -> bool) (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte. cbv beta. rewrite E. reflexivity. Qed.
Lemma pih_av_unp : forall (H : word -> bool) U0 (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
  aview tfibsegs H (unpoison U0 m') a = aview tfibsegs H (unpoison U0 m) a.
Proof.
intros H U0 m m' a E. unfold aview, mbyte. cbv beta. unfold mrestrict, unpoison in *.
destruct (H (Z_to_bv 64 a)); [reflexivity|]. destruct (in_ush U0 (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
rewrite E. reflexivity.
Qed.
End A.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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
#[local] Abbreviation IH := (pib_IH B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).

(* ================= the call-site state at skip_ws #4 (the member closed) ================= *)
Definition pib_IW4 (dn : list (list Z * PjTree.jv)) (rm : list (list Z * PjTree.jv)) (T : list PjGrammar.ev)
  (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs) (memC : word -> option byte) (mdC : Model)
  (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  ms = dn ++ rm /\ (1 <= i)%nat /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.tgo_obj i (Z.to_nat cap) rm /\
  (i <= Z.to_nat cap)%nat /\ cap <= 2 ^ 54 /\
  JC lyc Sc Uc W1 memC mdC (rd_ev T) /\
  YK11.getr regsC 1 = w64 0x851f4 /\ YK11.getr regsC 10 = w64 q /\
  RP regsC pib_RL /\ pib_frameL (rdW W1 memC) sp0 xr q v /\
  STKP lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc = concat (pi_mgo pr dd i rm) ++ pib_wsb pr dd ++ [125] ++ rest /\
  BLK lyc Sc Uc W1 memC L Da T peak1 /\
  OBJ W1 memC L (Z.of_nat i) kids keys cap dn Di.

(* ---- the entry's facts this step reads (FSW_parse_items_lh.v) ---- *)
Lemma H_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof. exact (pil_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP). Qed.
Lemma H_stk144 : 144 <= STK_parse_items (1 - k).
Proof. exact (pil_stk144 k S regs ot ms Hk HDEP). Qed.
Lemma H_qs : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof. exact (pil_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP). Qed.
Lemma H_vrng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof. exact (pil_v_rng B k ly S U W regs mem md v ch HPRE HPO0). Qed.
Lemma H_text : 4096 + HEAD <= text /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP ly S W (unpoison U mem) md mem p dd HAR HTX HIN0)
  as (H1 & _ & H3 & H4 & H5). lia.
Qed.

(* the registers at the skip_ws #4 stop, as pib_IW4 states them *)
Lemma H_regsP_stop : forall E' (regs2 : bvmap 5 word),
  Forall (fun r => YK11.getr regs2 (fst r) = sv_denot E' (snd r)) pib_RH ->
  ew E' 9 = Z_to_bv 64 q -> ew E' 19 = Z_to_bv 64 v -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E' 2) = sp0 - 144 -> ew E' 3 = Z_to_bv 64 (as_gp B) -> ew E' 4 = Z_to_bv 64 (as_tp B) ->
  ed E' = (fun _ => []) ->
  RP regs2 pib_RL /\ YK11.getr regs2 1 = w64 0x851f4 /\ YK11.getr regs2 10 = w64 q.
Proof.
intros E' regs2 HR E9 E19 E32 E2 E3 E4 Hed. rewrite Forall_forall in HR.
assert (G : forall r e, In (r, e) pib_RH -> YK11.getr regs2 r = sv_denot E' e) by (intros r e H; exact (HR (r, e) H)).
assert (G9 : YK11.getr regs2 9 = Z_to_bv 64 q) by (rewrite (G 9%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9).
assert (G19 : YK11.getr regs2 19 = Z_to_bv 64 v)
  by (rewrite (G 19%bv (SOff 19 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E19).
split; [|split; [rewrite (G 1%bv (SLit 0x851f4)) by (cbn; tauto); reflexivity |
  rewrite (G 10%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9]].
split; [unfold spZ; rewrite (G 2%bv (SOff 2 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E2|].
split; [exact G9|]. split; [exact G19|].
split; [rewrite (G 3%bv (SOff 3 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E3|].
split; [rewrite (G 4%bv (SOff 4 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E4|].
apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (G r e) by (unfold pib_RH; apply in_or_app; right; exact Hin).
pose proof (pil_RL_ok) as Hok. unfold pil_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
apply pik_sv_denot_agree; [rewrite Hed; reflexivity|].
intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
- rewrite E9, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). symmetry. exact G9.
- rewrite E19, (ew_Ereg_nat regs2 _ 19 19%bv eq_refl). symmetry. exact G19.
- rewrite E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ================= (H1) the member's close, to skip_ws #4 ================= *)
Lemma pi_step_H1 : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1 a
    D Dx ly' S' (W' : world tfibsegs) regs' mem' md' (Qc : world tfibsegs -> config -> Prop),
  IH dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a D Dx ly' S' W' regs' mem' md' ->
  (forall T2 ly2 S2 U2 (W2 : world tfibsegs) mem2 md2 regs2 pc2 Di2 Da2 peak2,
     pib_IW4 (dn ++ [(kk, x)]) rm T2 ly2 S2 U2 W2 mem2 md2 regs2 chq pc2 kids keys cap Di2 Da2 peak2 ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs A_skip_ws regs2 mem2 md2) Qc) ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x851d0) mem' (seg_rom tfibsegs)) md') Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a D Dx ly' S' W' regs' mem' md' Qc HIH KW.
unfold pib_IH in HIH. cbv zeta in HIH.
destruct HIH as (HIV & HPm & HJ2 & HJc & HARU' & HP & A0 & HS0 & HIN' & HWK' & HPERM' & HRT & HSUMx & HLENx & HPOk &
  HTX' & HG' & HHDR' & VBm & BLK' & KBm).
unfold pib_IV, pib_IK in HIV. cbv zeta in HIV.
destruct HIV as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HSTK & HTXT & HBL & HOBJ & Hu64 & Hcstr) &
  R1 & R10 & R11 & HZK & HPK).
set (i := length dn) in *.
set (Ka := Z.of_nat (length kk) + 1) in *.
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
pose proof HSTK as (HCH & HFW & Htop & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HRB & HPERM & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOBJ as (HHDR & HOP).
pose proof HARU as (HAR & _ & _).
pose proof HARU' as (HAR' & OK' & PO').
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof H_sp0 as (Hsp16 & Hsp1 & Hsp2). pose proof H_stk144 as H144.
pose proof H_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof H_vrng as (Hv1 & Hv2). pose proof H_text as (Gt1 & Gt2 & Gt3 & Gt4).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HTX as (_ & (TIN0 & _) & _).
assert (Hn : Z.of_nat i < cap) by lia.
pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR0 HPO0) as Hvimg0.
pose proof (fsw_pobj_low B lyc Sc W1 (unpoison Uc memC) mdC memC _ HAR HPK) as (Hvk1 & Hvk2).
pose proof (fsw_pobj_off_img B lyc Sc W1 (unpoison Uc memC) mdC memC _ HAR HPK) as Hvkimg.
(* ---- the key block is apart from v ---- *)
assert (HAPa : PjStruct.pj_apart [(a, Ka)] v).
{ intros b0 z [<-|[]] Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz.
  assert (HinL : In (a, Ka) (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Ka)]))
    by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  pose proof (HRB _ _ HinL) as (HinA & _ & HKa & _).
  destruct (pio_jr_frames B _ _ _ ly S W (unpoison U mem) md lyc Sc W1 (unpoison Uc memC) mdC _ HJ HAR0) as (Hfr & Hfa).
  apply (pio_new_apart B ly S W mem v lyc Sc W1 (unpoison Uc memC) mdC (a - HEAD) (Ka + HEAD) HAR HPO0 Hfr Hfa).
  - intros b mm Hb _ _. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hb.
  - exact HinA.
  - apply (pil_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
    unfold rd_hblocks. apply (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ _ HinL).
  - rewrite pio_req_hb by lia. unfold HEAD. lia. }
assert (HKaL : In (a, Ka) (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Ka)]))
  by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC a Ka HAR (HRB _ _ HKaL)) as (Ha1 & Ha2).
(* ---- the object across parse_value ---- *)
assert (EL : parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Ka)] =
  (parse_items_shape.pis_slots true kids keys cap ++ Di) ++ [(a, Ka)]) by apply app_assoc.
pose proof (pio_value B ly S U lyc Sc Uc W1 memC mdC ly' S' W' mem' md' _ _ _ v text len tcap i dn kids keys
  cap Di Da T a kk x D Dx eq_refl Hn HARU ltac:(rewrite <- app_assoc; exact HPERM) HUc ltac:(rewrite <- app_assoc; exact HDa)
  ltac:(rewrite <- app_assoc; exact HSUM) ltac:(rewrite <- app_assoc; exact HLEN) HHD ltac:(rewrite <- app_assoc; exact HRB) HPO1
  ltac:(rewrite <- app_assoc; exact HOP) Hu64 ltac:(rewrite <- app_assoc; exact Hcstr) HAPa HPm HJc HARU' HPERM' HRT HSUMx HLENx
  HTX' HHDR' VBm BLK' KBm) as PV.
cbv zeta in PV.
destruct PV as (RB6 & PERM6 & U6 & DA6 & SUM6 & LEN6 & HD6 & TX6 & PO6 & HDR6 & OP6 & U646 & CS6 & ND6 & NODUP6 & AP6).
rewrite <- !app_assoc in RB6, PERM6, DA6, SUM6, LEN6, OP6, CS6, ND6, NODUP6.
(* ---- the resume env ---- *)
set (p' := pc + Z.of_nat (length (if pr then [32] else [])) + Z.of_nat (length (concat (WriterValue.wvpieces x pr (dd + 1)))))
  in *.
set (xs := pib_xsK p' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a (Z.of_nat (length kk))) in *.
set (U' := Uc ++ rd_heads Dx) in *.
destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & Egp & Etp).
destruct (pib_xsK_nth p' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a (Z.of_nat (length kk)) (pil_xr_len regs))
  as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21).
set (E := Ereg regs' (fs_extraT ++ xs)) in *.
assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN') as (_ & _ & _ & Bp' & Bend & _).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlytop' & Hlylo' & Hlyhi' & _).
destruct HG' as (peak' & Hpk' & HG'').
(* ---- the start state: segment H, v's window narrowed to n ---- *)
assert (HA0 : YK11.getr regs' 10 = sv_denot E (SLit 0)) by (rewrite A0; reflexivity).
pose proof (fsw_pobj_off_img B ly' S' W' (unpoison U' mem') md' mem' v HAR' PO6) as Hvimg.
assert (HPD : pairwise_disjoint E ([] ++ fsT_ret_regions 144 pib_csL pib_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, E9u, E19u.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (pil_start k S regs ot ms Hk HDEP regs' xs W' mem' 0x851d0 pib_csL pib_gfP ((10%bv, SLit 0) :: pib_RL) [] [] []
  [] pib_RO pib_RO (40, 48) HS0 (pil_setr_ok B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL (SLit 0) HRP HP pil_RL_ok
  HA0) ltac:(vm_compute; reflexivity) (Forall_nil _) HPD I I I ltac:(left; cbn; lia) ltac:(left; cbn; lia)
  ltac:(right; cbn; lia) ltac:(vm_compute; reflexivity)) as HSS1.
change (pib_start 0x851d0 pib_csL pib_gfP (pib_rgs pib_csL pib_RO pib_RO (40, 48)) ((10%bv, SLit 0) :: pib_RL) [] [] [] [])
  with pib_ss_H in HSS1.
(* ---- the shadow entries: q, v ---- *)
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U9 : YP0e.U E (SOff 9 0) = q) by (apply U_atom; [exact E9 | lia]).
assert (U19 : YP0e.U E (SOff 19 0) = v) by (apply U_atom; [exact E19 | lia]).
assert (HSH : sh_ok tfibsegs fs_Bx pib_SHm E (rdW W' mem')).
{ unfold sh_ok, pib_SHm. constructor; [|constructor; [|constructor]].
  - exact (pil_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' U' W' mem' md'
      E 9 HARU' ltac:(congruence) ltac:(congruence) UB U9).
  - exact (pil_sh_v B k S regs ot v ms Hk HDEP ly' S' U' W' mem' md' E 19 HARU' PO6 UB U19). }
(* ---- the write windows: v->n ---- *)
assert (AWR : awr_ok tfibsegs B E (ss_mem pib_ss_H) STKt ot FP (ablocks B ly S) (ablocks B ly' S') ly' [] (frames S))
  by exact (pil_awr_rgs B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E ly' S' W' (unpoison U' mem') md'
    mem' [] pib_csL pib_RO pib_RO (40, 48) HAR' PO6 Hfr2 E2 E9u E19u (Forall_nil _) ltac:(cbn; lia) ltac:(cbn; lia)
    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)).
(* ---- the read-only view after the call ---- *)
assert (HROc : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem')).
{ apply (arodata_kept B _ _ _ lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' _ HJc HARU OK' PO'); [| |exact HRO].
  - apply sink_closed_pos. apply Forall_cons; [cbn [fst]; lia|].
    unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - intros a0 Ha0' Hf. apply inFP_app in Hf as [Hf|Hf].
    + destruct Hf as (rr & Hrr & Har). cbn [In] in Hrr. destruct Hrr as [<-|[]]. cbn [fst snd] in Har.
      pose proof (pih_img_lo a0 (fsw_roP_img a0 Ha0')) as Hi. unfold FS_IMG_END in *. destruct Hvkimg; lia.
    + exact (FSW_grow_holds.fs_pstat_not_ro a0 Hf Ha0'). }
(* ---- the run H to skip_ws #4 ---- *)
destruct pib_fin_H as (Fpc & Fob & Fresv & Fregs & Fnth0 & Fnth3 & Fnth4).
refine (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pib_SHm pib_ss_H) fs_Bx fs_Bspan pib_SHm
  pib_ss_H pib_st_H (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 0x851d0) mem' (seg_rom tfibsegs)) STKt ot FP ly S W
  (unpoison U mem) md [] ly' S' U' md' (rd_ev T + rd_ev (PjRoundTrip.ttrace x)) Qc HSS1 HSH pib_static_H pib_run_H I
  HARU' HJ2 _ AWR _).
{ rewrite Fob. constructor. }
intros ws2 ms2 mat2 Hlen2 HS2 SHOK2 HJ3 HARU3 HFra HFrr HG2.
set (K := run_K 0 fs_Bx pib_SHm pib_ss_H) in *.
set (E' := extK E K ws2) in *.
pose proof pib_K_H as HKb. fold K in HKb.
assert (HK : forall n, (n <= 54)%nat -> ew E' n = ew E n)
  by (intros n Hn0; apply (pil_ew_extK k S regs ot ms Hk HDEP); unfold xatom in HKb; lia).
assert (E'9 : ew E' 9 = Z_to_bv 64 q) by (rewrite HK by lia; exact E9).
assert (E'19 : ew E' 19 = Z_to_bv 64 v) by (rewrite HK by lia; exact E19).
assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite HK by lia; exact E32).
assert (E'2 : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite HK by lia; exact E2).
assert (E'3 : ew E' 3 = Z_to_bv 64 (as_gp B)) by (rewrite HK by lia; exact Egp).
assert (E'4 : ew E' 4 = Z_to_bv 64 (as_tp B)) by (rewrite HK by lia; exact Etp).
assert (E'19u : bv_unsigned (ew E' 19) = v) by (rewrite E'19; apply unsigned_lit_small; lia).
assert (Hed : ed E' = (fun _ => [])) by (unfold E'; rewrite pil_ed_extK; reflexivity).
set (M2 := ms_mem ms2) in *.
set (md2 := with_vm_backing (m_vm_lazy md') mat2 md') in *.
(* ---- what the run kept: every byte but v->n ---- *)
assert (KR : forall z, 0 <= z < 2 ^ 64 -> ~ (v + 40 <= z < v + 48) -> M2 (Z_to_bv 64 z) = mem' (Z_to_bv 64 z)).
{ intros z Hz H1. apply HFra. rewrite wz by lia. intros Hw. pose proof (pib_wr_H E v z E19u Hw). lia. }
assert (KRr : forall z, 0 <= z < 2 ^ 64 -> ~ (v + 40 <= z < v + 48) -> rdW W' M2 (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
  by (intros z Hz H1; unfold mrestrict; rewrite (KR z Hz H1); reflexivity).
assert (KRm : forall z, 0 <= z < 2 ^ 64 -> ~ (v + 40 <= z < v + 48) -> mbyte tfibsegs (rdW W' M2) z = mbyte tfibsegs (rdW W' mem') z)
  by (intros z Hz H1; unfold mbyte; rewrite (KRr z Hz H1); reflexivity).
(* ---- v->n := n + 1, the member closed ---- *)
pose proof (fsw_region_nth E' (sh_ss pib_st_H) (restrict (w_H W') ms2) 4 _ HS2 Fnth4) as RV. rewrite restrict_mem in RV.
unfold pib_vH in RV.
assert (V40 : val_mem tfibsegs (rdW W' M2) (v + 40) 8 (Z.of_nat i + 1)).
{ apply (fsw_field E' _ 19 v _ 0 56 40 48 40 8 (SOff (xatom 18) 1) (Z.of_nat i + 1) RV E'19u ltac:(cbn; tauto));
    [| cbn; lia | cbn; lia].
  apply bv_eq. rewrite denot_SOff, (HK (xatom 18)) by (unfold xatom; lia). rewrite EXn. unfold xs. rewrite X18.
  rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (WRz : forall z, v + 40 <= z < v + 48 -> writable_at tfibsegs (rdW W' M2) z).
{ intros z Hz. pose proof RV as (_ & _ & RVW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RVW.
  rewrite E'19u in RVW. replace z with (v + (z - v)) by lia. apply RVW. lia. }
assert (KEEPz : forall z, 0 <= z < alloc_ceiling -> ~ (v + 40 <= z < v + 48) ->
  rdW W' M2 (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z)) by (intros z Hz Hnv; apply KRr; lia).
pose proof (pio_snoc B ly' S' U' W' mem' md' M2 v text len tcap kids keys cap i dn kk x Di a D eq_refl Hn
  HARU' RB6 TX6 PO6 OP6 U646 CS6 ND6 NODUP6 AP6 V40 KEEPz WRz) as SN.
cbv zeta in SN. destruct SN as (HDR7 & OP7 & RB7 & TX7 & PO7).
(* ---- the skip_ws #4 configuration ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E' (sh_ss pib_st_H) ms2 HS2 Fresv) as Ems2. rewrite Fpc in Ems2.
rewrite Ems2.
change (SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_skip_ws (ms_regs ms2) M2 md2) Qc).
pose proof (pil_regs_of_stop E' (sh_ss pib_st_H) ms2 (w_H W') pib_RH HS2 Fregs) as RG.
destruct (H_regsP_stop E' (ms_regs ms2) RG E'9 E'19 E'32 E'2 E'3 E'4 Hed) as (RP2 & R1' & R10').
pose proof (fsw_region_nth E' (sh_ss pib_st_H) (restrict (w_H W') ms2) 0 _ HS2 Fnth0) as RF. rewrite restrict_mem in RF.
(* ---- the caller's window and the frame chain at q ---- *)
assert (AV : forall z, sp0 <= z < ly_top ly -> ~ (q <= z < q + 24) ->
  aview tfibsegs (w_H W') (unpoison U' M2) z = aview tfibsegs (w_H W1) (unpoison Uc memC) z).
{ intros z Hz Hq. rewrite (pih_av_unp (w_H W') U' mem' M2 z (KRr z ltac:(lia) ltac:(lia))).
  destruct (Z_lt_le_dec z ot) as [Hzo|Hzo].
  - destruct (HWK' z ltac:(rewrite Rsp; lia) Hq) as (Mz & _).
    rewrite (fsw_aview_unpoison_high B ly' S' U' W' mem' md' z HARU' ltac:(lia)),
      (fsw_aview_unpoison_high B lyc Sc Uc W1 memC mdC z HARU ltac:(lia)).
    unfold aview. rewrite Mz. reflexivity.
  - pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & HJ9 & _). apply HJ9; [lia | rewrite Rsp; lia]. }
assert (CH7 : achain ly' (aview tfibsegs (w_H W') (unpoison U' M2)) sp0 q chq)
  by exact (pis_chain_kept lyc ly' _ _ sp0 q (ly_top ly) chq HCH HFW Htop ltac:(congruence) AV).
assert (PIN7 : PjIn.pj_in_ok tfibsegs (rdW W' M2) q text len p' (dd + 1) tb).
{ apply (pil_pin_kept k S regs ot text len tb ms Hk HDEP (rdW W' mem') _ q p' (dd + 1) HIN').
  - intros z Hz. split; [exact (KRm z ltac:(lia) ltac:(lia))|].
    exact (writable_at_eq tfibsegs _ _ z (KRr z ltac:(lia) ltac:(lia))).
  - intros z Hz. unfold HEAD in *. apply KRm; [lia | destruct HVTX; lia]. }
assert (WK7 : wkeep tfibsegs W W' mem M2 sp0 ot q 24).
{ apply (pil_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W' memC M2 sp0 HWK); [|lia].
  intros z Hz Hq. destruct (HWK' z ltac:(rewrite Rsp; lia) Hq) as (Mz & Wz).
  pose proof (KRr z ltac:(lia) ltac:(lia)) as Ez.
  split; [unfold mbyte; rewrite Ez; exact Mz|].
  split; intros Hw.
  - exact (writable_at_eq tfibsegs _ _ z Ez (proj1 Wz Hw)).
  - exact (proj2 Wz (writable_at_eq tfibsegs _ _ z (eq_sym Ez) Hw)). }
(* ---- the read-only view and the statics after the run ---- *)
assert (RO7 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') M2)).
{ apply (pim_ro_keep B (aview tfibsegs (w_H W') mem')); [exact HROc|].
  intros a0 Ha0. apply pih_av. apply KRr.
  - pose proof (pih_img_lo a0 (fsw_roP_img a0 Ha0)). unfold FS_IMG_END in *. lia.
  - pose proof (pih_img_lo a0 (fsw_roP_img a0 Ha0)). unfold FS_IMG_END in *. destruct Hvimg; lia. }
assert (HG7 : fs_glob tfibsegs W' M2 (live + PjGrammar.held (T ++ PjRoundTrip.ttrace x)) peak'
  (cnt + Z.of_nat (length (T ++ PjRoundTrip.ttrace x))) fail).
{ rewrite PjGrammar.held_app, length_app, Nat2Z.inj_add, !Z.add_assoc.
  apply (pim_glob_eqon W' W' mem' M2 _ _ _ _); [|exact HG''].
  intros a0 Ha0. apply KRr.
  - pose proof (pih_img_lo a0 (pim_pstat_img a0 Ha0)). unfold FS_IMG_END in *. lia.
  - pose proof (pih_img_lo a0 (pim_pstat_img a0 Ha0)). unfold FS_IMG_END in *. destruct Hvimg; lia. }
(* ---- pib_IW4 ---- *)
apply (KW (T ++ PjRoundTrip.ttrace x) ly' S' U' W' M2 md2 (ms_regs ms2) p' (Di ++ [(a, Ka)] ++ D) (Da ++ Dx) peak').
unfold pib_IW4. cbv zeta.
replace (length (dn ++ [(kk, x)])) with (Datatypes.S i) by (rewrite length_app; cbn [length]; unfold i; lia).
split; [rewrite <- app_assoc; exact Hms|].
split; [lia|].
split; [rewrite <- app_assoc; exact Htr|].
split; [exact Hcap|].
split; [exact Hcap54|].
split.
{ split; [rewrite pim_rd_ev_app; exact HJ3|]. split; [exact HARU3|]. split; [exact RO7|].
  exact HD6. }
split; [exact R1'|]. split; [exact R10'|]. split; [exact RP2|].
split.
{ apply (pil_frameL_of B k ly S U W regs mem md q ot v text tcap ms ch Hk HPRE HVTX HPO0 HDEP HVSP E' _ 0 0 pib_csL
    E'2 E'19 E'32); [| exact RF | apply incl_refl].
  intros j Hj. rewrite HK by (unfold xatom; lia). unfold E.
  exact (pil_xsK_saved regs' p' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a (Z.of_nat (length kk)) j
    (pil_xr_len regs) Hj). }
split.
{ split; [exact CH7|]. split; [exact HFW|]. split; [congruence|]. split; [exact PIN7 | exact WK7]. }
split.
{ unfold p'. rewrite <- Z.add_assoc, <- Nat2Z.inj_add, <- length_app.
  apply pim_rest_skip; [unfold HEAD in *; pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & (Hb1 & _) & _); lia|].
  rewrite HTXT. rewrite <- !app_assoc. reflexivity. }
split.
{ split; [exact TX7|]. split; [exact PO7|]. split; [exact RB7|]. split; [exact PERM6|].
  split; [exact U6|].
  split; [exact DA6|]. split; [exact SUM6|]. split; [exact LEN6|]. split; [exact HG7 | lia]. }
split; [|exact OP7].
replace (Z.of_nat (Datatypes.S i)) with (Z.of_nat i + 1) by lia. exact HDR7.
Qed.
End H.
