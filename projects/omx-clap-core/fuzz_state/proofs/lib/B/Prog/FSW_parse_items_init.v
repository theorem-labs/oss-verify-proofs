(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) pi_init, the ENTRY SEGMENT of parse_items' walk on image B
   for an object with members (ms = (kk, x) :: rm): from parse_items' entry to the first grow call, with the member
   loop's call-site invariant pib_IG [] (FSW_parse_items_loop.v) for member 0 (T = [], kids = keys = cap = 0,
   Di = Da = [], peak1 = peak). The statement is FSW_parse_items_mloop.v's Section hypothesis HINIT (mloop.v:154),
   verbatim, under the Section setup of FSW_parse_items_lh.v's Section L (its 28 entry hypotheses verbatim) plus
   skip_ws_spec. The route:
     FSW_parse_items_pre.pi_sw1_s5 (stage A, skip_ws #1 at 0x84f58 over skip_ws_spec, the resume at 0x84f5c: the white
       space after `{` is the writer's indent wind pr (k + 1), the byte after it the key's opening quote; s5 = 2^64 - 1),
     FSW_parse_items_pre.pi_stageB_member_ro (0x84f5c .. the grow call at 0x84fac, ra 0x84fb0, the cursor byte 0x22;
       the memory unchanged at every address),
   then pib_IG: the journal, the registers pib_R0 (s5 from pi_sw1_s5, the rest from stage B), the frame's thirteen
   saved words and v's header (read off the resume state's frame and v regions, FSW_parse_items.pi_ssB0), struct pj_in,
   the frame chain at q (the bytes of [sp0, ot) off struct pj_in from pi_sw1_s5, those above ot from the journal), the
   text past the indent, v as a 0-member object over no blocks.
   pin_byte0 is FSW_parse_items_holds.v's pih_byte1 (a Theorem Labs lane) at offset 0.
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
FSW_parse_items_sws FSW_parse_items_pre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= image-free facts ================= *)
(* the first byte of the text at p, read out of rest_at (see the header) *)
Lemma pin_byte0 : forall (tb : list byte) text p c r,
  ReaderRes.rest_at tb text p = c :: r ->
  exists b, nth_error tb (Z.to_nat (p - text)) = Some b /\ bv_unsigned b = c.
Proof.
intros tb text p c r H. unfold ReaderRes.rest_at, ReaderRes.zb in H.
assert (E1 : nth_error (map (fun b : byte => bv_unsigned b) (skipn (Z.to_nat (p - text)) tb)) 0 = Some c)
  by (rewrite H; reflexivity).
rewrite nth_error_map, nth_error_skipn, Nat.add_0_r in E1.
destruct (nth_error tb (Z.to_nat (p - text))) as [b|] eqn:Eb; cbn in E1; [|discriminate].
exists b. split; [reflexivity|]. injection E1 as E1. exact E1.
Qed.
(* an atom plus an offset, as a register value *)
Lemma pin_den_off : forall E n z c, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (z + c).
Proof.
intros E n z c Hn Hz Hzc. unfold w64. apply bv_eq.
rewrite denot_SOff, Hn, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
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

(* ================= the entry premises (FSW_parse_items_lh.v Section L's, verbatim) ================= *)
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
(* callee: skip_ws (a Theorem Labs lane's B walk, a working branch) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.

(* ================= pi_init: FSW_parse_items_mloop.v's HINIT (mloop.v:154), verbatim ================= *)
Lemma pi_init : forall kk x rm (Qc : world tfibsegs -> config -> Prop), ms = (kk, x) :: rm ->
  (forall T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
     IG [] kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
     SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Qc.
Proof.
intros kk x rm Qc Hms KIG.
destruct HCH0 as (chq & HCH & HCHF).
(* ---- the entry's facts (FSW_parse_items_holds.v pi_nil's) ---- *)
set (STK := STK_parse_items (1 - k)) in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HPREU & HRO).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPREU) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAPRE & _ & _). pose proof HAPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO0) as (Hv4096 & Hvceil).
pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO0) as Hvimg.
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof Htxblk as (HinT & _ & _ & _).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md _ _ HAR HinT) as (_ & _ & Hreq).
pose proof (fsw_ablock_off_img B ly S W (unpoison U mem) md _ _ HAR HinT) as Htimg.
assert (HSTKf : FRAME_parse_items = 144) by reflexivity.
assert (HSTK : FRAME_parse_items + STK_skip_ws <= STK)
  by (unfold STK, STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
assert (HSW0 : 0 <= STK_skip_ws) by (vm_compute; discriminate).
assert (Hv8 : v mod 8 = 0) by (destruct HPO0 as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
unfold HEAD in *.
(* ---- the text: `{`, the indent ws, then the key's opening quote ---- *)
set (ws := concat (WriterValue.wind pr (Z.of_nat k + 1))).
set (rest' := concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++
  concat (WriterValue.wvpieces x pr (Z.of_nat k + 1)) ++ concat (pi_mgo pr (Z.of_nat k) 1%nat rm) ++
  pib_wsb pr (Z.of_nat k) ++ [125] ++ rest).
assert (HREST' : ReaderRes.rest_at tb text p = 123 :: ws ++ rest').
{ unfold rest', ws. rewrite HREST, Hms, pi_obj_cons. unfold pib_wsb.
  cbn [app]. rewrite <- !app_assoc. reflexivity. }
assert (Hws : Forall (fun c => PjGrammar.ws c = true) ws) by exact (pi_wind_ws pr (Z.of_nat k + 1)).
assert (Hstop : forall c r, rest' = c :: r -> PjGrammar.ws c = false).
{ intros c0 r0 E0. unfold rest' in E0. rewrite pi_spieces_head in E0. cbn [app] in E0.
  injection E0 as <- _. reflexivity. }
assert (HR1 : ReaderRes.rest_at tb text (p + 1 + Z.of_nat (length ws)) = rest').
{ assert (H1 : ReaderRes.rest_at tb text (p + 1) = ws ++ rest')
    by exact (pim_rest_skip tb text p [123] (ws ++ rest') ltac:(lia) HREST').
  exact (pim_rest_skip tb text (p + 1) ws rest' ltac:(lia) H1). }
assert (HR1c : exists r0, ReaderRes.rest_at tb text (p + 1 + Z.of_nat (length ws)) = 34 :: r0).
{ rewrite HR1. unfold rest'. rewrite pi_spieces_head. cbn [app]. eexists. reflexivity. }
destruct HR1c as (r0 & HR1c).
assert (Hpcl : p + 1 + Z.of_nat (length ws) < text + len).
{ pose proof (pi_rest_len _ q text len p _ tb HIN0) as Hrl. rewrite HREST' in Hrl.
  cbn [length] in Hrl. rewrite length_app in Hrl.
  assert (Hr0 : (0 < length rest')%nat)
    by (unfold rest'; rewrite pi_spieces_head; cbn [app length]; lia).
  lia. }
(* ---- stage A, skip_ws #1, the resume at 0x84f5c ---- *)
apply (pi_sw1_s5 SK B HSS HSW ly S U W regs mem md ch q ot v text len p tb tcap (Z.of_nat k) STK ws rest' 34
  live peak cnt fail Qc HPRE HHEADS HSTK H10 H11 H12 HIN0 HWIN HTX HPO0 HZERO HVSP HVTX ltac:(lia) HREST' Hws Hstop
  HGLOB).
intros ly' S' W' regs' mem' md' HST HJ1 HARU1 G2 G3 G4 G8 G9 G18 G19 G25 G26 G27 G21 QIN QTX QGL QAB HRO1 HWK1
  VW1 VD1.
pose proof (ARU_AR tfibsegs B ly' S' U W' mem' md' HARU1) as HAR1.
pose proof HJ1 as (_ & Hly1 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & Elo1 & Ehi1 & _).
assert (HH1 : FSupoisonU.fs_heads B ly' S' U) by (intros r Hr; rewrite QAB; exact (HHEADS r Hr)).
pose proof QTX as (_ & Htxblk1 & _).
pose proof Htxblk1 as (HinT1 & _ & _ & _).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ QIN) as (_ & _ & _ & Hpc' & _).
destruct (pin_byte0 tb text _ 34 r0 HR1c) as (b1 & Hb1 & Hb1v).
pose proof (pim_byte_tb _ q text len (p + 1 + Z.of_nat (length ws)) (Z.of_nat k + 1) tb (p + 1 + Z.of_nat (length ws))
  b1 QIN ltac:(lia) Hb1) as HBV.
rewrite Hb1v in HBV.
(* ---- what the resume state holds: the frame's saved words, v's header ---- *)
set (E := Ereg regs' (fs_extraT ++ pi_xsR (p + 1 + Z.of_nat (length ws)) (text + len) (Z.of_nat k + 1) regs 0 0 0 0 34))
  in HST.
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 144)
  by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact G2).
assert (E19 : bv_unsigned (ew E 19) = v)
  by (unfold E; rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19; unfold w64; apply wz; lia).
destruct (pi_xsR_nth (p + 1 + Z.of_nat (length ws)) (text + len) (Z.of_nat k + 1) regs 0 0 0 0 34)
  as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20).
assert (XR' : forall j, (j < 13)%nat ->
  ew E (xatom (3 + j)) = nth j (map (YK11.getr regs) pi_saved_regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite fsw_ew_xatom, (XR j Hj).
  do 13 (destruct j as [|j]; [reflexivity|]). lia. }
pose proof (fsw_region_nth E pi_ssB0 _ 0 (fstk_ret 144 pi_cs) HST eq_refl) as RF0.
change (ms_mem (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84f5c) mem' (seg_rom tfibsegs))))
  with (mrestrict (w_H W') mem') in RF0.
unfold fstk_ret in RF0.
pose proof (fsw_region_nth E pi_ssB0 _ 4 pi_vR HST eq_refl) as RV.
change (ms_mem (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84f5c) mem' (seg_rom tfibsegs))))
  with (mrestrict (w_H W') mem') in RV.
unfold pi_vR in RV.
assert (HF0 : pib_frame0 (mrestrict (w_H W') mem') (spZ regs) (map (YK11.getr regs) pi_saved_regs)).
{ unfold pib_frame0. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  assert (Hj13 : (j < 13)%nat) by lia.
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs - 144 + (136 - 8 * Z.of_nat j)) by lia.
  apply (fsw_field E _ 2 (spZ regs - 144) pi_cs 0 144 0 144 (136 - 8 * Z.of_nat j) 8%N (SOff (xatom (3 + j)) 0) _
    RF0 E2).
  - unfold pi_cs. destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]; cbn [Z.of_nat]; try lia; cbn [In]; tauto.
  - rewrite fsw_SOff0, (XR' j Hj13). symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (u64_range (nth j (map (YK11.getr regs) pi_saved_regs) (Z_to_bv 64 0))) as Hu.
    first [exact Hu | (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hu) | (cbn [Z.of_N Z.mul]; lia)].
  - cbn. lia. }
assert (VV0 : val_mem tfibsegs (mrestrict (w_H W') mem') v 4 6).
{ pose proof (fsw_field E _ 19 v _ 0 56 0 56 0 4%N (SLit 6) 6 RV E19 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0. }
assert (VV8 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 8) 8 0)
  by exact (fsw_field E _ 19 v _ 0 56 0 56 8 8%N (SLit 0) 0 RV E19 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)).
assert (VV16 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 16) 8 0)
  by exact (fsw_field E _ 19 v _ 0 56 0 56 16 8%N (SLit 0) 0 RV E19 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)).
assert (VV24 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 24) 8 0)
  by exact (fsw_field E _ 19 v _ 0 56 0 56 24 8%N (SOff (xatom 16) 0) 0 RV E19 ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; unfold E; rewrite fsw_ew_xatom; exact X16) ltac:(cbn; lia) ltac:(cbn; lia)).
assert (VV32 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 32) 8 0)
  by exact (fsw_field E _ 19 v _ 0 56 0 56 32 8%N (SOff (xatom 17) 0) 0 RV E19 ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; unfold E; rewrite fsw_ew_xatom; exact X17) ltac:(cbn; lia) ltac:(cbn; lia)).
assert (VV40 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 40) 8 0)
  by exact (fsw_field E _ 19 v _ 0 56 0 56 40 8%N (SOff (xatom 18) 0) 0 RV E19 ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; unfold E; rewrite fsw_ew_xatom; exact X18) ltac:(cbn; lia) ltac:(cbn; lia)).
assert (VV48 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 48) 8 0)
  by exact (fsw_field E _ 19 v _ 0 56 0 56 48 8%N (SOff (xatom 19) 0) 0 RV E19 ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; unfold E; rewrite fsw_ew_xatom; exact X19) ltac:(cbn; lia) ltac:(cbn; lia)).
(* ---- stage B's member arm: the byte is the key's opening quote 0x22, the grow call ---- *)
apply (pi_stageB_member_ro SK B ly S W (unpoison U mem) md [] ly' S' U W' regs regs' mem' md' (STK + (ot - spZ regs))
  ot (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) 0 q v (p + 1 + Z.of_nat (length ws)) (text + len) (Z.of_nat k + 1)
  0 0 0 0 34 Qc HST HJ1 HARU1 G2 ltac:(lia) ltac:(lia) G8 G9 G18 G19 G25 G26 G27
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBV).
- (* struct pj_in on the stack *)
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly' S' U W' mem' md' (w_H W') q 24 HARU1 ltac:(lia) ltac:(lia))).
  exact (pi_RA_stack B ly' S' W' (unpoison U mem') md' q 24 HAR1 ltac:(lia) ltac:(lia) Hq8 ltac:(reflexivity) ltac:(lia)).
- exact (pim_ra_v B _ ot ly S U W mem md [] ly' S' U W' mem' md' 0 v HJ1 HARU0 HARU1 HHEADS HH1 HPO0).
- apply (fsw_block_body_addressable B ly' S' U W' mem' md' _ _ (p + 1 + Z.of_nat (length ws)) 1 HARU1 HH1 HinT1);
    unfold HEAD in *; lia.
- exact (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR HPO0).
- intros a Ha. apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR HinT). lia.
- exact Hvimg.
- lia.
- lia.
- lia.
- lia.
- lia.
- intros a Ha. exact (pim_v_awr B _ ot ly S U W mem md [] ly' S' W' (unpoison U mem') md' 0 v _ ot a HJ1 HARU0 HPO0
    ltac:(unfold in_zr; cbn [fst snd]; lia)).
- (* ---- at grow: the invariant pib_IG [] ---- *)
  intros regsC memC mat R1 Rsp R10 R8' R9' R18' R19' R20 R23 R25' R26' R27' RF FRm FRall MG HJ2 HARU2.
  assert (EM : memC = mem').
  { apply functional_extensionality. intros w. pose proof (FRall (bv_unsigned w) (u64_range w)) as Hw.
    rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
  subst memC.
  rewrite Forall_forall in RF.
  pose proof (RF 3%bv ltac:(cbn; tauto)) as RC3. pose proof (RF 4%bv ltac:(cbn; tauto)) as RC4.
  pose proof (RF 21%bv ltac:(cbn; tauto)) as RC21.
  (* the registers *)
  assert (HRP0 : RP regsC pib_R0).
  { unfold pib_regsP.
    split; [exact Rsp|]. split; [exact R9'|]. split; [exact R19'|].
    split; [rewrite RC3, G3; exact Hgp|]. split; [rewrite RC4, G4; exact Htp|].
    set (EC := Ereg regsC fs_extraT).
    assert (EC9 : ew EC 9 = Z_to_bv 64 q)
      by (unfold EC; rewrite (ew_Ereg_nat regsC fs_extraT 9 9%bv eq_refl); exact R9').
    assert (EC32 : ew EC 32 = Z_to_bv 64 SHADOW_OFF)
      by (unfold EC; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
    unfold pib_R0.
    apply Forall_cons; [cbn [fst snd]; rewrite R8'; symmetry; apply pin_den_off; [exact EC9 | lia | lia]|].
    apply Forall_cons; [cbn [fst snd]; rewrite R18'; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite R20; symmetry; apply pin_den_off; [exact EC9 | lia | lia]|].
    apply Forall_cons.
    { cbn [fst snd]. rewrite RC21, G21.
      first [ reflexivity
            | (unfold w64; apply bv_eq; rewrite unsigned_lit_small by lia; symmetry;
               change (bv_unsigned (sv_denot EC (SLit 18446744073709551615)))
                 with (YP0e.U EC (SLit 18446744073709551615));
               rewrite U_lit by lia; reflexivity) ]. }
    apply Forall_cons; [cbn [fst snd]; rewrite R23; unfold w64; symmetry;
      apply pil_shx_denot; [exact EC9 | exact EC32 | lia | lia | lia]|].
    apply Forall_cons; [cbn [fst snd]; rewrite R25'; unfold w64; symmetry;
      apply pil_shx_denot; [exact EC9 | exact EC32 | lia | lia | lia]|].
    apply Forall_cons; [cbn [fst snd]; rewrite R26', fsw_SOff0, EC32; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite R27'; unfold w64; symmetry;
      rewrite (pil_shx_denot EC 9 q 0 EC9 EC32) by lia; rewrite Z.add_0_r; reflexivity|].
    apply Forall_nil. }
  (* struct pj_in, the frame chain, the caller's window *)
  assert (HSTKP : STKP ly' U W' mem' chq (p + 1 + Z.of_nat (length ws))).
  { unfold pib_stack. cbv zeta.
    split.
    { apply (pis_chain_kept ly ly' _ _ (spZ regs) q (ly_top ly) chq HCH HCHF eq_refl Etop1).
      intros a Ha Hq. destruct (Z_lt_le_dec a ot) as [Hao|Hao].
      - destruct (HWK1 a ltac:(lia) Hq) as (Ma & _).
        rewrite (fsw_aview_unpoison_high B ly' S' U W' mem' md' a HARU1 ltac:(lia)),
          (fsw_aview_unpoison_high B ly S U W mem md a HARU0 ltac:(lia)).
        unfold aview. rewrite Ma. reflexivity.
      - pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & HJ9 & _). apply HJ9; lia. }
    split; [exact HCHF|]. split; [exact Etop1|]. split; [exact QIN | exact HWK1]. }
  (* the blocks: none yet *)
  assert (HBLK : BLK ly' S' U W' mem' [] [] [] peak).
  { unfold pib_blocks.
    split; [exact QTX|].
    split; [exact (pim_pobj_mk B _ ot ly S U W mem md [] ly' S' U W' mem' md' 0 v HJ1 HARU0 HARU1 HHEADS HH1 HPO0 VW1)|].
    split; [intros a0 k0 Hin; destruct Hin|].
    split; [rewrite QAB; cbn [rd_hblocks map]; rewrite app_nil_r; apply Permutation_refl|].
    split; [cbn [rd_heads map]; rewrite app_nil_r; reflexivity|].
    split; [apply Permutation_refl|].
    split; [reflexivity|].
    split; [apply le_n|].
    split; [|lia].
    cbn [PjGrammar.held length]. change (Z.of_nat 0) with 0.
    replace (live + 0) with live by lia. replace (cnt + 0) with cnt by lia. exact QGL. }
  (* v: type 6, no member yet *)
  assert (HHDR : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 0 0 0 0 0 0).
  { unfold PjStruct.pj_hdr.
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + unfold PjStruct.pj_rw. split; [exact Hv8|]. split; [lia|]. split; [lia|].
      intros a Ha. split.
      * pose proof (VW1 (a - v) ltac:(lia)) as HW. replace (v + (a - v)) with a in HW by lia. exact HW.
      * exact (VD1 a Ha).
    + split; [lia|]. apply fsw_pj_word4_iff; first [lia | exact VV0 | (rewrite Z.add_0_r; exact VV0)].
    + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV8 | lia | lia | lia].
    + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV16 | lia | lia | lia].
    + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV24 | lia | lia | lia].
    + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV32 | lia | lia | lia].
    + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV40 | lia | lia | lia].
    + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV48 | lia | lia | lia]. }
  assert (HL0 : parse_items_shape.pis_slots true 0 0 0 ++ [] = []) by reflexivity.
  assert (HOBJ : OBJ W' mem' [] 0 0 0 0 [] []).
  { unfold pib_obj. split; [exact HHDR|].
    unfold parse_items_shape.pis_open. rewrite HL0.
    split; [constructor|].
    split; [intros b0 y Hin; destruct Hin|].
    split; [exact HHDR|].
    split.
    { unfold PjStruct.pj_slots_at. split; [right; reflexivity|]. split; [cbn [length Z.of_nat]; lia|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|]. intros H0; lia. }
    split; [intros _; reflexivity|].
    unfold parse_items_shape.pis_items. split; [reflexivity | exact eq_refl]. }
  (* the invariant *)
  apply (KIG [] ly' S' U W' mem' _ regsC chq (p + 1 + Z.of_nat (length ws)) 0 0 0 [] [] peak).
  unfold pib_IG. cbv zeta. rewrite HL0.
  split; [exact Hms|].
  split; [rewrite Hms, PjRoundTrip.tt_obj; reflexivity|].
  split; [exact (le_n 0)|].
  split; [lia|].
  split; [unfold pib_jc; split; [exact HJ2|]; split; [exact HARU2|]; split; [exact HRO1 | exact HH1]|].
  split; [exact R1|]. split; [exact R10|].
  split; [exact HRP0|].
  split; [exact HF0|].
  split; [exact HSTKP|].
  split; [exact HR1|].
  split; [exact HBLK | exact HOBJ].
Qed.
End I.
