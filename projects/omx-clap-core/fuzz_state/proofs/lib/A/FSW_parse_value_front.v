(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v; 249 of its 299 lines of code are new or changed and 2636 lines of the source are left out. *)
(* parse_value 0x82f9c on fs.asan: the FRONT of the walk, the entry -> the arm entry (0x831b0 for a string, 0x831a0 for
   an object): pv_seg0, pv_sm, pv_seg1, pv_loop, pv_disp of FSH_parse_value.v composed, with the entry data carried to
   the resume memory by FSH_parse_value.pv_front_keep / pv_front_keep_blk. Kept apart from FSH_parse_value.v because it
   is the slow part of the build (about 10 minutes on a build machine). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_ret FSH_Fn_reader FSW_rd
FSW_parse_value_tbl FSH_Fn_entry FSH_parse_value FSH_Fn_alloc FSW_K3 FSW_parse_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
Import ListNotations.
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Local Set Warnings "-abstract-large-number".
Section FR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* the integrator's narrowing rule (a Theorem Labs lane 12:0xZ): exactly FsRt's class-0 field, not the record *)
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\
  FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
(* the image facts (FSH_Rt.v, the reader statements' Section hypothesis; FSImgFacts.fs_img_facts_TfibB for TfibB) *)
Hypothesis IMG : fs_img_facts tfibsegs B.

(* parse_value's entry 0x82f9c -> the arm entry (0x831b0 for byte 34, 0x831a0 for byte 123): the prologue, the
   class-0 grant, the frame header, the white-space loop over ws and the dispatch. *)
Lemma pv_front : forall k ly S U (W : world tfibsegs) regs mem md ch q ot v text len p (tb : list byte) tcap
    (ws : list Z) b0 (rest : list Z) live peak cnt fail (Q : world tfibsegs -> config -> Prop),
  (k <= 2)%nat ->
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  YK11.getr regs 10%bv = w64 q -> YK11.getr regs 11%bv = w64 v ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = ws ++ b0 :: rest ->
  Forall (fun c => PjGrammar.ws c = true) ws ->
  b0 = 34 \/ b0 = 123 ->
  (* the entry data the arms carry (pv_arm_data, pv_arm_pobj) *)
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v -> pobj tfibsegs B ly S W mem v ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall ms' mdx' S2 pos,
     In (0, pos) (frames S2) -> frames S2 = (0, pos) :: frames S ->
     ablocks B ly S2 = ablocks B ly S -> st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     (b0 = 34 /\ ms' = mkst (ms_regs ms') (Z_to_bv 64 0x831b0) (ms_mem ms') (seg_rom tfibsegs) \/
      b0 = 123 /\ ms' = mkst (ms_regs ms') (Z_to_bv 64 0x831a0) (ms_mem ms') (seg_rom tfibsegs)) ->
     YK11.getr (ms_regs ms') 8%bv = Z_to_bv 64 (spZ regs) ->
     YK11.getr (ms_regs ms') 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
     YK11.getr (ms_regs ms') 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr (ms_regs ms') 19%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs ms') 20%bv = Z_to_bv 64 q ->
     YK11.getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF ->
     YK11.getr (ms_regs ms') 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
     YK11.getr (ms_regs ms') 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr (ms_regs ms') 3%bv = YK11.getr regs 3%bv ->
     YK11.getr (ms_regs ms') 4%bv = YK11.getr regs 4%bv ->
     YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) q 8 (p + Z.of_nat (length ws)) ->
     pv_inv (mrestrict (w_H W) (ms_mem ms')) regs (spZ regs) (frame_addr ly 0 pos) (flag_addr ly 0 pos) q
       (text + len) (p + Z.of_nat (length ws)) [b0] ->
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
       (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (* the entry data at the arm memory (FSH_parse_value.pv_arm_data / pv_arm_pobj) *)
     wkeep tfibsegs W W mem (ms_mem ms') (spZ regs) ot q 24 ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem ms')) q text len (p + Z.of_nat (length ws)) (Z.of_nat k) tb ->
     rd_text tfibsegs B ly S2 W (ms_mem ms') text len tcap ->
     pobj tfibsegs B ly S2 W (ms_mem ms') v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) (ms_mem ms')) v ->
     fs_glob tfibsegs W (ms_mem ms') live peak cnt fail ->
     (* the raw stack above s kept but in->p's word (the frame chains' agreement, FSW_parse_value_str.pv_arm_chains) *)
     (forall a, spZ regs <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
        mrestrict (w_H W) (ms_mem ms') (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_value regs mem md) Q.
Proof.
intros k ly S U W regs mem md ch q ot v text len p tb tcap ws b0 rest live peak cnt fail Q Hk HPRE HHEADS HFRL H10
  H11 HIN HWIN HTX HREST HWS Hb0 HZo HPo HGL K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the two constants as equations, so lia never needs `unfold ... in *` (which traverses the large symbolic states in
   the context: the first green of this lemma took 22 minutes that way) *)
assert (ESH : SHADOW_OFF = 2147450880) by reflexivity.
assert (EHD : HEAD = 16) by reflexivity.
pose proof HPRE as (HPREU & HRO). pose proof HPREU as (HAPRE & _ & _). pose proof HAPRE as (HAR & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HS0).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Ht0 & (Hp1 & Hp2) & Hend & Hqtx & Hlen & Hq8 & Hd).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
(* the text bytes at in->p: the white-space run and the first byte of the value's text *)
pose proof (pv_text_of_tb tb text len p (Z.of_nat k) q _ (ws ++ [b0]) rest HIN
  ltac:(rewrite HREST, <- app_assoc; reflexivity)) as HTXT.
assert (Hwslen : p + Z.of_nat (length ws) + 1 <= text + len).
{ assert (HL : (length (ws ++ [b0]) <= length (ReaderRes.rest_at tb text p))%nat).
  { rewrite HREST, !length_app. cbn [length]. lia. }
  unfold ReaderRes.rest_at, ReaderRes.zb in HL. rewrite length_map, length_skipn, length_app in HL.
  cbn [length] in HL. lia. }
destruct (HTXT 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as (Hc0r & Vc0).
set (c0 := nth 0 (ws ++ [b0]) 0) in Hc0r, Vc0.
rewrite Z.add_0_r in Vc0.
(* segment 0: the prologue up to the grant *)
apply (pv_seg0 B HGOT HCELL HGUAR HUCELL k ly S U W regs mem md ch
  ([(v, v + 56)] ++ FS_PSTAT_FP) ot Q Hk HPREU ltac:(lia) Hot16 Hotly Hpot).
intros ms mat HS HJ HARU HF HFr.
(* the registers at the grant's call site *)
destruct (pv_sm_site B ly S U W regs mem md ch k ms Hk HPREU HS)
  as (R2 & R9 & Fsp1 & Fal & R1 & R10m & R3m & R4m & R8m & R23m & R19m & R20m).
(* the grant *)
apply (pv_sm B SM0 errno_low ML SMP k ly S U W regs mem md ch
  ([(v, v + 56)] ++ FS_PSTAT_FP) ot ms mat Q Hk HPREU HFRL ltac:(lia) Hot16 HS HJ HARU).
intros S2 regs2 mem2 md2 pos HS2 HJ2 HARU2 HPRES R10g HBL HFRS HNIN HNEV HBB HZS HKEPT.
(* the registers the grant keeps *)
assert (P23 : YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres (ms_regs ms) regs2 23%bv HPRES ltac:(pv_cs)); exact R23m).
assert (P20 : YK11.getr regs2 20%bv = Z_to_bv 64 q).
{ rewrite (fsw_pres (ms_regs ms) regs2 20%bv HPRES ltac:(pv_cs)), R20m. exact H10. }
assert (P8 : YK11.getr regs2 8%bv = Z_to_bv 64 (spZ regs)).
{ rewrite (fsw_pres (ms_regs ms) regs2 8%bv HPRES ltac:(pv_cs)), R8m. unfold spZ. symmetry.
  apply Z_to_bv_bv_unsigned. }
assert (P9 : YK11.getr regs2 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)))
  by (rewrite (fsw_pres (ms_regs ms) regs2 9%bv HPRES ltac:(pv_cs)); exact R9).
assert (P19 : YK11.getr regs2 19%bv = Z_to_bv 64 v).
{ rewrite (fsw_pres (ms_regs ms) regs2 19%bv HPRES ltac:(pv_cs)), R19m. exact H11. }
assert (P3 : YK11.getr regs2 3%bv = YK11.getr regs 3%bv)
  by (rewrite (fsw_pres (ms_regs ms) regs2 3%bv HPRES ltac:(pv_cs)); exact R3m).
assert (P4 : YK11.getr regs2 4%bv = YK11.getr regs 4%bv)
  by (rewrite (fsw_pres (ms_regs ms) regs2 4%bv HPRES ltac:(pv_cs)); exact R4m).
assert (P2 : YK11.getr regs2 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)))
  by (rewrite (fsw_pres (ms_regs ms) regs2 2%bv HPRES ltac:(pv_cs)); exact R2).
(* the bytes the front does not write keep their entry value: the prologue's frame [sp - 160, sp) and the grant's
   fake-stack window are the only writes, and every byte the walk reads here is at or above alloc_ceiling *)
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (HWIN0 : forall x, in_wrange (Ereg regs fs_extraT) (ss_mem pv_ss0) x -> spZ regs - 160 <= x < spZ regs).
{ intros x (r & Hin & Hr).
  cbv [pv_ss0 fss0T_args ss_mem fsT_regions_args fsT_regions fs_uar_regions app] in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [fstk fs_got_region fs_bcell_region fs_got_uar_region fs_uar_cell_region
         YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp in Hr; lia. }
(* the bytes the front does not write keep their entry value *)
assert (KEEP0 : forall a, alloc_ceiling <= a < 2 ^ 64 ->
  ~ (32 * ((spZ regs - 160) / 32) - ESTACK <= a < 32 * ((spZ regs - 160) / 32)) ->
  ~ (spZ regs - 160 <= a < spZ regs) ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha Hs Hl.
  exact (pv_front_keep B ly S ly S2 U W mem (ms_mem ms) mem2 _ md2 (Ereg regs fs_extraT)
    (32 * ((spZ regs - 160) / 32) - ESTACK) (32 * ((spZ regs - 160) / 32)) (spZ regs - 160) (spZ regs) a
    HFr HWIN0 HKEPT HARU HARU2 Ha Hs Hl). }
(* the layout bounds astk_ok gives at the entry *)
pose proof HAPRE as (_ & _ & _ & _ & _ & Hstk2 & _).
pose proof Hstk2 as (Hal16' & Hstk0' & Hceil' & Hslo' & Hshi' & H47' & Hbot' & Htop' & Htop2').
pose proof (pv_stk k Hk) as FS.
(* no `set` abbreviation for the entry sp or the re-aligned sp: lia treats a local definition as a fresh atom, so the
   facts and the goals must name the same expression *)
(* the three words of struct pj_in and the text byte, carried to the resume memory *)
assert (Vq0 : val_mem tfibsegs (mrestrict (w_H W) mem2) q 8 p).
{ destruct HIN as (Hbp & _).
  pose proof (KindBGlue.bytes_at_le8_word tfibsegs (mrestrict (w_H W) mem) q (Z_to_bv 64 p) Hbp) as Hw.
  rewrite (unsigned_lit_small p ltac:(lia)) in Hw.
  apply (proj2 (val_mem_word_mem tfibsegs (mrestrict (w_H W) mem2) q p)).
  apply (KindBGlue.word_mem_frame tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) q p Hw).
  intros j Hj. apply KEEP0; lia. }
assert (Vq8 : val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 8) 8 (text + len)).
{ destruct HIN as (_ & Hbe & _).
  pose proof (KindBGlue.bytes_at_le8_word tfibsegs (mrestrict (w_H W) mem) (q + 8) (Z_to_bv 64 (text + len)) Hbe) as Hw.
  rewrite (unsigned_lit_small (text + len) ltac:(lia)) in Hw.
  apply (proj2 (val_mem_word_mem tfibsegs (mrestrict (w_H W) mem2) (q + 8) (text + len))).
  apply (KindBGlue.word_mem_frame tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) (q + 8) (text + len) Hw).
  intros j Hj. apply KEEP0; lia. }
pose proof Htxblk as (HinT & _).
pose proof (ARU_AR tfibsegs B ly S U W (ms_mem ms) _ HARU) as HAR1.
assert (KEEPT : forall j, 0 <= j < tcap -> mbyte tfibsegs (mrestrict (w_H W) mem2) (text + j)
  = mbyte tfibsegs (mrestrict (w_H W) mem) (text + j)).
{ intros j Hj.
  pose proof (fsw_ablock_low B ly S W (unpoison U (ms_mem ms)) _ _ _ HAR1 HinT) as (Hb4096 & Hbceil & Hreq).
  replace (text + j) with (text - HEAD + (HEAD + j)) by (unfold HEAD; lia).
  exact (pv_front_keep_blk B ly S ly S2 U W mem (ms_mem ms) mem2 _ _ md2 (Ereg regs fs_extraT)
    (32 * ((spZ regs - 160) / 32) - ESTACK) (32 * ((spZ regs - 160) / 32)) (spZ regs - 160) (spZ regs)
    (text - HEAD) (tcap + HEAD) (HEAD + j)
    HAR1 HFr HWIN0 ltac:(lia) HKEPT HARU HARU2 HinT ltac:(lia)). }
pose proof (Vc0 0%nat ltac:(cbn; lia)) as Vc0'.
cbn [Z.of_nat] in Vc0'. rewrite Z.add_0_r in Vc0'.
assert (Vc02 : val_mem tfibsegs (mrestrict (w_H W) mem2) p 1 c0).
{ intros j Hj. assert (j = 0%nat) by lia. subst j. cbn [Z.of_nat]. rewrite Z.add_0_r.
  replace p with (text + (p - text)) by lia. rewrite KEEPT by lia.
  replace (text + (p - text)) with p by lia. exact Vc0'. }
(* the frame (0, pos) of the resume state, and the text block apart from it *)
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite HFRS; left; reflexivity).
assert (HinT2 : In (text - HEAD, tcap + HEAD) (ablocks B ly S2)) by (rewrite HBL; exact HinT).
pose proof (sep_block_frame tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 (text - HEAD) (tcap + HEAD) 0 pos
  HAR2 HinT2 Hin0) as Hdbf.
unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes 0) with 64 in Hdbf.
assert (Hrq : tcap + HEAD <= req_size (tcap + HEAD))
  by (unfold req_size; destruct (Z.eqb_spec (tcap + HEAD) 0); lia).
pose proof (fsw_ablock_off_shadow B ly S2 W (unpoison U mem2) md2 _ _ HAR2 HinT2 p
  ltac:(lia)) as Hpsh.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in HF4096, HFc.
destruct (al_flag _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (_ & _ & HFLapp & HFLc).
unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFLapp.
(* segment 1: the frame header and the loop head *)
assert (HF8 : 512 <= frame_addr ly 0 pos / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
apply (pv_seg1 B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S S2 U W regs mem md
  regs2 mem2 md2 pos (spZ regs) (32 * ((spZ regs - 160) / 32)) v q p (text + len) c0 Q
  (HS2 (pv_xs (SHADOW_OFF + frame_addr ly 0 pos / 8) p (text + len) c0)) HJ2 HARU2 Hin0 R10g P23 P20 P8 P9 P19 P3 P4
  P2);
  try lia; [exact Vq0 | exact Vq8 | exact Vc02 |].
intros msh math HSh HJh HARUh KEEPh Q8 Q9 Q18 Q19 Q20 Q23 Q24 Q26 QG3 QG4 QSP.
(* the text bytes at the loop head: kept from the entry memory through the grant and segment 1 *)
assert (KEEPTX : forall j, (j < length (ws ++ [b0]))%nat ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem msh)) (p + Z.of_nat j)
  = mbyte tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat j)).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  pose proof (fsw_ablock_off_shadow B ly S2 W (unpoison U mem2) md2 _ _ HAR2 HinT2 (p + Z.of_nat j)
    ltac:(lia)) as Hjsh.
  transitivity (mbyte tfibsegs (mrestrict (w_H W) mem2) (p + Z.of_nat j)).
  - unfold mbyte. rewrite (KEEPh (Z_to_bv 64 (p + Z.of_nat j))); [reflexivity|].
    rewrite (wz (p + Z.of_nat j) ltac:(lia)).
    unfold pv_wr. lia.
  - replace (p + Z.of_nat j) with (text + (p - text + Z.of_nat j)) by lia.
    apply KEEPT. lia. }
assert (HTXTh : pv_text (mrestrict (w_H W) (ms_mem msh)) p (ws ++ [b0])).
{ intros j Hj. destruct (HTXT j Hj) as (Hr & Hv). split; [exact Hr|].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (KEEPTX j Hj).
  pose proof (Hv 0%nat ltac:(cbn; lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0. exact Hv0. }
(* the loop head's memory package, read off pv_hd's regions *)
set (Eh := Ereg (ms_regs msh) (pv_extra0 regs (flag_addr ly 0 pos) ++
  pv_xs (SHADOW_OFF + frame_addr ly 0 pos / 8) p (text + len) c0)) in HSh.
assert (EAh : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> YK11.getr (ms_regs msh) r = Z_to_bv 64 z ->
  0 <= z < 2 ^ 64 -> bv_unsigned (ew Eh n) = z)
  by (intros r n z Hn Hr Hz; subst Eh; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; lia).
assert (G20 : bv_unsigned (ew Eh 20) = q) by (apply (EAh 20%bv); [reflexivity | exact Q20 | lia]).
assert (G26 : bv_unsigned (ew Eh 26) = frame_addr ly 0 pos)
  by (apply (EAh 26%bv); [reflexivity | exact Q26 | lia]).
assert (G8 : bv_unsigned (ew Eh 8) = spZ regs) by (apply (EAh 8%bv); [reflexivity | exact Q8 | lia]).
assert (G48 : ew Eh 48 = Z_to_bv 64 p)
  by (subst Eh; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (G49 : ew Eh 49 = Z_to_bv 64 (text + len))
  by (subst Eh; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (G46 : ew Eh 46 = Z_to_bv 64 (flag_addr ly 0 pos)).
{ subst Eh. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
  rewrite app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. reflexivity. }
pv_region HSh 0%nat RQh. cbn [ms_mem restrict] in RQh.
pv_region HSh 2%nat RSh. cbn [ms_mem restrict] in RSh.
pv_region HSh 3%nat RFh. cbn [ms_mem restrict] in RFh.
assert (VQ0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msh)) q 8 p).
{ pose proof (fsw_field _ _ 20 q _ 0 24 0 8 0 8 (SOff 48 0) p RQh G20 ltac:(left; reflexivity)
    ltac:(rewrite fsw_SOff0; exact G48) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V. }
assert (VQ8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msh)) (q + 8) 8 (text + len)).
{ exact (fsw_field _ _ 20 q _ 0 24 0 8 8 8 (SOff 49 0) (text + len) RQh G20 ltac:(right; left; reflexivity)
    ltac:(rewrite fsw_SOff0; exact G49) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (VFL : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msh)) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos)).
{ exact (fsw_field _ _ 26 (frame_addr ly 0 pos) _ 56 64 0 0 56 8 (SOff 46 0) (flag_addr ly 0 pos) RFh G26
    ltac:(left; reflexivity) ltac:(rewrite fsw_SOff0; exact G46) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (WQ : forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem msh)) (q + o)).
{ intros o Ho. destruct RQh as (_ & _ & Hw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  rewrite G20 in Hw. apply Hw. lia. }
assert (VSV : pv_saved_ok (mrestrict (w_H W) (ms_mem msh)) (spZ regs) regs)
  by (exact (pv_saved_of_region (ms_regs msh) regs (flag_addr ly 0 pos) _ _ (spZ regs) _ _ _ _ RSh G8)).
(* the white-space loop, then the dispatch *)
assert (HWSB : Forall pv_wsb ws) by (apply (Forall_impl _ pv_ws_wsb HWS)).
assert (HHEADS2 : FSupoisonU.fs_heads B ly S2 U).
{ intros r Hr. destruct (HHEADS r Hr) as (H1 & m & H2 & H3). split; [exact H1|]. exists m. rewrite HBL. auto. }
assert (HRA : range_addressable (aview tfibsegs (w_H W) (ms_mem msh)) SHADOW_OFF p (Z.of_nat (length ws) + 1)).
{ apply (fsw_block_body_addressable B ly S2 U W (ms_mem msh) _ (text - HEAD) (tcap + HEAD) p
    (Z.of_nat (length ws) + 1) HARUh HHEADS2 ltac:(rewrite HBL; exact HinT));
    lia. }
destruct (al_blocks tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 _ _ HAR2 HinT2)
  as (_ & _ & _ & Happ & _ & _ & _).
unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Happ.
assert (HB1 : text + len <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= p)
  by lia.
assert (HB2 : text + len <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= p + Z.of_nat (length ws))
  by lia.
apply (pv_loop B ws (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S S2 U W mem md
  regs pos q (spZ regs) (32 * ((spZ regs - 160) / 32)) v (text + len) p b0 msh _ Q Hin0);
  try lia; try assumption.
- split; [exact HSh|]. split; [exact VQ0|].
  split; [split; [exact VSV|]; split; [exact VFL|]; split; [exact VQ8|]; split; [exact WQ | exact HTXTh]|].
  split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|].
  split; [exact Q23|]. split; [exact Q24|]. split; [exact Q26|]. split; [exact QG3|]. split; [exact QG4 | exact QSP].
- intros msd mdd HATd HJd HARUd HRAd KEEPd.
  apply (pv_disp B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S S2 U W mem md
    regs pos q (spZ regs) (32 * ((spZ regs - 160) / 32)) v (text + len) (p + Z.of_nat (length ws)) b0 msd mdd Q
    Hin0); try lia; try assumption.
  intros msa mda pca Harm Hshape A8 A9 A18 A19 A20 A23 A24 A26 AG3 AG4 ASP VQa HINVa HJa HARUa KEEPa.
  (* the entry data carried to the arm memory: the front's keeps, then pv_arm_data / pv_arm_pobj *)
  pose proof HINVa as (_ & _ & _ & WQa & _).
  pose proof (conj HFr (conj HWIN0 (conj HKEPT (conj HARU (conj HARU2 (conj KEEPh (conj KEEPd KEEPa)))))))
    as HKC.
  destruct (pv_arm_data B ly S S2 U W mem (ms_mem ms) mem2 (ms_mem msh) (ms_mem msd) (ms_mem msa) md _ md2
    (Ereg regs fs_extraT) pos (spZ regs) (32 * ((spZ regs - 160) / 32)) q ot v text len p (p + Z.of_nat (length ws))
    (Z.of_nat k) tb tcap live peak cnt fail HAR IMG HAR2 HFRS HBL HHEADS HKC ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) HIN HTX HZo HPo HGL VQa WQa ltac:(lia)) as (AWK & AIN & ATX & AZo & AGL).
  pose proof (pv_arm_pobj B ly S S2 U W mem (ms_mem ms) mem2 (ms_mem msh) (ms_mem msd) (ms_mem msa) md _ md2 mda
    (Ereg regs fs_extraT) pos (spZ regs) (32 * ((spZ regs - 160) / 32)) q v HAR HAR2 HFRS HBL HHEADS HKC
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HARUa HPo) as APo.
  assert (AGR : forall a, spZ regs <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
    mrestrict (w_H W) (ms_mem msa) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
  { intros a Ha Hq.
    exact (pv_arm_stk B ly S S2 U W mem (ms_mem ms) mem2 (ms_mem msh) (ms_mem msd) (ms_mem msa) _ md2
      (Ereg regs fs_extraT) pos (spZ regs) (32 * ((spZ regs - 160) / 32)) q a HAR2 HFRS HBL HHEADS HKC
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ha Hq). }
  apply (K msa mda S2 pos Hin0 HFRS HBL HNEV HBB); try assumption.
  destruct Harm as [(Hb & Hpc)|(Hb & Hpc)]; [left | right]; split; try assumption; rewrite <- Hpc; exact Hshape.
Qed.
End FR.
