(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) composition of the parse_items walk against
   lib/B/FSH_Fn_reader.parse_items_spec k (k = 0..1).
   THIS FILE SO FAR: the EMPTY-object instance (ms = []), the one complete machine path with a single callee, skip_ws:
   FSW_parse_items_sw.pi_sw1 (stage A, skip_ws #1 at 0x84f58 through skip_ws_spec, the resume at 0x84f5c), then
   FSW_parse_items.pi_stageB_close (the byte is `}`: in->p + 1, in->depth - 1, the ret 0x852fc) and FSW_ret.fsw_retU.
   pi_nil states the post with the empty object's numerals (no tick, U kept, in->p + 2, D = []); pi_holds_nil is the
   same in parse_items_spec's own shape (its premises with ms := [] and its post with D = Da = []), as the A walk's
   pitems_spec_nil is, so that the final parse_items_holds applies it for ms = [] without restating anything.
   Section hypotheses: FsShadowSyms B and skip_ws_spec only (no other callee is reached on this path).
   B-LOCAL COPIES of A-kit helpers with no B twin, copied from a working branch 493982bffc9
   proofs/omx-clap-core/fuzz_state/lib/A/FSW_pitems_dev.v (a Theorem Labs lane): pid_nil_tr / pid_nil_ev / pid_nil_held /
   pid_nil_len (renamed pih_nil_tr / pih_nil_ev / pih_nil_held / pih_nil_len) and pid_byte1 (pih_byte1), verbatim.
   parse_items_holds_of: parse_items_holds' final statement (memset contract last) with the two segments other provers
   own as its only open inputs, pib_HVALF (a Theorem Labs lane's piv_val: pib_IE -> pib_IH, 0x85048 .. 0x851d0) and pib_HINITF
   (a Theorem Labs lane's pi_init: the entry to the first grow call with pib_IG []), each stated at every entry of
   parse_items_spec k: ms = [] by pi_holds_nil, ms = m :: ms' by FSW_parse_items_mloop.pi_holds_cons.
   pib_HVALF_of_val discharges pib_HVALF by a Theorem Labs lane's FSW_parse_items_val.piv_val; parse_items_holds_init is the final
   statement with pib_HINITF the one open input; pib_HINITF_of_init discharges it by a Theorem Labs lane's
   FSW_parse_items_init.pi_init, and parse_items_holds is the function theorem.
   rule 24: proves parse_items (parse_items_holds : parse_items_spec k on image B, k <= 1). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem MState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_calls FSW_parse_items_mem FSW_parse_items_sw.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_parse_items_loop FSW_parse_items_mloop
  FSW_parse_items_val FSW_parse_items_init.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the empty object's text and trace (copied, see the header) ================= *)
Lemma pih_nil_tr : PjRoundTrip.ttrace (PjTree.JObj []) = [].
Proof. reflexivity. Qed.
Lemma pih_nil_ev : rd_ev (PjRoundTrip.ttrace (PjTree.JObj [])) = 0.
Proof. rewrite pih_nil_tr. reflexivity. Qed.
Lemma pih_nil_held : PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj [])) = 0.
Proof. rewrite pih_nil_tr. reflexivity. Qed.
Lemma pih_nil_len : Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj []))) = 0.
Proof. rewrite pih_nil_tr. reflexivity. Qed.
(* the empty object's second byte, read out of the spec's text premise *)
Lemma pih_byte1 : forall (tb : list byte) text p rest, text <= p ->
  ReaderRes.rest_at tb text p = [123; 125] ++ rest ->
  exists b, nth_error tb (Z.to_nat (p + 1 - text)) = Some b /\ bv_unsigned b = 125.
Proof.
intros tb text p rest Hp H. unfold ReaderRes.rest_at, ReaderRes.zb in H.
assert (E1 : nth_error (map (fun b : byte => bv_unsigned b) (skipn (Z.to_nat (p - text)) tb)) 1 = Some 125)
  by (rewrite H; reflexivity).
rewrite nth_error_map, nth_error_skipn in E1.
replace (Z.to_nat (p + 1 - text)) with (Z.to_nat (p - text) + 1)%nat by lia.
destruct (nth_error tb (Z.to_nat (p - text) + 1)) as [b|] eqn:Eb; cbn in E1; [|discriminate].
exists b. split; [reflexivity|]. injection E1 as E1. exact E1.
Qed.

Section N. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
(* the shadow-base cells of image B (FSH_Base.v) *)
Hypothesis HSS : FsShadowSyms B.
(* callee: skip_ws (a Theorem Labs lane's B walk, a working branch) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.

(* ---- the empty object: the post with its numerals ---- *)
Theorem pi_nil : forall (k : nat) ly S U (W : world tfibsegs) regs mem md ch q ot v text len p
    (tb : list byte) tcap (rest : list Z) live peak cnt fail,
  (k <= 1)%nat ->
  fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = [123; 125] ++ rest ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md)
    (fun W' c' =>
       fpostU tfibsegs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U
         W mem md 0 U
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + 2) (Z.of_nat k) tb /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks []) /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj []) [] /\
            rd_sum [] = PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj [])) /\
            (length (@nil (Z * Z)) <= length (PjRoundTrip.ttrace (PjTree.JObj [])))%nat /\
            pobj tfibsegs B ly' S' W' mem' v /\
            rd_text tfibsegs B ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob tfibsegs W' mem' (live + PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj []))) peak'
                 (cnt + Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj [])))) fail)) W' c').
Proof.
intros k ly S U W regs mem md ch q ot v text len p tb tcap rest live peak cnt fail
  Hk HPRE HHEADS H10 H11 H12 HIN HWIN HTX HREST HPO HZERO HVSP HVTX HGLOB.
set (STK := STK_parse_items (1 - k)) in *.
set (FP := [(v, v + 56)] ++ FS_PSTAT_FP).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HPREU & HRO).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPREU) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAPRE & _ & _). pose proof HAPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO) as Hvimg.
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof Htxblk as (HinT & _ & _ & _).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md _ _ HAR HinT) as (_ & _ & Hreq).
pose proof (fsw_ablock_off_img B ly S W (unpoison U mem) md _ _ HAR HinT) as Htimg.
assert (HSTKf : FRAME_parse_items = 144) by reflexivity.
assert (HSTK : FRAME_parse_items + STK_skip_ws <= STK)
  by (unfold STK, STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
assert (HSW0 : 0 <= STK_skip_ws) by (vm_compute; discriminate).
assert (HR' : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj []) (true) (Z.of_nat k)) ++ rest)
  by (rewrite pi_obj_nil; exact HREST).
pose proof (pi_p1_lt_end _ q text len p (Z.of_nat k) tb [] true (Z.of_nat k) rest HIN HR') as Hlt.
destruct (pih_byte1 tb text p rest ltac:(lia) HREST) as (b1 & Hb1 & Hb1v).
unfold HEAD in *.
assert (NIMG : forall a, v <= a < v + 56 -> ~ in_img tfibsegs a).
{ intros a Ha. destruct HPO as [[((cid & pos & Hin & Hc & H8 & X1 & X2) & _)|((b & m & Hb & X1 & X2) & _)] _].
  - exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md cid pos a HAR Hin ltac:(lia)).
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR Hb ltac:(unfold HEAD in X1; lia)). }
(* ---- stage A, skip_ws #1 (no white space after `{`), the resume at 0x84f5c ---- *)
apply (pi_sw1 SK B HSS HSW ly S U W regs mem md ch q ot v text len p tb tcap (Z.of_nat k) STK [] (125 :: rest) 125
  live peak cnt fail _ HPRE HHEADS HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO HVSP HVTX ltac:(lia)
  ltac:(rewrite HREST; reflexivity) (Forall_nil _)
  ltac:(intros c r E; injection E as <- _; reflexivity) HGLOB).
intros ly' S' W' regs' mem' md' HST HJ1 HARU1 G2 G3 G4 G8 G9 G18 G19 G25 G26 G27 HIN1 HTX1 HG1 HAB1 HRO1 HKEEP1
  HVW1 HVD1.
assert (EP1 : p + 1 + Z.of_nat (length (@nil Z)) = p + 1) by (cbn [length Z.of_nat]; lia).
rewrite EP1 in HST, HIN1.
pose proof HJ1 as (_ & Hly1 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & Elo1 & Ehi1 & _).
assert (HH1 : FSupoisonU.fs_heads B ly' S' U) by (intros r Hr; rewrite HAB1; exact (HHEADS r Hr)).
pose proof HTX1 as (_ & Htxblk1 & _).
pose proof Htxblk1 as (HinT1 & _ & _ & _).
pose proof (ARU_AR tfibsegs B ly' S' U W' mem' md' HARU1) as HAR1.
(* ---- stage B's close arm: in->p + 1, in->depth - 1, the ret ---- *)
apply (pi_stageB_close SK B ly S W (unpoison U mem) md [] ly' S' U W' regs regs' mem' md' (STK + (ot - spZ regs)) ot
  (spZ regs) FP 0 q v (p + 1) (text + len) (Z.of_nat k + 1) 0 0 0 0 _ HST HJ1 HARU1 G2 eq_refl ltac:(lia) ltac:(lia)
  G3 G4 G8 G9 G18 G19 G25 G26 G27 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
- (* the byte at in->p + 1 is `}` *)
  pose proof (pim_byte_tb _ q text len (p + 1) (Z.of_nat k + 1) tb (p + 1) b1 HIN1 ltac:(lia) Hb1) as V.
  rewrite Hb1v in V. exact V.
- (* struct pj_in on the stack *)
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly' S' U W' mem' md' (w_H W') q 24 HARU1 ltac:(lia) ltac:(lia))).
  exact (pi_RA_stack B ly' S' W' (unpoison U mem') md' q 24 HAR1 ltac:(lia) ltac:(lia) Hq8 ltac:(reflexivity) ltac:(lia)).
- exact (pim_ra_v B _ ot ly S U W mem md [] ly' S' U W' mem' md' 0 v HJ1 HARU0 HARU1 HHEADS HH1 HPO).
- apply (fsw_block_body_addressable B ly' S' U W' mem' md' _ _ (p + 1) 1 HARU1 HH1 HinT1);
    unfold HEAD in *; lia.
- exact (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR HPO).
- intros a Ha. apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR HinT). lia.
- exact Hvimg.
- lia.
- lia.
- lia.
- lia.
- lia.
- intros a Ha. exact (pim_v_awr B _ ot ly S U W mem md [] ly' S' W' (unpoison U mem') md' 0 v _ ot a HJ1 HARU0 HPO
    ltac:(unfold in_zr; cbn [fst snd]; lia)).
- (* the ret *)
  intros Ef ssf msf mat HSf Hrv Hpc RF1 RF10 HPf VQ0 VQ8 VQ16 VV0 VV8 VV16 VV24 VV32 VV40 VV48 FRf MGf HJf HARUf.
  set (mF := ms_mem msf) in *.
  apply (fsw_retU B pitems_tbl pitems_tbl_ok W' Ef ssf msf _ (STK + (ot - spZ regs)) ot FP regs ly S U W mem md ly' S' U 0
    _ HSf Hrv Hpc); [rewrite RF1; exact Hra | exact HJf | exact HARUf | exact HPf |].
  intros mat0. change (ms_mem msf) with mF.
  (* what the close did not write: outside the frame, struct pj_in and v *)
  assert (FRm : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 144 <= x < spZ regs) -> ~ (q <= x < q + 24) ->
    ~ (v <= x < v + 56) -> mrestrict (w_H W') mF (Z_to_bv 64 x) = mrestrict (w_H W') mem' (Z_to_bv 64 x))
    by (intros x Hx X1 X2 X3; unfold mrestrict; rewrite (FRf x Hx X1 X2 X3); reflexivity).
  assert (EQtx : pim_eqon (mrestrict (w_H W') mem') (mrestrict (w_H W') mF) (text - 16) (text + tcap))
    by (intros a Ha; apply FRm; lia).
  assert (VWF : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mF) (v + i))
    by (intros i Hi; apply (writable_at_grows tfibsegs (mrestrict (w_H W') mem')); [exact MGf | exact (HVW1 i Hi)]).
  assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
  pose proof HIN1 as (_ & _ & _ & HWQ & _).
  split; [exact RF10|].
  split.
  { replace (p + 1 + 1) with (p + 2) in VQ0 by lia. replace (Z.of_nat k + 1 - 1) with (Z.of_nat k) in VQ16 by lia.
    apply (pis_in_mk _ (mrestrict (w_H W') mem') q text len (p + 2) (Z.of_nat k) (p + 1) (Z.of_nat k + 1) tb HIN1
      VQ0 VQ8 VQ16).
    - intros i Hi. apply (writable_at_grows tfibsegs (mrestrict (w_H W') mem')); [exact MGf|].
      destruct HWQ as (_ & _ & HWQ3). exact (HWQ3 i Hi).
    - eapply pim_eqon_sub; [exact EQtx | lia | lia].
    - lia.
    - lia. }
  split.
  { intros a Ha Hq. destruct (HKEEP1 a Ha Hq) as (M1 & W1).
    assert (Em : mrestrict (w_H W') mF (Z_to_bv 64 a) = mrestrict (w_H W') mem' (Z_to_bv 64 a)) by (apply FRm; lia).
    rewrite (pim_mb_of_mr _ _ _ _ a Em). split; [exact M1|].
    rewrite W1. apply pim_wr_keep. exact Em. }
  split; [rewrite HAB1; cbn [rd_hblocks map]; rewrite app_nil_r; apply Permutation_refl|].
  split.
  { split; [|split; [intros a kk Hin; destruct Hin | intros x Hx; exact Hx]].
    cbn [PjStruct.pj_node].
    split; [constructor|]. split; [intros bb x Hin Hh; destruct Hin|].
    exists 0, 0, 0, 0, 0, 0.
    split.
    - unfold PjStruct.pj_hdr. cbn [PjTree.tag].
      split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + unfold PjStruct.pj_rw. split; [exact Hv8|]. split; [lia|]. split; [lia|].
        intros a Ha. split.
        * pose proof (VWF (a - v) ltac:(lia)) as HW. replace (v + (a - v)) with a in HW by lia. exact HW.
        * exact (pis_mrd_grows _ _ (Mem.wa a) MGf (HVD1 a Ha)).
      + split; [lia|]. apply fsw_pj_word4_iff; first [lia | exact VV0 | (rewrite Z.add_0_r; exact VV0)].
      + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV8 | lia | lia | lia].
      + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV16 | lia | lia | lia].
      + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV24 | lia | lia | lia].
      + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV32 | lia | lia | lia].
      + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV40 | lia | lia | lia].
      + split; [lia|]. apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact VV48 | lia | lia | lia].
    - cbn [length Z.of_nat]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [left; split; [reflexivity | split; reflexivity]|].
      exists []. split; [reflexivity | reflexivity]. }
  split; [rewrite pih_nil_tr; reflexivity|].
  split; [rewrite pih_nil_tr; cbn [length]; lia|].
  split; [exact (pim_pobj_mk B _ ot ly S U W mem md [] ly' S' U W' mF _ 0 v HJf HARU0 HARUf HHEADS HH1 HPO VWF)|].
  split.
  { split; [unfold HEAD; lia|]. split; [|exact Htxlen].
    destruct Htxblk1 as (TB1 & TB2 & TB3 & TB4). split; [exact TB1|]. split; [exact TB2|]. split; [exact TB3|].
    apply (pim_eqon_val (mrestrict (w_H W') mem') _ _ 8 tcap); [|exact TB4].
    unfold HEAD. eapply pim_eqon_sub; [exact EQtx | lia | cbn; lia]. }
  exists peak. split; [lia|].
  rewrite pih_nil_tr. cbn [PjGrammar.held length]. change (Z.of_nat 0) with 0.
  replace (live + 0) with live by lia. replace (cnt + 0) with cnt by lia.
  apply (pim_glob_eqon W' W' mem' mF live peak cnt fail); [|exact HG1].
  intros a Ha. pose proof (fs_segs_img a (pim_pstat_img a Ha)) as Hlo. unfold FS_IMG_END in Hlo.
  apply FRm; [lia | lia | lia |].
  intros Hv. exact (NIMG a Hv (pim_pstat_img a Ha)).
Qed.

(* ---- the same in parse_items_spec's own shape: the spec's premises verbatim with ms := [], its post with D = Da = []
   (the empty object allocates nothing); the premises the empty path does not read are taken and left unused ---- *)
Theorem pi_holds_nil : forall (k : nat) ly S U (W : world tfibsegs) regs mem md ch q ot v text len p
    (tb : list byte) tcap (pr : bool) (rest : list Z) live peak cnt fail,
  let tr := PjRoundTrip.ttrace (PjTree.JObj []) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj []) pr (Z.of_nat k)) in
  (k <= 1)%nat ->
  fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  spZ regs + 16 <= q -> (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
    Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = wt ++ rest ->
  FSDocStrs.fs_doc_values (PjTree.JObj []) -> FSDocStrs.fs_doc_strings (PjTree.JObj []) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj []) -> (PjTree.depth (PjTree.JObj []) <= 2 - k)%nat ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md)
    (fun W' c' => exists D Da,
       Permutation Da D /\
       fpostU tfibsegs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md
         (rd_ev tr) (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Z.of_nat (length wt)) (Z.of_nat k) tb /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj []) D /\ rd_sum D = PjGrammar.held tr /\
            (length D <= length tr)%nat /\ pobj tfibsegs B ly' S' W' mem' v /\
            rd_text tfibsegs B ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob tfibsegs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').
Proof.
intros k ly S U W regs mem md ch q ot v text len p tb tcap pr rest live peak cnt fail.
cbv zeta.
intros Hk HPRE HHEADS _ H10 H11 H12 HIN HWIN _ _ HTX HREST _ _ _ _ HPO HZERO HVSP HVTX HGLOB _ _ _ _ _.
assert (HW2 : Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj []) pr (Z.of_nat k)))) = 2)
  by (rewrite pi_obj_nil; reflexivity).
assert (HR2 : ReaderRes.rest_at tb text p = [123; 125] ++ rest) by (rewrite HREST, pi_obj_nil; reflexivity).
eapply SRr_mono;
  [ exact (pi_nil k ly S U W regs mem md ch q ot v text len p tb tcap rest live peak cnt fail
             Hk HPRE HHEADS H10 H11 H12 HIN HWIN HTX HR2 HPO HZERO HVSP HVTX HGLOB) |].
intros W' c' _ HQ. exists [], []. split; [apply Permutation_refl|].
rewrite pih_nil_ev, HW2. cbn [rd_heads map]. rewrite app_nil_r.
exact HQ.
Qed.
End N.

(* ================= parse_items_holds' final shape, its two open inputs explicit ================= *)
(* the entry premises of parse_items_spec k (its own list, its order, but (k <= 1) and FsShadowSyms taken outside),
   then the conclusion C *)
Definition pib_entry {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat)
  (C : forall ly S U (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
     (q ot v text len p tcap : Z) (tb : list byte) (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z)
     (live peak cnt fail : Z) (ch : list (Z * Z * Z)), Prop) : Prop :=
  forall ly S U (W : world tfibsegs) regs mem md q ot v text len p tcap (tb : list byte) ms pr rest live peak cnt fail ch,
  fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  rd_win tfibsegs regs ly W mem q ot -> spZ regs + 16 <= q -> rd_text tfibsegs B ly S W mem text len tcap ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb ->
  (v + 56 <= text - HEAD \/ text + tcap <= v) -> pobj tfibsegs B ly S W mem v ->
  quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))) ->
  rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)) ->
  live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64 ->
  st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX ->
  blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest ->
  FSDocStrs.fs_doc_values (PjTree.JObj ms) -> FSDocStrs.fs_doc_strings (PjTree.JObj ms) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms) -> (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  C ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch.
(* a Theorem Labs lane's piv_val (FSW_parse_items_mloop.v Section hypothesis HVAL, at every entry) *)
Definition pib_HVALF {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat) : Prop :=
  @pib_entry fx rc SK B k (fun ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch =>
  forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1 a
    ly' S' (W' : world tfibsegs) regs' mem' md' (Qc : world tfibsegs -> config -> Prop),
  pib_IE B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail dn kk x rm T lyc Sc Uc W1 memC mdC
    regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' ->
  (forall T2 lyc2 Sc2 Uc2 (W2 : world tfibsegs) mem2 md2 regs2 chq2 pc2 Da2 peak2 D Dx ly3 S3 (W3 : world tfibsegs) regs3
     mem3 md3,
     pib_IH B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail dn kk x rm T2 lyc2 Sc2 Uc2 W2
       mem2 md2 regs2 chq2 pc2 kids keys cap Di Da2 peak2 a D Dx ly3 S3 W3 regs3 mem3 md3 ->
     SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 0x851d0) mem3 (seg_rom tfibsegs)) md3) Qc) ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs)) md') Qc).
(* a Theorem Labs lane's pi_init (FSW_parse_items_mloop.v Section hypothesis HINIT, at every entry) *)
Definition pib_HINITF {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat) : Prop :=
  @pib_entry fx rc SK B k (fun ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch =>
  forall kk x rm (Qc : world tfibsegs -> config -> Prop), ms = (kk, x) :: rm ->
  (forall T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
     pib_IG B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail [] kk x rm T lyc Sc Uc W1 memC
       mdC regsC chq pc kids keys cap Di Da peak1 ->
     SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Qc).

Theorem parse_items_holds_of : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat),
  (k <= 1)%nat -> FsShadowSyms B -> @skip_ws_spec fx rc SK tfibsegs B -> @grow_spec fx rc SK tfibsegs B ->
  @parse_string_spec fx rc SK tfibsegs B -> @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k) ->
  FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset ->
  @pib_HVALF fx rc SK B k -> @pib_HINITF fx rc SK B k ->
  @parse_items_spec fx rc SK tfibsegs B k.
Proof.
intros fx rc SK B k Hk HSS HSW HGROW HPS _ _ HVF HIF. unfold parse_items_spec.
intros ly S U W regs mem md ch q ot v text len p tb tcap ms pr rest live peak cnt fail.
destruct ms as [|[kk x] rm].
- exact (pi_holds_nil SK B HSS HSW k ly S U W regs mem md ch q ot v text len p tb tcap pr rest live peak cnt fail).
- cbv zeta. intros Hk' HPRE HHEADS HFRL H10 H11 H12 HIN0 HWIN HQ16 HCH0 HTX HREST HDV HDS HWF HDEP HPO0 HZERO HVSP HVTX
    HGLOB HQT HSZ HLIVE HEV HBB.
  eapply (pi_holds_cons B k ly S U W regs mem md q ot v text len p tcap tb ((kk, x) :: rm) pr rest live peak cnt fail ch);
    try assumption; try reflexivity.
  + exact (HVF ly S U W regs mem md q ot v text len p tcap tb ((kk, x) :: rm) pr rest live peak cnt fail ch HPRE HHEADS
      HWIN HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HFRL H10 H11 H12 HCH0 HREST HDV HDS HWF HDEP HZERO HVSP HGLOB).
  + exact (HIF ly S U W regs mem md q ot v text len p tcap tb ((kk, x) :: rm) pr rest live peak cnt fail ch HPRE HHEADS
      HWIN HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HFRL H10 H11 H12 HCH0 HREST HDV HDS HWF HDEP HZERO HVSP HGLOB).
Qed.

(* ================= the segment 0x85048 .. 0x851d0 discharged: a Theorem Labs lane's piv_val ================= *)
(* pib_HVALF from FSW_parse_items_val.piv_val (a Theorem Labs lane, 68d63eeea0b, merged at 1a8bf4e5820; `Proof using All`: its
   Section's variables, the 28 entry hypotheses, then HSW, HPV, HMS) *)
Lemma pib_HVALF_of_val : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat),
  (k <= 1)%nat -> FsShadowSyms B -> @skip_ws_spec fx rc SK tfibsegs B ->
  @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k) -> FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset ->
  @pib_HVALF fx rc SK B k.
Proof.
intros fx rc SK B k Hk HSS HSW HPV HMS. unfold pib_HVALF, pib_entry.
intros ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch
  HPRE HHEADS HWIN HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HFRL H10 H11 H12 HCH0 HREST HDV HDS HWF HDEP HZERO HVSP
  HGLOB.
exact (piv_val B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch Hk HSS HPRE HHEADS
  HWIN HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HFRL H10 H11 H12 HCH0 HREST HDV HDS HWF HDEP HZERO HVSP HGLOB HSW
  HPV HMS).
Qed.

(* parse_items_holds' final statement with a Theorem Labs lane's pi_init (pib_HINITF) as the ONE open input *)
Theorem parse_items_holds_init : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms)
  (k : nat),
  (k <= 1)%nat -> FsShadowSyms B -> @skip_ws_spec fx rc SK tfibsegs B -> @grow_spec fx rc SK tfibsegs B ->
  @parse_string_spec fx rc SK tfibsegs B -> @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k) ->
  FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset ->
  @pib_HINITF fx rc SK B k ->
  @parse_items_spec fx rc SK tfibsegs B k.
Proof.
intros fx rc SK B k Hk HSS HSW HGROW HPS HPV HMS HIF.
exact (parse_items_holds_of B k Hk HSS HSW HGROW HPS HPV HMS (pib_HVALF_of_val B k Hk HSS HSW HPV HMS) HIF).
Qed.

(* ================= the entry to the first grow call discharged: a Theorem Labs lane's pi_init ================= *)
Lemma pib_HINITF_of_init : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat),
  (k <= 1)%nat -> FsShadowSyms B -> @skip_ws_spec fx rc SK tfibsegs B -> @pib_HINITF fx rc SK B k.
Proof.
intros fx rc SK B k Hk HSS HSW. unfold pib_HINITF, pib_entry.
intros ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch
  HPRE HHEADS HWIN HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HFRL H10 H11 H12 HCH0 HREST HDV HDS HWF HDEP HZERO HVSP
  HGLOB.
intros kk x rm Qc E K.
eapply (pi_init B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch); try eassumption.
Qed.

(* ================= THE FUNCTION THEOREM: parse_items on image B (fs.asan-ubsan, 0x84e70) ================= *)
Theorem parse_items_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat),
  (k <= 1)%nat -> FsShadowSyms B -> @skip_ws_spec fx rc SK tfibsegs B -> @grow_spec fx rc SK tfibsegs B ->
  @parse_string_spec fx rc SK tfibsegs B -> @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k) ->
  FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset ->
  @parse_items_spec fx rc SK tfibsegs B k.
Proof.
intros fx rc SK B k Hk HSS HSW HGROW HPS HPV HMS.
exact (parse_items_holds_init B k Hk HSS HSW HGROW HPS HPV HMS (pib_HINITF_of_init B k Hk HSS HSW)).
Qed.
