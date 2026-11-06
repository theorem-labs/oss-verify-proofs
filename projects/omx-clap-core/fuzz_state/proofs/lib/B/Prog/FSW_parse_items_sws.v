(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) a skip_ws call inside parse_items' member loop on image B
   (B only: image A inlines the white-space loops, so the A walk has no twin of this step).
   pis_loop_sw: at a call of skip_ws from the member loop (skip_ws #2 0x84ffc -> 0x85000, skip_ws #4 0x851f0 ->
   0x851f4; the frame is the member loop's pib_frameL, the callee-saved registers pib_RL), the call through skip_ws_spec
   (FSW_parse_items_sw.pic_call_sw), the resume (FSW_parse_items_calls.pic_after_callT) and the narrowing to the next
   segment's start state pib_start r pib_csL gf (pib_rgs pib_csL fw qw vw) pib_RL [the cursor byte c] [] pib_wsc0 []
   (FSW_parse_items_lh.pil_start), with every piece of the loop invariant carried to the resume: the caller's journal
   from the entry (no tick, U kept), the registers, the frame, struct pj_in at in->p past the white space, the chain at
   q, the caller's window, the text, v, the live list, the statics and the open object.
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
FSW_parse_items_loop FSW_parse_items_mem FSW_parse_items_sw FSW_parse_items_obj FSW_parse_items_lh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the member loop's frame survives a memory change that keeps its 144 bytes *)
Lemma pis_frameL_mb : forall (M M' : word -> option byte) sp0 xr qq vv,
  (forall a, sp0 - 144 <= a < sp0 -> mbyte tfibsegs M' a = mbyte tfibsegs M a) ->
  pib_frameL M sp0 xr qq vv -> pib_frameL M' sp0 xr qq vv.
Proof.
intros M M' sp0 xr qq vv E (H0 & F0 & F8 & F16 & F24 & F32).
assert (V : forall a z, sp0 - 144 <= a -> a + 8 <= sp0 -> val_mem tfibsegs M a 8 z -> val_mem tfibsegs M' a 8 z)
  by (intros a z H1 H2 Hv; apply (pim_val_mb M M' a 8 z); [intros i Hi; apply E; cbn in Hi; lia | exact Hv]).
split; [|split; [apply V; [lia | lia | exact F0]|split; [apply V; [lia | lia | exact F8]|
  split; [apply V; [lia | lia | exact F16]|split; [apply V; [lia | lia | exact F24] | apply V; [lia | lia | exact F32]]]]]].
unfold pib_frame0 in *. rewrite Forall_forall in *. intros j Hj. apply in_seq in Hj.
apply V; [lia | lia | exact (H0 j ltac:(apply in_seq; lia))].
Qed.

(* the frame chain at qq across a memory change off [qq, qq + 24), reads bounded by the stack top (image-free; the A walk's
   piG_fpchain_kept / piG_chain_kept, a working branch 4480a5df1ae lib/A/FSW_parse_items_stG.v, renamed) *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pis_fpchain_kept : forall (l1 l2 : Z -> option Z) qq s top cl bp,
  fpchain l1 bp top cl -> (bp = qq \/ qq + 40 <= bp) -> s + 16 <= bp -> bp + 16 < top ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) cl ->
  (forall a, s <= a -> a + 8 <= top -> a + 8 <= qq \/ qq + 24 <= a -> l2 a = l1 a) -> fpchain l2 bp top cl.
Proof.
intros l1 l2 qq s top cl. induction cl as [|[[fp ra] nfp] cl IH]; intros bp H Hq Hb Ht HF Hl; cbn [fpchain] in *.
- destruct H as (r & Hr & Hr2). exists r. rewrite Hl by lia. split; assumption.
- destruct H as (E & H8 & Hra & Hnfp & H4 & Hrest). subst fp.
  inversion HF as [|? ? Hr HF']; subst. cbn [fst snd] in Hr.
  split; [reflexivity|]. split; [exact H8|]. split; [rewrite Hl by lia; exact Hra|].
  split; [rewrite Hl by lia; exact Hnfp|]. split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  assert (Hn : bp < nfp /\ nfp < top - 16).
  { unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb1 Eb2].
    apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. lia. }
  apply (IH nfp Hrest); [| lia | lia | exact HF' | exact Hl].
  destruct Hr as [Hr | Hr]; [exfalso; congruence | right; exact Hr].
Qed.
Lemma pis_chain_kept : forall ly1 ly2 (rd1 rd2 : reader) s qq top chq,
  achain ly1 rd1 s qq chq -> Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) chq ->
  ly_top ly1 = top -> ly_top ly2 = top ->
  (forall a, s <= a < top -> ~ (qq <= a < qq + 24) -> rd2 a = rd1 a) -> achain ly2 rd2 s qq chq.
Proof.
intros ly1 ly2 rd1 rd2 s qq top chq H HF E1 E2 Hrd. unfold achain in *. rewrite E2. rewrite E1 in H.
destruct H as [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H|]. right.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
apply (pis_fpchain_kept (rdword rd1) (rdword rd2) qq s top chq qq H4 (or_introl eq_refl) H1 ltac:(lia) HF).
intros a Ha Ht Hout. apply rdword_ext. intros j Hj. apply Hrd; lia.
Qed.
End C.

Local Ltac pws_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; unfold acallee_saved; lia.
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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

(* ---- the entry's facts this step reads (FSW_parse_items_lh.v) ---- *)
Lemma W_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof. exact (pil_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP). Qed.
Lemma W_stk : 144 + STK_skip_ws <= STK_parse_items (1 - k).
Proof.
assert (HF : FRAME_parse_items + STK_skip_ws <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
change FRAME_parse_items with 144 in HF. exact HF.
Qed.
Lemma W_qs : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof. exact (pil_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP). Qed.
Lemma W_vrng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof. exact (pil_v_rng B k ly S U W regs mem md v ch HPRE HPO0). Qed.

(* ================= the step ================= *)
Lemma pis_loop_sw : forall (r : Z) (xs : list word) (gf : list (nat * afact)) (fw qw vw : Z * Z) (c : Z)
    lyc Sc Uc (W1 : world tfibsegs) memC mdC kc regsC chq pc (ws more : list Z)
    T Da peak1 kids keys cap dn Di (Qc : world tfibsegs -> config -> Prop),
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  let n := Z.of_nat (length dn) in
  let pc' := pc + Z.of_nat (length ws) in
  JC lyc Sc Uc W1 memC mdC kc ->
  YK11.getr regsC 1 = w64 r -> YK0s.ret_ok (w64 r) -> 4096 <= r < 2 ^ 64 ->
  YK11.getr regsC 10 = w64 q -> RP regsC pib_RL ->
  pib_frameL (rdW W1 memC) sp0 xr q v ->
  STKP lyc Uc W1 memC chq pc ->
  ReaderRes.rest_at tb text pc = ws ++ c :: more -> Forall (fun c0 => PjGrammar.ws c0 = true) ws ->
  PjGrammar.ws c = false ->
  BLK lyc Sc Uc W1 memC L Da T peak1 ->
  OBJ W1 memC L n kids keys cap dn Di -> n <= cap ->
  nth 0 xs (Z_to_bv 64 0) = Z_to_bv 64 pc' -> nth 1 xs (Z_to_bv 64 0) = Z_to_bv 64 (text + len) ->
  nth 2 xs (Z_to_bv 64 0) = Z_to_bv 64 (dd + 1) ->
  (forall j, (j < 13)%nat -> nth (3 + j) xs (Z_to_bv 64 0) = nth j xr (Z_to_bv 64 0)) ->
  nth 16 xs (Z_to_bv 64 0) = Z_to_bv 64 kids -> nth 17 xs (Z_to_bv 64 0) = Z_to_bv 64 keys ->
  nth 18 xs (Z_to_bv 64 0) = Z_to_bv 64 n -> nth 19 xs (Z_to_bv 64 0) = Z_to_bv 64 cap ->
  (forall regs', YK11.getr regs' 9 = w64 q -> YK11.getr regs' 19 = w64 v ->
     atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf) ->
  regions_wf ([pik_treg (xatom 0) 0 [c]] ++ fsT_ret_regions 144 pib_csL pib_rs) = true ->
  regions_wf ([pik_treg (xatom 0) 0 [c]] ++ pib_rgs pib_csL fw qw vw) = true ->
  (snd fw <= fst fw \/ 0 <= fst fw /\ snd fw <= 144) -> (snd qw <= fst qw \/ 0 <= fst qw /\ snd qw <= 24) ->
  (snd vw <= fst vw \/ 0 <= fst vw /\ snd vw <= 56) ->
  (forall ly' S' (W' : world tfibsegs) regs' mem' md',
     JC ly' S' Uc W' mem' md' kc -> aregs_preserved regsC regs' -> RP regs' pib_RL ->
     pib_frameL (rdW W' mem') sp0 xr q v ->
     STKP ly' Uc W' mem' chq pc' ->
     BLK ly' S' Uc W' mem' L Da T peak1 ->
     OBJ W' mem' L n kids keys cap dn Di ->
     ablocks B ly' S' = ablocks B lyc Sc ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs))
       (pib_start r pib_csL gf (pib_rgs pib_csL fw qw vw) pib_RL [pik_treg (xatom 0) 0 [c]] [] pib_wsc0 [])
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_skip_ws regsC memC mdC) Qc.
Proof.
intros r xs gf fw qw vw c lyc Sc Uc W1 memC mdC kc regsC chq pc ws more T Da peak1 kids keys cap dn Di Qc L n pc'
  HJC R1 Hret Hr R10 HRP HFR HSTK HRST Hws Hc HBL HOBJ Hncap X0 X1 X2 XR X16 X17 X18 X19 HGF Hwf1 Hwf2 Hfw Hqw Hvw K.
assert (Hpcd : pc' = pc + Z.of_nat (length ws)) by reflexivity.
assert (Hnd : n = Z.of_nat (length dn)) by reflexivity.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof W_sp0 as (Hal16 & Hsp1 & Hsp2). pose proof W_stk as Hstk.
pose proof W_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof W_vrng as (Hv1 & Hv2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
assert (HSW0 : 0 <= STK_skip_ws) by (vm_compute; discriminate).
destruct HJC as (HJ & HARU & HRO & HHD).
pose proof HARU as (HAR & OKc & POc).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
destruct HSTK as (HCH & HCHF & HTOP & HIN & HWK).
destruct HBL as (HTXc & HPOc & HBLc & HPERMc & HUc & HDac & HSUMc & HLENc & HGc & Hpk1).
destruct HOBJ as (HHDRc & HOPc).
pose proof HTXc as (Ht4 & HRBc & Htlc). pose proof HRBc as (HinTc & _ & Htc0 & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc (dd + 1)
  HAR HTXc HIN) as (Ht0 & Hpc & Htl & Htc & Hac).
unfold HEAD in Ht0.
assert (Hlen : Z.of_nat (length (ReaderRes.rest_at tb text pc)) = text + len - pc)
  by (unfold ReaderRes.rest_at, ReaderRes.zb; rewrite length_map, length_skipn;
      pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & _ & _ & Htb & _); lia).
assert (Hpc' : pc' < text + len)
  by (rewrite Hpcd; rewrite HRST, length_app in Hlen; cbn [length] in Hlen; lia).
(* s0 = q + 16, read off the callee-saved list *)
assert (R8 : YK11.getr regsC 8 = w64 (q + 16)).
{ rewrite Forall_forall in RL. pose proof (RL (8%bv, SOff 9 16) ltac:(cbn; tauto)) as R8'. cbn [fst snd] in R8'.
  rewrite R8'.
  apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regsC _ 9 9%bv eq_refl), R9.
  unfold w64. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (HRST' : ReaderRes.rest_at tb text pc = ws ++ (c :: more)) by exact HRST.
(* ---- the call ---- *)
apply (pic_call_sw SK B HSW STKt ot FP ly S W (unpoison U mem) md [] lyc Sc Uc W1 memC mdC kc regsC q text len pc
  (dd + 1) tb tcap ws (c :: more) (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail Qc
  HJ HARU HRO HHD).
- rewrite R1. exact Hret.
- unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
- exact R3.
- exact R4.
- exact R10.
- exact R8.
- rewrite Rsp. change (spZ regs) with sp0. rewrite Zminus_mod, Hal16. reflexivity.
- rewrite Rsp. unfold STKt. lia.
- rewrite Rsp. lia.
- lia.
- exact HIN.
- exact HTXc.
- exact HRST'.
- exact Hws.
- intros c0 r0 E. injection E as <- _. exact Hc.
- exact HGc.
- intros ly' S' W' regs' mem' md' HJc OK' PO' HP QIN QWK QAB QTX QGL.
  (* ---- the resume env ---- *)
  set (E := Ereg regs' (fs_extraT ++ xs)).
  destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
  fold E in E9, E19, E32, E2, E3, E4.
  assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
  assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (EX0u : bv_unsigned (ew E (xatom 0)) = pc').
  { rewrite EXn, X0.
    apply unsigned_lit_small.
    lia. }
  assert (G9 : YK11.getr regs' 9 = w64 q) by (rewrite (pil_kept regsC regs' 9%bv HP ltac:(pws_acs)); exact R9).
  assert (G19 : YK11.getr regs' 19 = w64 v)
    by (rewrite (pil_kept regsC regs' 19%bv HP ltac:(pws_acs)); exact R19).
  assert (G2 : spZ regs' = spZ regsC)
    by (unfold spZ; rewrite (pil_kept regsC regs' 2%bv HP ltac:(pws_acs)); reflexivity).
  (* ---- the bytes skip_ws kept: block and frame bytes (its footprint is empty), the window but q's 8 ---- *)
  assert (KB : forall x, ((exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= x < p0 + req_size n0) \/
      (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
      rdW W' mem' (Z_to_bv 64 x) = rdW W1 memC (Z_to_bv 64 x))
    by (intros x Hx; exact (proj2 (fsw_journal_kept_byte B _ _ _ lyc Sc Uc W1 memC mdC ly' S' Uc W' mem' md' 0 x HJc HARU
          OK' PO' Hx (pim_inFP_nil x)))).
  assert (KV : forall x, v <= x < v + 56 -> rdW W' mem' (Z_to_bv 64 x) = rdW W1 memC (Z_to_bv 64 x)).
  { intros x Hx. apply KB.
    destruct HPOc as [[((cid & pos & Hin & Hcid & H8 & X1' & X2') & _)|((b & m & Hb & X1' & X2') & _)] _].
    - right. exists cid, pos. split; [exact Hin | lia].
    - left. exists b, m. split; [exact Hb | unfold HEAD in X1'; lia]. }
  assert (KL : forall a0 k0 x, In (a0, k0) L -> a0 <= x < a0 + k0 ->
      rdW W' mem' (Z_to_bv 64 x) = rdW W1 memC (Z_to_bv 64 x)).
  { intros a0 k0 x Hin Hx. destruct (HBLc a0 k0 Hin) as (Hin0 & _ & Hk0 & _). apply KB. left.
    exists (a0 - HEAD), (k0 + HEAD). split; [exact Hin0 | rewrite pio_req_hb by lia; unfold HEAD in *; lia]. }
  assert (WK8 : forall a, sp0 - 144 <= a < ot -> ~ (q <= a < q + 8) ->
      mbyte tfibsegs (rdW W' mem') a = mbyte tfibsegs (rdW W1 memC) a /\
      (writable_at tfibsegs (rdW W1 memC) a <-> writable_at tfibsegs (rdW W' mem') a))
    by (intros a Ha Hq; rewrite Rsp in QWK; exact (QWK a ltac:(lia) Hq)).
  assert (HFR' : pib_frameL (rdW W' mem') sp0 xr q v)
    by (apply (pis_frameL_mb (rdW W1 memC)); [intros a Ha; exact (proj1 (WK8 a ltac:(lia) ltac:(lia))) | exact HFR]).
  (* ---- v's header and the object ---- *)
  assert (SV : forall x, v <= x < v + 56 -> parse_items_shape.pis_same tfibsegs (rdW W1 memC) (rdW W' mem') x)
    by (intros x Hx; apply pio_same_raw; exact (KV x Hx)).
  assert (HHDR' : PjStruct.pj_hdr tfibsegs (rdW W' mem') v 6 0 0 kids keys n cap)
    by exact (parse_items_shape.pis_hdr_frame tfibsegs _ _ v 6 0 0 kids keys n cap HHDRc SV).
  assert (HOP' : parse_items_shape.pis_open tfibsegs (rdW W' mem') (ReaderRes.lin L) v true 0 kids keys cap n
      (map snd dn) (map fst dn) Di).
  { apply (parse_items_shape.pis_frame tfibsegs _ _ _ _ v true 0 kids keys cap n (map snd dn) (map fst dn) Di 0 n HOPc
      HHDR' ltac:(lia) (fun a0 k0 H => H)).
    intros z Hz. rewrite length_map in Hz.
    destruct (pio_ifoot_in kids keys cap n Di z ltac:(lia) Hz) as ((a0 & k0) & Hin0 & Hh0).
    unfold PjStruct.pj_holds in Hh0. cbn [fst snd] in Hh0.
    apply pio_same_raw. exact (KL a0 k0 z Hin0 Hh0). }
  (* ---- the resume ---- *)
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ QIN) as (_ & _ & _ & Hp' & _).
  assert (HPOc' : pobj tfibsegs B ly' S' W' mem' v).
  { apply (pobj_kept_call B _ _ _ lyc Sc Uc W1 memC mdC ly' S' Uc W' mem' md' 0 v HJc HARU OK' PO');
      [intros a _ Ha; exact (pim_inFP_nil a Ha) | intros a Ha; exfalso; exact (pim_inFP_nil a Ha)
      | intros rr Hrr; rewrite QAB; exact (HHD rr Hrr) | exact HPOc]. }
  assert (HCS : Forall (YP09.chunk_ok tfibsegs E (rdW W' mem') (sp0 - 144)) pib_csL)
    by (apply (pil_csL_ok E _ sp0 xr q v (pil_xr_len regs)); [intros j Hj; rewrite EXn; exact (XR j Hj)
        | exact E19 | exact E32 | lia | lia | exact HFR']).
  assert (HRS : Forall (region_ok tfibsegs E (rdW W' mem')) pib_rs).
  { constructor; [|constructor; [|constructor]].
    - apply (pis_q_ok E _ q text len pc' (dd + 1) tb E9u);
        [rewrite EXn; exact X0 | rewrite EXn; exact X1 | rewrite EXn; exact X2 | exact QIN].
    - pose proof HHDR' as (_ & Hty' & _ & _ & Hkids' & Hkeys' & Hn' & Hcap').
      unfold pib_vR, pib_vch. apply (fsw_pj_part_okW tfibsegs _ _ 19 v v 0 56 0 56);
        [lia | lia | destruct HPOc' as [_ Hw']; exact Hw' | exact E19u | lia | lia | right; lia |].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      + apply (fsw_pj_chunk4 tfibsegs _ _ v 0 (SLit 6) 6); [rewrite Z.add_0_r; exact Hty' | reflexivity].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff (xatom 16) 0) kids); [exact Hkids' | rewrite fsw_SOff0, EXn; exact X16].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff (xatom 17) 0) keys); [exact Hkeys' | rewrite fsw_SOff0, EXn; exact X17].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SOff (xatom 18) 0) n); [exact Hn' | rewrite fsw_SOff0, EXn; exact X18].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 48 (SOff (xatom 19) 0) cap); [exact Hcap' | rewrite fsw_SOff0, EXn; exact X19]. }
  pose proof (fsw_pobj_off_img B lyc Sc W1 (unpoison Uc memC) mdC memC v HAR HPOc) as Hvimg.
  assert (HPD : pairwise_disjoint E (fsT_ret_regions 144 pib_csL pib_rs)).
  { apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2, E9u, E19u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  destruct (pic_after_callT B STKt ot FP [] ly S U W1 mem md W lyc Sc Uc memC mdC kc STK_skip_ws [] sp0 144 regsC
    ly' S' Uc W' regs' mem' md' 0 xs pib_csL pib_rs gf r (proj1 HSS) (proj2 HSS) HJ HARU HJc
    ltac:(intros a Ha; exfalso; exact (pim_inFP_nil a Ha)) OK' PO' HP Rsp ltac:(lia) HSW0
    ltac:(rewrite Rsp; change (spZ regs) with sp0; rewrite Zminus_mod, Hal16; reflexivity) ltac:(lia) ltac:(rewrite Rsp; unfold STKt; lia)
    ltac:(vm_compute; reflexivity) HCS HRS HPD (HGF regs' G9 G19)) as (HJ2 & HARU2 & HST).
  rewrite Z.add_0_r in HJ2.
  (* ---- the start state ---- *)
  destruct (pil_txt_bytes k S regs ot text len tb ms Hk HDEP (rdW W' mem') q pc' (dd + 1) [c] more QIN
    ltac:(rewrite Hpcd; rewrite (pim_rest_skip tb text pc ws (c :: more) ltac:(lia) HRST); reflexivity))
    as (Hbs & Hbyt).
  assert (RT : region_ok tfibsegs E (rdW W' mem') (pik_treg (xatom 0) 0 [c])).
  { apply (pik_treg_ok E _ (xatom 0) pc' 0 [c] EX0u ltac:(lia) ltac:(lia)); [cbn [length]; lia | exact Hbs |].
    intros j Hj. rewrite Z.add_0_r. exact (Hbyt j Hj). }
  assert (Himg : text + tcap <= 65536 \/ FS_IMG_END <= text - HEAD).
  { destruct (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HAR HinTc) as [H|H];
      try rewrite pio_req_hb in H by lia; lia. }
  assert (DJ : all_disjoint E (pik_treg (xatom 0) 0 [c]) (fsT_ret_regions 144 pib_csL pib_rs)).
  { apply (pil_treg_disj B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTX HPO0 HDEP
      E [c] pib_csL pc' EX0u E2 E9u E19u); try lia. cbn [length]. lia. }
  assert (HC : conds_ok E pib_wsc0)
    by (apply (pil_conds_wsc0 k S regs ot ms Hk HDEP E pc' (text + len)); [rewrite EXn; exact X0 | rewrite EXn; exact X1 | lia | lia | lia]).
  pose proof (pil_start k S regs ot ms Hk HDEP regs' xs W' mem' r pib_csL gf pib_RL [pik_treg (xatom 0) 0 [c]] [] pib_wsc0 []
    fw qw vw HST (pil_setr_R B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP pil_RL_ok) Hwf1
    ltac:(constructor; [exact RT | constructor]) (conj DJ HPD) I HC I Hfw Hqw Hvw Hwf2) as HSS0.
  (* ---- the invariant at the resume ---- *)
  pose proof HJc as (_ & Hlyc & _).
  pose proof HJ2 as (_ & Hly2 & _).
  destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop' & Hslo' & Hshi' & _).
  pose proof HPRE as ((HAP0 & _ & _) & _). pose proof HAP0 as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & _ & _ & _ & H47l & _ & Htopl & Htopl2).
  assert (AV : forall z, sp0 <= z < ly_top ly -> ~ (q <= z < q + 24) ->
      aview tfibsegs (w_H W') (unpoison Uc mem') z = aview tfibsegs (w_H W1) (unpoison Uc memC) z).
  { intros z Hz Hq. destruct (Z_lt_le_dec z ot) as [Hzo|Hzo].
    - destruct (WK8 z ltac:(lia) ltac:(lia)) as (Mz & _).
      rewrite (fsw_aview_unpoison_high B ly' S' Uc W' mem' md' z HARU2 ltac:(lia)),
        (fsw_aview_unpoison_high B lyc Sc Uc W1 memC mdC z HARU ltac:(lia)).
      unfold aview. rewrite Mz. reflexivity.
    - pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & HJ9 & _). apply HJ9; [lia | rewrite Rsp; lia]. }
  rewrite R1. change (w64 r) with (Z_to_bv 64 r).
  apply (K ly' S' W' regs' mem' md').
  + split; [exact HJ2|]. split; [exact HARU2|].
    split; [exact (arodata_kept B _ _ _ lyc Sc Uc W1 memC mdC ly' S' Uc W' mem' md' 0 HJc HARU OK' PO' pis_sink_nil
      (fun a _ => pim_inFP_nil a) HRO)|].
    intros rr Hrr. rewrite QAB. exact (HHD rr Hrr).
  + exact HP.
  + pose proof (pil_setr_R B k S regs q ot v ms Hk HDEP regsC regs' [] pib_RL HRP HP pil_RL_ok) as HR'.
    rewrite app_nil_r in HR'.
    split; [rewrite G2; exact Rsp|]. split; [exact G9|]. split; [exact G19|].
    split; [rewrite (pil_kept regsC regs' 3%bv HP ltac:(pws_acs)); exact R3|].
    split; [rewrite (pil_kept regsC regs' 4%bv HP ltac:(pws_acs)); exact R4|].
    apply (Forall_impl _ (fun r0 (H : fst r0 <> 0%bv /\ _) => proj2 H) HR').
  + exact HFR'.
  + split.
    { apply (pis_chain_kept lyc ly' _ _ sp0 q (ly_top ly) chq HCH HCHF HTOP ltac:(congruence)).
      intros z Hz Hq. exact (AV z Hz Hq). }
    split; [exact HCHF|]. split; [congruence|]. split; [exact QIN|].
    apply (pil_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W' memC mem' (sp0 - 144) HWK); [|lia].
    intros a Ha Hq. exact (WK8 a ltac:(lia) ltac:(lia)).
  + split; [exact QTX|]. split; [exact HPOc'|].
    split; [exact (rd_blocks_ok_kept_call B _ _ _ lyc Sc Uc W1 memC mdC ly' S' Uc W' mem' md' 0 L HJc HARU OK' PO'
      (fun a0 k0 x _ _ => pim_inFP_nil x) HBLc)|].
    split; [rewrite QAB; exact HPERMc|]. split; [exact HUc|]. split; [exact HDac|]. split; [exact HSUMc|].
    split; [exact HLENc|]. split; [exact QGL | exact Hpk1].
  + split; [exact HHDR' | exact HOP'].
  + exact QAB.
  + exact HSS0.
Qed.
End W.
