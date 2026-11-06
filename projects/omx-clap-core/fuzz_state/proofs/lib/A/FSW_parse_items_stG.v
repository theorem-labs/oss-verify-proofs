(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the GROW STEP of parse_items' member loop (pi_step_G),
   from the call-site invariant pi_IG at grow (A_grow) to pi_IP at the parse_string call (A_parse_string). Route: the
   grow call (FSW_parse_items_grow.pig_call_84b68 for the first member, pig_call_84e60 for a later one; frame pi_cs0 /
   pi_csL) with its premises from pi_IG (budget pi_budget, slots pi_slots_of, q's fields pi_pin_vals, the chain
   achain_lower); the object across grow by FSW_parse_items_obj.pio_grow; the resume state turned into the segment's
   start state (pi_start_T, the text window from pi_txt_bytes, its v region narrowed to no write window by
   pik_st_ok_setm - a Theorem Labs lane's decision, so that frame_of keeps every byte of v); the segment S1f / S1 pr k
   re-measured on that state (piG_run_s1f / piG_run_s1) and run with fsw_run_tok_AJU; at the stop pi_IP is built:
   registers, frame (pi_frameL_of), struct pj_in with in->p past the white space, the chain and the caller's window
   (pi_chain_kept, pi_wkeep_trans), the blocks and the object (every byte below alloc_ceiling kept).
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
(* callee: grow (S0 30057674945, lib/A/Prog/FSW_grow_holds.v grow_holds) *)
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.
#[local] Abbreviation JC := (pi_jc B k ly S U W regs mem md ot v).
#[local] Abbreviation RP := (pi_regsP B regs q v).
#[local] Abbreviation STKP := (pi_stack k ly W regs mem q ot text len tb).
#[local] Abbreviation BLK := (pi_blocks B ly S U v text len tcap live peak cnt fail).

(* ================= the two start states, measured with v read-only =================
   a Theorem Labs lane's decision (09:5xZ): the resume state's v region (pig_v_region, write window [0, 56)) is narrowed
   to the same five chunks with NO write window (pik_st_ok_setm, a subregion), so that frame_of keeps every byte of v
   (num, str and the padding, which no chunk describes). S1f / S1 never write v; the runs below are re-measured on the
   narrowed states. *)
Definition pig_v_regionG : YP09.region := YP09.mkRegion (Some 20%nat) 0 56 0 0 (YP09.r_chunks pig_v_region).
Definition pig_rsG : list YP09.region := [pig_q_region; pig_v_regionG].
(* the seg.v start state of S1f / S1 (pi_ss_s1f / pi_ss_s1), white space ws before the key's opening quote *)
Definition piG_ssB (r : Z) (cs : list YP09.chunk) (R : list (bv 5 * sv)) (ws : list Z) : sstate :=
  pik_addf (pik_addr (pik_setr (fss_retT r 144 cs pig_rs pig_gf) ((10%bv, SLit 0) :: R))
    [pik_treg (xatom 0) 0 (ws ++ [34])]) [] (pi_wsc (length ws) 0) [].
Definition piG_ss (r : Z) (cs : list YP09.chunk) (R : list (bv 5 * sv)) (ws : list Z) : sstate :=
  pik_setm (piG_ssB r cs R ws) (pik_treg (xatom 0) 0 (ws ++ [34]) :: fsT_ret_regions 144 cs pig_rsG).
Definition piG_SH (ws : list Z) : list shent := mkSHE (xatom 0) 0 (1 + Z.of_nat (length ws)) :: pi_SHm.
Definition piG_q (ws : list Z) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) (Z.of_nat (length ws)))); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))].
(* the stop at parse_string: pc, no obligation, the registers of the call, the frame cs', q (in->p past ws), v *)
Definition piG_fin (cs' : list YP09.chunk) (ws : list Z) (st : shst) : Prop :=
  let s := sh_ss st in
  ss_pc s = A_parse_string /\ sh_obls st = [] /\ ss_resv s = None /\ pi_regs_are s pi_regs_ps = true /\
  nth_error (ss_mem s) 1 = Some (YP09.mkRegion (Some 2%nat) 0 144 0 144 cs') /\
  nth_error (ss_mem s) 4 = Some (piG_q ws) /\ nth_error (ss_mem s) 5 = Some pig_v_regionG.

(* S1f: grow #1 resume 0x84b6c -> parse_string *)
Definition piG_cs_s1f : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (pi_shv 20 24)); YP09.mkChunk 32 (CVal 8 (SOff 20 32));
   YP09.mkChunk 16 (CVal 8 (pi_shv 8 16)); YP09.mkChunk 8 (CVal 8 (SOff 8 8))] ++ pi_cs0.
Definition piG_st_s1f : shst := fst (pi_tok_run (piG_SH []) (piG_ss 0x84b6c pi_cs0 pi_R0 [])).
Lemma piG_run_s1f : pi_tok_run (piG_SH []) (piG_ss 0x84b6c pi_cs0 pi_R0 []) = (piG_st_s1f, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma piG_static_s1f : sh_static_ok (run_K 0 fs_Bx (piG_SH []) (piG_ss 0x84b6c pi_cs0 pi_R0 [])) fs_Bx fs_Bspan
  (piG_SH []) (ss_facts (piG_ss 0x84b6c pi_cs0 pi_R0 [])) (ss_mem (piG_ss 0x84b6c pi_cs0 pi_R0 [])) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piG_fin_s1f : piG_fin piG_cs_s1f [] piG_st_s1f.
Proof. unfold piG_fin. vm_compute. repeat split; reflexivity. Qed.
Lemma piG_K_s1f : (xatom 20 <= run_K 0 fs_Bx (piG_SH []) (piG_ss 0x84b6c pi_cs0 pi_R0 []))%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma piG_wf_s1f : regions_wf (ss_mem (piG_ss 0x84b6c pi_cs0 pi_R0 [])) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piG_incl_s1f : incl pi_csL piG_cs_s1f.
Proof.
intros c Hc. unfold pi_csL in Hc. unfold piG_cs_s1f. apply in_app_or in Hc as [Hc | Hc]; apply in_or_app.
- left. destruct Hc as [<- | [<- | [<- | [<- | []]]]]; cbn [In]; tauto.
- right. exact Hc.
Qed.

(* S1: grow #2 resume 0x84e64 -> parse_string, white space pi_wsb pr (k + 1) before the key *)
Definition piG_st_s1 (pr : bool) (k : nat) : shst :=
  fst (pi_tok_run (piG_SH (pi_wsb pr (Z.of_nat k + 1))) (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1)))).
Lemma piG_run_s1 : forall pr k, (k <= 1)%nat ->
  pi_tok_run (piG_SH (pi_wsb pr (Z.of_nat k + 1))) (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1))) =
    (piG_st_s1 pr k, TS_stopped SR_fetch).
Proof. intros [|] [|[|k0]] Hk0; try lia; vm_compute; reflexivity. Qed.
Lemma piG_static_s1 : forall pr k, (k <= 1)%nat ->
  sh_static_ok (run_K 0 fs_Bx (piG_SH (pi_wsb pr (Z.of_nat k + 1))) (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1))))
    fs_Bx fs_Bspan (piG_SH (pi_wsb pr (Z.of_nat k + 1)))
    (ss_facts (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1))))
    (ss_mem (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1)))) = true.
Proof. intros [|] [|[|k0]] Hk0; try lia; vm_compute; reflexivity. Qed.
Lemma piG_fin_s1 : forall pr k, (k <= 1)%nat -> piG_fin pi_csL (pi_wsb pr (Z.of_nat k + 1)) (piG_st_s1 pr k).
Proof. intros [|] [|[|k0]] Hk0; try lia; unfold piG_fin; vm_compute; repeat split; reflexivity. Qed.
Lemma piG_K_s1 : forall pr k, (k <= 1)%nat ->
  (xatom 20 <= run_K 0 fs_Bx (piG_SH (pi_wsb pr (Z.of_nat k + 1)))
     (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1))))%nat.
Proof. intros [|] [|[|k0]] Hk0; try lia; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma piG_wf_s1 : forall pr k, (k <= 1)%nat ->
  regions_wf (ss_mem (piG_ss 0x84e64 pi_csL pi_RL (pi_wsb pr (Z.of_nat k + 1)))) = true.
Proof. intros [|] [|[|k0]] Hk0; try lia; vm_compute; reflexivity. Qed.

(* ================= small facts ================= *)
Lemma piG_subregion_refl : forall rg, YP06.subregion rg rg.
Proof.
intros rg. unfold YP06.subregion. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [right; lia | intros c Hc; exact Hc].
Qed.
(* the narrowed region list is a submemory of the resume state's *)
Lemma piG_submem : forall bs cs, YP06.submem (pik_treg (xatom 0) 0 bs :: fsT_ret_regions 144 cs pig_rsG)
  (pik_treg (xatom 0) 0 bs :: fsT_ret_regions 144 cs pig_rs).
Proof.
intros bs cs. unfold fsT_ret_regions, pig_rsG, pig_rs. cbn [app].
do 5 (apply YP06.submem_keep; [apply piG_subregion_refl|]).
apply YP06.submem_keep; [|exact (YP06.submem_nil [])].
unfold YP06.subregion, pig_v_regionG, pig_v_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia | intros c Hc; exact Hc].
Qed.
(* an address no image byte lies at *)
Lemma piG_not_img : forall a, FS_IMG_END <= a -> ~ in_img tfibsegs a.
Proof. intros a Ha Hi. pose proof (fs_segs_img a Hi). lia. Qed.
(* equal views of an off-image byte are equal raw bytes *)
Lemma piG_raw_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  ~ in_img tfibsegs a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hi E. apply (pio_raw_of_mbyte (mrestrict H m) (mrestrict H' m') a Ha Hi).
unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* a 4-byte field as pj_in_ok's le4 bytes (FSW_pitems_dev.pid_val_le4, restated) *)
Lemma piG_val_le4 : forall m a z, val_mem tfibsegs m a 4 z -> 0 <= z < 2 ^ 32 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  lib.Lib.Mem.bytes_at tfibsegs m a (lib.Lib.Mem.le4 (Z_to_bv 64 z)).
Proof.
intros m a z Hv Hr Ha Hb. split; [exact Ha|]. rewrite lib.Lib.Mem.length_le4. split; [lia|].
intros i Hi. unfold lib.Lib.Mem.le4. rewrite MState.unsigned_lit by lia.
rewrite KindBGlue.kb_nth_le_bytes by exact Hi.
transitivity (mbyte tfibsegs m (a + Z.of_nat i)); [reflexivity|].
rewrite (Hv i Hi). f_equal. rewrite fpj_le_byte_bv.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia). reflexivity.
Qed.

(* ================= the entry's facts this step reads ================= *)
Lemma G_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 <= 2 ^ 47.
Proof. exact (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP). Qed.
Lemma G_stk144 : 144 <= STK_parse_items (1 - k).
Proof. exact (pi_stk144 k S regs ot ms Hk HDEP). Qed.
Lemma G_qs : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof. exact (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP). Qed.
Lemma G_vrng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof. exact (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0). Qed.
Lemma G_env : forall regsC regs' xs R, RP regsC R -> aregs_preserved regsC regs' ->
  ew (Ereg regs' (fs_extraT ++ xs)) 8 = Z_to_bv 64 q /\ ew (Ereg regs' (fs_extraT ++ xs)) 20 = Z_to_bv 64 v /\
  ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF /\
  bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - 144 /\
  ew (Ereg regs' (fs_extraT ++ xs)) 3 = Z_to_bv 64 (as_gp B) /\ ew (Ereg regs' (fs_extraT ++ xs)) 4 = Z_to_bv 64 (as_tp B).
Proof. exact (pi_env_at B k S regs q ot v ms Hk HDEP). Qed.

(* the write ranges of the narrowed start state: the frame and q *)
Lemma piG_wrange : forall E r cs R ws z, bv_unsigned (ew E 2) = sp0 - 144 -> bv_unsigned (ew E 8) = q ->
  in_wrange E (ss_mem (piG_ss r cs R ws)) z -> (sp0 - 144 <= z < sp0) \/ (q <= z < q + 24).
Proof.
intros E r cs R ws z E2 E8 (rg & Hin & Hz).
unfold piG_ss, pik_setm, fsT_ret_regions, pig_rsG in Hin. cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fstk_ret fs_got_region fs_bcell_region pig_q_region pig_v_regionG YP09.r_base YP09.r_wlo YP09.r_whi
       base_val] in Hz; rewrite ?E2, ?E8 in Hz; lia.
Qed.

(* the registers at the parse_string stop, as pi_IP states them *)
Lemma piG_regsP_stop : forall E' (regs2 : bvmap 5 word),
  Forall (fun r => YK11.getr regs2 (fst r) = sv_denot E' (snd r)) pi_regs_ps ->
  ew E' 8 = Z_to_bv 64 q -> ew E' 20 = Z_to_bv 64 v -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E' 2) = sp0 - 144 -> ew E' 3 = Z_to_bv 64 (as_gp B) -> ew E' 4 = Z_to_bv 64 (as_tp B) ->
  ed E' = (fun _ => []) ->
  RP regs2 pi_RL /\ YK11.getr regs2 1 = w64 0x84c50 /\ YK11.getr regs2 10 = w64 q.
Proof.
intros E' regs2 HR E8 E20 E32 E2 E3 E4 Hed. rewrite Forall_forall in HR.
assert (G : forall r e, In (r, e) pi_regs_ps -> YK11.getr regs2 r = sv_denot E' e) by (intros r e H; exact (HR (r, e) H)).
assert (G8 : YK11.getr regs2 8 = Z_to_bv 64 q) by (rewrite (G 8%bv (SOff 8 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E8).
assert (G20 : YK11.getr regs2 20 = Z_to_bv 64 v)
  by (rewrite (G 20%bv (SOff 20 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E20).
split; [|split; [rewrite (G 1%bv (SLit 0x84c50)) by (cbn; tauto); reflexivity |
  rewrite (G 10%bv (SOff 8 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E8]].
split; [unfold spZ; rewrite (G 2%bv (SOff 2 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E2|].
split; [exact G8|]. split; [exact G20|].
split; [rewrite (G 3%bv (SOff 3 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E3|].
split; [rewrite (G 4%bv (SOff 4 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E4|].
apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (G r e) by (unfold pi_regs_ps; apply in_or_app; right; exact Hin).
pose proof pi_RL_ok as Hok. unfold pi_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
apply pik_sv_denot_agree; [rewrite Hed; reflexivity|].
intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
- rewrite E8, (ew_Ereg_nat regs2 _ 8 8%bv eq_refl). symmetry. exact G8.
- rewrite E20, (ew_Ereg_nat regs2 _ 20 20%bv eq_refl). symmetry. exact G20.
- rewrite E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* struct pj_in at a new memory with in->p moved: the three fields read off the stop's q region, q writable, the text
   kept *)
Lemma piG_pin_new : forall m m' qq pc pc' d, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  val_mem tfibsegs m' qq 8 pc' -> val_mem tfibsegs m' (qq + 8) 8 (text + len) -> val_mem tfibsegs m' (qq + 16) 4 d ->
  (forall o, 0 <= o < 24 -> writable_at tfibsegs m' (qq + o)) -> text <= pc' <= text + len ->
  (forall x, text <= x < text + len -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  PjIn.pj_in_ok tfibsegs m' qq text len pc' d tb.
Proof.
intros m m' qq pc pc' d HIN V0 V8 V16 HW Hp HT.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & _ & Hte & _ & _ & _ & Hd).
destruct HIN as (B1 & B2 & B3 & (W0 & W1 & W2) & H5 & H6 & H7 & H8 & H9 & B10 & Hi11 & Hi12).
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj Hp (conj H9 (conj _ (conj Hi11 Hi12))))))))))).
- apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact V0 | lia | lia | lia].
- apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact V8 | lia | lia | lia].
- apply piG_val_le4; [exact V16 | lia | lia | lia].
- split; [exact W0|]. split; [exact W1|]. intros i Hi. exact (HW i Hi).
- destruct B10 as (A0 & A1 & A2). split; [exact A0|]. split; [exact A1|]. intros i Hi.
  transitivity (mbyte tfibsegs m (text + Z.of_nat i)); [exact (HT (text + Z.of_nat i) ltac:(lia)) | exact (A2 i Hi)].
Qed.

(* ================= the step, for either grow call ================= *)
Lemma piG_gen : forall (r : Z) (cs : list YP09.chunk) (R : list (bv 5 * sv)) (ws : list Z) (cs' : list YP09.chunk)
  (st : shst) dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
  (Qc : world tfibsegs -> config -> Prop),
  pig_call_at B r -> pi_R_ok R = true ->
  regions_wf (fsT_ret_regions 144 cs pig_rs) = true -> regions_wf (ss_mem (piG_ss r cs R ws)) = true ->
  pi_tok_run (piG_SH ws) (piG_ss r cs R ws) = (st, TS_stopped SR_fetch) ->
  sh_static_ok (run_K 0 fs_Bx (piG_SH ws) (piG_ss r cs R ws)) fs_Bx fs_Bspan (piG_SH ws)
    (ss_facts (piG_ss r cs R ws)) (ss_mem (piG_ss r cs R ws)) = true ->
  (xatom 20 <= run_K 0 fs_Bx (piG_SH ws) (piG_ss r cs R ws))%nat ->
  piG_fin cs' ws st -> incl pi_csL cs' ->
  ms = dn ++ (kk, x) :: rm ->
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.tgo_obj (length dn) (Z.to_nat cap) ((kk, x) :: rm) ->
  (length dn <= Z.to_nat cap)%nat -> 0 <= cap ->
  JC lyc Sc Uc W1 memC mdC (rd_ev T) ->
  YK11.getr regsC 1 = w64 r -> YK11.getr regsC 10 = w64 v -> RP regsC R ->
  (forall regs' k' y' cap', aregs_preserved regsC regs' ->
     Forall (YP09.chunk_ok tfibsegs
       (Ereg regs' (fs_extraT ++ pig_xs pc (text + len) (dd + 1) xr k' y' (Z.of_nat (length dn)) cap'))
       (rdW W1 memC) (sp0 - 144)) cs) ->
  STKP lyc Uc W1 memC chq pc ->
  ReaderRes.rest_at tb text pc = ws ++ concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++
    concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd (Datatypes.S (length dn)) rm) ++
    pi_wsb pr dd ++ [125] ++ rest ->
  BLK lyc Sc Uc W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) Da T peak1 ->
  pi_obj v W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) (Z.of_nat (length dn)) kids keys cap dn Di ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' kids' keys' cap' Da' peak1',
     IP dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Di Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_parse_string regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Qc.
Proof.
intros r cs R ws cs' st dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc
  Hcall HRok Hwf Hwf2 HRUN HSTAT HKb HFIN Hincl Hms Htr Hicap Hcap0 HJC R1 R10 HRP HCS HSTK HREST' HBL HOBJ KIP.
set (i := length dn) in *.
set (L := parse_items_shape.pis_slots true kids keys cap ++ Di) in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof G_sp0 as (Hal16 & Hsp1 & Hsp2). pose proof G_stk144 as H144.
pose proof G_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof G_vrng as (Hv1 & Hv2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HGLOB as (_ & _ & _ & _ & (Hlive0 & _) & _).
pose proof HTX as (_ & (HTXe & _) & _).
pose proof (HBL) as HBL0. pose proof (HOBJ) as HOBJ0.
destruct HJC as (HJ & HARUc & HRO & HHDc).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnevj & _ & _ & _ & _ & _ & _ & _ & Hstkj & _).
pose proof Hstkj as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
pose proof HARUc as (HARc & OKc & POc).
destruct HSTK as (HCH & HCHF & HTOP & HIN & HWK).
destruct HBL as (HTXc & HPOc & HBLc & HPERMc & HUc & HDac & HSUMc & HLENc & HGc & Hpk1).
destruct HOBJ as (HHDRc & HOPc).
pose proof HRP as (Rsp & R8 & R20 & R3 & R4 & _).
pose proof HTXc as (_ & HRBc & Htlc). pose proof HRBc as (HinTc & _ & Htc0 & _).
destruct (pi_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc (dd + 1)
  HARc HTXc HIN) as (Ht0 & Hpc & Htl & Htc & Hac).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & Hte62 & _ & Htblen & _ & _).
(* ---- the text at in->p: ws, then the key's opening quote ---- *)
destruct (pi_mem_facts_gen (1 - k) ms HDV HDS HWF ltac:(lia) dn kk x rm Hms) as (Hplain & _).
assert (HRL : Z.of_nat (length (ReaderRes.rest_at tb text pc)) = text + len - pc).
{ unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn. lia. }
assert (Hws : pc + Z.of_nat (length ws) < text + len).
{ rewrite HREST' in HRL. rewrite !length_app in HRL. cbn [length] in HRL. lia. }
assert (HRw : exists more, ReaderRes.rest_at tb text pc = (ws ++ [34]) ++ more).
{ rewrite HREST', (pim_spieces_plain kk Hplain). eexists. rewrite <- (app_assoc ws [34]). reflexivity. }
destruct HRw as (more & HRw).
(* ---- the trace and the budget of grow ---- *)
set (capn := Z.to_nat cap) in *.
assert (Ecapn : Z.of_nat capn = cap) by (unfold capn; lia).
set (X := PjRoundTrip.grow_ev true i capn).
assert (EX : grow_tr 6 (Z.of_nat i) cap = X) by (rewrite <- Ecapn; apply pim_grow_tr; exact Hicap).
set (Y := PjGrammar.EAlloc (Datatypes.S (length (flat_map PjRoundTrip.ech kk))) :: PjRoundTrip.ttrace x ++
  PjRoundTrip.tgo_obj (Datatypes.S i) (PjRoundTrip.gcap i capn) rm).
assert (Htr3 : PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ X ++ Y) by (rewrite Htr, pim_tgo_cons; reflexivity).
destruct (pi_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc L T X Y Htr3 Hnevj HPERMc
  HSUMc HLENc) as (BQ & BL & BE & BBy & BS).
destruct (pi_slots_of B k ly S U regs ot v text len tcap ms live peak cnt fail Hk HDEP lyc Sc Uc W1 memC mdC Da T peak1
  (Z.of_nat i) kids keys cap dn Di HARUc HBL0 HOBJ0 Hcap0) as (HSL & HBO & HAP & HINC & HNE & HRSd).
(* ---- grow's premises ---- *)
assert (HQg : quiet (cnt + Z.of_nat (length T)) fail (Z.of_nat (length (grow_tr 6 (Z.of_nat i) cap))))
  by (rewrite EX; exact BQ).
assert (HMX : Z.of_nat i = cap -> 56 * ReaderRes.cap2 cap + HEAD < MALLOC_MAX).
{ intros Ei. rewrite <- Ecapn. rewrite (pim_cap2 i capn ltac:(lia) ltac:(lia)).
  exact (proj1 (pim_grow_size i capn ltac:(lia) ltac:(lia) BS)). }
assert (HLV : live + PjGrammar.held T + rd_live (grow_tr 6 (Z.of_nat i) cap) < 2 ^ 64) by (rewrite EX; exact BL).
assert (HEVg : st_nev Sc + rd_ev (grow_tr 6 (Z.of_nat i) cap) <= EV_MAX) by (rewrite EX; exact BE).
assert (HBBg : blocks_bytes Sc + rd_live (grow_tr 6 (Z.of_nat i) cap) <= LIVE_MAX) by (rewrite EX; exact BBy).
assert (HRS : rd_sum (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) <= live + PjGrammar.held T)
  by lia.
destruct (pi_pin_vals k S regs ot text len tb ms Hk HDEP (rdW W1 memC) q pc (dd + 1) HIN) as (VP & VE & VD).
assert (HCHc : achain lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) (spZ regsC) q chq)
  by (rewrite Rsp; apply (achain_lower _ _ sp0); [exact HCH | lia]).
assert (Hp4 : 4096 <= pc <= 2 ^ 47 - 2 ^ 23) by (unfold HEAD in Ht0; lia).
assert (He4 : 4096 <= text + len <= 2 ^ 47 - 2 ^ 23) by (unfold HEAD in Ht0; lia).
assert (Hd2 : 0 <= dd + 1 <= 2) by (unfold dd; lia).
(* ---- the grow call ---- *)
refine (Hcall (1 - k)%nat sp0 ot ly S U W mem md [] lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq q pc (text + len) (dd + 1) xr
  v 0 0 kids keys (Z.of_nat i) cap (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail cs Qc
  HJ HARUc HRO HHDc R1 Rsp Hal16 ltac:(lia) R8 R20 R10 R3 R4 HCHc Hsq Hq24 Hq8 VP VE VD Hp4 He4 Hd2 (pi_xr_len regs)
  HPOc HHDRc HSL HBO HAP HINC HNE HGc HQg HRS HMX HLV HEVg HBBg Hwf HCS _).
intros ly' S' U' W' regs' mem' md' k' y' cap' Dold Dnew HRES HJ2 HJg HARU' HP A0 HST PERM HHDR' HSL' HBLK' MVK MVY
  HPO' HG' QK.
pose proof HARU' as (HAR' & OK' & PO').
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfr2 & _).
destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop' & Hslo' & Hshi' & _).
cbn [app] in Hfr2.
destruct HG' as (peak' & Hpk' & HG').
(* ---- the object across grow ---- *)
destruct (pio_grow B ly S U lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' (rd_ev (grow_tr 6 (Z.of_nat i) cap)) (sp0 - 144)
  v text len tcap i dn kids keys cap k' y' cap' Dold Dnew Di Da T eq_refl Hicap Hcap0 HARUc HHDc HHEADS HTXc HTXe HPOc
  HBLc HPERMc HUc HDac HSUMc HLENc HHDRc HOPc HRES HJg HARU' PERM HHDR' HSL' HBLK' MVK MVY HPO' BS)
  as (Da' & HTX' & HBL' & HPERM' & HU' & HDa' & HSUM' & HLEN' & HHD' & Ecap' & Hncap' & HOP').
(* ---- the resume env ---- *)
set (xs := pig_xs pc (text + len) (dd + 1) xr k' y' (Z.of_nat i) cap') in *.
destruct (G_env regsC regs' xs R HRP HP) as (E8 & E20 & E32 & E2 & E3 & E4).
pose proof (pig_xs_nth pc (text + len) (dd + 1) xr k' y' (Z.of_nat i) cap' (pi_xr_len regs)) as HXN. cbv zeta in HXN.
destruct HXN as (X0 & X1 & X2 & _).
set (E := Ereg regs' (fs_extraT ++ xs)) in *.
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 pc) by (unfold E; rewrite fsw_ew_xatom; exact X0).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E; rewrite fsw_ew_xatom; exact X1).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 (dd + 1)) by (unfold E; rewrite fsw_ew_xatom; exact X2).
assert (EX0u : bv_unsigned (ew E (xatom 0)) = pc) by (rewrite EX0; apply wz; lia).
assert (E8u : bv_unsigned (ew E 8) = q) by (rewrite E8; apply wz; lia).
assert (E20u : bv_unsigned (ew E 20) = v) by (rewrite E20; apply wz; lia).
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (UX0 : YP0e.U E (SOff (xatom 0) 0) = pc) by (apply U_atom; [exact EX0 | lia]).
assert (U8 : YP0e.U E (SOff 8 0) = q) by (apply U_atom; [exact E8 | lia]).
assert (U20 : YP0e.U E (SOff 20 0) = v) by (apply U_atom; [exact E20 | lia]).
(* ---- grow kept the text block and q ---- *)
assert (TK : forall z, text - HEAD <= z < text + tcap -> rdW W' mem' (Z_to_bv 64 z) = rdW W1 memC (Z_to_bv 64 z)).
{ intros z Hz.
  refine (proj2 (fsw_journal_kept_byte B STK_grow (sp0 - 144) _ lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' _ z
    HJg HARUc OK' PO' _ _)).
  - left. exists (text - HEAD), (tcap + HEAD). split; [exact HinTc|]. rewrite pio_req_hb by lia. lia.
  - apply pio_off_FPg.
    + destruct HVTX; lia.
    + intros p0 k0 Hpk Hz0. destruct (HBO p0 k0 Hpk) as (Hin0 & _ & Hk0 & _). rewrite pio_req_hb in Hz0 by lia.
      assert (Hne : (text, tcap) <> (p0, k0)).
      { intros Eq. injection Eq as <- <-. apply (HNE (text - HEAD, tcap + HEAD)); [|exact HTXe].
        exact (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ (text, tcap) Hpk). }
      exact (pio_rb_disj B lyc Sc W1 (unpoison Uc memC) mdC text tcap p0 k0 z z HARc HinTc Hin0 Htc0 Hk0 Hne
        ltac:(lia) ltac:(lia) eq_refl).
    + exact (proj1 (proj2 (proj2 (pio_rb_geo B lyc Sc W1 (unpoison Uc memC) mdC memC text tcap z HARc HRBc
        ltac:(lia))))). }
assert (QR : forall z, q <= z < q + 24 -> rdW W' mem' (Z_to_bv 64 z) = rdW W1 memC (Z_to_bv 64 z)).
{ intros z Hz. apply (pio_raw_of_mbyte _ _ z ltac:(lia)); [apply piG_not_img; unfold FS_IMG_END; lia | exact (QK z Hz)]. }
assert (HIN' : PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len pc (dd + 1) tb).
{ apply (pi_pin_kept k S regs ot text len tb ms Hk HDEP (rdW W1 memC) (rdW W' mem') q pc (dd + 1) HIN).
  - intros z Hz. split; [exact (QK z Hz) | exact (writable_at_eq tfibsegs _ _ z (QR z Hz))].
  - intros z Hz. unfold mbyte. rewrite (TK z ltac:(unfold HEAD; lia)). reflexivity. }
(* ---- the start state ---- *)
destruct (pi_txt_bytes k S regs ot text len tb ms Hk HDEP (rdW W' mem') q pc (dd + 1) (ws ++ [34]) more HIN' HRw)
  as (Hbs & Hbyt).
assert (RT : region_ok tfibsegs E (rdW W' mem') (pik_treg (xatom 0) 0 (ws ++ [34]))).
{ apply (pik_treg_ok E _ (xatom 0) pc 0 (ws ++ [34]) EX0u ltac:(lia) ltac:(lia));
    [rewrite length_app; cbn [length]; lia | exact Hbs |].
  intros j Hj. rewrite Z.add_0_r. exact (Hbyt j Hj). }
assert (Himg : text + tcap <= 65536 \/ FS_IMG_END <= text - HEAD).
{ destruct (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HARc HinTc) as [H|H];
    try rewrite pio_req_hb in H by lia; lia. }
assert (DJ : all_disjoint E (pik_treg (xatom 0) 0 (ws ++ [34])) (fsT_ret_regions 144 cs pig_rs)).
{ apply (pi_treg_disj B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTX HPO0 HDEP
    E (ws ++ [34]) cs pc EX0u E2 E8u E20u); try lia. rewrite length_app. cbn [length]. lia. }
assert (HC : conds_ok E (pi_wsc (length ws) 0))
  by (apply (pi_conds_ws k S regs ot ms Hk HDEP E (length ws) 0 pc (text + len) EX0 EX1); lia).
assert (HA0 : YK11.getr regs' 10 = sv_denot E (SLit 0)) by (rewrite A0; reflexivity).
pose proof (pi_start_T B k S regs q ot v ms Hk HDEP regsC regs' xs W' mem' r cs pig_rs pig_gf R (SLit 0) (ws ++ [34])
  (pi_wsc (length ws) 0) HST HRP HP HRok HA0 RT DJ HC) as HB.
pose proof (pik_st_ok_setm E (piG_ssB r cs R ws) _ _ HB (piG_submem (ws ++ [34]) cs) Hwf2) as HG0.
change (pik_setm (piG_ssB r cs R ws) (pik_treg (xatom 0) 0 (ws ++ [34]) :: fsT_ret_regions 144 cs pig_rsG))
  with (piG_ss r cs R ws) in HG0.
(* ---- the shadow entries ---- *)
pose proof HTX' as (_ & (HinT' & _) & _).
assert (HSH : sh_ok tfibsegs fs_Bx (piG_SH ws) E (rdW W' mem')).
{ unfold sh_ok, piG_SH, pi_SHm. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (pi_sh_blk B k S regs ot ms Hk HDEP ly' S' U' W' mem' md' E (xatom 0) (text - HEAD) (tcap + HEAD) pc 0
      (1 + Z.of_nat (length ws)) HARU' HHD' HinT'); [unfold HEAD in *; lia | lia | lia | exact UB | exact UX0].
  - exact (pi_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' U' W' mem' md'
      E 8 HARU' Hslo' Hshi' UB U8).
  - exact (pi_sh_v B k S regs ot v ms Hk HDEP ly' S' U' W' mem' md' E 20 HARU' HPO' UB U20). }
(* ---- the write windows ---- *)
pose proof (pi_awr_ret B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E ly' S' W' (unpoison U' mem') md'
  mem' cs HAR' HPO' Hfr2 E2 E8u E20u) as AW0.
assert (AWR : awr_ok tfibsegs B E (ss_mem (piG_ss r cs R ws)) (STK_parse_items (1 - k) + (ot - sp0)) ot
  ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B ly' S') ly' [] (frames S)).
{ intros a (rg & Hin & Ha). apply AW0.
  unfold piG_ss, pik_setm, fsT_ret_regions, pig_rsG in Hin. cbn [ss_mem app In] in Hin.
  unfold fsT_ret_regions, pig_rs.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - cbn [pik_treg YP09.r_wlo YP09.r_whi] in Ha. lia.
  - exists (fstk_ret 144 cs). split; [cbn [app In]; left; reflexivity | exact Ha].
  - exists fs_got_region. split; [cbn [app In]; right; left; reflexivity | exact Ha].
  - exists (fs_bcell_region 32). split; [cbn [app In]; right; right; left; reflexivity | exact Ha].
  - exists pig_q_region. split; [cbn [app In]; right; right; right; left; reflexivity | exact Ha].
  - cbn [pig_v_regionG YP09.r_wlo YP09.r_whi] in Ha. lia. }
(* ---- the run S1f / S1 to parse_string ---- *)
unfold piG_fin in HFIN. cbv zeta in HFIN.
destruct HFIN as (Fpc & Fob & Fresv & Fregs & Fnth1 & Fnth4 & Fnth5).
refine (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx (piG_SH ws) (piG_ss r cs R ws)) fs_Bx
  fs_Bspan (piG_SH ws) (piG_ss r cs R ws) st (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
  (STK_parse_items (1 - k) + (ot - sp0)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md [] ly' S' U' md'
  (rd_ev T + rd_ev (grow_tr 6 (Z.of_nat i) cap)) Qc HG0 HSH HSTAT HRUN I HARU' HJ2 _ AWR _).
{ rewrite Fob. constructor. }
intros ws2 ms2 mat2 Hlen2 HS2 SHOK2 HJ3 HARU3 HFra HFrr HG2.
set (K := run_K 0 fs_Bx (piG_SH ws) (piG_ss r cs R ws)) in *.
set (E' := extK E K ws2) in *.
assert (HK : forall n, (n <= 52)%nat -> ew E' n = ew E n)
  by (intros n Hn; apply (pi_ew_extK k S regs ot ms Hk HDEP); unfold xatom in HKb; lia).
assert (E'8 : ew E' 8 = Z_to_bv 64 q) by (rewrite HK by lia; exact E8).
assert (E'20 : ew E' 20 = Z_to_bv 64 v) by (rewrite HK by lia; exact E20).
assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite HK by lia; exact E32).
assert (E'2 : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite HK by lia; exact E2).
assert (E'3 : ew E' 3 = Z_to_bv 64 (as_gp B)) by (rewrite HK by lia; exact E3).
assert (E'4 : ew E' 4 = Z_to_bv 64 (as_tp B)) by (rewrite HK by lia; exact E4).
assert (E'8u : bv_unsigned (ew E' 8) = q) by (rewrite E'8; apply wz; lia).
assert (Hed : ed E' = (fun _ => [])) by (unfold E'; rewrite pi_ed_extK; reflexivity).
assert (D4 : forall n z c, ew E' n = Z_to_bv 64 z -> 0 <= z -> 0 <= c -> z + c < 2 ^ 64 ->
  sv_denot E' (SOff n c) = Z_to_bv 64 (z + c)).
{ intros n z c Hn Hz Hc Hzc. apply bv_eq. rewrite denot_SOff, Hn, (wz z) by lia. rewrite (wz (z + c)) by lia.
  apply zcanon_id. unfold M64. lia. }
(* ---- what the run kept: every byte but the frame and q ---- *)
assert (KR : forall z, 0 <= z < 2 ^ 64 -> ~ (sp0 - 144 <= z < sp0) -> ~ (q <= z < q + 24) ->
  ms_mem ms2 (Z_to_bv 64 z) = mem' (Z_to_bv 64 z)).
{ intros z Hz H1 H2. apply HFra. rewrite wz by lia. intros Hw.
  destruct (piG_wrange E r cs R ws z E2 E8u Hw) as [Hw'|Hw']; contradiction. }
assert (SB : same_below mem' (ms_mem ms2) alloc_ceiling) by (intros z Hz; apply KR; lia).
assert (SBm : forall z, 0 <= z < alloc_ceiling -> rdW W' (ms_mem ms2) (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
  by (intros z Hz; unfold mrestrict; rewrite (SB z Hz); reflexivity).
assert (AV : forall z, sp0 <= z < 2 ^ 64 -> ~ (q <= z < q + 24) ->
  rdW W' (ms_mem ms2) (Z_to_bv 64 z) = rdW W1 memC (Z_to_bv 64 z)).
{ intros z Hz Hq.
  assert (Ea : aview tfibsegs (w_H W') (unpoison U' mem') z = aview tfibsegs (w_H W1) (unpoison Uc memC) z).
  { pose proof HJg as (_ & _ & _ & _ & _ & _ & _ & _ & HJ9 & _). apply HJ9; lia. }
  rewrite (fsw_aview_unpoison_high B ly' S' U' W' mem' md' z HARU' ltac:(lia)),
    (fsw_aview_unpoison_high B lyc Sc Uc W1 memC mdC z HARUc ltac:(lia)) in Ea.
  rewrite <- (piG_raw_of_aview _ _ _ _ z ltac:(lia) (piG_not_img z ltac:(unfold FS_IMG_END; lia)) Ea).
  unfold mrestrict. rewrite (KR z ltac:(lia) ltac:(lia) Hq). reflexivity. }
(* ---- the parse_string configuration ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E' (sh_ss st) ms2 HS2 Fresv) as Ems2. rewrite Fpc in Ems2.
rewrite Ems2.
change (SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_parse_string (ms_regs ms2) (ms_mem ms2)
  (with_vm_backing (m_vm_lazy md') mat2 md')) Qc).
apply (KIP (T ++ X) ly' S' U' W' (ms_mem ms2) (with_vm_backing (m_vm_lazy md') mat2 md') (ms_regs ms2) chq
  (pc + Z.of_nat (length ws)) k' y' cap' Da' peak').
(* ---- pi_IP ---- *)
pose proof (pi_regs_of_stop E' (sh_ss st) ms2 (w_H W') pi_regs_ps HS2 Fregs) as RG.
destruct (piG_regsP_stop E' (ms_regs ms2) RG E'8 E'20 E'32 E'2 E'3 E'4 Hed) as (RP2 & R1' & R10').
pose proof (fsw_region_nth E' (sh_ss st) (restrict (w_H W') ms2) 4 (piG_q ws) HS2 Fnth4) as RQ.
rewrite restrict_mem in RQ. unfold piG_q in RQ.
pose proof (fsw_region_nth E' (sh_ss st) (restrict (w_H W') ms2) 1 _ HS2 Fnth1) as RF. rewrite restrict_mem in RF.
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem')).
{ apply (arodata_kept B STK_grow (sp0 - 144) _ lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' _ HJg HARUc OK' PO');
    [| | exact HRO].
  - apply sink_closed_pos. apply Forall_app. split; [repeat constructor; cbn [fst]; lia|].
    apply Forall_app. split.
    + apply Forall_forall. intros rr Hrr. unfold ablocks_fp, rd_hblocks in Hrr.
      apply in_map_iff in Hrr as (b1 & <- & Hb1). apply in_map_iff in Hb1 as ((aa, kk0) & <- & Haa).
      destruct (HBO aa kk0 Haa) as (Hin & _). cbn [fst snd].
      destruct (fsw_ablock_low B lyc Sc W1 (unpoison Uc memC) mdC _ _ HARc Hin) as (Hb4 & _). lia.
    + unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - intros a Hro0. apply pio_off_FPg.
    + intros Hva. exact ((proj1 (proj2 (pio_v_geo B lyc Sc W1 (unpoison Uc memC) mdC memC v a HARc HPOc ltac:(lia))))
        (fsw_roP_img a Hro0)).
    + intros p0 k0 Hpk Hz. pose proof (HBO p0 k0 Hpk) as HRB0. pose proof HRB0 as (_ & _ & Hk0 & _).
      rewrite pio_req_hb in Hz by lia.
      exact ((proj1 (proj2 (pio_rb_geo B lyc Sc W1 (unpoison Uc memC) mdC memC p0 k0 a HARc HRB0 ltac:(lia))))
        (fsw_roP_img a Hro0)).
    + intros Hps. exact (FSW_grow_holds.fs_pstat_not_ro a Hps Hro0). }
unfold pi_IP. cbv beta zeta.
split; [exact Hms|].
split; [rewrite Htr3, <- app_assoc, Ecap', Nat2Z.id; reflexivity|].
split; [lia|].
split; [destruct HSL' as (_ & (_ & Hc54) & _); exact Hc54|].
split.
{ split; [rewrite pim_rd_ev_app, <- EX; exact HJ3|].
  split; [exact HARU3|]. split; [exact (arodata_below B W' mem' (ms_mem ms2) SB HRO') | exact HHD']. }
split; [exact R1'|]. split; [exact R10'|]. split; [exact RP2|].
split.
{ apply (pi_frameL_of B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTX HPO0 HDEP
    HVSP E' _ cs' (pi_xr_len regs) E'2 E'8 E'20 E'32); [| exact RF | exact Hincl].
  intros j Hj. rewrite HK by (unfold xatom; lia).
  exact (pi_pig_xs_saved regs' pc (text + len) (dd + 1) xr k' y' (Z.of_nat i) cap' j (pi_xr_len regs) Hj). }
split.
{ split.
  { apply (pi_chain_kept lyc ly' _ _ sp0 q (ly_top ly) chq HCH HCHF HTOP Htop').
    intros z Hz Hq.
    rewrite (fsw_aview_unpoison_high B ly' S' U' W' (ms_mem ms2) _ z HARU3 ltac:(lia)),
      (fsw_aview_unpoison_high B lyc Sc Uc W1 memC mdC z HARUc ltac:(lia)).
    unfold aview, mbyte. rewrite (AV z ltac:(lia) Hq). reflexivity. }
  split; [exact HCHF|]. split; [exact Htop'|].
  split.
  { assert (V0 : val_mem tfibsegs (rdW W' (ms_mem ms2)) q 8 (pc + Z.of_nat (length ws))).
    { pose proof (fsw_field E' _ 8 q _ 0 24 0 24 0 8 (SOff (xatom 0) (Z.of_nat (length ws))) (pc + Z.of_nat (length ws))
        RQ E'8u ltac:(cbn; tauto) (D4 (xatom 0) pc (Z.of_nat (length ws)) ltac:(rewrite HK by (unfold xatom; lia); exact EX0) ltac:(lia) ltac:(lia)
        ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite Z.add_0_r in V. exact V. }
    assert (V8 : val_mem tfibsegs (rdW W' (ms_mem ms2)) (q + 8) 8 (text + len)).
    { pose proof (fsw_field E' _ 8 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len) RQ E'8u ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0, HK by (unfold xatom; lia); exact EX1) ltac:(cbn; lia) ltac:(cbn; lia)) as V. exact V. }
    assert (V16 : val_mem tfibsegs (rdW W' (ms_mem ms2)) (q + 16) 4 (dd + 1)).
    { pose proof (fsw_field E' _ 8 q _ 0 24 0 24 16 4 (SOff (xatom 2) 0) (dd + 1) RQ E'8u ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0, HK by (unfold xatom; lia); exact EX2) ltac:(cbn; lia) ltac:(cbn; lia)) as V. exact V. }
    pose proof RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E'8u in RQW.
    apply (piG_pin_new (rdW W1 memC) _ q pc _ (dd + 1) HIN V0 V8 V16 RQW ltac:(lia)).
    intros z Hz. unfold mbyte. rewrite (SBm z ltac:(unfold HEAD in *; lia)), (TK z ltac:(unfold HEAD in *; lia)).
    reflexivity. }
  apply (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W' memC (ms_mem ms2) sp0 HWK); [|lia].
  intros z Hz Hq. pose proof (AV z ltac:(lia) Hq) as Ez. split.
  - unfold mbyte. rewrite Ez. reflexivity.
  - split; intros Hw; [exact (writable_at_eq tfibsegs _ _ z Ez Hw) | exact (writable_at_eq tfibsegs _ _ z (eq_sym Ez) Hw)]. }
split; [exact (pim_rest_skip tb text pc ws _ ltac:(lia) HREST')|].
split.
{ pose proof HTX' as (Ht4' & HRB' & Hlt').
  destruct (fsw_rblock_low B ly' S' W' (unpoison U' mem') md' mem' text tcap HAR' HRB') as (Lt1 & Lt2).
  split; [split; [exact Ht4'|]; split; [|exact Hlt']|].
  { apply (pio_rblock_keep B ly' S' W' mem' (ms_mem ms2) text tcap HRB'). intros z Hz. apply SBm. unfold HEAD in *. lia. }
  split; [exact (pobj_below B ly' S' W' (unpoison U' mem') md' mem' (ms_mem ms2) v HAR' SB HPO')|].
  split; [exact (rd_blocks_ok_below B ly' S' W' (unpoison U' mem') md' mem' (ms_mem ms2) _ HAR' SB HBL')|].
  split; [exact HPERM'|]. split; [exact HU'|]. split; [exact HDa'|]. split; [exact HSUM'|]. split; [exact HLEN'|].
  split; [|lia].
  apply (fs_glob_below W' mem' (ms_mem ms2) _ _ _ _ SB).
  rewrite PjGrammar.held_app, length_app, Nat2Z.inj_add, <- EX.
  replace (live + (PjGrammar.held T + PjGrammar.held (grow_tr 6 (Z.of_nat i) cap)))
    with (live + PjGrammar.held T + PjGrammar.held (grow_tr 6 (Z.of_nat i) cap)) by lia.
  replace (cnt + (Z.of_nat (length T) + Z.of_nat (length (grow_tr 6 (Z.of_nat i) cap))))
    with (cnt + Z.of_nat (length T) + Z.of_nat (length (grow_tr 6 (Z.of_nat i) cap))) by lia.
  exact HG'. }
assert (HH2 : PjStruct.pj_hdr tfibsegs (rdW W' (ms_mem ms2)) v 6 0 0 k' y' (Z.of_nat i) cap').
{ apply (parse_items_shape.pis_hdr_frame tfibsegs (rdW W' mem') _ v 6 0 0 k' y' (Z.of_nat i) cap' HHDR').
  intros z Hz. apply pio_same_raw. apply SBm. lia. }
split; [exact HH2|].
apply (parse_items_shape.pis_frame tfibsegs (rdW W' mem') _ _ _ v true 0 k' y' cap' (Z.of_nat i) (map snd dn)
  (map fst dn) Di 0 (Z.of_nat i) HOP' HH2 ltac:(lia) (fun a0 k0 H => H)).
intros z Hz. rewrite length_map in Hz.
destruct (pio_ifoot_in k' y' cap' (Z.of_nat i) Di z ltac:(lia) Hz) as ((a0 & k0) & Hin0 & Hh0).
destruct (fsw_rblock_low B ly' S' W' (unpoison U' mem') md' mem' a0 k0 HAR' (HBL' a0 k0 Hin0)) as (L1 & L2).
unfold PjStruct.pj_holds in Hh0. cbn [fst snd] in Hh0.
apply pio_same_raw. apply SBm. unfold HEAD in *. lia.
Qed.

(* ================= (G) the grow step ================= *)
Lemma pi_step_G : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
    (Qc : world tfibsegs -> config -> Prop),
  IG dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' kids' keys' cap' Da' peak1',
     IP dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Di Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_parse_string regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc HIG KIP.
unfold pi_IG in HIG. cbv zeta in HIG.
destruct HIG as (Hms & Htr & Hicap & Hcap0 & HJC & R1 & R10 & HRP & HFR & HSTK & HREST' & HBL & HOBJ).
pose proof G_qs as (_ & _ & _ & Hqc & Hq47). pose proof G_vrng as (Hv1 & Hv2).
pose proof asan_consts as (C1 & _).
destruct (Nat.eqb (length dn) 0) eqn:Ei.
- (* the first member: grow #1 at 0x84b68, segment S1f *)
  refine (piG_gen 0x84b6c pi_cs0 pi_R0 [] piG_cs_s1f piG_st_s1f dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys
    cap Di Da peak1 Qc (pig_call_84b68 B HSS HGROW) pi_R0_ok pi_wf_cs0_g piG_wf_s1f piG_run_s1f piG_static_s1f
    piG_K_s1f piG_fin_s1f piG_incl_s1f Hms Htr Hicap Hcap0 HJC R1 R10 HRP _ HSTK HREST' HBL HOBJ KIP).
  intros regs' k' y' cap' HP. apply (pi_cs0_ok _ _ sp0 xr (pi_xr_len regs)); [|exact HFR].
  intros j Hj. exact (pi_pig_xs_saved regs' pc (text + len) (dd + 1) xr k' y' _ cap' j (pi_xr_len regs) Hj).
- (* a later member: grow #2 at 0x84e60, segment S1 pr k *)
  refine (piG_gen 0x84e64 pi_csL pi_RL (pi_wsb pr (dd + 1)) pi_csL (piG_st_s1 pr k) dn kk x rm T lyc Sc Uc W1 memC mdC
    regsC chq pc kids keys cap Di Da peak1 Qc (pig_call_84e60 B HSS HGROW) pi_RL_ok pi_wf_csL_g (piG_wf_s1 pr k Hk)
    (piG_run_s1 pr k Hk) (piG_static_s1 pr k Hk) (piG_K_s1 pr k Hk) (piG_fin_s1 pr k Hk) (incl_refl _)
    Hms Htr Hicap Hcap0 HJC R1 R10 HRP _ HSTK HREST' HBL HOBJ KIP).
  intros regs' k' y' cap' HP.
  destruct (G_env regsC regs' (pig_xs pc (text + len) (dd + 1) xr k' y' (Z.of_nat (length dn)) cap') pi_RL HRP HP)
    as (E8 & E20 & E32 & _).
  apply (pi_csL_ok _ _ sp0 xr q v (pi_xr_len regs)); [| exact E8 | exact E20 | exact E32 | lia | lia | lia | lia
    | exact HFR].
  intros j Hj. exact (pi_pig_xs_saved regs' pc (text + len) (dd + 1) xr k' y' _ cap' j (pi_xr_len regs) Hj).
Qed.
End X.
