(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): step Ve of parse_items' member loop, the LAST member
   (rm = []): from pi_IV at the parse_value call (0x84d98) to parse_items_spec k's post Q at the `ret` (0x84f10).
   Route: FSW_parse_items_calls.pic_call_pv_84d98 (parse_value at level k + 1; the frame chunks pi_csL under the resume
   env, the budgets by pi_budget, the member facts by pi_mem_facts); FSW_parse_items_obj.pio_value on the callee's
   post; the resume state cut to the frame, the shadow-base cells, q and v (pik_st_ok_setm), with v's write window
   NARROWED to [40, 48) (a Theorem Labs lane's rule for the v-bytes gap: pig_v_region's window [0, 56) would let the run's
   frame_of lose v's padding, num and str), the callee-saved registers restated, the read-only text window
   pi_wsb pr k ++ [125] and the white-space conditions added; that state is the S4e start state with the narrowed
   window (pve_ss pr k), measured here like FSW_parse_items_seg.v's pi_ss_s4e (same stop, 4 cases); the run by
   fsw_run_tok_AJU; at the stop pio_snoc (the store v->n := n + 1) and pio_close (ms = dn ++ [(kk, x)]); the ret by
   FSW_ret.fsw_retU as FSW_pitems_dev.v's pitems_nil does it; Q's post from the stop's q region (in->p past `}`,
   in->depth = k; the absolute position from the two rest_at lengths), the windows kept (wkeep), the blocks and the
   trace (T ++ ttrace x = ttrace (JObj ms)). No atexit / __cxa_atexit call is met.
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
(* callee: parse_value at level k + 1 *)
Hypothesis HPV : @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k).

(* ================= the S4e start state with v's write window narrowed to v->n ================= *)
Definition pve_v : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 56 40 48
    [YP09.mkChunk 0 (CVal 4 (SLit 6)); YP09.mkChunk 24 (CVal 8 (SOff (xatom 16) 0));
     YP09.mkChunk 32 (CVal 8 (SOff (xatom 17) 0)); YP09.mkChunk 40 (CVal 8 (SOff (xatom 18) 0));
     YP09.mkChunk 48 (CVal 8 (SOff (xatom 19) 0))].
Definition pve_rs : list YP09.region := [pig_q_region; pve_v].
Definition pve_ss (b : bool) (j : nat) : sstate :=
  let ws := pi_wsb b (Z.of_nat j) in
  pik_addf (pik_addr (pik_setr (fss_retT 0x84d9c 144 pi_csL pve_rs pic_gf) ((10%bv, SLit 0) :: pi_RL))
    [pik_treg (xatom 0) 0 (ws ++ [125])]) [] (pi_wsc (length ws) 0) [].
Definition pve_st (b : bool) (j : nat) : shst := fst (pi_tok_run (pi_SH_s4e b j) (pve_ss b j)).
(* the stop's q and v regions *)
Definition pve_qstop (b : bool) (j : nat) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 24 0 24
    [YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) (-1)));
     YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) (1 + Z.of_nat (length (pi_wsb b (Z.of_nat j))))));
     YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))].
Definition pve_vstop : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 56 40 48
    [YP09.mkChunk 40 (CVal 8 (SOff (xatom 18) 1)); YP09.mkChunk 0 (CVal 4 (SLit 6));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 16) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 17) 0));
     YP09.mkChunk 48 (CVal 8 (SOff (xatom 19) 0))].
(* the callee-saved registers at the ret: sp = the entry sp, gp, tp, s0 .. s11 = xatom 4 .. 15 *)
Definition pve_expect (r : bv 5) : sv :=
  if Z.eqb (bv_unsigned r) 2 then SOff 2 144
  else if Z.eqb (bv_unsigned r) 3 then SOff 3 0
  else if Z.eqb (bv_unsigned r) 4 then SOff 4 0
  else if Z.eqb (bv_unsigned r) 8 then SOff (xatom 4) 0
  else if Z.eqb (bv_unsigned r) 9 then SOff (xatom 5) 0
  else SOff (xatom (Z.to_nat (bv_unsigned r) - 12)) 0.

(* MEASURED (vm_compute on the pinned fs.asan, 4 cases): the run goes to the ret with no obligation *)
Lemma pve_K : forall b j, (j <= 1)%nat -> run_K 0 fs_Bx (pi_SH_s4e b j) (pve_ss b j) = 53%nat.
Proof. intros [|] [|[|j]] Hj; try lia; vm_compute; reflexivity. Qed.
Lemma pve_static : forall b j, (j <= 1)%nat ->
  sh_static_ok (run_K 0 fs_Bx (pi_SH_s4e b j) (pve_ss b j)) fs_Bx fs_Bspan (pi_SH_s4e b j)
    (ss_facts (pve_ss b j)) (ss_mem (pve_ss b j)) = true.
Proof. intros [|] [|[|j]] Hj; try lia; vm_compute; reflexivity. Qed.
Lemma pve_run : forall b j, (j <= 1)%nat ->
  pi_tok_run (pi_SH_s4e b j) (pve_ss b j) = (pve_st b j, TS_stopped (SR_jalr (SOff (xatom 3) 0))).
Proof. intros [|] [|[|j]] Hj; try lia; vm_compute; reflexivity. Qed.
Lemma pve_fin : forall b j, (j <= 1)%nat ->
  let s := sh_ss (pve_st b j) in
  ss_pc s = 0x84f10 /\ sh_obls (pve_st b j) = [] /\ ss_resv s = None /\
  pi_regs_are s pi_regs_ret = true /\
  forallb (fun r => sv_eqb (sr_get (ss_regs s) r) (pve_expect r)) CALLEE_SAVED = true /\
  nth_error (ss_mem s) 4 = Some (pve_qstop b j) /\ nth_error (ss_mem s) 5 = Some pve_vstop.
Proof. intros [|] [|[|j]] Hj; try lia; vm_compute; repeat split; reflexivity. Qed.
Lemma pve_wf : regions_wf (fsT_ret_regions 144 pi_csL pve_rs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pve_cs_eq : CALLEE_SAVED = [2; 3; 4]%bv ++ map (fun j => nth j pi_saved 0%bv) (seq 1 12).
Proof. vm_compute. reflexivity. Qed.
Lemma pve_expect_saved : forall j, (1 <= j < 13)%nat -> pve_expect (nth j pi_saved 0%bv) = SOff (xatom (3 + j)) 0.
Proof. intros j Hj. do 13 (destruct j as [|j]; [try lia; vm_compute; reflexivity|]). lia. Qed.

(* ================= the region lists ================= *)
Lemma pve_subregion_refl : forall r, subregion r r.
Proof. intros r. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia | intros c Hc; exact Hc]. Qed.
Lemma pve_subregion_v : subregion pve_v pig_v_region.
Proof.
unfold pve_v, pig_v_region, subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia | intros c Hc; exact Hc].
Qed.
Lemma pve_sub_g : submem (fsT_ret_regions 144 pi_csL pve_rs) (fsT_ret_regions 144 pi_csL pig_rs).
Proof.
unfold fsT_ret_regions, pve_rs, pig_rs. cbn [app].
repeat apply submem_keep; try apply pve_subregion_refl; try exact pve_subregion_v; try apply submem_nil.
Qed.
Lemma pve_sub_c : forall cap', submem (fsT_ret_regions 144 pi_csL pve_rs) (fsT_ret_regions 144 pi_csL (pic_rs cap')).
Proof.
intros cap'. unfold fsT_ret_regions, pve_rs, pic_rs. cbn [app].
repeat apply submem_keep; try apply pve_subregion_refl; try exact pve_subregion_v; try apply submem_nil.
Qed.
(* the start state's write windows: inside the resume's (pig_rs), and where they lie *)
Lemma pve_wr_sub : forall E z bs, in_wrange E (pik_treg (xatom 0) 0 bs :: fsT_ret_regions 144 pi_csL pve_rs) z ->
  in_wrange E (fsT_ret_regions 144 pi_csL pig_rs) z.
Proof.
intros E z bs (r & Hin & Hr). unfold fsT_ret_regions, pve_rs in Hin. cbn [app In] in Hin.
unfold fsT_ret_regions, pig_rs. cbn [app].
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- cbn [pik_treg YP09.r_wlo YP09.r_whi] in Hr. lia.
- exists (fstk_ret 144 pi_csL). split; [left; reflexivity | exact Hr].
- exists fs_got_region. split; [right; left; reflexivity | exact Hr].
- exists (fs_bcell_region 32). split; [right; right; left; reflexivity | exact Hr].
- exists pig_q_region. split; [right; right; right; left; reflexivity | exact Hr].
- exists pig_v_region. split; [right; right; right; right; left; reflexivity|].
  cbn [pve_v pig_v_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hr |- *. lia.
Qed.
Lemma pve_wr_cases : forall E z bs, in_wrange E (pik_treg (xatom 0) 0 bs :: fsT_ret_regions 144 pi_csL pve_rs) z ->
  bv_unsigned (ew E 2) <= z < bv_unsigned (ew E 2) + 144 \/ bv_unsigned (ew E 8) <= z < bv_unsigned (ew E 8) + 24 \/
  bv_unsigned (ew E 20) + 40 <= z < bv_unsigned (ew E 20) + 48.
Proof.
intros E z bs (r & Hin & Hr). unfold fsT_ret_regions, pve_rs in Hin. cbn [app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fstk_ret fs_got_region fs_bcell_region pig_q_region pve_v YP09.r_base YP09.r_wlo YP09.r_whi base_val]
    in Hr; lia.
Qed.

(* ================= small facts ================= *)
Lemma pve_bytes_at_eq : forall (m m' : word -> option byte) a bs,
  (forall j, (j < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  Mem.bytes_at tfibsegs m a bs -> Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (H i Hi). exact (H3 i Hi).
Qed.
Lemma pve_wr_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.
Lemma pve_val_eq : forall (m m' : word -> option byte) a n z,
  (forall j, (j < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  val_mem tfibsegs m a n z -> val_mem tfibsegs m' a n z.
Proof. intros m m' a n z H Hv j Hj. unfold mbyte. rewrite (H j Hj). exact (Hv j Hj). Qed.

(* ================= (Ve) the last member: parse_value call -> S4e -> the ret ================= *)
Lemma pi_step_Ve : forall dn kk x T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1 a,
  IV dn kk x [] T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_value regsC memC mdC) Q.
Proof.
intros dn kk x T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a HIV.
unfold pi_IV, pi_IK in HIV. cbv zeta in HIV.
destruct HIV as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HST & HTXT & HBL & HOBJ & Hu64 & Hcstr) &
  R1 & R10 & R11 & HZK & HPK).
(* ---- the entry's facts ---- *)
pose proof HPRE as (HPREU & _).
pose proof HPREU as (HAPRE & _ & _).
pose proof HAPRE as (HAR0 & Hra0 & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & Hhi47 & _ & _ & Htophi).
pose proof (pi_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsplo & Hsphi).
pose proof (pi_stk144 k S regs ot ms Hk HDEP) as Hstk144.
pose proof (pi_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof (pi_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv4096 & Hvc).
pose proof HWIN as (Hsq & Hq24 & _ & Hotly & _).
pose proof asan_consts as (C1 & _).
pose proof HTX as (Htx4096 & HtxB & Htxlen).
pose proof HtxB as (HinT & _ & Htcap0 & _).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR0 HtxB) as (_ & Htcapc).
assert (Himg : text + tcap <= 65536 \/ FS_IMG_END <= text - HEAD).
{ pose proof (fsw_ablock_off_img B ly S W (unpoison U mem) md _ _ HAR0 HinT) as Hi.
  rewrite pio_req_hb in Hi by exact Htcap0. unfold HEAD in *. destruct Hi as [Hi|Hi]; [left|right]; lia. }
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & Ht0 & (Hp0 & Hp0e) & Hte & _ & Hlen & _).
pose proof (pi_rest_len _ _ _ _ _ _ _ HIN0) as HRL0. rewrite HREST, length_app in HRL0.
assert (EK1 : Z.of_nat (Datatypes.S k) = Z.of_nat k + 1) by lia.
(* ---- the invariant's pieces ---- *)
pose proof HJC as (HJ1 & HARU1 & HRO1 & HHD1).
pose proof HARU1 as (HAR1 & _ & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfr1 & Hnev1 & _). cbn [app] in Hfr1.
pose proof HRP as (Rsp & R8 & R20 & R3 & R4 & _).
destruct HST as (HCH1 & HCHF & Htop1 & HIN1 & HWK1).
destruct HBL as (HTX1 & HPO1 & HRB1 & HPERM1 & HUc & HDa & HSUM1 & HLEN1 & HGL1 & Hpk1).
destruct HOBJ as (HHDR1 & HOP1).
pose proof HOP1 as (_ & HAP1 & _).
assert (Hn : Z.of_nat (length dn) < cap) by lia.
destruct (pi_mem_facts k S regs ot ms Hk HDV HDS HWF HDEP dn kk x [] Hms) as (Hplain & HSO & HSTR & HWFx & HDEPx).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN1) as (_ & _ & _ & (Hpc0 & Hpce) & _).
assert (ETR : PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.ttrace x)
  by (rewrite Htr; cbn [PjRoundTrip.tgo_obj]; rewrite app_nil_r; reflexivity).
assert (EV : rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) = rd_ev T + rd_ev (PjRoundTrip.ttrace x))
  by (rewrite ETR; apply pim_rd_ev_app).
assert (HTXT' : ReaderRes.rest_at tb text pc = (if pr then [32] else []) ++
  concat (WriterValue.wvpieces x pr (Z.of_nat (Datatypes.S k))) ++ (pi_wsb pr (Z.of_nat k) ++ [125] ++ rest)).
{ rewrite HTXT, EK1. reflexivity. }
(* the key block is apart from v (a block live at the call but not at the entry) *)
assert (HinA : In (a, Z.of_nat (length kk) + 1)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (HAPa : PjStruct.pj_apart [(a, Z.of_nat (length kk) + 1)] v).
{ intros b z Hb Hh. destruct Hb as [<-|[]]. unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
  pose proof (HRB1 _ _ HinA) as (HinAb & _ & HKa & _).
  destruct (pio_jr_frames B _ _ _ ly S W (unpoison U mem) md lyc Sc W1 (unpoison Uc memC) mdC _ HJ1 HAR0)
    as (Hfr & HFA).
  assert (Hz : a - HEAD <= z < a - HEAD + req_size (Z.of_nat (length kk) + 1 + HEAD)).
  { rewrite pio_req_hb by exact HKa. unfold HEAD in *. lia. }
  exact (pio_new_apart B ly S W mem v lyc Sc W1 (unpoison Uc memC) mdC (a - HEAD) (Z.of_nat (length kk) + 1 + HEAD)
    HAR1 HPO0 Hfr HFA
    (fun b mm Hbm _ _ => Permutation_in _ (Permutation_sym HPERM1) (in_or_app _ _ _ (or_introl Hbm)))
    HinAb (pio_perm_fresh B lyc Sc W1 (unpoison Uc memC) mdC (ablocks B ly S) _ a _ HAR1 HPERM1 HinA) z Hz). }
(* the budgets of parse_value's events ttrace x *)
destruct (pi_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc _ T (PjRoundTrip.ttrace x) []
  ltac:(rewrite ETR, app_nil_r; reflexivity) Hnev1 HPERM1 HSUM1 HLEN1) as (B1 & B2 & B3 & B4 & B5).
(* ---- the parse_value call ---- *)
pose proof (pic_call_pv_84d98 B HSS k HPV (spZ regs) ot ly S U W mem md [] lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq q
  text len pc tb tcap (map (YK11.getr regs) pi_saved) v 0 0 kids keys (Z.of_nat (length dn)) cap x pr
  (if pr then [32] else []) (pi_wsb pr (Z.of_nat k) ++ [125] ++ rest) (live + PjGrammar.held T) peak1
  (cnt + Z.of_nat (length T)) fail pi_csL Q) as CALL.
cbv zeta in CALL.
apply CALL; clear CALL.
- exact Hk.
- exact HJ1.
- exact HARU1.
- exact HRO1.
- exact HHD1.
- rewrite Hfr1, EK1. exact HFRL.
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
- apply (achain_lower _ _ (spZ regs)); [exact HCH1 | lia].
- rewrite Htop1. exact HCHF.
- lia.
- exact Hq24.
- rewrite EK1. exact HIN1.
- exact HTX1.
- exact HinT.
- exact HTXT'.
- exact (pim_wsep_ws pr).
- exact HSO.
- exact HSTR.
- exact HWFx.
- exact HDEPx.
- exact (pi_xr_len regs).
- exact HPO1.
- exact HHDR1.
- exact Hn.
- intros a0 k0 Hin. apply HRB1. apply in_or_app. left. exact Hin.
- intros b z Hb Hh. apply (HAP1 b z); [apply in_or_app; left; exact Hb | exact Hh].
- intros b Hb. unfold rd_hblocks in Hb. apply in_map_iff in Hb as ([p0 k0] & <- & Hin). cbn [fst snd].
  apply (pio_perm_fresh B lyc Sc W1 (unpoison Uc memC) mdC (ablocks B ly S) _ p0 k0 HAR1 HPERM1).
  apply in_or_app. left. exact Hin.
- exact HPK.
- exact HZK.
- exact HGL1.
- exact B1.
- exact B5.
- exact B2.
- exact B3.
- exact B4.
- exact pi_wf_csL.
- intros regs' HP.
  match goal with |- Forall (YP09.chunk_ok _ (Ereg _ (fs_extraT ++ ?xs)) _ _) _ =>
    destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pi_RL HRP HP) as (E8 & E20 & E32 & _) end.
  apply (pi_csL_ok _ (rdW W1 memC) (spZ regs) (map (YK11.getr regs) pi_saved) q v (pi_xr_len regs));
    [intros j Hj; apply pi_pig_xs_saved; [apply pi_xr_len | exact Hj] | exact E8 | exact E20 | exact E32
    | lia | lia | lia | lia | exact HFL].
- intros Dx Dax ly6 S6 W6 regs6 mem6 md6 HPDx HJ6 HJv HARU6 HP6 R106 HS6 HIN6 HWK6 HPERM6 HRT6 HSUM6 HLEN6 HPOK6
    HTX6 HGL6 HHDR6 HVB6 HBK6 HKY6.
  (* ---- the object after parse_value: pio_value ---- *)
  assert (EL : parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)] =
    (parse_items_shape.pis_slots true kids keys cap ++ Di) ++ [(a, Z.of_nat (length kk) + 1)]) by apply app_assoc.
  rewrite EL in HPERM1, HDa, HSUM1, HLEN1, HRB1, HOP1, Hcstr.
  edestruct (pio_value B ly S U lyc Sc Uc W1 memC mdC ly6 S6 W6 mem6 md6 _ _ _ v text len tcap (length dn) dn kids keys
    cap Di Da T a kk x Dx Dax eq_refl Hn HARU1 HPERM1 HUc HDa HSUM1 HLEN1 HHD1 HRB1 HPO1 HOP1 Hu64 Hcstr HAPa HPDx HJv
    HARU6 HPERM6 HRT6 HSUM6 HLEN6 HTX6 HHDR6 HVB6 HBK6 HKY6)
    as (RB6 & PM6 & EU & PD & SUM3 & LEN3 & HD6 & TX6 & PO6 & HH6 & OP6 & U6 & C6 & N6 & ND6 & AP6).
  assert (EL3 : ((parse_items_shape.pis_slots true kids keys cap ++ Di) ++ [(a, Z.of_nat (length kk) + 1)]) ++ Dx =
    parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)] ++ Dx)
    by (rewrite <- !app_assoc; reflexivity).
  rewrite EL3 in RB6, PM6, PD, SUM3, LEN3, OP6, C6, N6, ND6.
  (* ---- the resume env ---- *)
  set (p1 := pc + Z.of_nat (length (if pr then [32] else [])) +
    Z.of_nat (length (concat (WriterValue.wvpieces x pr (Z.of_nat (Datatypes.S k)))))) in *.
  destruct (pi_env_at B k S regs q ot v ms Hk HDEP regsC regs6 (pig_xs p1 (text + len) (Z.of_nat (Datatypes.S k))
    (map (YK11.getr regs) pi_saved) kids keys (Z.of_nat (length dn)) cap) pi_RL HRP HP6) as (E8 & E20 & E32 & E2 & E3 & E4).
  set (E0 := Ereg regs6 (fs_extraT ++ pig_xs p1 (text + len) (Z.of_nat (Datatypes.S k)) (map (YK11.getr regs) pi_saved)
    kids keys (Z.of_nat (length dn)) cap)) in *.
  assert (EX0 : ew E0 (xatom 0) = Z_to_bv 64 p1) by (unfold E0; rewrite fsw_ew_xatom; reflexivity).
  assert (EX1 : ew E0 (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E0; rewrite fsw_ew_xatom; reflexivity).
  assert (EX2 : ew E0 (xatom 2) = Z_to_bv 64 (Z.of_nat (Datatypes.S k))) by (unfold E0; rewrite fsw_ew_xatom; reflexivity).
  assert (EX18 : ew E0 (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn))) by (unfold E0; rewrite fsw_ew_xatom; reflexivity).
  assert (EXs : forall j, (j < 13)%nat -> ew E0 (xatom (3 + j)) = nth j (map (YK11.getr regs) pi_saved) (Z_to_bv 64 0))
    by (intros j Hj; unfold E0; apply pi_pig_xs_saved; [apply pi_xr_len | exact Hj]).
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN6) as (_ & _ & _ & (Hp1a & Hp1b) & Hte6 & _).
  assert (U0 : bv_unsigned (ew E0 (xatom 0)) = p1) by (rewrite EX0; apply unsigned_lit_small; lia).
  assert (E8u : bv_unsigned (ew E0 8) = q) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (E20u : bv_unsigned (ew E0 20) = v) by (rewrite E20; apply unsigned_lit_small; lia).
  (* ---- the text at in->p and the absolute position ---- *)
  assert (HR1 : ReaderRes.rest_at tb text p1 = pi_wsb pr (Z.of_nat k) ++ [125] ++ rest).
  { unfold p1. rewrite <- Z.add_assoc, <- Nat2Z.inj_add, <- length_app.
    apply pim_rest_skip; [lia | rewrite <- app_assoc; exact HTXT']. }
  pose proof (pi_rest_len _ _ _ _ _ _ _ HIN6) as HRL1. rewrite HR1, !length_app in HRL1. cbn [length] in HRL1.
  assert (EPOS : p1 + (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k)))) =
    p + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))))) by lia.
  (* ---- the start state ---- *)
  assert (HR1' : ReaderRes.rest_at tb text p1 = (pi_wsb pr (Z.of_nat k) ++ [125]) ++ rest)
    by (rewrite <- app_assoc; exact HR1).
  destruct (pi_txt_bytes k S regs ot text len tb ms Hk HDEP (rdW W6 mem6) q p1 (Z.of_nat (Datatypes.S k)) _ rest HIN6 HR1')
    as (Hbs & Hbm).
  assert (RT : region_ok tfibsegs E0 (rdW W6 mem6) (pik_treg (xatom 0) 0 (pi_wsb pr (Z.of_nat k) ++ [125]))).
  { apply (pik_treg_ok E0 (rdW W6 mem6) (xatom 0) p1 0 _ U0); [lia | lia | rewrite length_app; cbn [length]; lia
    | exact Hbs |].
    intros i0 Hi0. rewrite Z.add_0_r. exact (Hbm i0 Hi0). }
  assert (DJ : all_disjoint E0 (pik_treg (xatom 0) 0 (pi_wsb pr (Z.of_nat k) ++ [125])) (fsT_ret_regions 144 pi_csL pve_rs)).
  { apply (all_disjoint_sub E0 _ _ _ (fsT_ret_regions 144 pi_csL pig_rs) (pve_subregion_refl _) pve_sub_g).
    apply (pi_treg_disj B k ly S U W regs mem md q ot v text len p tcap tb ms ch Hk HPRE HWIN HQ16 HIN0 HVTX HPO0 HDEP E0
      _ pi_csL p1 U0 E2 E8u E20u); [lia | rewrite length_app; cbn [length]; lia | lia | exact Htcapc | exact Htx4096
      | exact Himg]. }
  assert (CO : conds_ok E0 (pi_wsc (length (pi_wsb pr (Z.of_nat k))) 0))
    by (apply (pi_conds_ws k S regs ot ms Hk HDEP E0 _ 0 p1 (text + len) EX0 EX1); lia).
  assert (HS7 : st_ok tfibsegs E0 (fss_retT 0x84d9c 144 pi_csL pve_rs pic_gf)
    (restrict (w_H W6) (mkst regs6 (Z_to_bv 64 0x84d9c) mem6 (seg_rom tfibsegs))))
    by exact (pik_st_ok_setm E0 _ _ (fsT_ret_regions 144 pi_csL pve_rs) HS6 (pve_sub_c cap) pve_wf).
  assert (HS8 : st_ok tfibsegs E0 (pve_ss pr k)
    (restrict (w_H W6) (mkst regs6 (Z_to_bv 64 0x84d9c) mem6 (seg_rom tfibsegs))))
    by exact (pi_start_T B k S regs q ot v ms Hk HDEP regsC regs6 _ W6 mem6 0x84d9c pi_csL pve_rs pic_gf pi_RL (SLit 0)
      _ _ HS7 HRP HP6 pi_RL_ok R106 RT DJ CO).
  (* ---- the shadow entries: the text window, q, v ---- *)
  assert (UB : YP0e.U E0 fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  pose proof HJ6 as (_ & HLY6 & _ & _ & _ & Hfr6 & _). cbn [app] in Hfr6.
  pose proof HLY6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hslo6 & Hshi6 & _).
  pose proof TX6 as (_ & HtxB6 & _). pose proof HtxB6 as (HinT6 & _).
  assert (SH8 : sh_ok tfibsegs fs_Bx (pi_SH_s4e pr k) E0 (rdW W6 mem6)).
  { unfold sh_ok, pi_SH_s4e. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (pi_sh_blk B k S regs ot ms Hk HDEP ly6 S6 _ W6 mem6 md6 E0 (xatom 0) (text - HEAD) (tcap + HEAD) p1 0
        (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k)))) HARU6 HD6 HinT6);
        [unfold HEAD; lia | lia | unfold HEAD; lia | exact UB |].
      apply U_atom; [exact EX0 | lia].
    - apply (pi_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly6 S6 _ W6 mem6 md6 E0
        8 HARU6 Hslo6 Hshi6 UB). apply U_atom; [exact E8 | lia].
    - apply (pi_sh_v B k S regs ot v ms Hk HDEP ly6 S6 _ W6 mem6 md6 E0 20 HARU6 PO6 UB). apply U_atom; [exact E20 | lia]. }
  (* ---- the write windows ---- *)
  pose proof HARU6 as (HAR6 & _ & _).
  assert (AW : awr_ok tfibsegs B E0 (ss_mem (pve_ss pr k)) (STK_parse_items (1 - k) + (ot - spZ regs)) ot
    ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B ly6 S6) ly6 [] (frames S)).
  { intros a0 Ha0. apply (pi_awr_ret B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E0 ly6 S6 W6 _ md6 mem6
      pi_csL HAR6 PO6 Hfr6 E2 E8u E20u).
    exact (pve_wr_sub E0 a0 (pi_wsb pr (Z.of_nat k) ++ [125]) Ha0). }
  (* ---- the run S4e (narrowed v window) to the ret ---- *)
  pose proof (pve_fin pr k Hk) as FIN. cbv zeta in FIN.
  destruct FIN as (Hpc9 & Hob9 & Hrv9 & Hregs9 & Hcs9 & HQ9 & HV9).
  eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W6 FUEL E0 (run_K 0 fs_Bx (pi_SH_s4e pr k) (pve_ss pr k)) fs_Bx
    fs_Bspan (pi_SH_s4e pr k) (pve_ss pr k) (pve_st pr k) (TS_stopped (SR_jalr (SOff (xatom 3) 0)))
    (mkst regs6 (Z_to_bv 64 0x84d9c) mem6 (seg_rom tfibsegs)) (STK_parse_items (1 - k) + (ot - spZ regs)) ot
    ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md [] ly6 S6 (Uc ++ rd_heads Dax) md6
    (rd_ev T + rd_ev (PjRoundTrip.ttrace x))).
  + exact HS8.
  + exact SH8.
  + exact (pve_static pr k Hk).
  + exact (pve_run pr k Hk).
  + exact I.
  + exact HARU6.
  + exact HJ6.
  + rewrite Hob9. constructor.
  + exact AW.
  + intros ws ms7 mat7 Hlen9 HS9 SH9 HJ9 HARU9 HFR9 HFR9' HG9.
    rewrite (pve_K pr k Hk) in HS9.
    set (E9 := extK E0 53 ws) in *.
    assert (EW : forall n0, (n0 < 53)%nat -> ew E9 n0 = ew E0 n0)
      by (intros n0 Hn0; exact (pi_ew_extK k S regs ot ms Hk HDEP ws E0 53 n0 Hn0)).
    pose proof (pi_regs_of_stop E9 (sh_ss (pve_st pr k)) ms7 (w_H W6) pi_regs_ret HS9 Hregs9) as HRG.
    rewrite Forall_forall in HRG.
    assert (G10 : YK11.getr (ms_regs ms7) 10%bv = sv_denot E9 (SLit 0))
      by exact (HRG (10%bv, SLit 0) ltac:(left; reflexivity)).
    assert (G1 : YK11.getr (ms_regs ms7) 1%bv = sv_denot E9 (SOff (xatom 3) 0))
      by exact (HRG (1%bv, SOff (xatom 3) 0) ltac:(do 14 right; left; reflexivity)).
    (* Q with D := slots ++ Di ++ [(a, Ka)] ++ Dx, Da := Da ++ Dax *)
    eapply SRr_mono.
    2: { intros W' c' _ HF. cbv beta delta [pi_Q].
         exists (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)] ++ Dx),
           (Da ++ Dax).
         split; [exact PD | exact HF]. }
    refine (fsw_retU B pitems_tbl pitems_tbl_ok W6 E9 (sh_ss (pve_st pr k)) ms7 (with_vm_backing (m_vm_lazy md6) mat7 md6)
      (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md ly6 S6
      (U ++ rd_heads (Da ++ Dax)) (rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms))) _ HS9 Hrv9 _ _ _ _ _ _).
    * rewrite Hpc9. vm_compute. reflexivity.
    * rewrite G1, fsw_SOff0, EW by (unfold xatom; lia).
      change (xatom 3) with (xatom (3 + 0)). rewrite (EXs 0%nat) by lia. exact Hra0.
    * rewrite EV, <- EU. exact HJ9.
    * rewrite <- EU. exact HARU9.
    * apply (fsw_preserved (w_H W6) E9 (sh_ss (pve_st pr k)) ms7 regs pve_expect HS9 Hcs9).
      intros r Hr. rewrite pve_cs_eq in Hr. apply in_app_or in Hr as [Hr|Hr].
      -- destruct Hr as [<-|[<-|[<-|[]]]].
         ++ change (pve_expect 2%bv) with (SOff 2 144). apply bv_eq. rewrite denot_SOff, EW, E2 by lia.
            unfold spZ. rewrite Z.sub_add. apply zcanon_id. pose proof (u64_range (YK11.getr regs 2)). unfold M64. lia.
         ++ change (pve_expect 3%bv) with (SOff 3 0). rewrite fsw_SOff0, EW, E3 by lia. symmetry. exact Hgp0.
         ++ change (pve_expect 4%bv) with (SOff 4 0). rewrite fsw_SOff0, EW, E4 by lia. symmetry. exact Htp0.
      -- apply in_map_iff in Hr as (j & <- & Hj). apply in_seq in Hj.
         rewrite pve_expect_saved by lia. rewrite fsw_SOff0, EW by (unfold xatom; lia). rewrite EXs by lia.
         rewrite (nth_indep _ (Z_to_bv 64 0) (YK11.getr regs 0%bv)) by (rewrite length_map; unfold pi_saved;
           cbn [length]; lia).
         apply map_nth.
    * intros mat. cbv beta.
      (* ---- the memory after the run ---- *)
      assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> ~ in_wrange E0 (ss_mem (pve_ss pr k)) z ->
        rdW W6 (ms_mem ms7) (Z_to_bv 64 z) = rdW W6 mem6 (Z_to_bv 64 z)).
      { intros z Hz Hnw. apply HFR9'. rewrite unsigned_lit_small by exact Hz. exact Hnw. }
      assert (WRC : forall z, in_wrange E0 (ss_mem (pve_ss pr k)) z ->
        spZ regs - 144 <= z < spZ regs - 144 + 144 \/ q <= z < q + 24 \/ v + 40 <= z < v + 48).
      { intros z Hz. pose proof (pve_wr_cases E0 z (pi_wsb pr (Z.of_nat k) ++ [125]) Hz) as Hc.
        rewrite E2, E8u, E20u in Hc. exact Hc. }
      assert (E9_8 : bv_unsigned (ew E9 8) = q) by (rewrite EW by lia; exact E8u).
      assert (E9_20 : bv_unsigned (ew E9 20) = v) by (rewrite EW by lia; exact E20u).
      assert (D9 : forall n0 z c, (n0 < 53)%nat -> ew E0 n0 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
        sv_denot E9 (SOff n0 c) = Z_to_bv 64 (z + c)).
      { intros n0 z c Hn0 Hz Hz0 Hzc. apply bv_eq. rewrite denot_SOff, EW, Hz by exact Hn0.
        rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
      pose proof (fsw_region_nth _ _ _ 4 _ HS9 HQ9) as RQ. rewrite restrict_mem in RQ. unfold pve_qstop in RQ.
      pose proof (fsw_region_nth _ _ _ 5 _ HS9 HV9) as RV. rewrite restrict_mem in RV. unfold pve_vstop in RV.
      (* ---- the store v->n := n + 1 closes the member: pio_snoc ---- *)
      assert (VAL40 : val_mem tfibsegs (rdW W6 (ms_mem ms7)) (v + 40) 8 (Z.of_nat (length dn) + 1)).
      { exact (fsw_field E9 _ 20 v _ 0 56 40 48 40 8 (SOff (xatom 18) 1) (Z.of_nat (length dn) + 1) RV E9_20
          ltac:(cbn; tauto) (D9 (xatom 18) (Z.of_nat (length dn)) 1 ltac:(unfold xatom; lia) EX18 ltac:(lia) ltac:(lia)) ltac:(cbn; lia)
          ltac:(cbn; lia)). }
      assert (KEEPv : forall z, 0 <= z < alloc_ceiling -> ~ (v + 40 <= z < v + 48) ->
        rdW W6 (ms_mem ms7) (Z_to_bv 64 z) = rdW W6 mem6 (Z_to_bv 64 z)).
      { intros z Hz Hzv. apply KEEP; [lia|]. intros Hw. apply WRC in Hw. lia. }
      assert (WR40 : forall z, v + 40 <= z < v + 48 -> writable_at tfibsegs (rdW W6 (ms_mem ms7)) z).
      { intros z Hz. pose proof RV as (_ & _ & RVW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RVW.
        rewrite E9_20 in RVW. replace z with (v + (z - v)) by lia. apply RVW. lia. }
      destruct (pio_snoc B ly6 S6 (Uc ++ rd_heads Dax) W6 mem6 md6 (ms_mem ms7) v text len tcap kids keys cap (length dn)
        dn kk x Di a Dx eq_refl Hn HARU6 RB6 TX6 PO6 OP6 U6 C6 N6 ND6 AP6 VAL40 KEEPv WR40)
        as (SNh & SNo & SNb & SNt & SNp).
      (* ---- struct pj_in at the ret: in->p past `}`, in->depth = k ---- *)
      pose proof (fsw_field E9 _ 8 q _ 0 24 0 24 0 8 (SOff (xatom 0) (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k)))))
        (p1 + (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k))))) RQ E9_8 ltac:(cbn; tauto)
        (D9 (xatom 0) p1 (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k)))) ltac:(unfold xatom; lia) EX0 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as VQ0.
      pose proof (fsw_field E9 _ 8 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len + 0) RQ E9_8 ltac:(cbn; tauto)
        (D9 (xatom 1) (text + len) 0 ltac:(unfold xatom; lia) EX1 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as VQ8.
      pose proof (fsw_field E9 _ 8 q _ 0 24 0 24 16 4 (SOff (xatom 2) (-1)) (Z.of_nat (Datatypes.S k) + -1) RQ E9_8
        ltac:(cbn; tauto) (D9 (xatom 2) (Z.of_nat (Datatypes.S k)) (-1) ltac:(unfold xatom; lia) EX2 ltac:(lia) ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VQ16.
      rewrite Z.add_0_r in VQ0, VQ8. rewrite EPOS in VQ0.
      replace (Z.of_nat (Datatypes.S k) + -1) with (Z.of_nat k) in VQ16 by lia.
      pose proof HIN6 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
      assert (PIN : PjIn.pj_in_ok tfibsegs (rdW W6 (ms_mem ms7)) q text len
        (p + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))))) (Z.of_nat k) tb).
      { refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 _))))))))))).
        - exact (proj2 (fsw_val_pj_u64 tfibsegs _ q _ VQ0 ltac:(lia) ltac:(lia) ltac:(lia))).
        - exact (proj2 (fsw_val_pj_u64 tfibsegs _ (q + 8) _ VQ8 ltac:(lia) ltac:(lia) ltac:(lia))).
        - exact (proj1 (fsw_pj_word4_iff tfibsegs _ (q + 16) (Z.of_nat k) ltac:(lia) ltac:(lia)) VQ16).
        - pose proof RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW.
          rewrite E9_8 in RQW. split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
        - lia.
        - apply (pve_bytes_at_eq (rdW W6 mem6)); [|exact I10].
          intros k0 Hk0. apply KEEP; [lia|]. intros Hw. apply WRC in Hw. unfold HEAD in *. lia.
        - lia. }
      (* ---- the caller's window, kept ---- *)
      assert (WKa : wkeep tfibsegs W W6 mem mem6 (spZ regs) ot q 24)
        by exact (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W6 memC mem6 (spZ regsC) HWK1 HWK6 ltac:(lia)).
      assert (WKb : wkeep tfibsegs W6 W6 mem6 (ms_mem ms7) (spZ regs) ot q 24).
      { intros z Hz Hzq.
        assert (Ez : rdW W6 (ms_mem ms7) (Z_to_bv 64 z) = rdW W6 mem6 (Z_to_bv 64 z))
          by (apply KEEP; [lia | intros Hw; apply WRC in Hw; lia]).
        split; [exact (pio_mbyte_raw _ _ z Ez) | exact (pve_wr_eq _ _ z Ez)]. }
      (* ---- the globals, kept (image addresses, off every write window) ---- *)
      assert (GK : forall g z, 65536 <= g -> g + 8 <= 6279168 ->
        val_mem tfibsegs (rdW W6 mem6) g 8 z -> val_mem tfibsegs (rdW W6 (ms_mem ms7)) g 8 z).
      { intros g z Hg1 Hg2 Hv. apply (pve_val_eq (rdW W6 mem6)); [|exact Hv].
        intros j Hj. pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR0 HPO0) as Hvimg.
        unfold FS_IMG_END in Hvimg. apply KEEP; [lia | intros Hw; apply WRC in Hw; lia]. }
      refine (conj _ (conj PIN (conj _ (conj PM6 (conj _ (conj _ (conj _ (conj SNp (conj SNt _))))))))).
      -- rewrite G10. reflexivity.
      -- exact (pi_wkeep_trans k S W regs mem q ot ms Hk HDEP W6 W6 mem6 (ms_mem ms7) (spZ regs) WKa WKb (Z.le_refl _)).
      -- rewrite Hms.
         exact (pio_close B ly6 S6 W6 (ms_mem ms7) v kids keys cap (dn ++ [(kk, x)])
           (Di ++ [(a, Z.of_nat (length kk) + 1)] ++ Dx) SNo SNb).
      -- rewrite ETR. exact SUM3.
      -- rewrite ETR. exact LEN3.
      -- destruct HGL6 as (pk & Hpk & HG6). exists pk. split; [lia|].
         rewrite ETR, PjGrammar.held_app, length_app, Nat2Z.inj_add, !Z.add_assoc.
         destruct HG6 as (G1' & G2' & G3' & G4' & GR).
         split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1']|].
         split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2']|].
         split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3']|].
         split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4']|].
         exact GR.
Qed.

End X.
