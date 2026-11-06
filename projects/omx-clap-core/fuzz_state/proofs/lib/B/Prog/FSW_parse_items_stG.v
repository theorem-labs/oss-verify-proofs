(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the GROW STEP of parse_items' member loop on image B:
   from the call-site invariant at grow (pib_IG) to the one at parse_string (pib_IP), in two halves split at the call of
   skip_ws #2 (0x84ffc, ra 0x85000), whose call-site state is pib_IW (this file):
     pi_step_G2 : pib_IW -> skip_ws #2 (FSW_parse_items_sws.pis_loop_sw) -> segment D 0x85000 .. parse_string
                  (FSW_parse_items_seg.pib_run_D, the byte at in->p is the key's opening quote) -> pib_IP.
   The B form of the A walk's pi_step_G / piG_gen (a working branch 4480a5df1ae
   lib/A/FSW_parse_items_stG.v), whose post-run half it follows; B calls skip_ws where A inlines the white space.
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
FSW_parse_items_sws FSW_parse_items_grow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= segment D's stop (measured; vm_compute) ================= *)
(* the registers at the parse_string call: ra 0x85048, a0 = q, sp, gp, tp, s1 = q, s3 = v and the loop's callee-saved *)
Definition pib_RD : list (bv 5 * sv) :=
  [(1%bv, SLit 0x85048); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (9%bv, SOff 9 0); (10%bv, SOff 9 0);
   (19%bv, SOff 19 0)] ++ pib_RL.
Lemma pib_fin_D :
  ss_pc (sh_ss pib_st_D) = A_parse_string /\ sh_obls pib_st_D = [] /\ ss_resv (sh_ss pib_st_D) = None /\
  pib_regs_are (sh_ss pib_st_D) pib_RD = true /\
  nth_error (ss_mem (sh_ss pib_st_D)) 1 = Some (YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL) /\
  nth_error (ss_mem (sh_ss pib_st_D)) 4 = Some (YP09.mkRegion (Some 9%nat) 0 24 0 0 (YP09.r_chunks pi_qR)) /\
  nth_error (ss_mem (sh_ss pib_st_D)) 5 = Some (YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pib_K_D : (xatom 20 <= run_K 0 fs_Bx pib_SHc pib_ss_D)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma pib_wf_D : regions_wf (ss_mem pib_ss_D) = true.
Proof. vm_compute. reflexivity. Qed.
(* segment D writes nothing *)
Lemma pib_D_ro : forall E a, ~ in_wrange E (ss_mem pib_ss_D) a.
Proof.
intros E a (rg & Hin & Ha).
unfold pib_ss_D, pib_start, pik_addf, pik_addr, pik_setr, pik_setm, pib_rgs, pib_RO in Hin. cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fs_got_region fs_bcell_region YP09.r_wlo YP09.r_whi fst snd] in Ha; lia.
Qed.

(* segments C / J: the stop at skip_ws #2 (ra 0x85000, a0 = q) *)
Definition pib_RW : list (bv 5 * sv) :=
  [(1%bv, SLit 0x85000); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (9%bv, SOff 9 0); (10%bv, SOff 9 0);
   (19%bv, SOff 19 0)] ++ pib_RL.
(* segment C writes the five locals; its stop lists them in the order it wrote them *)
Definition pib_cs_C : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (pi_shx 19 32)); YP09.mkChunk 24 (CVal 8 (pi_shx 19 24));
   YP09.mkChunk 16 (CVal 8 (SOff 19 32)); YP09.mkChunk 32 (CVal 8 (SOff 19 24));
   YP09.mkChunk 0 (CVal 8 (SLit 1152921504606846976))] ++ pi_cs.
Definition pib_finW (fw : Z * Z) (cs' : list YP09.chunk) (st : shst) : Prop :=
  let s := sh_ss st in
  ss_pc s = A_skip_ws /\ sh_obls st = [] /\ ss_resv s = None /\ pib_regs_are s pib_RW = true /\
  nth_error (ss_mem s) 0 = Some (YP09.mkRegion (Some 2%nat) 0 144 (fst fw) (snd fw) cs') /\
  nth_error (ss_mem s) 3 = Some (YP09.mkRegion (Some 9%nat) 0 24 0 0 (YP09.r_chunks pi_qR)) /\
  nth_error (ss_mem s) 4 = Some (YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch).
Lemma pib_fin_C : pib_finW (0, 144) pib_cs_C pib_st_C.
Proof. unfold pib_finW. vm_compute. repeat split; reflexivity. Qed.
Lemma pib_fin_J : pib_finW pib_RO pib_csL pib_st_J.
Proof. unfold pib_finW. vm_compute. repeat split; reflexivity. Qed.
Lemma pib_K_C : (xatom 20 <= run_K 0 fs_Bx pib_SHm pib_ss_C)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma pib_K_J : (xatom 20 <= run_K 0 fs_Bx pib_SHm pib_ss_J)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma pib_incl_C : incl pib_csL pib_cs_C.
Proof.
intros c Hc. unfold pib_csL in Hc. unfold pib_cs_C. apply in_app_or in Hc as [Hc | Hc]; apply in_or_app.
- left. destruct Hc as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [In]; tauto.
- right. exact Hc.
Qed.
(* the write ranges of a C / J start state: the frame's window only *)
Lemma pib_wr_CJ : forall E r cs gf R fw s a, bv_unsigned (ew E 2) = s ->
  in_wrange E (ss_mem (pib_start r cs gf (pib_rgs cs fw pib_RO pib_RO) R [] [] [] [])) a ->
  s + fst fw <= a < s + snd fw.
Proof.
intros E r cs gf R fw s a E2 (rg & Hin & Ha).
unfold pib_start, pik_addf, pik_addr, pik_setr, pik_setm, pib_rgs, pib_RO in Hin. cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val fst snd] in Ha; rewrite ?E2 in Ha; lia.
Qed.

(* an address no image byte lies at; equal views of an off-image byte are equal raw bytes (the A walk's piG_not_img /
   piG_raw_of_aview, lib/A/FSW_parse_items_stG.v 4480a5df1ae, renamed) *)
Lemma pib_not_img : forall a, FS_IMG_END <= a -> ~ in_img tfibsegs a.
Proof. intros a Ha Hi. pose proof (fs_segs_img a Hi). lia. Qed.
Lemma pib_raw_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  ~ in_img tfibsegs a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hi E. apply (pio_raw_of_mbyte (mrestrict H m) (mrestrict H' m') a Ha Hi).
unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* the saved-register entries of the resume env's extra words *)
Lemma pib_xs_saved_nth : forall p0 e d xr0 k' y' n cap' j, length xr0 = 13%nat -> (j < 13)%nat ->
  nth (3 + j) (pib_xs p0 e d xr0 k' y' n cap') (Z_to_bv 64 0) = nth j xr0 (Z_to_bv 64 0).
Proof.
intros p0 e d xr0 k' y' n cap' j Hl Hj. unfold pib_xs.
change ([Z_to_bv 64 p0; Z_to_bv 64 e; Z_to_bv 64 d] ++ xr0 ++ ?t) with
  (Z_to_bv 64 p0 :: Z_to_bv 64 e :: Z_to_bv 64 d :: xr0 ++ t).
change (nth (3 + j) (?a :: ?b :: ?c :: ?l) ?z) with (nth j l z).
rewrite app_nth1 by lia. reflexivity.
Qed.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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
(* callees: skip_ws (a Theorem Labs lane's B walk), grow (a Theorem Labs lane's B walk, lib/B/Prog/FSW_grow_holds.v) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.

(* ================= the call-site state at skip_ws #2 ================= *)
Definition pib_IW (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjGrammar.EAlloc (Datatypes.S (length (flat_map PjRoundTrip.ech kk)))
    :: PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S i) (Z.to_nat cap) rm /\
  (Datatypes.S i <= Z.to_nat cap)%nat /\ cap <= 2 ^ 54 /\
  JC lyc Sc Uc W1 memC mdC (rd_ev T) /\
  YK11.getr regsC 1 = w64 0x85000 /\ YK11.getr regsC 10 = w64 q /\
  RP regsC pib_RL /\ pib_frameL (rdW W1 memC) sp0 xr q v /\
  STKP lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    (if Nat.eqb i 0 then [] else pib_wsb pr (dd + 1)) ++ concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++
    concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pib_wsb pr dd ++
    [125] ++ rest /\
  BLK lyc Sc Uc W1 memC L Da T peak1 /\
  OBJ W1 memC L (Z.of_nat i) kids keys cap dn Di.

(* ---- the entry's facts this step reads (FSW_parse_items_lh.v) ---- *)
Lemma G_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof. exact (pil_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP). Qed.
Lemma G_stk144 : 144 <= STK_parse_items (1 - k).
Proof. exact (pil_stk144 k S regs ot ms Hk HDEP). Qed.
Lemma G_qs : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof. exact (pil_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP). Qed.
Lemma G_vrng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof. exact (pil_v_rng B k ly S U W regs mem md v ch HPRE HPO0). Qed.
Lemma G_v8 : v mod 8 = 0.
Proof. destruct HPO0 as [[(_ & Hm & _)|(_ & Hm & _)] _]. exact Hm. exact Hm. Qed.
Lemma G_text : 4096 + HEAD <= text /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP ly S W (unpoison U mem) md mem p dd HAR HTX HIN0)
  as (H1 & _ & H3 & H4 & H5). lia.
Qed.
Lemma G_q46 : 2 ^ 46 <= q.
Proof. pose proof G_qs as (_ & _ & _ & Hqc & _). pose proof asan_consts as (C1 & _). lia. Qed.

(* the atom facts pib_gf under a member-loop resume env *)
Lemma G_atoms : forall regs' p' kids keys n cap, YK11.getr regs' 9 = w64 q -> YK11.getr regs' 19 = w64 v ->
  4096 <= p' <= 2 ^ 47 - 2 ^ 23 -> 4096 <= kids <= 2 ^ 47 - 2 ^ 23 -> kids mod 16 = 0 ->
  4096 <= keys <= 2 ^ 47 - 2 ^ 23 -> keys mod 16 = 0 -> 0 <= n <= 2 ^ 54 -> 0 <= cap <= 2 ^ 54 ->
  atoms_ok (Ereg regs' (fs_extraT ++ pib_xs p' (text + len) (dd + 1) xr kids keys n cap)) pib_gf.
Proof.
intros regs' p' kids keys n cap G9 G19 Hp Hk1 Hk2 Hy1 Hy2 Hn Hc.
pose proof G_qs as (_ & _ & Hq8 & Hqc & Hq47). pose proof G_q46 as Hq46. pose proof G_vrng as (Hv1 & Hv2).
pose proof G_v8 as Hv8. pose proof G_text as (Ht1 & Ht2 & Ht3 & Ht4). unfold HEAD in Ht1.
destruct (pib_xs_nth p' (text + len) (dd + 1) xr kids keys n cap (pil_xr_len regs)) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
set (xs := pib_xs p' (text + len) (dd + 1) xr kids keys n cap) in *.
assert (XA : forall j, ew (Ereg regs' (fs_extraT ++ xs)) (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; apply fsw_ew_xatom).
assert (E9 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 9) = q)
  by (rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), G9; unfold w64; apply unsigned_lit_small; lia).
assert (E19 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 19) = v)
  by (rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19; unfold w64; apply unsigned_lit_small; lia).
unfold pib_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E19, !XA, X0, X1, X2, X16, X17, X18, X19.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & Hpb & _).
unfold dd.
rewrite (unsigned_lit_small p'), (unsigned_lit_small (text + len)), (unsigned_lit_small (Z.of_nat k + 1)),
  (unsigned_lit_small kids), (unsigned_lit_small keys), (unsigned_lit_small n), (unsigned_lit_small cap) by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
repeat split; try lia; try apply Z.mod_1_r; try exact Hq8; try exact Hv8; try exact Hk2; try exact Hy2.
Qed.

(* the registers at the parse_string stop, as pib_IP states them *)
Lemma G_regsP_stopD : forall E' (regs2 : bvmap 5 word),
  Forall (fun r => YK11.getr regs2 (fst r) = sv_denot E' (snd r)) pib_RD ->
  ew E' 9 = Z_to_bv 64 q -> ew E' 19 = Z_to_bv 64 v -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E' 2) = sp0 - 144 -> ew E' 3 = Z_to_bv 64 (as_gp B) -> ew E' 4 = Z_to_bv 64 (as_tp B) ->
  ed E' = (fun _ => []) ->
  RP regs2 pib_RL /\ YK11.getr regs2 1 = w64 0x85048 /\ YK11.getr regs2 10 = w64 q.
Proof.
intros E' regs2 HR E9 E19 E32 E2 E3 E4 Hed. rewrite Forall_forall in HR.
assert (G : forall r e, In (r, e) pib_RD -> YK11.getr regs2 r = sv_denot E' e) by (intros r e H; exact (HR (r, e) H)).
assert (G9 : YK11.getr regs2 9 = Z_to_bv 64 q) by (rewrite (G 9%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9).
assert (G19 : YK11.getr regs2 19 = Z_to_bv 64 v)
  by (rewrite (G 19%bv (SOff 19 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E19).
split; [|split; [rewrite (G 1%bv (SLit 0x85048)) by (cbn; tauto); reflexivity |
  rewrite (G 10%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9]].
split; [unfold spZ; rewrite (G 2%bv (SOff 2 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E2|].
split; [exact G9|]. split; [exact G19|].
split; [rewrite (G 3%bv (SOff 3 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E3|].
split; [rewrite (G 4%bv (SOff 4 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E4|].
apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (G r e) by (unfold pib_RD; apply in_or_app; right; exact Hin).
pose proof (pil_RL_ok) as Hok. unfold pil_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
apply pik_sv_denot_agree; [rewrite Hed; reflexivity|].
intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
- rewrite E9, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). symmetry. exact G9.
- rewrite E19, (ew_Ereg_nat regs2 _ 19 19%bv eq_refl). symmetry. exact G19.
- rewrite E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* the registers at the skip_ws #2 stop (segments C / J), as pib_IW states them *)
Lemma G_regsP_stopW : forall E' (regs2 : bvmap 5 word),
  Forall (fun r => YK11.getr regs2 (fst r) = sv_denot E' (snd r)) pib_RW ->
  ew E' 9 = Z_to_bv 64 q -> ew E' 19 = Z_to_bv 64 v -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E' 2) = sp0 - 144 -> ew E' 3 = Z_to_bv 64 (as_gp B) -> ew E' 4 = Z_to_bv 64 (as_tp B) ->
  ed E' = (fun _ => []) ->
  RP regs2 pib_RL /\ YK11.getr regs2 1 = w64 0x85000 /\ YK11.getr regs2 10 = w64 q.
Proof.
intros E' regs2 HR E9 E19 E32 E2 E3 E4 Hed. rewrite Forall_forall in HR.
assert (G : forall r e, In (r, e) pib_RW -> YK11.getr regs2 r = sv_denot E' e) by (intros r e H; exact (HR (r, e) H)).
assert (G9 : YK11.getr regs2 9 = Z_to_bv 64 q) by (rewrite (G 9%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9).
assert (G19 : YK11.getr regs2 19 = Z_to_bv 64 v)
  by (rewrite (G 19%bv (SOff 19 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E19).
split; [|split; [rewrite (G 1%bv (SLit 0x85000)) by (cbn; tauto); reflexivity |
  rewrite (G 10%bv (SOff 9 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E9]].
split; [unfold spZ; rewrite (G 2%bv (SOff 2 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E2|].
split; [exact G9|]. split; [exact G19|].
split; [rewrite (G 3%bv (SOff 3 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E3|].
split; [rewrite (G 4%bv (SOff 4 0)) by (cbn; tauto); rewrite fsw_SOff0; exact E4|].
apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (G r e) by (unfold pib_RW; apply in_or_app; right; exact Hin).
pose proof (pil_RL_ok) as Hok. unfold pil_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
apply pik_sv_denot_agree; [rewrite Hed; reflexivity|].
intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
- rewrite E9, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). symmetry. exact G9.
- rewrite E19, (ew_Ereg_nat regs2 _ 19 19%bv eq_refl). symmetry. exact G19.
- rewrite E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ================= (G2) skip_ws #2 and segment D, to parse_string ================= *)
Lemma pi_step_G2 : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
    (Qc : world tfibsegs -> config -> Prop),
  pib_IW dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' kids' keys' cap' Da' peak1',
     IP dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Di Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_parse_string regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_skip_ws regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc HIW KIP.
unfold pib_IW in HIW. cbv zeta in HIW.
destruct HIW as (Hms & Htr & Hicap & Hcap54 & HJC & R1 & R10 & HRP & HFR & HSTK & HRST & HBL & HOBJ).
set (i := length dn) in *.
set (L := parse_items_shape.pis_slots true kids keys cap ++ Di) in *.
set (ws := if Nat.eqb i 0 then [] else pib_wsb pr (dd + 1)) in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof G_sp0 as (Hal16 & Hsp1 & Hsp2). pose proof G_stk144 as H144.
pose proof G_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof G_vrng as (Hv1 & Hv2).
pose proof G_text as (Gt1 & Gt2 & Gt3 & Gt4).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HJC as (HJ & HARU & HRO & HHD). pose proof HARU as (HAR & _).
pose proof HBL as (HTXc & HPOc & HBLc & _).
pose proof HSTK as (_ & _ & _ & HIN & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc (dd + 1)
  HAR HTXc HIN) as (Ht0 & Hpc & Htl & Htc & Hac).
unfold HEAD in Ht0.
(* the text at in->p: ws, then the key's opening quote *)
assert (HRw : exists more, ReaderRes.rest_at tb text pc = ws ++ 34 :: more)
  by (rewrite HRST, pi_spieces_head; eexists; reflexivity).
destruct HRw as (more & HRw).
assert (Hws : Forall (fun c0 => PjGrammar.ws c0 = true) ws)
  by (unfold ws; destruct (Nat.eqb i 0); [constructor | apply pi_wind_ws]).
assert (HRL : Z.of_nat (length (ReaderRes.rest_at tb text pc)) = text + len - pc)
  by (unfold ReaderRes.rest_at, ReaderRes.zb; rewrite length_map, length_skipn;
      pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & _ & _ & Htb & _); lia).
assert (Hwsl : pc + Z.of_nat (length ws) < text + len)
  by (rewrite HRw, length_app in HRL; cbn [length] in HRL; lia).
(* v's arrays: cap > 0, the kids and keys blocks are live reader blocks *)
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
destruct (pib_xs_nth (pc + Z.of_nat (length ws)) (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap (pil_xr_len regs))
  as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
(* ---- skip_ws #2 and the resume at 0x85000 ---- *)
apply (pis_loop_sw B k ly S U W regs mem md q ot v text len p tcap tb ms live peak cnt fail ch Hk HSS HPRE
  HWIN HQ16 HIN0 HVTX HPO0 HDEP HVSP HSW 0x85000 (pib_xs (pc + Z.of_nat (length ws)) (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap) pib_gf
  pib_RO pib_RO pib_RO 34 lyc Sc Uc W1 memC mdC (rd_ev T) regsC chq pc ws more T Da peak1 kids keys cap dn Di Qc
  HJC R1 ltac:(unfold YK0s.ret_ok; vm_compute; reflexivity) ltac:(lia) R10 HRP HFR HSTK HRw Hws ltac:(reflexivity)
  HBL HOBJ ltac:(lia) X0 X1 X2 (fun j Hj => pib_xs_saved_nth _ _ _ xr _ _ _ _ j (pil_xr_len regs) Hj) X16 X17 X18 X19).
- intros regs' G9 G19. apply (G_atoms regs' _ kids keys (Z.of_nat i) cap G9 G19); lia.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. cbn. lia.
- left. cbn. lia.
- left. cbn. lia.
- intros ly' S' W' regs' mem' md' HJC' HP HRP' HFR' HSTK' HBL' HOBJ' QAB HSS0.
  change (pib_start 0x85000 pib_csL pib_gf (pib_rgs pib_csL pib_RO pib_RO pib_RO) pib_RL [pik_treg (xatom 0) 0 [34]] []
    pib_wsc0 []) with pib_ss_D in HSS0.
  set (pc' := pc + Z.of_nat (length ws)) in *.
  set (xs := pib_xs pc' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap) in *.
  set (E := Ereg regs' (fs_extraT ++ xs)) in *.
  destruct HJC' as (HJ2 & HARU2 & HRO2 & HHD2). pose proof HARU2 as (HAR2 & _).
  destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
  fold E in E9, E19, E32, E2, E3, E4.
  assert (EX0 : ew E (xatom 0) = Z_to_bv 64 pc') by (unfold E; rewrite fsw_ew_xatom; exact X0).
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
  (* ---- the shadow entries ---- *)
  assert (HSH : sh_ok tfibsegs fs_Bx pib_SHc E (rdW W' mem')).
  { unfold sh_ok, pib_SHc, pib_SHm. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (pil_sh_blk B k S regs ot ms Hk HDEP ly' S' Uc W' mem' md' E (xatom 0) (text - HEAD) (tcap + HEAD) pc' 0 1
        HARU2 HHD2 HinT'); [unfold HEAD; lia | lia | unfold HEAD; lia | exact UB | exact UX0].
    - exact (pil_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' Uc W' mem' md'
        E 9 HARU2 ltac:(congruence) ltac:(congruence) UB U9).
    - exact (pil_sh_v B k S regs ot v ms Hk HDEP ly' S' Uc W' mem' md' E 19 HARU2 HPO' UB U19). }
  (* ---- the write windows: none ---- *)
  assert (AWR : awr_ok tfibsegs B E (ss_mem pib_ss_D) STKt ot FP (ablocks B ly S) (ablocks B ly' S') ly' []
    (frames S)).
  { intros a Ha. exfalso. exact (pib_D_ro E a Ha). }
  (* ---- segment D: to parse_string ---- *)
  destruct pib_fin_D as (Fpc & Fob & Fresv & Fregs & Fnth1 & Fnth4 & Fnth5).
  refine (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pib_SHc pib_ss_D) fs_Bx fs_Bspan
    pib_SHc pib_ss_D pib_st_D (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 0x85000) mem' (seg_rom tfibsegs))
    STKt ot FP ly S W (unpoison U mem) md [] ly' S' Uc md' (rd_ev T) Qc HSS0 HSH pib_static_D pib_run_D I HARU2 HJ2 _
    AWR _).
  { rewrite Fob. constructor. }
  intros ws2 ms2 mat2 Hlen2 HS2 SHOK2 HJ3 HARU3 HFra HFrr HG2.
  set (K := run_K 0 fs_Bx pib_SHc pib_ss_D) in *.
  set (E' := extK E K ws2) in *.
  pose proof pib_K_D as HKb. fold K in HKb.
  assert (HK : forall n, (n <= 52)%nat -> ew E' n = ew E n)
    by (intros n Hn; apply (pil_ew_extK k S regs ot ms Hk HDEP); unfold xatom in HKb; lia).
  assert (E'9 : ew E' 9 = Z_to_bv 64 q) by (rewrite HK by lia; exact E9).
  assert (E'19 : ew E' 19 = Z_to_bv 64 v) by (rewrite HK by lia; exact E19).
  assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite HK by lia; exact E32).
  assert (E'2 : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite HK by lia; exact E2).
  assert (E'3 : ew E' 3 = Z_to_bv 64 (as_gp B)) by (rewrite HK by lia; exact E3).
  assert (E'4 : ew E' 4 = Z_to_bv 64 (as_tp B)) by (rewrite HK by lia; exact E4).
  assert (Hed : ed E' = (fun _ => [])) by (unfold E'; rewrite pil_ed_extK; reflexivity).
  (* ---- segment D wrote nothing ---- *)
  assert (KR : forall y : word, ms_mem ms2 y = mem' y) by (intros y; apply HFra; apply pib_D_ro).
  assert (RW : forall z, rdW W' (ms_mem ms2) z = rdW W' mem' z) by (intros z; unfold mrestrict; rewrite KR; reflexivity).
  assert (MB : forall a, mbyte tfibsegs (rdW W' (ms_mem ms2)) a = mbyte tfibsegs (rdW W' mem') a)
    by (intros a; unfold mbyte; rewrite RW; reflexivity).
  assert (WR : forall a, writable_at tfibsegs (rdW W' mem') a <-> writable_at tfibsegs (rdW W' (ms_mem ms2)) a)
    by (intros a; split; intros Hw; [exact (writable_at_eq tfibsegs _ _ a (RW _) Hw)
        | exact (writable_at_eq tfibsegs _ _ a (eq_sym (RW _)) Hw)]).
  assert (SB : same_below mem' (ms_mem ms2) alloc_ceiling) by (intros z Hz; apply KR).
  (* ---- the parse_string configuration ---- *)
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E' (sh_ss pib_st_D) ms2 HS2 Fresv) as Ems2. rewrite Fpc in Ems2.
  rewrite Ems2.
  change (SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_parse_string (ms_regs ms2) (ms_mem ms2)
    (with_vm_backing (m_vm_lazy md') mat2 md')) Qc).
  pose proof (pil_regs_of_stop E' (sh_ss pib_st_D) ms2 (w_H W') pib_RD HS2 Fregs) as RG.
  destruct (G_regsP_stopD E' (ms_regs ms2) RG E'9 E'19 E'32 E'2 E'3 E'4 Hed) as (RP2 & R1' & R10').
  apply (KIP T ly' S' Uc W' (ms_mem ms2) (with_vm_backing (m_vm_lazy md') mat2 md') (ms_regs ms2) chq pc' kids keys cap
    Da peak1).
  unfold pib_IP. cbv zeta.
  split; [exact Hms|]. split; [exact Htr|]. split; [exact Hicap|]. split; [exact Hcap54|].
  split.
  { split; [exact HJ3|]. split; [exact HARU3|]. split; [exact (arodata_below B W' mem' (ms_mem ms2) SB HRO2)|].
    exact HHD2. }
  split; [exact R1'|]. split; [exact R10'|]. split; [exact RP2|].
  split; [exact (pis_frameL_mb (rdW W' mem') _ sp0 xr q v (fun a _ => MB a) HFR')|].
  split.
  { destruct HSTK' as (HCH' & HCHF' & HTOP' & HIN' & HWK').
    pose proof HPRE as ((HAP0 & _ & _) & _). pose proof HAP0 as (_ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (_ & _ & _ & _ & _ & H47l & _ & Htopl & Htopl2).
    split.
    { apply (pis_chain_kept ly' ly' _ _ sp0 q (ly_top ly) chq HCH' HCHF' HTOP' HTOP').
      intros z Hz Hq.
      rewrite (fsw_aview_unpoison_high B ly' S' Uc W' (ms_mem ms2) _ z HARU3 ltac:(lia)),
        (fsw_aview_unpoison_high B ly' S' Uc W' mem' md' z HARU2 ltac:(lia)).
      unfold aview. rewrite MB. reflexivity. }
    split; [exact HCHF'|]. split; [exact HTOP'|].
    split; [apply (pil_pin_kept k S regs ot text len tb ms Hk HDEP (rdW W' mem') _ q pc' (dd + 1) HIN');
      [intros z _; split; [exact (MB z) | exact (proj1 (WR z))] | intros z _; exact (MB z)]|].
    apply (pil_wkeep_trans k S W regs mem q ot ms Hk HDEP W' W' mem' (ms_mem ms2) sp0 HWK'); [|lia].
    intros a _ _. split; [exact (MB a) | exact (WR a)]. }
  split; [exact (pim_rest_skip tb text pc ws _ ltac:(lia) HRST)|].
  split.
  { split; [split; [exact Ht4'|]; split;
      [exact (fs_rblock_below B ly' S' W' (unpoison Uc mem') md' mem' (ms_mem ms2) text tcap HAR2 SB HRBt') | exact Hlt']|].
    split; [exact (pobj_below B ly' S' W' (unpoison Uc mem') md' mem' (ms_mem ms2) v HAR2 SB HPO')|].
    split; [exact (rd_blocks_ok_below B ly' S' W' (unpoison Uc mem') md' mem' (ms_mem ms2) _ HAR2 SB HRB')|].
    split; [exact HPERM'|]. split; [exact HU'|]. split; [exact HDa'|]. split; [exact HSUM'|]. split; [exact HLEN'|].
    split; [exact (fs_glob_below W' mem' (ms_mem ms2) _ _ _ _ SB HG') | exact Hpk']. }
  destruct HOBJ' as (HH' & HOP').
  assert (SV : forall z, parse_items_shape.pis_same tfibsegs (rdW W' mem') (rdW W' (ms_mem ms2)) z)
    by (intros z; apply pio_same_raw; apply RW).
  assert (HH2 : PjStruct.pj_hdr tfibsegs (rdW W' (ms_mem ms2)) v 6 0 0 kids keys (Z.of_nat i) cap)
    by exact (parse_items_shape.pis_hdr_frame tfibsegs _ _ v 6 0 0 kids keys (Z.of_nat i) cap HH' (fun z _ => SV z)).
  split; [exact HH2|].
  exact (parse_items_shape.pis_frame tfibsegs _ _ _ _ v true 0 kids keys cap (Z.of_nat i) (map snd dn) (map fst dn) Di 0
    (Z.of_nat i) HOP' HH2 ltac:(lia) (fun a0 k0 H => H) (fun z _ => SV z)).
Qed.
(* ================= (G1) the grow call and segment C / J, to skip_ws #2 ================= *)
Lemma piG1_gen : forall (r : Z) (cs : list YP09.chunk) (R : list (bv 5 * sv)) (fw : Z * Z) (cs' : list YP09.chunk)
  (st : shst) dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
  (Qc : world tfibsegs -> config -> Prop),
  let ss := pib_start r cs pib_gf (pib_rgs cs fw pib_RO pib_RO) ((10%bv, SLit 0) :: R) [] [] [] [] in
  pib_grow_at B r -> pil_R_ok R = true -> In (8%bv, SOff 9 16) R ->
  regions_wf (fsT_ret_regions 144 cs pib_rs) = true -> regions_wf (pib_rgs cs fw pib_RO pib_RO) = true ->
  0 <= fst fw -> snd fw <= 144 ->
  pib_run pib_SHm ss = (st, TS_stopped SR_fetch) ->
  sh_static_ok (run_K 0 fs_Bx pib_SHm ss) fs_Bx fs_Bspan pib_SHm (ss_facts ss) (ss_mem ss) = true ->
  (xatom 20 <= run_K 0 fs_Bx pib_SHm ss)%nat ->
  pib_finW fw cs' st -> incl pib_csL cs' ->
  ms = dn ++ (kk, x) :: rm ->
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.tgo_obj (length dn) (Z.to_nat cap) ((kk, x) :: rm) ->
  (length dn <= Z.to_nat cap)%nat -> 0 <= cap ->
  JC lyc Sc Uc W1 memC mdC (rd_ev T) ->
  YK11.getr regsC 1 = w64 r -> YK11.getr regsC 10 = w64 v -> RP regsC R ->
  (forall regs' k' y' cap', aregs_preserved regsC regs' ->
     Forall (YP09.chunk_ok tfibsegs
       (Ereg regs' (fs_extraT ++ pib_xs pc (text + len) (dd + 1) xr k' y' (Z.of_nat (length dn)) cap'))
       (rdW W1 memC) (sp0 - 144)) cs) ->
  STKP lyc Uc W1 memC chq pc ->
  ReaderRes.rest_at tb text pc =
    (if Nat.eqb (length dn) 0 then [] else pib_wsb pr (dd + 1)) ++ concat (WriterSpec.spieces kk) ++
    WriterValue.wsep pr ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++
    concat (pi_mgo pr dd (Datatypes.S (length dn)) rm) ++ pib_wsb pr dd ++ [125] ++ rest ->
  BLK lyc Sc Uc W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) Da T peak1 ->
  OBJ W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) (Z.of_nat (length dn)) kids keys cap dn Di ->
  (forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' kids' keys' cap' Da' peak1',
     pib_IW dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Di Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_skip_ws regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Qc.
Proof.
intros r cs R fw cs' st dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 Qc ss
  Hcall HRok HR8 Hwf Hwf2 Hfw1 Hfw2 HRUN HSTAT HKb HFIN Hincl Hms Htr Hicap Hcap0 HJC R1 R10 HRP HCS HSTK HREST' HBL
  HOBJ KIW.
set (i := length dn) in *.
set (L := parse_items_shape.pis_slots true kids keys cap ++ Di) in *.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof G_sp0 as (Hal16 & Hsp1 & Hsp2). pose proof G_stk144 as H144.
pose proof G_qs as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof G_vrng as (Hv1 & Hv2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HTX as (_ & (HTXe & _) & _).
pose proof (HBL) as HBL0. pose proof (HOBJ) as HOBJ0.
destruct HJC as (HJ & HARUc & HRO & HHDc).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnevj & _ & _ & _ & _ & _ & _ & _ & Hstkj & _).
pose proof Hstkj as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
pose proof HARUc as (HARc & OKc & POc).
destruct HSTK as (HCH & HCHF & HTOP & HIN & HWK).
destruct HBL as (HTXc & HPOc & HBLc & HPERMc & HUc & HDac & HSUMc & HLENc & HGc & Hpk1).
destruct HOBJ as (HHDRc & HOPc).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
assert (R8 : YK11.getr regsC 8 = w64 (q + 16)).
{ rewrite Forall_forall in RL. pose proof (RL (8%bv, SOff 9 16) HR8) as R8'. cbn [fst snd] in R8'.
  rewrite R8'. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regsC _ 9 9%bv eq_refl), R9.
  unfold w64. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
pose proof HTXc as (_ & HRBc & Htlc). pose proof HRBc as (HinTc & _ & Htc0 & _).
destruct (pil_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc (dd + 1)
  HARc HTXc HIN) as (Ht0 & Hpc & Htl & Htc & Hac).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & Hte62 & _ & Htblen & _ & _).
(* ---- the trace and the budget of grow ---- *)
set (capn := Z.to_nat cap) in *.
assert (Ecapn : Z.of_nat capn = cap) by (unfold capn; lia).
set (X := PjRoundTrip.grow_ev true i capn).
assert (EX : grow_tr 6 (Z.of_nat i) cap = X) by (rewrite <- Ecapn; apply pim_grow_tr; exact Hicap).
set (Y := PjGrammar.EAlloc (Datatypes.S (length (flat_map PjRoundTrip.ech kk))) :: PjRoundTrip.ttrace x ++
  PjRoundTrip.tgo_obj (Datatypes.S i) (PjRoundTrip.gcap i capn) rm).
assert (Htr3 : PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ X ++ Y) by (rewrite Htr, pim_tgo_cons; reflexivity).
destruct (pil_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc L T X Y Htr3 Hnevj HPERMc
  HSUMc HLENc) as (BQ & BL & BE & BBy & BS).
destruct (pil_slots_of B k ly S U regs ot v text len tcap ms live peak cnt fail Hk HDEP lyc Sc Uc W1 memC mdC Da T peak1
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
  by (pose proof HGLOB as (_ & _ & _ & _ & (Hlive0 & _) & _); lia).
destruct (pil_pin_vals k S regs ot text len tb ms Hk HDEP (rdW W1 memC) q pc (dd + 1) HIN) as (VP & VE & VD).
assert (Hp4 : 4096 <= pc <= 2 ^ 47 - 2 ^ 23) by (unfold HEAD in Ht0; lia).
assert (He4 : 4096 <= text + len <= 2 ^ 47 - 2 ^ 23) by (unfold HEAD in Ht0; lia).
assert (Hd2 : 1 <= dd + 1 <= 2) by (unfold dd; lia).
(* ---- the grow call ---- *)
refine (Hcall (1 - k)%nat sp0 ot ly S U W mem md [] lyc Sc Uc W1 memC mdC (rd_ev T) regsC q pc (text + len) (dd + 1) xr
  v 0 0 kids keys (Z.of_nat i) cap (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail cs Qc
  HJ HARUc HRO HHDc R1 Rsp Hal16 ltac:(lia) R8 R9 R19 R10 R3 R4 Hsq Hq24 Hq8 ltac:(lia) VP VE VD Hp4 He4 Hd2
  (pil_xr_len regs) HPOc HHDRc HSL HBO HAP HINC HNE HGc HQg HRS HMX HLV HEVg HBBg Hwf HCS _).
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
set (xs := pib_xs pc (text + len) (dd + 1) xr k' y' (Z.of_nat i) cap') in *.
destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs R HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
set (E := Ereg regs' (fs_extraT ++ xs)) in *.
assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U9 : YP0e.U E (SOff 9 0) = q) by (apply U_atom; [exact E9 | lia]).
assert (U19 : YP0e.U E (SOff 19 0) = v) by (apply U_atom; [exact E19 | lia]).
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
{ intros z Hz. apply (pio_raw_of_mbyte _ _ z ltac:(lia)); [apply pib_not_img; unfold FS_IMG_END; lia | exact (QK z Hz)]. }
assert (HIN' : PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len pc (dd + 1) tb).
{ apply (pil_pin_kept k S regs ot text len tb ms Hk HDEP (rdW W1 memC) (rdW W' mem') q pc (dd + 1) HIN).
  - intros z Hz. split; [exact (QK z Hz) | exact (writable_at_eq tfibsegs _ _ z (QR z Hz))].
  - intros z Hz. unfold mbyte. rewrite (TK z ltac:(unfold HEAD; lia)). reflexivity. }
(* ---- the start state ---- *)
pose proof (fsw_pobj_off_img B ly' S' W' (unpoison U' mem') md' mem' v HAR' HPO') as Hvimg.
assert (HPD : pairwise_disjoint E ([] ++ fsT_ret_regions 144 cs pib_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, E9u, E19u.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (HA0 : YK11.getr regs' 10 = sv_denot E (SLit 0)) by (rewrite A0; reflexivity).
pose proof (pil_start k S regs ot ms Hk HDEP regs' xs W' mem' r cs pib_gf ((10%bv, SLit 0) :: R) [] [] [] [] fw pib_RO
  pib_RO HST (pil_setr_ok B k S regs q ot v ms Hk HDEP regsC regs' xs R (SLit 0) HRP HP HRok HA0) Hwf (Forall_nil _)
  HPD I I I ltac:(right; lia) ltac:(left; cbn; lia) ltac:(left; cbn; lia) Hwf2) as HB.
fold ss in HB.
(* ---- the shadow entries: q, v ---- *)
assert (HSH : sh_ok tfibsegs fs_Bx pib_SHm E (rdW W' mem')).
{ unfold sh_ok, pib_SHm. constructor; [|constructor; [|constructor]].
  - exact (pil_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S' U' W' mem' md'
      E 9 HARU' ltac:(congruence) ltac:(congruence) UB U9).
  - exact (pil_sh_v B k S regs ot v ms Hk HDEP ly' S' U' W' mem' md' E 19 HARU' HPO' UB U19). }
(* ---- the write windows: the frame's ---- *)
assert (AWR : awr_ok tfibsegs B E (ss_mem ss) STKt ot FP (ablocks B ly S) (ablocks B ly' S') ly' [] (frames S))
  by exact (pil_awr_rgs B k ly S U W regs mem md q ot v ms ch Hk HPRE HWIN HQ16 HDEP E ly' S' W' (unpoison U' mem') md'
    mem' [] cs fw pib_RO pib_RO HAR' HPO' Hfr2 E2 E9u E19u (Forall_nil _) Hfw1 Hfw2 ltac:(cbn; lia) ltac:(cbn; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)).
(* ---- the run C / J to skip_ws #2 ---- *)
unfold pib_finW in HFIN. cbv zeta in HFIN.
destruct HFIN as (Fpc & Fob & Fresv & Fregs & Fnth0 & Fnth3 & Fnth4).
refine (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pib_SHm ss) fs_Bx fs_Bspan pib_SHm ss st
  (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) STKt ot FP ly S W (unpoison U mem) md [] ly'
  S' U' md' (rd_ev T + rd_ev (grow_tr 6 (Z.of_nat i) cap)) Qc HB HSH HSTAT HRUN I HARU' HJ2 _ AWR _).
{ rewrite Fob. constructor. }
intros ws2 ms2 mat2 Hlen2 HS2 SHOK2 HJ3 HARU3 HFra HFrr HG2.
set (K := run_K 0 fs_Bx pib_SHm ss) in *.
set (E' := extK E K ws2) in *.
assert (HK : forall n, (n <= 52)%nat -> ew E' n = ew E n)
  by (intros n Hn; apply (pil_ew_extK k S regs ot ms Hk HDEP); unfold xatom in HKb; lia).
assert (E'9 : ew E' 9 = Z_to_bv 64 q) by (rewrite HK by lia; exact E9).
assert (E'19 : ew E' 19 = Z_to_bv 64 v) by (rewrite HK by lia; exact E19).
assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite HK by lia; exact E32).
assert (E'2 : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite HK by lia; exact E2).
assert (E'3 : ew E' 3 = Z_to_bv 64 (as_gp B)) by (rewrite HK by lia; exact E3).
assert (E'4 : ew E' 4 = Z_to_bv 64 (as_tp B)) by (rewrite HK by lia; exact E4).
assert (Hed : ed E' = (fun _ => [])) by (unfold E'; rewrite pil_ed_extK; reflexivity).
(* ---- what the run kept: every byte but the frame ---- *)
assert (KR : forall z, 0 <= z < 2 ^ 64 -> ~ (sp0 - 144 <= z < sp0) ->
  ms_mem ms2 (Z_to_bv 64 z) = mem' (Z_to_bv 64 z)).
{ intros z Hz H1. apply HFra. rewrite wz by lia. intros Hw.
  pose proof (pib_wr_CJ E r cs pib_gf ((10%bv, SLit 0) :: R) fw (sp0 - 144) z E2 Hw). lia. }
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
  rewrite <- (pib_raw_of_aview _ _ _ _ z ltac:(lia) (pib_not_img z ltac:(unfold FS_IMG_END; lia)) Ea).
  unfold mrestrict. rewrite (KR z ltac:(lia) ltac:(lia)). reflexivity. }
assert (QM : forall z, q <= z < q + 24 -> rdW W' (ms_mem ms2) (Z_to_bv 64 z) = rdW W' mem' (Z_to_bv 64 z))
  by (intros z Hz; unfold mrestrict; rewrite (KR z ltac:(lia) ltac:(lia)); reflexivity).
(* ---- the skip_ws #2 configuration ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E' (sh_ss st) ms2 HS2 Fresv) as Ems2. rewrite Fpc in Ems2.
rewrite Ems2.
change (SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_skip_ws (ms_regs ms2) (ms_mem ms2)
  (with_vm_backing (m_vm_lazy md') mat2 md')) Qc).
pose proof (pil_regs_of_stop E' (sh_ss st) ms2 (w_H W') pib_RW HS2 Fregs) as RG.
destruct (G_regsP_stopW E' (ms_regs ms2) RG E'9 E'19 E'32 E'2 E'3 E'4 Hed) as (RP2 & R1' & R10').
pose proof (fsw_region_nth E' (sh_ss st) (restrict (w_H W') ms2) 0 _ HS2 Fnth0) as RF. rewrite restrict_mem in RF.
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
apply (KIW (T ++ X) ly' S' U' W' (ms_mem ms2) (with_vm_backing (m_vm_lazy md') mat2 md') (ms_regs ms2) chq pc k' y' cap'
  Da' peak').
unfold pib_IW. cbv zeta. fold i.
split; [exact Hms|].
split; [rewrite Htr3, <- app_assoc, Ecap', Nat2Z.id; reflexivity|].
split; [lia|].
split; [destruct HSL' as (_ & (_ & Hc54) & _); exact Hc54|].
split.
{ split; [rewrite pim_rd_ev_app, <- EX; exact HJ3|].
  split; [exact HARU3|]. split; [exact (arodata_below B W' mem' (ms_mem ms2) SB HRO') | exact HHD']. }
split; [exact R1'|]. split; [exact R10'|]. split; [exact RP2|].
split.
{ apply (pil_frameL_of B k ly S U W regs mem md q ot v text tcap ms ch Hk HPRE HVTX HPO0 HDEP HVSP E' _ (fst fw) (snd fw) cs'
    E'2 E'19 E'32); [| exact RF | exact Hincl].
  intros j Hj. rewrite HK by (unfold xatom; lia). unfold E.
  exact (pil_xs_saved regs' pc (text + len) (dd + 1) xr k' y' (Z.of_nat i) cap' j (pil_xr_len regs) Hj). }
split.
{ split.
  { apply (pis_chain_kept lyc ly' _ _ sp0 q (ly_top ly) chq HCH HCHF HTOP ltac:(congruence)).
    intros z Hz Hq.
    rewrite (fsw_aview_unpoison_high B ly' S' U' W' (ms_mem ms2) _ z HARU3 ltac:(lia)),
      (fsw_aview_unpoison_high B lyc Sc Uc W1 memC mdC z HARUc ltac:(lia)).
    unfold aview, mbyte. rewrite (AV z ltac:(lia) Hq). reflexivity. }
  split; [exact HCHF|]. split; [congruence|].
  split.
  { apply (pil_pin_kept k S regs ot text len tb ms Hk HDEP (rdW W' mem') _ q pc (dd + 1) HIN').
    - intros z Hz. split; [unfold mbyte; rewrite (QM z Hz); reflexivity|].
      exact (writable_at_eq tfibsegs _ _ z (QM z Hz)).
    - intros z Hz. unfold mbyte. rewrite (SBm z ltac:(unfold HEAD in *; lia)). reflexivity. }
  apply (pil_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W' memC (ms_mem ms2) sp0 HWK); [|lia].
  intros z Hz Hq. pose proof (AV z ltac:(lia) Hq) as Ez. split.
  - unfold mbyte. rewrite Ez. reflexivity.
  - split; intros Hw; [exact (writable_at_eq tfibsegs _ _ z Ez Hw) | exact (writable_at_eq tfibsegs _ _ z (eq_sym Ez) Hw)]. }
split; [exact HREST'|].
split.
{ pose proof HTX' as (Ht4' & HRB' & Hlt').
  split; [split; [exact Ht4'|]; split;
    [exact (fs_rblock_below B ly' S' W' (unpoison U' mem') md' mem' (ms_mem ms2) text tcap HAR' SB HRB') | exact Hlt']|].
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
unfold pib_IG in HIG. cbv zeta in HIG.
destruct HIG as (Hms & Htr & Hicap & Hcap0 & HJC & R1 & R10 & HRP & HFR & HSTK & HREST' & HBL & HOBJ).
pose proof G_vrng as (Hv1 & Hv2). pose proof G_text as (_ & _ & _ & Gt4).
assert (KG2 : forall T' lyc' Sc' Uc' (W' : world tfibsegs) mem' md' regs' chq' pc' kids' keys' cap' Da' peak1',
     pib_IW dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Di Da' peak1' ->
     SRr tfibsegs W' (YG0d.cfg_at tfibsegs A_skip_ws regs' mem' md') Qc)
  by (intros T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Da' peak1' HIW;
      exact (pi_step_G2 dn kk x rm T' lyc' Sc' Uc' W' mem' md' regs' chq' pc' kids' keys' cap' Di Da' peak1' Qc HIW KIP)).
destruct (Nat.eqb (length dn) 0) eqn:Ei.
- (* the first member: grow #1 at 0x84fac, segment C *)
  refine (piG1_gen 0x84fb0 pi_cs pib_R0 (0, 144) pib_cs_C pib_st_C dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids
    keys cap Di Da peak1 Qc (pib_call_grow1 B HSS HGROW) pil_R0_ok ltac:(cbn; tauto) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia) pib_run_C pib_static_C pib_K_C pib_fin_C pib_incl_C
    Hms Htr Hicap Hcap0 HJC R1 R10 HRP _ HSTK _ HBL HOBJ KG2).
  + intros regs' k' y' cap' HP. apply (pil_cs0_ok _ _ sp0 xr (pil_xr_len regs)); [|exact HFR].
    intros j Hj. exact (pil_xs_saved regs' pc (text + len) (dd + 1) xr k' y' _ cap' j (pil_xr_len regs) Hj).
  + first [exact HREST' | (rewrite Ei; exact HREST') | (rewrite Ei in HREST'; exact HREST')
      | (rewrite Ei; rewrite Ei in HREST'; exact HREST')].
- (* a later member: grow #2 at 0x8524c, segment J *)
  refine (piG1_gen 0x85250 pib_csL pib_RL pib_RO pib_csL pib_st_J dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids
    keys cap Di Da peak1 Qc (pib_call_grow2 B HSS HGROW) pil_RL_ok ltac:(cbn; tauto) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia) pib_run_J pib_static_J pib_K_J pib_fin_J
    (incl_refl _) Hms Htr Hicap Hcap0 HJC R1 R10 HRP _ HSTK _ HBL HOBJ KG2).
  + intros regs' k' y' cap' HP.
    destruct (pil_env_at B k S regs q ot v ms Hk HDEP regsC regs'
      (pib_xs pc (text + len) (dd + 1) xr k' y' (Z.of_nat (length dn)) cap') pib_RL HRP HP) as (E9 & E19 & E32 & _).
    apply (pil_csL_ok _ _ sp0 xr q v (pil_xr_len regs)); [| exact E19 | exact E32 | lia | lia | exact HFR].
    intros j Hj. exact (pil_xs_saved regs' pc (text + len) (dd + 1) xr k' y' _ cap' j (pil_xr_len regs) Hj).
  + first [exact HREST' | (rewrite Ei; exact HREST') | (rewrite Ei in HREST'; exact HREST')
      | (rewrite Ei; rewrite Ei in HREST'; exact HREST')].
Qed.
End X.
