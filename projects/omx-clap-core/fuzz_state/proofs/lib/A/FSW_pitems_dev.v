(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): parse_items_spec's EMPTY-object instance (ms = []),
   the one complete machine path that calls no callee: pitems_nil (the entry run, the 0x84ad0 branch, the literal `}`
   byte, the run to the ret, FSW_ret.fsw_retU) and pitems_spec_nil (the same in parse_items_spec's own shape), which
   FSW_parse_items_holds.parse_items_holds takes for ms = []. *)
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
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_rd FSW_pj
FSW_parse_items_tbl FSW_parse_items.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Fn_reader FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the empty object's text and trace, as numerals: both are what the machine measurement needs *)
Lemma pid_nil_wt : forall (pr : bool) (dd : Z),
  concat (WriterValue.wvpieces (PjTree.JObj []) pr dd) = [123; 125].
Proof. exact pi_obj_nil. Qed.
Lemma pid_nil_tr : PjRoundTrip.ttrace (PjTree.JObj []) = [].
Proof. reflexivity. Qed.
Lemma pid_nil_ev : rd_ev (PjRoundTrip.ttrace (PjTree.JObj [])) = 0.
Proof. rewrite pid_nil_tr. reflexivity. Qed.
Lemma pid_nil_live : rd_live (PjRoundTrip.ttrace (PjTree.JObj [])) = 0.
Proof. rewrite pid_nil_tr. reflexivity. Qed.
Lemma pid_nil_held : PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj [])) = 0.
Proof. rewrite pid_nil_tr. reflexivity. Qed.
Lemma pid_nil_len : Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj []))) = 0.
Proof. rewrite pid_nil_tr. reflexivity. Qed.
(* MEASURED: the entry run takes no token, so the post-run env is the entry env itself *)
Lemma pid_j_84ad0 : sh_j pi_st_84ad0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.
(* THE EMPTY OBJECT'S BYTE AS A LITERAL: on ms = [] the byte at in->p + 1 is `}` = 125 (pi_obj_nil), so the walk can
   give it as a CVal literal, not a CData chunk. Then the engine decides the ws test (32 < 125) and the brace test
   (125 = 125) itself, and no model branch is left between 0x84ad0 and the ret. *)
Definition pid_tb_lit : YP09.region :=
  YP09.mkRegion (Some (xatom 0)) 0 2 0 0 [YP09.mkChunk 1 (CVal 1 (SLit 125))].
Definition pid_ss_lit : sstate :=
  mkSS (ss_pc pi_ss_ws0) (ss_regs pi_ss_ws0) (pid_tb_lit :: ss_mem pi_ss_ws0) (ss_resv pi_ss_ws0) (ss_facts pi_ss_ws0).
Lemma pid_tb_lit_wf : region_wf pid_tb_lit = true.
Proof. vm_compute. reflexivity. Qed.
(* MEASURED: from the literal-byte state the run goes straight to the ret, with no obligation and no model branch *)
Definition pid_st_ret : shst := fst (sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL pid_ss_lit).
Lemma pid_lit_static_ok : sh_static_ok pi_K2 fs_Bx fs_Bspan pi_SH1 (ss_facts pid_ss_lit) (ss_mem pid_ss_lit) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pid_run_lit :
  sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL pid_ss_lit =
    (pid_st_ret, TS_stopped (SR_jalr (SOff 1%nat 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pid_ret_facts :
  ss_pc (sh_ss pid_st_ret) = 0x84f10 /\ sh_obls pid_st_ret = [] /\ ss_resv (sh_ss pid_st_ret) = None /\
  sh_j pid_st_ret = 4%nat.
Proof. vm_compute. repeat split. Qed.

(* the empty object's second byte, read out of the spec's text premise *)
Lemma pid_byte1 : forall (tb : list byte) text p rest, text <= p ->
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

(* a run only edits chunks: the write windows of the region list are the entry's, so the write-range facts carry *)
Lemma pid_wr_skel : forall E (rs rs' : list YP09.region),
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs =
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs' ->
  forall a, in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' H a (r & Hin & Ha).
assert (Hm : In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)
               (map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs'))
  by (rewrite <- H; apply (in_map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r))); exact Hin).
apply in_map_iff in Hm as (r' & Er & Hin').
injection Er as E1 E2 E3. exists r'. split; [exact Hin'|].
first [rewrite E1, E2, E3; exact Ha | rewrite <- E1, <- E2, <- E3; exact Ha].
Qed.
Lemma pid_skel_ws0 :
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem pi_ss_ws0) =
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem pi_ss0).
Proof. vm_compute. reflexivity. Qed.
Lemma pid_wr_lit : forall E a, in_wrange E (ss_mem pid_ss_lit) a -> in_wrange E (ss_mem pi_ss0) a.
Proof.
intros E a (r & [<- | Hin] & Ha).
- cbn [pid_tb_lit YP09.r_wlo YP09.r_whi] in Ha. lia.
- exact (pid_wr_skel E (ss_mem pi_ss_ws0) (ss_mem pi_ss0) pid_skel_ws0 a (ex_intro _ r (conj Hin Ha))).
Qed.
(* the same for the regions' extents (base, lo, hi): disjointness from the entry state's regions carries *)
Lemma pid_ext_skel : forall E r (rs rs' : list YP09.region),
  map (fun x => (YP09.r_base x, YP09.r_lo x, YP09.r_hi x)) rs =
  map (fun x => (YP09.r_base x, YP09.r_lo x, YP09.r_hi x)) rs' ->
  all_disjoint E r rs' -> all_disjoint E r rs.
Proof.
intros E r rs. induction rs as [|x rs IH]; intros [|y rs'] Hm Hd; cbn [map] in Hm; try discriminate; [exact I|].
injection Hm as E1 E2 E3 Hm. cbn [all_disjoint] in *. destruct Hd as (Hxy & Hd).
split; [|exact (IH rs' Hm Hd)].
unfold extent_disjoint in *.
first [rewrite E1, E2, E3; exact Hxy | rewrite <- E1, <- E2, <- E3; exact Hxy].
Qed.
Lemma pid_skel3_ws0 :
  map (fun x => (YP09.r_base x, YP09.r_lo x, YP09.r_hi x)) (ss_mem pi_ss_ws0) =
  map (fun x => (YP09.r_base x, YP09.r_lo x, YP09.r_hi x)) (ss_mem pi_ss0).
Proof. vm_compute. reflexivity. Qed.
(* a 4-byte field read out of a region chunk (val_mem) as the Lib form pj_in_ok states (le4); KindBGlue has only the
   8-byte twin word_mem_le8 *)
Lemma pid_val_le4 : forall m a v, val_mem tfibsegs m a 4 v -> 0 <= v < 2 ^ 32 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  Mem.bytes_at tfibsegs m a (Mem.le4 (Z_to_bv 64 v)).
Proof.
intros m a v Hv Hr Ha Hb. split; [exact Ha|]. rewrite Mem.length_le4. split; [lia|].
intros i Hi. unfold Mem.le4. rewrite MState.unsigned_lit by lia.
rewrite KindBGlue.kb_nth_le_bytes by exact Hi.
transitivity (mbyte tfibsegs m (a + Z.of_nat i)); [reflexivity|].
rewrite (Hv i Hi). f_equal. rewrite fpj_le_byte_bv.
rewrite (Z.mod_small v) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia). reflexivity.
Qed.
(* bytes the walk did not write read the same *)
Lemma pid_bytes_at_eq : forall (m m' : word -> option byte) a bs,
  (forall k, (k < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  Mem.bytes_at tfibsegs m a bs -> Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (H i Hi). exact (H3 i Hi).
Qed.
(* a byte that is defined stays defined as the memory grows *)
Lemma pid_mrd_grows : forall (m m' : word -> option byte) x, mem_grows m m' ->
  (exists b, Mem.mrd tfibsegs m x = Some b) -> exists b, Mem.mrd tfibsegs m' x = Some b.
Proof.
intros m m' x HG (b & Hb). unfold Mem.mrd in *.
destruct (m x) as [c|] eqn:E1; destruct (m' x) as [c'|] eqn:E2; try (eexists; reflexivity).
- exfalso. apply (HG x); [rewrite E1; discriminate | exact E2].
- exists b. exact Hb.
Qed.
(* one byte's value and writability, from the raw memories being equal there *)
Lemma pid_mbyte_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma pid_wr_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.
(* a field read is the same when the bytes under it are *)
Lemma pid_val_eq : forall (m m' : word -> option byte) a n z,
  (forall j, (j < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat j)) = m (Z_to_bv 64 (a + Z.of_nat j))) ->
  val_mem tfibsegs m a n z -> val_mem tfibsegs m' a n z.
Proof. intros m m' a n z H Hv j Hj. unfold mbyte. rewrite (H j Hj). exact (Hv j Hj). Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL_GOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis TL_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.

(* the write-permission facts of the entry state carry to the literal-byte state *)
Lemma pid_awr_lit : forall E STK sp0 FP bl0 blc ly own fr0,
  awr_ok tfibsegs B E (ss_mem pi_ss0) STK sp0 FP bl0 blc ly own fr0 ->
  awr_ok tfibsegs B E (ss_mem pid_ss_lit) STK sp0 FP bl0 blc ly own fr0.
Proof. intros E STK sp0 FP bl0 blc ly own fr0 H a Ha. apply H. exact (pid_wr_lit E a Ha). Qed.

(* the empty object: from the entry to the ret, in a post with D = Da = [] *)
Theorem pitems_nil : forall (k : nat) ly S U (W : world tfibsegs) regs mem md ch q ot v text len p
    (tb : list byte) tcap (pr : bool) (rest : list Z) live peak cnt fail,
  (k <= 1)%nat ->
  fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  spZ regs + 16 <= q ->
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
intros k ly S U W regs mem md ch q ot v text len p tb tcap pr rest live peak cnt fail
  Hk HPRE HHEADS HFRL H10 H11 H12 HIN HWIN HQ16 HTX HREST HPO HZERO HVSP HVTX HGLOB.
pose proof HPRE as (HPREU & HRO).
assert (HFP : forall a, v <= a < v + 56 -> inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a).
{ intros a Ha. exists (v, v + 56). split; [left; reflexivity|]. cbn [fst snd]. lia. }
eapply (pitems_entry_run B TL_GOT TL_CELL ly S U W regs mem md ch q ot v text len p tb tcap (Z.of_nat k)
  (STK_parse_items (1 - k)) ([(v, v + 56)] ++ FS_PSTAT_FP)).
all: try eassumption.
2: lia.
1: unfold STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia.
intros ws ms1 mat1 Hlen HS SHOK HJ HARU HF HFr HG.
rewrite pid_j_84ad0 in Hlen. destruct ws as [|w ws]; [clear Hlen | discriminate Hlen].
cbn [extK] in HS, SHOK.
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) (Z.of_nat k))) in *.
(* the model facts the 0x84ad0 branch reads: in->p + 1 and in->end as numbers *)
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & (Hp1 & Hp2) & Hend & _).
assert (HR' : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj []) pr (Z.of_nat k)) ++ rest)
  by (rewrite pi_obj_nil; exact HREST).
pose proof (pi_p1_lt_end _ q text len p (Z.of_nat k) tb [] pr (Z.of_nat k) rest HIN HR') as Hlt.
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (U1 : YP0e.U E (SOff (xatom 0) 1) = p + 1) by (apply U_atom_off; [exact EX0 | lia | lia]).
assert (U2 : YP0e.U E (SOff (xatom 1) 0) = text + len)
  by (rewrite (U_atom_off E (xatom 1) (text + len) 0 EX1) by lia; lia).
apply (SRr_sym_branch tfibsegs W E (sh_ss pi_st_84ad0) ms1 _ _ BC_LTU (SOff (xatom 0) 1) (SOff (xatom 1) 0) HS).
2: { intros Hb _. exfalso. rewrite branch_ltu_U, U1, U2 in Hb. apply Z.ltb_ge in Hb. lia. }
intros _ HS2.
(* ---- the layout facts the literal-byte region needs (as pitems_entry derives them) ---- *)
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPREU as (HAPRE & _ & _).
pose proof HAPRE as (HAR & _).
pose proof (fsw_sp B (STK_parse_items (1 - k)) ly S U W regs mem md ch HPREU) as (_ & HceilSTK & H47sp & HS0).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & _ & Hqtx & Hlen & _).
assert (HSTKf : FRAME_parse_items <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) (Z.of_nat k)) 2 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = q)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) (Z.of_nat k)) 10 10%bv eq_refl), H10;
      apply MState.unsigned_lit; lia).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
assert (E11 : bv_unsigned (ew E 11) = v)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) (Z.of_nat k)) 11 11%bv eq_refl), H11;
      apply MState.unsigned_lit; lia).
(* ---- the empty object's second byte: 125 on the entry memory, and still 125 after the entry run ---- *)
destruct (pid_byte1 tb text p rest ltac:(lia) HREST) as (b1 & Hb1 & Hb1v).
assert (Hb1e : b1 = Z_to_bv 8 125) by (apply bv_eq; rewrite Hb1v; reflexivity).
pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbat & _).
assert (Hm0 : mbyte tfibsegs (mrestrict (w_H W) mem) (p + 1) = Some (Z_to_bv 8 125)).
{ destruct Hbat as (_ & _ & Hbat).
  pose proof (Hbat (Z.to_nat (p + 1 - text)) ltac:(lia)) as Hx.
  rewrite Hb1, Hb1e in Hx. rewrite Z2Nat.id in Hx by lia.
  replace (text + (p + 1 - text)) with (p + 1) in Hx by lia. exact Hx. }
assert (HnwT : forall y, text <= y < text + len -> ~ in_wrange E (ss_mem pi_ss0) y).
{ intros y Hy (r & Hin & Hr).
  unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs in Hin. cbn [ss_mem app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [fstk fs_got_region fs_bcell_region pi_q_region pi_v_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    unfold FRAME_parse_items, HEAD in *; lia. }
assert (Hnw : ~ in_wrange E (ss_mem pi_ss0) (p + 1)) by (apply HnwT; lia).
assert (Hm1 : mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (p + 1) = Some (Z_to_bv 8 125)).
{ unfold mbyte. rewrite (HFr (Z_to_bv 64 (p + 1))); [exact Hm0|].
  rewrite (MState.unsigned_lit (p + 1)) by lia. exact Hnw. }
(* ---- the literal-byte region holds on the memory after the entry run ---- *)
assert (RLIT : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms1)) pid_tb_lit).
{ unfold region_ok, pid_tb_lit.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EX0, (MState.unsigned_lit p) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ p 1 1 (SLit 125) 125); [reflexivity | cbn; lia | cbn; lia |].
  intros k0 Hk0. assert (k0 = 0%nat) by lia. subst k0. cbn [Z.of_nat]. rewrite Z.add_0_r.
  match goal with |- mbyte _ _ _ = Some (Z_to_bv 8 ?x) => replace x with 125 by (vm_compute; reflexivity) end.
  exact Hm1. }
(* ---- the literal region is apart from the entry state's regions (stack frame, image cells, q, v) ---- *)
pose proof Htxblk as (HinT & _).
pose proof (fsw_ablock_off_img B ly S W (unpoison U mem) md _ _ HAR HinT) as Himg.
pose proof (fsw_ablock_low B ly S W (unpoison U mem) md _ _ HAR HinT) as (Hb4096 & Hbceil & Hbreq).
assert (DJ0 : all_disjoint E pid_tb_lit (ss_mem pi_ss0)).
{ apply all_disjoint_of_extents.
  unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, pi_rs,
    pi_q_region, pi_v_region, pid_tb_lit, extent_of_region.
  cbn [ss_mem app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EX0, (MState.unsigned_lit p) by lia. rewrite E2, E10, E11.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
    FRAME_parse_items, HEAD in *.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (DJ : all_disjoint E pid_tb_lit (ss_mem pi_ss_ws0)) by exact (pid_ext_skel E pid_tb_lit _ _ pid_skel3_ws0 DJ0).
assert (HS3 : st_ok tfibsegs E pid_ss_lit (restrict (w_H W) ms1)).
{ unfold pid_ss_lit.
  apply (st_ok_add_region' tfibsegs E pi_ss_ws0 (restrict (w_H W) ms1) pid_tb_lit);
    [exact HS2 | exact pid_tb_lit_wf | rewrite restrict_mem; exact RLIT | exact DJ]. }
(* ---- one shadow entry more: the text byte at in->p + 1, a body byte of the text block ---- *)
assert (SHOK1 : sh_ok tfibsegs fs_Bx pi_SH1 E (mrestrict (w_H W) (ms_mem ms1))).
{ unfold sh_ok, pi_SH1. constructor; [|exact SHOK].
  apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms1) E fs_Bx (xatom 0) (p + 1) 1 p 1 2);
  [ exact (fsw_block_body_addressable B ly S U W (ms_mem ms1) _ _ _ (p + 1) 1 HARU HHEADS HinT
             ltac:(unfold HEAD in *; lia) ltac:(lia) ltac:(unfold HEAD in *; lia))
  | unfold fs_Bx; apply U_atom;
      [unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity | unfold SHADOW_OFF; lia]
  | apply U_atom; [exact EX0 | lia]
  | lia | lia | ].
  intros x Hx. cbn [Z.min Z.max] in Hx.
  exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR HinT x ltac:(unfold HEAD in *; lia)). }
(* ---- the run from the literal-byte state to the ret ---- *)
eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W FUEL E pi_K2 fs_Bx fs_Bspan pi_SH1 pid_ss_lit pid_st_ret
  (TS_stopped (SR_jalr (SOff 1%nat 0))) ms1 (STK_parse_items (1 - k) + (ot - spZ regs)) ot
  ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md [] ly S U (with_vm_backing (m_vm_lazy md) mat1 md) 0).
- exact HS3.
- exact SHOK1.
- exact pid_lit_static_ok.
- exact pid_run_lit.
- exact I.
- exact HARU.
- exact HJ.
- destruct pid_ret_facts as (_ & Hob & _). rewrite Hob. constructor.
- apply pid_awr_lit.
  exact (pi_awr_ok B ly S W mem regs q ot v text len p (Z.of_nat k) (STK_parse_items (1 - k))
    ([(v, v + 56)] ++ FS_PSTAT_FP) Hsq Hq24 HceilSTK HSTKf H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPO HFP).
- intros ws2 ms2 mat2 Hlen2 HS4 SHOK2 HJ2 HARU2 HF2 HFr2 HG2.
  destruct pid_ret_facts as (Hpcf & Hobf & Hresvf & Hjf). rewrite Hjf in Hlen2.
  repeat (let w := fresh "w" in
    destruct ws2 as [|w ws2]; [discriminate Hlen2 | cbn [length] in Hlen2; apply eq_add_S in Hlen2 || injection Hlen2 as Hlen2]).
  destruct ws2; [clear Hlen2 | discriminate Hlen2].
  cbn [extK] in HS4, SHOK2.
  pose proof HAPRE as (_ & Hra & _).
  refine (fsw_retU B pitems_tbl pitems_tbl_ok W _ _ ms2 _ (STK_parse_items (1 - k) + (ot - spZ regs)) ot
    ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md ly S U 0 _ HS4 Hresvf _ _ HJ2 HARU2 _ _).
  + rewrite Hpcf. vm_compute. reflexivity.
  + rewrite (st_ok_restrict_reg tfibsegs _ _ _ ms2 1%bv HS4).
    match goal with |- context [sr_get ?l 1%bv] => replace (sr_get l 1%bv) with (SOff 1 0) by (vm_compute; reflexivity) end.
    rewrite fsw_SOff0. unfold pi_K2. repeat rewrite ew_ewset_other by lia.
    unfold E. rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) (Z.of_nat k)) 1 1%bv eq_refl). exact Hra.
  + apply (fsw_preserved _ _ _ ms2 regs (fun r : bv 5 => SOff (Z.to_nat (bv_unsigned r)) 0) HS4);
      [vm_compute; reflexivity|].
    intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
    all: cbn beta; rewrite fsw_SOff0; unfold pi_K2; repeat rewrite ew_ewset_other by lia; unfold E.
    all: lazymatch goal with |- ew _ ?n = getr _ ?r => exact (ew_Ereg_nat regs _ n r eq_refl) end.
  + intros mat0.
    match type of HS4 with st_ok _ ?E' _ _ => set (E4 := E') in * end.
    assert (E4_11 : bv_unsigned (ew E4 11) = v)
      by (unfold E4, pi_K2; repeat rewrite ew_ewset_other by lia; exact E11).
    assert (E4_10 : bv_unsigned (ew E4 10) = q)
      by (unfold E4, pi_K2; repeat rewrite ew_ewset_other by lia; exact E10).
    assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm8 & _)|(_ & Hm8 & _)] _]; exact Hm8).
    pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO) as Hvimg.
    pose proof (fsw_region_nth _ _ _ 4 (YP09.mkRegion (Some 10%nat) 0 24 0 24
      [YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0)); YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 2));
       YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))]) HS4 ltac:(vm_compute; reflexivity)) as RQ.
    pose proof (fsw_region_nth _ _ _ 5 pi_v_region6 HS4 ltac:(vm_compute; reflexivity)) as RV.
    assert (D4 : forall n z c, ew E n = Z_to_bv 64 z -> 0 <= z -> 0 <= c -> z + c < 2 ^ 64 -> (n < 200)%nat ->
              sv_denot E4 (SOff n c) = Z_to_bv 64 (z + c)).
    { intros n z c Hn Hz Hc Hzc Hn200. apply bv_eq. rewrite denot_SOff.
      unfold E4, pi_K2. repeat rewrite ew_ewset_other by lia.
      rewrite Hn, (MState.unsigned_lit z) by lia. rewrite (MState.unsigned_lit (z + c)) by lia.
      apply zcanon_id. unfold M64. lia. }
    assert (EX2 : ew E (xatom 2) = Z_to_bv 64 (Z.of_nat k)) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
    pose proof (fsw_field _ _ 10 q _ _ _ _ _ 0 8 (SOff (xatom 0) 2) (p + 2) RQ E4_10 ltac:(cbn; tauto)
      (D4 _ p 2 EX0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv; lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as HPV0.
    pose proof (D4 _ (text + len) 0 EX1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv; lia)) as DN8.
    rewrite Z.add_0_r in DN8.
    pose proof (D4 _ (Z.of_nat k) 0 EX2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv; lia)) as DN16.
    rewrite Z.add_0_r in DN16.
    pose proof (fsw_field _ _ 10 q _ _ _ _ _ 8 8 (SOff (xatom 1) 0) (text + len) RQ E4_10 ltac:(cbn; tauto)
      DN8 ltac:(cbn; lia) ltac:(cbn; lia)) as HPV8.
    pose proof (fsw_field _ _ 10 q _ _ _ _ _ 16 4 (SOff (xatom 2) 0) (Z.of_nat k) RQ E4_10 ltac:(cbn; tauto)
      DN16 ltac:(cbn; lia) ltac:(cbn; lia)) as HPV16.
    rewrite Z.add_0_r in HPV0.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 0 4 (SLit 6) 6 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV0. rewrite Z.add_0_r in HV0.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 8 8 (SLit 0) 0 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV8.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 16 8 (SLit 0) 0 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV16.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 24 8 (SLit 0) 0 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV24.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 32 8 (SLit 0) 0 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV32.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 40 8 (SLit 0) 0 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV40.
    pose proof (fsw_field _ _ 11 v _ _ _ _ _ 48 8 (SLit 0) 0 RV E4_11 ltac:(cbn; tauto) ltac:(reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HV48.
    destruct RQ as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E4_10 in RQW.
    destruct RV as (_ & _ & RVW & _). unfold pi_v_region6 in RVW.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RVW. rewrite E4_11 in RVW.
    assert (UBx : YP0e.U E4 fs_Bx = SHADOW_OFF).
    { unfold fs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
      unfold E4, pi_K2. repeat rewrite ew_ewset_other by lia.
      unfold E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
    assert (UV : YP0e.U E4 (SOff 11 0) = v)
      by (apply U_atom; [apply bv_eq; rewrite E4_11, (MState.unsigned_lit v) by lia; reflexivity | lia]).
    assert (RA2 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF v 56).
    { pose proof SHOK2 as SH2. unfold sh_ok, pi_SH1, pi_SH in SH2.
      apply Forall_inv_tail, Forall_inv_tail, Forall_inv in SH2.
      destruct SH2 as (RA & _). cbn [she_m she_lo she_hi] in RA.
      rewrite UBx, UV, Z.add_0_r in RA. rewrite aview_rd_of. exact RA. }
    assert (KEEP0 : forall y, 0 <= y < 2 ^ 64 -> ~ in_wrange E (ss_mem pi_ss0) y ->
      mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 y) = mrestrict (w_H W) mem (Z_to_bv 64 y)).
    { intros y Hy Hn. rewrite (HFr2 (Z_to_bv 64 y)).
      - rewrite (HFr (Z_to_bv 64 y)); [reflexivity|]. rewrite (MState.unsigned_lit y) by lia. exact Hn.
      - rewrite (MState.unsigned_lit y) by lia. intros Hw. exact (Hn (pid_wr_lit E y Hw)). }
    assert (VDEF : forall a, v <= a < v + 56 ->
      exists b, Mem.mrd tfibsegs (mrestrict (w_H W) (ms_mem ms2)) (Mem.wa a) = Some b).
    { intros a Ha. apply (pid_mrd_grows (mrestrict (w_H W) (ms_mem ms1))); [exact HG2|].
      apply (pid_mrd_grows (mrestrict (w_H W) mem)); [exact HG|].
      destruct HZERO as (_ & (_ & _ & HZB)).
      pose proof (HZB (Z.to_nat (a - v)) ltac:(rewrite repeat_length; lia)) as Hx.
      rewrite pi_nth_repeat in Hx by lia.
      rewrite Z2Nat.id in Hx by lia. replace (v + (a - v)) with a in Hx by lia.
      eexists. exact Hx. }
    pose proof HAPRE as (_ & _ & _ & _ & _ & Hstk2 & _).
    pose proof Hstk2 as (Hal16' & Hstk0' & Hceil' & Hslo' & Hshi' & H47' & Hbot' & Htop' & Htop2').
    pose proof HIN as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
    split.
    { rewrite (st_ok_restrict_reg tfibsegs _ _ _ ms2 10%bv HS4).
      match goal with |- context [sr_get ?l 10%bv] =>
        replace (sr_get l 10%bv) with (SLit 0) by (vm_compute; reflexivity) end.
      reflexivity. }
    split.
    { refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
      - apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HPV0 | lia | lia | lia].
      - apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HPV8 | lia | lia | lia].
      - apply pid_val_le4; [exact HPV16 | lia | lia | lia].
      - destruct I4 as (W1 & W1' & _). split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
      - lia.
      - apply (pid_bytes_at_eq (mrestrict (w_H W) mem)); [|exact I10].
        intros k0 Hk0. apply KEEP0; [lia | apply HnwT; lia]. }
    split.
    { intros a Ha Hnq.
      assert (Hout : ~ in_wrange E (ss_mem pi_ss0) a).
      { intros (r & Hin & Hr).
        unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs in Hin. cbn [ss_mem app In] in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
          cbn [fstk fs_got_region fs_bcell_region pi_q_region pi_v_region YP09.r_base YP09.r_wlo YP09.r_whi base_val]
            in Hr;
          unfold FRAME_parse_items, HEAD in *; lia. }
      assert (Em : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
        by (apply KEEP0; [lia | exact Hout]).
      split; [exact (pid_mbyte_eq _ _ a Em) | exact (pid_wr_eq _ _ a Em)]. }
    split; [cbn [rd_hblocks map]; rewrite app_nil_r; apply Permutation_refl|].
    split.
    { split; [|split; [intros a kk Hin; destruct Hin | intros x Hx; exact Hx]].
      cbn [PjStruct.pj_node].
      split; [constructor|]. split; [intros bb x Hin Hh; destruct Hin|].
      exists 0, 0, 0, 0, 0, 0.
      split.
      - unfold PjStruct.pj_hdr. cbn [PjTree.tag].
        split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        + unfold PjStruct.pj_rw. split; [exact Hv8|]. split; [lia|]. split; [lia|].
          intros a Ha. split; [|exact (VDEF a Ha)].
          pose proof (RVW (a - v) ltac:(lia)) as HW. replace (v + (a - v)) with a in HW by lia. exact HW.
        + split; [lia|]. apply pid_val_le4; [exact HV0 | lia | lia | lia].
        + split; [lia|]. apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HV8 | lia | lia | lia].
        + split; [lia|]. apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HV16 | lia | lia | lia].
        + split; [lia|]. apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HV24 | lia | lia | lia].
        + split; [lia|]. apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HV32 | lia | lia | lia].
        + split; [lia|]. apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HV40 | lia | lia | lia].
        + split; [lia|]. apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HV48 | lia | lia | lia].
      - cbn [length Z.of_nat]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        split; [left; split; [reflexivity | split; reflexivity]|].
        exists []. split; [reflexivity | reflexivity]. }
    split; [rewrite pid_nil_tr; reflexivity|].
    split; [rewrite pid_nil_tr; cbn [length]; lia|].
    split.
    { split.
      - destruct HPO as [[HFo | HHo] _].
        + left. destruct HFo as (PF1 & PF2 & _). split; [exact PF1|]. split; [exact PF2 | exact RA2].
        + right. destruct HHo as (PH1 & PH2 & _). split; [exact PH1|]. split; [exact PH2 | exact RA2].
      - intros i Hi. exact (RVW i Hi). }
    split.
    { split; [exact Htx4096|]. split; [|exact Htxlen].
      destruct Htxblk as (TB1 & TB2 & TB3 & TB4). split; [exact TB1|]. split; [exact TB2|]. split; [exact TB3|].
      apply (pid_val_eq (mrestrict (w_H W) mem)); [|exact TB4].
      intros j Hj. apply KEEP0; [unfold HEAD in *; lia|].
      intros (r & Hin & Hr).
      unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs in Hin. cbn [ss_mem app In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        cbn [fstk fs_got_region fs_bcell_region pi_q_region pi_v_region YP09.r_base YP09.r_wlo YP09.r_whi base_val]
          in Hr;
        unfold FRAME_parse_items, HEAD, FS_IMG_END in *; lia. }
    exists peak. split; [lia|].
    rewrite pid_nil_tr. cbn [PjGrammar.held length Z.of_nat].
    replace (live + 0) with live by lia.
    replace (cnt + Z.of_nat 0) with cnt by (cbn [Z.of_nat]; lia).
    assert (GK : forall g z, 0xa3ca0 <= g -> g + 8 <= 0x5da608 ->
      val_mem tfibsegs (mrestrict (w_H W) mem) g 8 z -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) g 8 z).
    { intros g z Hg1 Hg2 Hv. apply (pid_val_eq (mrestrict (w_H W) mem)); [|exact Hv].
      intros j Hj. apply KEEP0; [lia|].
      intros (r & Hin & Hr).
      unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs in Hin. cbn [ss_mem app In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        cbn [fstk fs_got_region fs_bcell_region pi_q_region pi_v_region YP09.r_base YP09.r_wlo YP09.r_whi base_val]
          in Hr;
        unfold FRAME_parse_items, HEAD, FS_IMG_END in *; lia. }
    destruct HGLOB as (G1 & G2 & G3 & G4 & GR).
    split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
    split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
    split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
    split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
    exact GR.
Qed.

(* ---- the same stage in parse_items_spec's own shape, so that the walk's final theorem can apply it for the
   ms = [] case without restating anything: the spec's premises verbatim with ms := [], and its post with
   D = Da = [] (the empty object allocates nothing). ---- *)
Theorem pitems_spec_nil : forall (k : nat) ly S U (W : world tfibsegs) regs mem md ch q ot v text len p
    (tb : list byte) tcap (pr : bool) (rest : list Z) live peak cnt fail,
  let tr := PjRoundTrip.ttrace (PjTree.JObj []) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj []) pr (Z.of_nat k)) in
  (k <= 1)%nat ->
  fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  spZ regs + 16 <= q ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
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
       fpostU tfibsegs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U
         W mem md (rd_ev tr) (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Z.of_nat (length wt)) (Z.of_nat k) tb /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj []) D /\ rd_sum D = PjGrammar.held tr /\
            (length D <= length tr)%nat /\ pobj tfibsegs B ly' S' W' mem' v /\
            rd_text tfibsegs B ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob tfibsegs W' mem' (live + PjGrammar.held tr) peak'
                 (cnt + Z.of_nat (length tr)) fail)) W' c').
Proof.
intros k ly S U W regs mem md ch q ot v text len p tb tcap pr rest live peak cnt fail.
cbv zeta.
intros Hk HPRE HHEADS HFRL H10 H11 H12 HIN HWIN HQ16 HCH HTX HREST _ _ _ _ HPO HZERO HVSP HVTX HGLOB _ _ _ _ _.
assert (HW2 : Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj []) pr (Z.of_nat k)))) = 2)
  by (rewrite pi_obj_nil; reflexivity).
assert (HR2 : ReaderRes.rest_at tb text p = [123; 125] ++ rest)
  by (rewrite HREST; rewrite pi_obj_nil; reflexivity).
eapply SRr_mono;
  [ exact (pitems_nil k ly S U W regs mem md ch q ot v text len p tb tcap pr rest live peak cnt fail
             Hk HPRE HHEADS HFRL H10 H11 H12 HIN HWIN HQ16 HTX HR2 HPO HZERO HVSP HVTX HGLOB) |].
intros W' c' Hle HQ. exists [], []. split; [apply Permutation_refl|].
rewrite pid_nil_ev, HW2. cbn [rd_heads map]. rewrite app_nil_r.
exact HQ.
Qed.

End D.

(* closure audit of the composed stage *)
Print Assumptions pitems_nil.
Print Assumptions pitems_spec_nil.
