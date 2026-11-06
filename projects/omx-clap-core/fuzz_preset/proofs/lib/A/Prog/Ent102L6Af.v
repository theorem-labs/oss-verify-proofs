(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4):
   SEGMENT L6f of LLVMFuzzerTestOneInput (entry 0x815e0), the FREE lane, proved against lib/A/Ent102CutsA.v's
   `seg_L6f_stmt` (cut_free E fk -> cut_exit E fk):
     +0x1bc  mv a0, s5          a0 := &doc = fk + 32 (ec_rkd)
     +0x1c0  jal ra, pj_free    the kit's tpj_free_specX (ec_texts' et_pj_free, CTX0 = ec_ctx0 = [[EC_RA]], n = DOC_D) by
                                lib/Reusable/YCbqGcallW.v aj_call_xW, at the callee window e1 = 0, v = &doc, the doc's
                                blocks D (Lam ~ D) and their order list F (PRH_PjOrder.pj_fdR_foR of cut_free's pj_fdR):
                                FP = (v, v + 56) :: ablocks_fp (prhPj_hbl D)
     +0x1c4  the return site = EC_EXIT, where cut_exit is assembled from the composed journal (entry-relative), the
             callee's journal (frame, saved block, frame shadow, flag word) and the kit's post (Lam' = [], the blocks back
             to the entry's, the ledger with its most / own, the room, memnorm, the position one model event later).
   STATEMENT: lib/A/Ent102CutsA.v, read at blob 99822ff0d52f
   (commit aabc9294a5b9: the batch kit's pre-merge tip d607d12e4b0f plus the wild
   budget through the cuts):
   seg_L6f_stmt over ec_hyps (e_dw E),
   cut_free / cut_exit at the exact room position (os_c = e_os E ++ [trp], the index after the accepted tail's pieces),
   the per-cut budgets ec_ccut / ec_lcut at cuts 10 and 11, ec_inv's `exists most own, prh_ledger .. most own`. The
   RECORD ec_hyps is read by name: ech_img's ei_sio / ei_sio_frame / ei_frame / ei_pst_ro, ech_texts' et_pj_free /
   et_stk, ech_univ's eu_pjf, ech_ccut_ok / ech_lcut_ok; ech_pay is not read (pj_free only frees: the count is paid by
   ec_ccut_ok's monotonicity 10 -> 11, the live bytes by the entry budget). ec_pre's parts are taken by their TYPES
   (lib/A/Prog/Ent102CallA.v ec_conj_pick), before the cut's float state fy enters the context.
   RE-FIT: the earlier Qed at a2d6bb26a279 (lane L6Lane) was against CutsA f40892fb5ddb and the kit's old pj_free text
   (rp_* entry position, prh_own / prh_most keeps, pj_fdR); then re-fitted to the local free-order text 40183db4cf90
   and the kit's NEW text. THE WILD BUDGET: ec_inv's last argument wk, cut_free at ec_wk_free (76) and cut_exit at
   ec_wk_exit = ec_wk_free + prh_wk F_pj_free (76; ec_wk_values); tpj_free_specX is NOT budgeted (no wild_room
   premise, fpostWm post), so the call rule stays aj_call_xW, run on the PLAIN journal that CutsA's ec_journal_rebase
   gives (entry depot moved to the cut's), and the exit's journal is CutsA's ec_journal_unbase at the cut's own WS.
   LISTING: a Theorem Labs lane's whole-program listing lib/A/Listing_prog.v (blob 7ed1529926bd; slot k = byte offset 4k from
   the entry; the bodies are those of 1ab147923c5d), with the PAListing PL_102_A of lib/A/Ent102PLA.v (blob
   a55fa7414ddf); the image half stays generic ({PA : PAImg A_prog_listing}; lib/A/PAImg_prog.v is not loaded, no
   vm_compute on pa_val / pa_sigma).
   The kit TEXTS (at these blobs): lib/A/PRH_FnPj.v blob 838c63d8cd16 tpj_free_specX (:746: post-implication form, the
   class-24 premise under v <> 0, supplied from the room position by Ent102L6AfLem.v l6f_ccnt24; the order list F;
   the position transfer under `prh_run_at .. (prhPj_free_evs F)`) and lib/A/PRH_Base.v blob 966b522cc722 (fpre with
   FRM0-ENTRY, fwin, fpostWm, prh_ledger and its named projection prh_ledger_heads; the ledger is otherwise read
   through lib/A/Prog/S1Ledger.v's prh_ledger_hblock, never a positional destruct); PRH_PjOrder.v blob e5917626b82b
   (pj_fdR_foR); the kit lemmas prhPj_free_evs_supply and prhPj_bulk_nil_pos (PRH_FnPj.v :359, :282).
   THE POSITION AT THE EXIT: the model's event at cut_free's index is call_tail's last piece
   [HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))] (lib/A/Prog/Ent102TailA.v blob 2a7ebdbc9dcf ec_tail_run), and
   the exit's index is one more (lib/A/Ent102PosA.v blob 18f53d9e171d ec_call_evs_ranout_false). The kit's post moves the
   position only under the ORDERED run premise [HBulk (map (fun b => snd b + cf_head) F)]: iface_room_pos reads the
   free history in order (YGcfFrees.cf_frees_follow), so a Permutation tie does not close it. The ordered tie
   (PJF-TIE) is cut_free's conjunct ec_pjf (the kit's shape: an order list at every depth bound >= depth t, taken at DOC_D);
   no Section premise.
   rule 24: proves function LLVMFuzzerTestOneInput, segment L6f (reuse search: `proof-index LLVMFuzzerTestOneInput`
   exit=0, output the lane's index output, the internal file idx-llvm-newpin.txt: 30 named, 1290 by address, 105 related, 7
   released lemma(s), 0 UNRELEASED hit(s) on live working heads; no released ASan walk on the #102 pins; checker
   R24CheckLLVMF CONFIRM; NEW walk). TEMPLATE: this walk's own earlier Qed of this row (a2d6bb26a279, by path); the
   exit's position step follows lib/A/Prog/Ent102L4jA.v of a working branch 7a3f2f1e8f63 (l4j_pos:
   the index arithmetic over ec_call_evs_ranout_false). The step rules, the geometry and the pure facts are
   lib/A/Prog/Ent102L6AfLem.v's (blob a37e0dc13d12, its header names their sources).
   NUMERALS: 0x1bc / 0x1c0 / 0x1c4 are this lane's slot offsets (DERIVED: EC_FREE - EC_BASE, +4, +8); 128 / 120 / 104 /
   88 / 56 / 32 / 16 / 8 are LENGTHs (the frame, the flag-pointer slot, the saved block, the doc's end, struct pj, the
   doc's offset in the frame and the frame's alignment, its shadow bytes, the word); 144 is EC_SAVE + 16; 32768 is
   LLVMF_STK; 4096, 2 ^ 40, 2 ^ 47, 2 ^ 64 and the ASan band constants are the engine's range facts. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102CallA Ent102TailA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* THE POSITION STEP over pj_free's one bulk event (image-free): the run's event at i is HBulk Lb, F carries Lb's
   requests IN ORDER, and the kit's post moves the position over prhPj_free_evs F. F = []: no event, Lb = [], and the
   kit's prhPj_bulk_nil_pos steps over the model's HBulk []; else the kit's prhPj_free_evs_supply gives the run premise. *)
Lemma l6f_nth_skipn : forall (A : Type) (l : list A) i, nth_error l i = hd_error (skipn i l).
Proof. intros A l. induction l as [|a l IH]; intros [|i]; cbn; first [reflexivity | apply IH]. Qed.

Section STEP. Context {cp : CfParams}.
Lemma l6f_pos_step : forall sm x os i H0 hist (S S' : astate) (F : list (Z * Z)) (Lb : list Z),
  map (fun b => snd b + cf_head) F = Lb ->
  prh_run_at sm x os i [PresetReqAt.HBulk Lb] ->
  (forall sm0 x0 os0 i0 H00 hist0, PresetRoomPos.iface_room_pos sm0 x0 os0 i0 H00 hist0 S ->
     prh_run_at sm0 x0 os0 i0 (prhPj_free_evs F) ->
     exists hist', PresetRoomPos.iface_room_pos sm0 x0 os0 (i0 + length (prhPj_free_evs F))%nat H00 hist' S') ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S'.
Proof.
intros sm x os i H0 hist S S' F Lb HF HR HT HP.
destruct F as [|b F'].
- cbn [map] in HF. subst Lb.
  assert (Hn : nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HBulk [])).
  { unfold prh_run_at in HR. cbn [length] in HR. rewrite l6f_nth_skipn.
    destruct (skipn i (PresetRun.hruns sm x os)) as [|e r]; cbn in HR |- *; [discriminate HR|].
    injection HR as He. rewrite He. reflexivity. }
  destruct (HT sm x os i H0 hist HP (prhPj_run_at_nil sm x os i)) as (h' & H').
  cbn [prhPj_free_evs length] in H'. rewrite Nat.add_0_r in H'.
  exists h'. exact (proj1 (prhPj_bulk_nil_pos sm x os i H0 h' S' Hn) H').
- destruct (HT sm x os i H0 hist HP (prhPj_free_evs_supply sm x os i (b :: F') Lb HF HR)) as (h' & H').
  cbn [prhPj_free_evs length] in H'. rewrite Nat.add_1_r in H'.
  exists h'. exact H'.
Qed.
End STEP.

Section L6F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
(* the cut file's two budget functions (count and live bytes per cut index; this lane goes from cut 10 to cut 11) *)
Variables ec_ccut ec_lcut : @ecx rc A_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
(* segment L6f is after check_no_overread's frees: its cuts, journals and lane are at wle' over the fixed zone
   (Ent102CutsA.v ec_invR / ec_laneR WLE'), and pj_free's text concludes SRr' segs RZ_cf with its post at wle' *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).

Theorem seg_L6f_A :
  @seg_L6f_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L6f_stmt, ec_laneR.
intros E fk HYP W c Hcut.
(* the parts of ec_hyps this lane reads, by name: the texts (pj_free's, the stack table), the image facts, the
   universe at pj_free's call, and the two budgets' monotonicity (cut 10 -> cut 11; this lane calls nothing that
   counts or holds beyond pj_free's frees, so ec_pay is not read) *)
pose proof (ech_texts _ _ _ _ _ _ _ _ _ _ HYP) as HTX. pose proof (ech_img _ _ _ _ _ _ _ _ _ _ HYP) as HIMG.
pose proof (ech_univ _ _ _ _ _ _ _ _ _ _ HYP) as HUNIV.
pose proof (ech_ccut_ok _ _ _ _ _ _ _ _ _ _ HYP) as HCC. pose proof (ech_lcut_ok _ _ _ _ _ _ _ _ _ _ HYP) as HLC.
pose proof (ei_sio _ _ _ _ _ _ HIMG) as Hsio.
pose proof (ei_sio_frame _ _ _ _ _ _ HIMG) as Hsioframe.
pose proof (ei_frame _ _ _ _ _ _ HIMG) as Hfrm.
pose proof (ei_pst_ro _ _ _ _ _ _ HIMG) as Hpstro.
pose proof (eu_pjf _ _ HUNIV) as HUPJ. pose proof (et_stk _ _ _ _ _ HTX) as HSTKT.
pose proof (et_pj_free _ _ _ _ _ HTX) as PJF.
(* THE HULL BUDGET AT A POSITION (ec_hyps' ech_hull_pay): pj_free's text asks `v <> 0 -> hull_budget S []` *)
pose proof (ech_hull_pay _ _ _ _ _ _ _ _ _ _ HYP) as HHULL.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt & k & D & trp & t & Hat & Hinv & Hrout & HCC10
  & HLC10 & Hrkd & Hfr & HLD & HFD & HPJF & Hnb & Hjr).
destruct Hinv as ((WSj & HJw & HWB) & HOWN & (gmost & gown & HLED) & HSIO & HRO & HLIVE & (hist0 & HR0) & HCNT & HPRE
  & HPAY & HPERM & HBYTES & HMN).
(* THE WILD BUDGET (cut_free at ec_wk_free, cut_exit at ec_wk_exit = ec_wk_free + prh_wk F_pj_free; the kit's pj_free text
   is not budgeted): the cut's journal at its budget WSj is rebased to the PLAIN journal from the entry with the depot
   moved to the cut's (Ent102CutsA.v ec_journal_rebaseR); the lane runs its plain steps and call on it, and the exit's
   journal is unbased back to WSj (ec_journal_unbaseR); all at the lane's wle' *)
pose proof HJw as HJ. apply ec_journal_rebaseR in HJ.
(* ec_pre's parts BY TYPE (Ent102CallA.v ec_conj_pick), while the only float state in the context is the entry's fx *)
assert (HPREX : afn_pre_x SEGS B ARc LLVMF_STK (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [])
  by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (HS0E : s0Z (e_regs E) < YM05.alloc_ceiling) by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (HNC : (e_n E = 0 /\ e_p E = EC_EMPTY) \/
  (0 < e_n E < 2 ^ 26 /\ In (e_p E, e_n E) (ablocks B (e_ly E) (e_S E))))
  by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (HBB0 : blocks_bytes (e_S E) + LIVE_LIB <= LIVE_MAX)
  by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (HRO0 : arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
  (aview SEGS (w_H (e_W E)) (e_mem E))) by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (HSIO0 : EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E)))
  by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (Hi0 : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)))
  by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (Hsm : e_sm E = ReaderRes.jr_strtod) by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
(* the run has at most 4 calls: ec_pre's length (e_os E) <= 3 and this call's triple *)
assert (HOS3 : (length (e_os E) <= 3)%nat) by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
assert (HOS4 : (length (e_os E ++ [trp]) <= 4)%nat) by (rewrite length_app; cbn [length]; lia).
assert (HNL : e_n E = Z.of_nat (length (e_pl E))) by (pose proof HPRE as X; unfold ec_pre in X; ec_conj_pick X).
destruct Hat as (fy & Hfz & Hkept & Hc). subst c.
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & Hflagw). subst own.
pose proof HPREX as (_ & _ & Hra40 & Hgp0 & Htp0 & _ & _ & _ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HAR as (HARcf & HXS).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (l6f_LAWS B).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (l6f_geom B ly S Hp W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh).
change (EC_FRAME_BYTES / 8) with 16 in Gsh.
unfold EC_FRAME_BYTES in Gceil, Gfr, Gapp.
destruct Hrkd as (Hrk & R21).
pose proof Hrk as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
pose proof Hfr as (Hsaved & Hshv & Hal32).
pose proof Hsaved as (Sra & S8 & _).
(* ---- the model's events: the HBulk of pj_free (&doc) at cut_free's index, the exit's index one later ---- *)
assert (Hlen : Z.of_nat (length (e_x E)) <= EC_NMAX) by (unfold e_x, ec_bytes; rewrite length_map; lia).
assert (Hck : ck_read (e_x E) = Some t) by (unfold ck_read, PjGrammar.json_read; rewrite <- Hsm; exact Hjr).
pose proof (ec_tail_run E trp t Hi0 Hsm Hlen Hrout Hck) as HRUN.
replace (ec_rt E t ++ ec_rej E ++ ec_sw E t ++ [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))])
  with ((ec_rt E t ++ ec_rej E ++ ec_sw E t) ++ [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))])
  in HRUN by (rewrite <- !app_assoc; reflexivity).
apply prh_run_at_app_iff in HRUN as [_ HRUN].
replace (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E) + length (ec_rt E t ++ ec_rej E ++ ec_sw E t))%nat
  with (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t ++ ec_rej E ++ ec_sw E t))%nat
  in HRUN by (rewrite !length_app; lia).
assert (Eidx : (e_i0 E + length (ec_call_evs E trp))%nat =
  Datatypes.S (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t ++ ec_rej E ++ ec_sw E t))).
{ assert (Hx : Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB)
    by (unfold EC_NMAX in Hlen; unfold PresetReqAt.MAXB; lia).
  assert (Heq : ec_call_evs E trp = ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t ++ ec_rej E ++ ec_sw E t ++
    [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))]).
  { rewrite (Ent102PosA.ec_call_evs_ranout_false rc A_prog_listing PA E trp Hx Hrout). f_equal.
    unfold PresetRun.call_rest, PresetRun.call_tail, ec_pn, ec_sc, ec_rt, ec_rej, ec_sw. cbv zeta.
    rewrite Hjr. reflexivity. }
  rewrite Heq, !length_app. cbn [length]. lia. }
(* pj_free's order list of the doc's tree WITH its ordered tie: cut_free's ec_pjf (the kit's shape) at the depth bound
   DOC_D; the reading's depth is <= MAXD (PjGrammar.json_read_depth on cut_free's accepted reading) *)
assert (Hdep : (PjTree.depth t <= DOC_D)%nat).
{ pose proof (PjGrammar.json_read_depth (e_sm E) (e_x E) t Hjr) as Hd. unfold DOC_D. lia. }
destruct (HPJF DOC_D Hdep) as (F & HFO & HTIE).
(* ---- the arithmetic of the cut: sp0, A = (sp0 - 128) & -32, the frame fk ---- *)
assert (Rsp : YM05.alloc_ceiling + 32768 <= e_sp0 E <= 2 ^ 47) by lia.
assert (Hsp16 : e_sp0 E = 16 * (e_sp0 E / 16))
  by (pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D0; rewrite Hal16 in D0; lia).
assert (EA : e_A E = (e_sp0 E - 128) / 32 * 32).
{ unfold e_A, ec_A, EC_SAVE. apply l6f_land_neg32. lia. }
assert (HA32 : e_A E mod 32 = 0) by (rewrite EA; apply Z.mod_mul; lia).
assert (HAb : e_sp0 E - 144 <= e_A E <= e_sp0 E - 128).
{ rewrite EA.
  pose proof (Z.div_mod (e_sp0 E - 128) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (e_sp0 E - 128) 32 ltac:(lia)) as D2. lia. }
assert (Hfk32 : fk = 32 * (fk / 32))
  by (pose proof (Z.div_mod fk 32 ltac:(lia)) as D0; rewrite Gal in D0; lia).
assert (Hfk8 : fk = 8 * (fk / 8)).
{ pose proof (Z.div_mod fk 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound fk 8 ltac:(lia)) as D1. lia. }
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
assert (HSPr : spZ regs = e_A E).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
(* ======== +0x1bc  mv a0, s5 ======== *)
unfold cfg_at.
change (w64 EC_FREE) with (Z_to_bv 64 (BASE + 0x1bc)).
l6f_fd 0x1bc Hpl1 Hd1.
eapply (l6f_step_addiR (fx := fy) WLE' W regs mem md _ 0x1bc _ _ _ _ (10%bv : bv 5) (getr regs (21%bv : bv 5))
  ltac:(lia) Hpl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (21%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJm1.
(* ======== +0x1c0  jal ra, pj_free ======== *)
change (0x1bc + 4) with 0x1c0.
l6f_fdc 0x1c0 Hpl2.
eapply (l6f_step_callR (fx := fy) WLE' W _ mem _ _ 0x1c0 _ _ (1%bv : bv 5) ltac:(lia) Hpl2).
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJm1) as HJm2.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
(* ---- the callee's registers ---- *)
assert (HSPC : spZ regsc = e_sp0 E + (e_A E - e_sp0 E)).
{ unfold spZ. rewrite Eregsc, !getr_other by l6f_regne. rewrite R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HS0C : s0Z regsc = e_sp0 E).
{ unfold s0Z. rewrite Eregsc, !getr_other by l6f_regne. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by l6f_regne. rewrite R3. exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by l6f_regne. rewrite R4. exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + 0x1c4)).
{ rewrite Eregsc. apply getr_same. l6f_regne. }
assert (HA10 : getr regsc 10 = w64 (ec_doc fk)).
{ rewrite Eregsc, getr_other by l6f_regne. rewrite getr_same by l6f_regne. exact R21. }
(* the return site is a listing slot of the image: in [kImgLo, kImgEnd), below the ceiling *)
l6f_fd 0x1c4 Hpl3 Hd3.
pose proof (l6f_img_bounds B ly S Hp W mem md (BASE + 0x1c4) HAR
  (l6f_slot_img (PA := PA) 0x1c4 _ ltac:(lia) Hpl3)) as HRIMG.
unfold kImgLo, kImgEnd in HRIMG.
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x1c4)))
  by exact (ret_ok_codeptr_v (PI := PA) 0x1c4 ltac:(lia) eq_refl).
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 0x1c4))) by (rewrite unsigned_lit_small by lia; lia).
assert (HRAC : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite HRA1, unsigned_lit_small by lia; lia).
(* ---- the callee's stack: STK_pj_free DOC_D - (A - sp0) <= LLVMF_STK (et_stk, ei_frame) ---- *)
assert (HSTKF : 0 <= STK_pj_free DOC_D).
{ unfold STK_pj_free. apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; [lia | apply pi_frame_nonneg] |].
  apply l6f_zmaxl_nonneg. }
assert (HBUD : STK_pj_free DOC_D - (e_A E - e_sp0 E) <= LLVMF_STK).
{ unfold STK_LLVMFuzzerTestOneInput in HSTKT.
  lazymatch type of HSTKT with _ + zmaxl ?l <= _ =>
    assert (Hz : STK_pj_free DOC_D <= zmaxl l)
      by (apply l6f_zmaxl_in; cbn [In]; do 15 right; left; reflexivity) end.
  unfold EC_SAVE in Hfrm. lia. }
assert (HO16 : (e_A E - e_sp0 E) mod 16 = 0).
{ pose proof (Z.div_mod (e_A E) 32 ltac:(lia)) as D1. rewrite HA32 in D1.
  replace (e_A E - e_sp0 E) with ((2 * (e_A E / 32) - e_sp0 E / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
(* ---- the frame chain at the call: s0 = sp0, the entry's ra and s0 saved below it ---- *)
assert (Hch : exists ch1, achain ly (aview SEGS (w_H W) mem) (e_sp0 E + (e_A E - e_sp0 E)) (s0Z regsc) ch1).
{ rewrite HS0C. destruct (Z_lt_le_dec (e_sp0 E) (ly_top ly - 16)) as [Hlt|Hge].
  - exists [(e_sp0 E, raZ (e_regs E), s0Z (e_regs E))].
    apply (achain_push ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem) (e_sp0 E) (s0Z (e_regs E))
      (raZ (e_regs E)) []).
    + apply achain_low. exact HS0E.
    + rewrite Etop. lia.
    + intros a _. reflexivity.
    + apply l6f_rdword_of_rd64; [exact Sra | unfold raZ; apply u64_range].
    + apply l6f_rdword_of_rd64; [exact S8 | unfold s0Z; apply u64_range].
    + exact Hra40.
    + lia.
    + rewrite Hsp16. replace (16 * (e_sp0 E / 16)) with ((2 * (e_sp0 E / 16)) * 8) by lia.
      apply Z.mod_mul. lia.
    + exact Hlt.
    + lia.
  - exists []. unfold achain. left. split; [right; left; lia | reflexivity]. }
destruct Hch as (ch1 & Hch).
(* ---- the callee's footprint: the doc's 56 bytes in this call's own frame, and D's allocator blocks ---- *)
pose (FP1 := if ec_doc fk =? 0 then [] else (ec_doc fk, ec_doc fk + 56) :: ablocks_fp (prhPj_hbl D)).
assert (Hne0 : (ec_doc fk =? 0) = false) by (apply Z.eqb_neq; unfold ec_doc; lia).
assert (HBLKS : forall a k0, In (a, k0) D -> In (a - cf_head, k0 + cf_head) (ablocks B ly S)).
{ intros a k0 HinD.
  assert (HinL : In (a, k0) Lam) by exact (Permutation_in _ (Permutation_sym HLD) HinD).
  exact (proj1 (proj2 (prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAX 0 a k0 gmost gown HLED HinL))). }
assert (HNOTE : forall a k0, In (a, k0) D -> ~ In (a - cf_head, k0 + cf_head) (ablocks B (e_ly E) (e_S E))).
{ intros a k0 HinD Hine.
  assert (HinL : In (a, k0) Lam) by exact (Permutation_in _ (Permutation_sym HLD) HinD).
  destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md _ _ HAR (HBLKS a k0 HinD)) as (_ & _ & _ & _ & _ & Hpw).
  pose proof (l6f_nodup_pw _ (prh_ablocks_nonneg_cf B ly S Hp W mem md HARcf) Hpw) as HND.
  pose proof (Permutation_NoDup HPERM HND) as HND2.
  unfold ck_hblks in HND2.
  exact (l6f_nodup_app_l _ _ _ HND2 (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Lam (a, k0) HinL)
    Hine). }
(* the flag word and the frame's shadow bytes are outside the callee's footprint *)
assert (HNF : forall a, (fk + 120 <= a < fk + 128 \/ shadow_addr fk <= a < shadow_addr fk + 16) -> ~ inFP FP1 a).
{ intros a Ha Hfp. unfold FP1 in Hfp. rewrite Hne0 in Hfp. cbv beta iota in Hfp. apply inFP_cons in Hfp.
  destruct Hfp as [Hd | Hb].
  - unfold ec_doc in Hd. destruct Ha as [Ha | Ha]; [lia|]. rewrite Esh in Ha. unfold SHADOW_OFF in Ha.
    destruct Gapp as (_ & [Hl | (Hh & _)]); [unfold kLowShadowBeg in Hl | unfold kHighMemBeg in Hh]; lia.
  - destruct Hb as (r & Hr & Hra). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
    apply in_map_iff in Hr as ((a' & k') & <- & HinD). cbn [fst snd] in Hra.
    destruct Ha as [Ha | Ha].
    + exact (l6f_blk_frame B ly S Hp W mem md _ _ LLVMF_FS_CLASS pos a HAR (HBLKS a' k' HinD) Hin
        ltac:(rewrite <- Hfkeq; change (fs_frame_bytes LLVMF_FS_CLASS) with 128; lia) Hra).
    + destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md _ _ HAR (HBLKS a' k' HinD)) as (_ & _ & _ & Happ & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. rewrite Esh in Ha. unfold SHADOW_OFF in Ha.
      lia. }
(* ======== the call: pj_free's text at the callee window 0 (its SRr' and post at wle': aj_call_xWR at WLE') ======== *)
eapply SRrG_mono.
{ eapply (aj_call_xWR (fx := fy) (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
    (wle'_refl SEGS _) (wle'_trans SEGS _) W regsc mem
    (@pa_sigma rc A_prog_listing PA AS_pj_free)
    LLVMF_STK (e_sp0 E) [] (e_ly E) _ [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)] ly S Hp mdc k
    (STK_pj_free DOC_D) 0 FP1 (e_A E - e_sp0 E) (Z_to_bv 64 (BASE + 0x1c4)) ch1 _
    HJm2 HSPC HO16 ltac:(lia) HSTKF HBUD ltac:(lia) eq_refl ltac:(lia) HGP HTP HRA1 HRAW HRA4 Hch).
  - (* the callee: tpj_free_specX at v = &doc, D with its order list F, Lam, the cut's ledger (most / own) *)
    intros HPRE1 HWIN1. unfold fpostW_xR.
    eapply (PJF fy gmost gown ly S Hp W regsc mem mdc ch1 0 (ec_doc fk) D F Lam peak cnt SIZE_MAX 0).
    + split; [exact HPRE1|]. split; [exact HRO|].
      split; [rewrite HSPC, Eshi; lia|]. split; [exact HRAC | exact Hfz].
    + exact HUPJ.
    + exact HLIVE.
    + intros _. exact (l6f_ccnt24 _ _ _ _ _ _ S HR0).
    + (* the hull budget of its frees (none secondary): ech_hull_pay at the cut's position, the empty list *)
      intros _. exact (HHULL (e_sm E) (e_x E) (e_os E ++ [trp]) _ (e_H0 E) hist0 S [] HOS4 HR0
        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    + exact HA10.
    + exact HWIN1.
    + right. split; [unfold ec_doc; lia|]. split; [unfold ec_doc; lia|]. split; [exact HFO|].
      unfold ec_doc.
      split; [lia|].
      split.
      { right; right; left. exists LLVMF_FS_CLASS, pos. split; [exact Hin|]. rewrite <- Hfkeq.
        change (fs_frame_bytes LLVMF_FS_CLASS) with 128. lia. }
      split.
      { split.
        - rewrite Hfk32. replace (32 * (fk / 32) + 32) with ((4 * (fk / 32) + 4) * 8) by lia.
          apply Z.mod_mul. lia.
        - intros x Hx. apply (apresent_writable SEGS). exact (proj1 (Gfr x ltac:(lia))). }
      split.
      { unfold amem_range. destruct Gapp as (_ & [Hl | (Hh & Hc')]).
        - left. unfold kLowShadowBeg in Hl. unfold kLowMemEnd. lia.
        - right. unfold kHighMemBeg in Hh |- *. unfold ASAN_CEIL in Hc'. unfold kHighMemEnd. lia. }
      split.
      { intros a Ha. split; [exact (proj1 (proj2 (Gfr a ltac:(lia))))|].
        pose proof HPRE1 as (_ & _ & _ & _ & _ & Hstk1 & _). destruct Hstk1 as (_ & _ & Hc1 & Hl1 & _). lia. }
      split.
      { intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
        replace (SHADOW_OFF + x / 8) with (shadow_addr fk + (x / 8 - fk / 8)) by (rewrite Esh; lia).
        apply (l6f_shadow_zero (PA := PA) (w_H W) mem (shadow_addr fk) Hshv).
        pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2. lia. }
      { intros s Hs. apply (aview_some_of_apresent SEGS).
        assert (E1 : shadow_addr (fk + 32) = shadow_addr fk + 4).
        { unfold shadow_addr. rewrite Hfk8 at 1. replace (8 * (fk / 8) + 32) with ((fk / 8 + 4) * 8) by lia.
          rewrite Z.div_mul by lia. lia. }
        assert (E2 : shadow_addr (fk + 32 + 56 - 1) = shadow_addr fk + 10).
        { unfold shadow_addr. rewrite Hfk8 at 1. replace (8 * (fk / 8) + 32 + 56 - 1) with ((fk / 8 + 10) * 8 + 7) by lia.
          rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
        rewrite E1, E2 in Hs.
        pose proof (Z.div_mod (shadow_addr fk + 4) 8 ltac:(lia)) as D1.
        pose proof (Z.mod_pos_bound (shadow_addr fk + 4) 8 ltac:(lia)) as D2.
        pose proof (Z.div_mod (shadow_addr fk + 10) 8 ltac:(lia)) as D3.
        pose proof (Z.mod_pos_bound (shadow_addr fk + 10) 8 ltac:(lia)) as D4.
        assert (HS0 : shadow_addr fk = 0x7fff8000 + 4 * (fk / 32)) by (rewrite Esh; unfold SHADOW_OFF; lia).
        replace s with (shadow_addr fk + (s - shadow_addr fk)) by lia.
        exact (proj1 (Gsh (s - shadow_addr fk) ltac:(lia))). }
    + (* The batch kit: pj_free's text takes prh_head_wide (8 <= cf_head); the image's ei_head gives cf_head = HEAD *)
      unfold prh_head_wide. rewrite (ei_head _ _ _ _ _ _ HIMG). unfold PresetReqAt.HEAD. lia.
    + exact HLED.
  - (* the footprint: the doc in this call's own frame, D's blocks are blocks taken since the entry *)
    intros a Ha. unfold FP1 in Ha. rewrite Hne0 in Ha. cbv beta iota in Ha. apply inFP_cons in Ha.
    destruct Ha as [Ha | Ha].
    + right. right. left. exists (LLVMF_FS_CLASS, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq. change (fs_frame_bytes LLVMF_FS_CLASS) with 128.
      unfold ec_doc in Ha. lia.
    + right. left. destruct Ha as (r & Hr & Hra). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
      apply in_map_iff in Hr as ((a' & k') & <- & HinD). cbn [fst snd] in Hra.
      exists (a' - cf_head), (k' + cf_head). split; [exact (HBLKS a' k' HinD)|].
      split; [exact (HNOTE a' k' HinD) | exact Hra]. }
(* ======== +0x1c4: the exit cut ======== *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & HJ1 & _ & HP2 & HK).
destruct HK as (HK & HKmn). cbv beta in HK.
(* The kit's post (PRH_FnPj.v 838c63d8cd16): the room, the position transfer over prhPj_free_evs F, Lam' with D split
   off, the blocks, the ledger *)
(* its post's second conjunct is the hull use of its frees (none secondary), not read by this lane *)
destruct HK as (HRL2 & _ & HTR & Lam' & HpLam & HpBlk & HLED2 & _ & _ & _).
(* the position one model event later: the HBulk of pj_free (&doc), with the ordered tie of cut_free's ec_pjf *)
assert (Hpos2 : exists h2, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
  (e_i0 E + length (ec_call_evs E trp))%nat (e_H0 E) h2 S2).
{ rewrite Eidx.
  exact (l6f_pos_step _ _ _ _ _ hist0 S S2 F _ HTIE HRUN HTR HR0). }
assert (HL0 : Lam' = []).
{ pose proof (Permutation_length HpLam) as E1. pose proof (Permutation_length HLD) as E2.
  rewrite length_app in E1. destruct Lam' as [|x tl]; [reflexivity|]. cbn [length] in E1. lia. }
subst Lam'.
assert (HHp2 : Hp2 = []).
{ pose proof (prh_ledger_heads B ly2 S2 Hp2 W2 mem2 [] peak cnt SIZE_MAX 0 gmost gown HLED2) as Hh. cbn [map] in Hh.
  apply Permutation_sym, Permutation_nil in Hh. exact Hh. }
assert (HBLK2 : Permutation (ablocks B ly2 S2) (ablocks B (e_ly E) (e_S E))).
{ apply (Permutation_app_inv_l (prhPj_hbl D)).
  apply (Permutation_trans (Permutation_sym HpBlk)). apply (Permutation_trans HPERM).
  apply Permutation_app_tail. unfold ck_hblks, prhPj_hbl. apply Permutation_map. exact HLD. }
pose proof HJ1 as (_ & Hly1 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & F4 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & EF2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2c & F3c & _).
assert (Hfa2 : frame_addr ly2 LLVMF_FS_CLASS pos = frame_addr ly LLVMF_FS_CLASS pos)
  by (unfold frame_addr; rewrite EF2; reflexivity).
assert (Hga2 : flag_addr ly2 LLVMF_FS_CLASS pos = flag_addr ly LLVMF_FS_CLASS pos)
  by (unfold flag_addr; rewrite EF2; reflexivity).
exists ly2, S2, Hp2, regs2, mem2, md2, [(LLVMF_FS_CLASS, pos)], peak, cnt, 0, (k + k1), trp.
split; [exists fy; split; [exact Hfz|]; split; [exact Hkept | reflexivity]|].
split.
{ (* ec_inv at the exit, Lam = [] *)
  split.
  { exists WSj. split; [eapply ec_journal_unbaseR; [exact HJw | exact HJc]|].
    destruct ec_wk_values as (_ & _ & _ & _ & _ & _ & _ & Ewf & Ewe & _). rewrite Ewe. rewrite Ewf in HWB. exact HWB. }
  split.
  { exists pos. split; [reflexivity|]. split; [rewrite Hfa2; exact Hfkeq|]. split; [exact Hfk0|].
    rewrite Hga2. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hflagw].
    intros i Hi. apply (F4 LLVMF_FS_CLASS pos _ Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq.
      change (fs_frame_bytes LLVMF_FS_CLASS) with 128. unfold EC_FRAME_BYTES. lia.
    - apply HNF. left. unfold EC_FRAME_BYTES. lia. }
  split; [exists gmost, gown; exact HLED2|].
  split.
  { apply (Hsioframe (aview SEGS (w_H (e_W E)) (e_mem E)) (aview SEGS (w_H W2) mem2)); [|exact HSIO0].
    intros a Ha. destruct (Hsio a Ha) as ((Ho & He) & Hi & Hnp).
    apply F3c; [exact Hi | exact Ho | exact He | exact Hnp | apply fp_spares_closed; exact sink_closed_nil]. }
  split.
  { intros a Hro Ho He.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr];
      [exists s; split; [exact Hs | lia] | exact (@pa_relro_img rc A_prog_listing PA a Hr)]. }
    assert (Hsp : fp_spares (SK := SK) [] a) by (apply fp_spares_closed; exact sink_closed_nil).
    rewrite (F3c a Hi Ho He (fun Hp' => Hpstro a Hp' Hro) Hsp).
    exact (HRO0 a Hro Ho He). }
  split; [exact HRL2|].
  split; [exact Hpos2|].
  split; [exact HCNT|].
  split; [exact HPRE|].
  split.
  { destruct HNC as [(Hn0 & _) | (_ & Hinp)];
    [left; exact Hn0 | right; exact (Permutation_in _ (Permutation_sym HBLK2) Hinp)]. }
  split; [unfold ck_hblks; cbn [map app]; exact HBLK2|].
  split.
  { intros i Hi. destruct HNC as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
    pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
    apply (F2c (e_p E) (e_n E) i Hinp (Permutation_in _ (Permutation_sym HBLK2) Hinp) ltac:(lia)).
    intros (r & Hr & _). destruct Hr. }
  exact (HKmn HMN). }
split; [exact HHp2|].
(* the two budgets at cut 11, paid from cut 10's: the count is unchanged, the blocks are the entry's again *)
split; [destruct (HCC E 10%nat 11%nat) as (_ & Hc1011); specialize (Hc1011 ltac:(lia)); lia|].
split.
{ destruct (HLC E 11%nat 11%nat) as ((_ & Hl11) & _).
  rewrite (prh_blocks_bytes_ablocks B ly2 S2), (l6f_bsum_perm _ _ HBLK2),
    <- (prh_blocks_bytes_ablocks B (e_ly E) (e_S E)).
  lia. }
split.
{ (* ec_rk: every register the cut reads is callee-saved *)
  split; [rewrite (l6f_pres regsc regs2 (2%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R2|].
  split; [rewrite (l6f_pres regsc regs2 (3%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R3|].
  split; [rewrite (l6f_pres regsc regs2 (4%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R4|].
  split; [rewrite (l6f_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R8|].
  split; [rewrite (l6f_pres regsc regs2 (9%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R9|].
  split; [rewrite (l6f_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R18|].
  split; [rewrite (l6f_pres regsc regs2 (19%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R19|].
  split; [rewrite (l6f_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R20|].
  split; [rewrite (l6f_pres regsc regs2 (26%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
          exact R26|].
  rewrite (l6f_pres regsc regs2 (27%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne. exact R27. }
(* ec_frame: the saved block is above the callee's window, the frame's shadow is outside its footprint *)
split; [|split; [|exact Hal32]].
- assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
    rd64 (aview SEGS (w_H W) mem) a v -> rd64 (aview SEGS (w_H W2) mem2) a v).
  { intros a v Ha1 Ha2 Hr. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hr].
    intros j Hj. apply F1; lia. }
  unfold ec_saved in Hsaved |- *.
  repeat (split; [apply KS; [lia | lia | exact (proj1 Hsaved)] | apply proj2 in Hsaved]).
  apply KS; [lia | lia | exact Hsaved].
- apply (l6f_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hshv].
  intros i Hi. change (Z.of_nat (length ec_frame_shadow)) with 16 in Hi.
  apply (F4 LLVMF_FS_CLASS pos _ Hin).
  + right. unfold in_zr. cbn [fst snd]. rewrite <- Hfkeq. change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16. lia.
  + apply HNF. right. lia.
Qed.

End L6F.

Print Assumptions seg_L6f_A.
About seg_L6f_A.
