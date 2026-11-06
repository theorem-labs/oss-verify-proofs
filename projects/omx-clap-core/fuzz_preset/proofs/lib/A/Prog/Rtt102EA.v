(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_string_seg_ent.v, with its module names changed; 1582 of its 1646 lines of code are new or changed and 650 lines of the source are left out. *)
(* STATE ON THE STEP-2 DRAFT TIP (7ed43ad5685e; the R contract of Rtt102Cut.v at wave 0 448ecd157e57): the stretch
   concludes YA0nH.SRr' SEGS RZ_cf (the re-hiding move) and its journals re_J / re_AJ are at RZW := YA0nH.wle' SEGS
   RZ_cf (CrtFit's WLE contract). The walk runs the engine's R forms: the entry journal YCbqG.ajournal_x_initR at the
   reflexive wle', the runners YC1fPx.paj_run_x_invR / paj_run_to_x_invR, frame_alloc_1 through
   YGcallMxmn.aj_stack_malloc_at_xmR (it concludes the plain SRr with W2 = W, lifted by YA0nH.SRr_SRr'), pj_write
   through YCbqGcall.aj_call_xF_spR (its text tpj_write_specX concludes SRr' with fpostFm at wle'), composed by
   YSRrG.SRr'_bind. Every fact read after pj_write comes from the journals' aview clauses (the ajxR_ projections), never
   from the world conjunct. pj_write's new entry premise `(length rp_os <= 4)%nat` is rtt_pre's 29th conjunct. No
   Section hypothesis changed. *)
(* STATE ON THE BATCH KIT'S CUT (the batch kit walk lane, shared layer 80a1d52c32c7: the cut 7cdbb61b5fa0 merged at
   c46ea8f2977, Rtt102Cut.v / Rtt102FR1Kit.v re-fitted): the stretch is `rtt_seg_e_A : RTT_SEG_E`, UNCONDITIONAL. The
   one withheld fact of the pre-cut file, K0-REFUTE-PJW (premise re_K0_REFUTE_PJW of rtt_seg_e_A_of_refute, which was
   DeadK1's tpj_write_specX text verbatim, the DeadK1 head c753d960f56, PRH_FnWriter.v blob 0bd195c1199a),
   RETIRES: the cut's lib/A/PRH_FnWriter.v (blob d89d3c67b78c) carries that text as its own tpj_write_specX, taken here
   as the callee-text Section hypothesis TPJW (owned by the kit, at every float state, as every callee text of the walk).
   THE COMPARISON, re_K0_REFUTE_PJW against the cut's tpj_write_specX at n := DOC_D, conjunct by conjunct (a token
   diff of the two texts with comments stripped; spellings segs / rdW / pa_sigma / module prefixes normalised):
     binders        `rp_sm : list Z -> Z * Z` GONE (the run's strtod model is keyed); rp_x rp_os rp_i rp_H0 rp_hist
                    most own, ly S Hp W regs mem md ch v pretty t D Lam peak cnt fail ran: EQUAL
     premise 1      fpre B ARx (STK_pj_write DOC_D) ly S Hp W regs mem md ch: EQUAL
     premise 2      prh_univ_closure B CTX0 DW -> prh_univ_closure B CTX0 (DW gone with the 4a / 4b split)
     premise 3      room_live_cf S: EQUAL
     premise 4      iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> the same at ReaderRes.jr_strtod
     (old 5)        `rp_sm = ReaderRes.jr_strtod`: GONE (jr_strtod is written where rp_sm stood)
     premise 5      prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_pjw_evs [] cnt fail (wdpieces t
                    (negb (pretty =? 0))))) -> the same at ReaderRes.jr_strtod
     premises 6-9   getr regs 10 = w64 v, getr regs 11 = w64 pretty, 0 <= pretty < 2 ^ 31, prh_ledger ..: EQUAL
     premise 10     prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_pjw_evs [] ..) -> the same at ReaderRes.jr_strtod
     premises 11-21 pj_nodeR, the place of v, range_addressable, prhWriter_tree_vis, D in Lam, depth <= DOC_D, the
                    depth's 2 ^ 31 bound, the fake-frame count, WMAX, WMAX + cf_head, the live bound: EQUAL
     post           fpostFm .. (STK_pj_write DOC_D) [], binders ok ran' q Lam' peak', prh_oks, a0 = q, room_live_cf S',
                    K0-DEAD-PJWRITE `prh_granted ok cnt fail (prhWriter_k ..)`, pj_nodeR, prhWriter_tree_vis,
                    prh_ledger, both outcome arms: EQUAL; the granted path's `exists hist', iface_room_pos rp_sm ..`
                    -> the same at ReaderRes.jr_strtod
   So at rp_sm := ReaderRes.jr_strtod - the only value E ever supplied (rtt_pre's old `rp_sm = jr_strtod`) - the cut's
   text IS the old premise with that equation discharged and DW dropped: no conjunct weaker, none stronger. Beneath the
   unchanged words the engine moved (the internal file ENGINE-DIFF.md: prh_univ_closure's body, astk_ok's ACALL_PREFIX, AR_laws_x's
   fields, ajournal_x = ajournal_xw .. [] with its 18th conjunct); this file is re-checked against them.
   THE WILD BUDGET: E's two callees (__asan_stack_malloc_1, pj_write) store no wild trace, so E's journal FROM THE
   ENTRY ITSELF (re_AJ below, the empty budget) reaches RT_PJW; Rtt102Cut.rtt_J_of_AJ gives the cut's depot-moved
   rtt_J and rtt_wild_of_AJ at WS = [] gives both rtt_wild facts (rtt_carry's at prh_wk F_round_trip_text,
   rtt_at_pjw's at 0). rtt_pre's 26th conjunct (the wild room) is not read by E. The Section hypotheses are listed at
   `Section f` with their owners. *)
(* fuzz_preset, WalkRtt102 lane E: STRETCH E of round_trip_text's walk on the #102 pins, AT IMAGE A'
   (fuzz_preset.asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4, entry 0x8496c, listing slot 3299).
   THE STATEMENT IS Rtt102Cut.v's: `RTT_SEG_E = rtt_seg RT_PJW rtt_at_pjw -> rtt_seg_entry`, from the function's
   entry (cfg_at (pa_sigma AS_round_trip_text), rtt_pre D) to the cut RT_PJW (+304, A' 0x84a9c, pj_write's return
   site). The cut layer is NOT edited by this file; its definitions are the goal and the premises.
   THE BODY WALKED (+0 .. +0x12c, A' capstone listing :2-78; the same words on B'):
     +0    `addi sp,sp,-0xa0`, `sd zero,0(sp)`, the 13 saves (ra..s11 at sp0-8 .. sp0-104), `addi s0,sp,0xa0`,
           `andi sp,sp,-0x20`, `mv s1,sp`, `mv s3,a2` (copy), `mv s5,a1` (pretty), the two GOT loads
           (+0x58 the use-after-return flag's GOT word, +0x5c the shadow-base GOT word)
     +96   `lw a2,0(a2)`: the use-after-return flag (ARx_const_law: its value is 1)
     +100  `ld s9,0(a1)` (the shadow base), `mv s4,a0` (doc), `beqz a2` (not taken: the flag is 1), `li a0,0x80`
     +116  `jal __asan_stack_malloc_1` = RT_SM, through YGcallMxmn.v's aj_stack_malloc_at_xmR at class RT_CID = 1.
           THE CAPACITY PREMISE `count_cid 1 (frames Sc) < fs_frames 1` is Rtt102Cut.rtt_capacity at the entry
           state, carried to the call state by the journal's `frames Sc = own ++ frames S` at own = [].
     +120  `mv s2,a0`, `mv s10,s2`, `bnez s2` (taken: a0 = frame_addr <> 0 by the rule's post and the frames law,
           so the real-stack fallback +0x8c .. +0xa4 is dead), `sd s10,0x10(s1)`, the frame header
           (F+0 the magic, F+8 the description, F+16 the pc), `srli a3,s10,3; add s9,a3,s9` (s9 := shadow_addr F),
           the 16 shadow bytes ([f1 x4, f8 x7 over granules 4..10, f3 x5]), `mv a0,s4; mv a1,s5`
     +0x12c `jal pj_write`, through YCbqGcall.v's aj_call_xF_spR (pj_write's text is float-form, fpostFm) with the kit's
           tpj_write_specX at n := DOC_D (Section hypothesis TPJW); its post's K0-DEAD-PJWRITE conjunct refutes the
           failed arm (re_refute_pj_write_failed), so only the granted outcome reaches RT_PJW.
   NO WITHHELD FACT: K0-REFUTE-PJW is the cut's own tpj_write_specX (see the comparison above). G4 is gone (g_most
   and g_own_ran_out ride in prh_ledger since base f9eda666dd9).
   TEMPLATES (read, followed, numerals never copied): the S10 walk at 37251f6b9a5 lib/A/Prog/
   S10TxString.v (ts_A :2087, ts_at_B :1950) and S10TxStrGlue.v (ts_A1_entry / ts_A2_entry / ts_A3_entry,
   ts_side_run / ts_side_move) for the prologue, the flag, the frame call and the side facts - round_trip_text's
   prologue and GOT pair are the same instruction sequence as tx_string's, in the same registers;
   the H2H5 walk head 1934271f1f40 lib/A/Prog/H5RttS1.v (rt1_putN_failed .. rt1_wfail, image-free,
   Qed on the old pins) for the writer's pure model, and H5RttE1.v for this function's own prologue shape.
   NUMERALS. LENGTH: 5 / 8 / 13 / 16 / 32 / 64 / 128 / 160 (register and word widths, the saved-register count,
   `addi sp,sp,-0xa0`, `andi sp,sp,-0x20`, the fake frame of class 1), 2 ^ 62 / 2 ^ 64 (counter widths),
   2 ^ 28 (prhWriter_WMAX), 56 (struct pj), 4096 (ESTACK). DERIVED: 96 / 100 / 116 / 120 (byte offsets inside
   round_trip_text, equal on A' and B'), 2 ^ 31 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (the image band, the shadow span and
   the user range), atom indices (the engine's numbering), the A_OBJ indices 0 / 1 / 12 (the listing's object
   slots: the two GOT words and the shadow cell). WORD: register indices. NO ADDRESS LITERAL: every code address
   is `pa_sigma AS_<name>` or `pa_val A_TEXT + 4 * A_prog_slot AS_round_trip_text`. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm YSRrMemnorm YGcfRoomLive.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the zone
   (YGcfRehidePost.RZ_cf), used qualified as Rtt102Cut.v uses them: every stretch concludes YA0nH.SRr' SEGS RZ_cf and
   every journal is at RZW := YA0nH.wle' SEGS RZ_cf (CrtFit's WLE contract) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetRoomPosKeep.
(* the request model of record (PresetReqAt 379c33e9e482 on this base): w_evs / wcaps, which RT_K_W and the cut's
   final capacity count *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetFlush.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp WriterSpec
  WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
(* The kit's supply file, PIN-FREE on base f9eda666dd9 (blob d6e52752685a): it turns pj_write's post position into the
   model's w_evs (PRH_Supply.prhWriter_pjw_evs_granted / prhWriter_pjw_evs_w_evs), which RT_K_W counts. Cited,
   never re-proved *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA Rtt102Cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- THE WRITER'S PURE MODEL (image-free; H5RttS1.v rt1_* at 1934271f1f40, Qed there, rebuilt here under
   this lane's names because that file is an old-pin file and is not required) ---- *)
Lemma re_nth_hd : forall (l : list bool), nth 0 l true = hd true l.
Proof. intros [|x l]; reflexivity. Qed.
Lemma re_nth_tl : forall (l : list bool) i, nth (S i) l true = nth i (tl l) true.
Proof. intros [|x l] i; [destruct i|]; reflexivity. Qed.

(* a failed writer stays as it is *)
Lemma re_putN_failed : forall P ok st, WriterApp.w_failed st <> 0 ->
  PRH_FnWriter.prhWriter_putN ok st P = st.
Proof.
induction P as [|b P IH]; intros ok st H; [reflexivity|].
cbn [PRH_FnWriter.prhWriter_putN]. unfold PRH_FnWriter.prhWriter_grows.
rewrite (proj2 (Z.eqb_neq _ 0) H). cbn [andb].
assert (E1 : WriterApp.put1 st b = st).
{ unfold WriterApp.put1. destruct (Z.eqb_spec (WriterApp.w_failed st) 0); [lia | reflexivity]. }
rewrite E1. apply IH. exact H.
Qed.

(* the calls list only grows *)
Lemma re_putN_calls : forall P ok st, exists l,
  WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ l.
Proof.
induction P as [|b P IH]; intros ok st; [exists []; rewrite app_nil_r; reflexivity|].
cbn [PRH_FnWriter.prhWriter_putN]. destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G.
- destruct (IH (tl ok) (PRH_FnWriter.prhWriter_put1 (hd true ok) st b)) as [l E]. rewrite E.
  unfold PRH_FnWriter.prhWriter_put1. rewrite G. cbv zeta.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [|destruct (hd true ok)]; cbn [WriterApp.w_calls];
    eexists; rewrite <- app_assoc; reflexivity.
- destruct (IH ok (WriterApp.put1 st b)) as [l E]. rewrite E.
  unfold WriterApp.put1. destruct (negb (WriterApp.w_failed st =? 0)); [exists l; reflexivity|].
  cbv zeta.
  destruct (Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b) + 1 <=? WriterApp.w_cap st);
    [exists l; reflexivity|].
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); cbn [WriterApp.w_calls];
    eexists; rewrite <- app_assoc; reflexivity.
Qed.

(* g_fail_at stays SIZE_MAX: nothing on the bounded path injects a failure *)
Lemma re_wfail_max : forall P ok st, WriterApp.w_fail st = 2 ^ 64 - 1 ->
  WriterApp.w_fail (PRH_FnWriter.prhWriter_putN ok st P) = 2 ^ 64 - 1.
Proof.
induction P as [|b P IH]; intros ok st H; [exact H|].
cbn [PRH_FnWriter.prhWriter_putN]. destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G; apply IH.
- unfold PRH_FnWriter.prhWriter_put1. rewrite G. cbv zeta.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [reflexivity|].
  destruct (hd true ok); cbn [WriterApp.w_fail]; exact H.
- unfold WriterApp.put1. destruct (negb (WriterApp.w_failed st =? 0)); [exact H|]. cbv zeta.
  destruct (Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b) + 1 <=? WriterApp.w_cap st);
    [cbn [WriterApp.w_fail]; exact H|].
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); cbn [WriterApp.w_fail]; [reflexivity | exact H].
Qed.

(* A RUN THAT ENDS UNFAILED: every grow accepted, so its calls are grow_calls of the pieces, g_count grew by
   their number and the capacity is grow_cap's *)
Lemma re_wsucc : forall P ok st,
  WriterApp.w_failed st = 0 -> 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
  (forall i, (i < length (WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st)
                              (WriterSpec.piece_lens P)))%nat -> nth i ok true = true) /\
  WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++
    WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st) (WriterSpec.piece_lens P) /\
  WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok st P) = (WriterApp.w_cnt st + Z.of_nat (length
    (WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st)
       (WriterSpec.piece_lens P)))) mod 2 ^ 64 /\
  WriterApp.w_fail (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_fail st /\
  WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok st P) =
    WriterSpec.grow_cap (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st) (WriterSpec.piece_lens P).
Proof.
induction P as [|b P IH]; intros ok [f t c n fl cs] Hf Hn Hend;
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *;
  subst f.
- cbn [PRH_FnWriter.prhWriter_putN WriterSpec.piece_lens map WriterSpec.grow_calls WriterSpec.grow_cap length
       WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *.
  split; [intros i Hi; lia|]. split; [rewrite app_nil_r; reflexivity|].
  split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|]. split; reflexivity.
- unfold WriterSpec.piece_lens. cbn [map]. fold (WriterSpec.piece_lens P).
  cbn [WriterSpec.grow_calls WriterSpec.grow_cap].
  cbn [PRH_FnWriter.prhWriter_putN] in Hend |- *.
  unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in Hend |- *.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap] in Hend |- *.
  rewrite Z.eqb_refl in Hend |- *. cbn [andb] in Hend |- *.
  destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  + unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in Hend |- *.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in Hend |- *.
    rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) Hg) in Hend |- *. cbn [andb] in Hend |- *. cbv zeta in Hend |- *.
    destruct (Z.eqb_spec n fl) as [Enf|Enf].
    * rewrite re_putN_failed in Hend by (cbn [WriterApp.w_failed]; lia). cbn [WriterApp.w_failed] in Hend. lia.
    * destruct (hd true ok) eqn:Hhd.
      2:{ rewrite re_putN_failed in Hend by (cbn [WriterApp.w_failed]; lia). cbn [WriterApp.w_failed] in Hend. lia. }
      assert (Hn' : 0 <= (n + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
      destruct (IH (tl ok) (WriterApp.mkW 0 (t ++ b)
                  (WriterSpec.newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1))
                  ((n + 1) mod 2 ^ 64) fl
                  (cs ++ [WriterSpec.newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)])) eq_refl Hn' Hend)
        as (I1 & I2 & I3 & I4 & I5).
      cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
        in I1, I2, I3, I4, I5.
      rewrite length_app, Nat2Z.inj_add in I1, I2, I3, I5.
      split; [|split; [|split; [|split]]].
      -- intros i Hi. destruct i as [|i]; [rewrite re_nth_hd; exact Hhd|].
         rewrite re_nth_tl. apply I1. cbn [length] in Hi. lia.
      -- rewrite I2, <- app_assoc. reflexivity.
      -- rewrite I3. cbn [length]. rewrite Zplus_mod_idemp_l. f_equal. lia.
      -- exact I4.
      -- exact I5.
  + unfold WriterApp.put1 in Hend |- *.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in Hend |- *.
    cbn [negb Z.eqb] in Hend |- *. cbv zeta in Hend |- *.
    rewrite (proj2 (Z.leb_le _ _) Hg) in Hend |- *.
    destruct (IH ok (WriterApp.mkW 0 (t ++ b) c n fl cs) eq_refl Hn Hend) as (I1 & I2 & I3 & I4 & I5).
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in I1, I2, I3, I4, I5.
    rewrite length_app, Nat2Z.inj_add in I1, I2, I3, I5.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4 | exact I5].
Qed.

(* A RUN THAT ENDS FAILED: its first failing grow is the injected one or a refusal, at an index the accepting
   run reaches *)
Lemma re_wfail : forall P ok st,
  WriterApp.w_failed st = 0 -> 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) <> 0 ->
  exists i, (i < length (WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st)
                           (WriterSpec.piece_lens P)))%nat /\
    (i < PRH_FnWriter.prhWriter_k ok st P)%nat /\
    ((WriterApp.w_cnt st + Z.of_nat i) mod 2 ^ 64 = WriterApp.w_fail st \/ nth i ok true = false).
Proof.
induction P as [|b P IH]; intros ok [f t c n fl cs] Hf Hn Hend;
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *;
  subst f.
- cbn [PRH_FnWriter.prhWriter_putN WriterApp.w_failed] in Hend. lia.
- unfold PRH_FnWriter.prhWriter_k. unfold WriterSpec.piece_lens. cbn [map]. fold (WriterSpec.piece_lens P).
  cbn [WriterSpec.grow_calls].
  cbn [PRH_FnWriter.prhWriter_putN] in Hend |- *.
  unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in Hend |- *.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_calls] in Hend |- *.
  rewrite Z.eqb_refl in Hend |- *. cbn [andb] in Hend |- *.
  destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  + unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in Hend |- *.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in Hend |- *.
    rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) Hg) in Hend |- *. cbn [andb] in Hend |- *. cbv zeta in Hend |- *.
    destruct (Z.eqb_spec n fl) as [Enf|Enf].
    * exists 0%nat. rewrite re_putN_failed by (cbn [WriterApp.w_failed]; lia).
      cbn [WriterApp.w_calls length]. rewrite length_app. cbn [length].
      split; [lia|]. split; [lia|]. left. rewrite Z.add_0_r, Z.mod_small by lia. exact Enf.
    * destruct (hd true ok) eqn:Hhd.
      -- assert (Hn' : 0 <= (n + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
         set (c1 := WriterSpec.newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) in *.
         destruct (IH (tl ok) (WriterApp.mkW 0 (t ++ b) c1 ((n + 1) mod 2 ^ 64) fl (cs ++ [c1])) eq_refl Hn' Hend)
           as (i & I1 & I2 & I3).
         unfold PRH_FnWriter.prhWriter_k in I2.
         cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
           in I1, I2, I3.
         rewrite length_app, Nat2Z.inj_add in I1.
         destruct (re_putN_calls P (tl ok) (WriterApp.mkW 0 (t ++ b) c1 ((n + 1) mod 2 ^ 64) fl (cs ++ [c1])))
           as [l El].
         cbn [WriterApp.w_calls] in El. rewrite El in I2 |- *. rewrite !length_app in I2 |- *.
         cbn [length] in I2 |- *.
         exists (S i). split; [cbn [length]; lia|]. split; [lia|].
         destruct I3 as [I3|I3]; [left | right].
         ++ rewrite <- I3. rewrite Zplus_mod_idemp_l. f_equal. lia.
         ++ rewrite re_nth_tl. exact I3.
      -- exists 0%nat. rewrite re_putN_failed by (cbn [WriterApp.w_failed]; lia).
         cbn [WriterApp.w_calls length]. rewrite length_app. cbn [length].
         split; [lia|]. split; [lia|]. right. rewrite re_nth_hd. exact Hhd.
  + unfold WriterApp.put1 in Hend |- *.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in Hend |- *.
    cbn [negb Z.eqb] in Hend |- *. cbv zeta in Hend |- *.
    rewrite (proj2 (Z.leb_le _ _) Hg) in Hend |- *.
    destruct (IH ok (WriterApp.mkW 0 (t ++ b) c n fl cs) eq_refl Hn Hend) as (i & I1 & I2 & I3).
    unfold PRH_FnWriter.prhWriter_k in I2.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in I1, I2, I3.
    rewrite length_app, Nat2Z.inj_add in I1.
    exists i. split; [exact I1|]. split; [exact I2 | exact I3].
Qed.

(* a register a segment did not write: its end value is the segment's start value (S10TxString.v:117) *)
Ltac tskeep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.


(* A FRAME BIG ENOUGH TO HOLD A struct pj HAS A WHOLE NUMBER OF SHADOW GRANULES. fs_frame_bytes cid is
   `Z.shiftl 64 cid`, which for a NEGATIVE class is 64 >> |cid| <= 32, so a frame of at least 56 bytes has
   0 <= cid and its size is 64 * 2 ^ cid. Needed where a frame's shadow range (fs_frame_bytes cid / 8 bytes)
   must cover the shadow of a 56-byte object inside that frame. *)
Lemma re_fs_div8 : forall cid, 56 <= fs_frame_bytes cid -> 0 <= cid /\ fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. destruct (Z_lt_le_dec cid 0) as [Hc|Hc].
- exfalso. unfold fs_frame_bytes in H.
  replace cid with (- (- cid)) in H by lia. rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 in H by lia.
  pose proof (Z.pow_le_mono_r 2 1 (- cid) ltac:(lia) ltac:(lia)) as Hp. change (2 ^ 1) with 2 in Hp.
  assert (64 / 2 ^ (- cid) <= 32) by (apply Z.div_le_upper_bound; lia). lia.
- split; [exact Hc|]. rewrite fs_frame_bytes_eq by exact Hc.
  pose proof (Z.pow_nonneg 2 cid ltac:(lia)) as Hpn.
  apply Z.mod_divide; [lia|]. exists (8 * 2 ^ cid). lia.
Qed.
(* the number of grows of a run that ends unfailed is the model's wcalls of the whole document *)
Lemma re_wcalls_of : forall (t : PjTree.jv) (p : bool),
  Z.of_nat (length (WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 0 0))))
     (WriterApp.w_cap (WriterApp.w0 0 0)) (WriterSpec.piece_lens (WriterValue.wdpieces t p))))
  = PjWriteHyp.wcalls t p.
Proof. intros t p. unfold PjWriteHyp.wcalls, WriterApp.w0. cbn [WriterApp.w_text WriterApp.w_cap length]. reflexivity. Qed.

(* THE WRITER'S FINAL CAPACITY IN MODEL TERMS (base d026aa245c5's `capw = last (PresetReqAt.wcaps t p) 0`): the
   capacity a run of grows reaches is the last capacity it asked for, or the start capacity when it asked none.
   Derived here from WriterSpec's two parallel fixpoints, so the cut's new conjunct needs no kit text. *)
Lemma re_last_nonempty : forall (L : list Z) x d1 d2, last (x :: L) d1 = last (x :: L) d2.
Proof. induction L as [|y L IH]; intros x d1 d2; [reflexivity|]. cbn [last]. apply IH. Qed.
Lemma re_last_cons : forall (L : list Z) (a d : Z), last (a :: L) d = last L a.
Proof. intros [|b L] a d; [reflexivity|]. cbn [last]. apply re_last_nonempty. Qed.
Lemma re_grow_cap_last : forall ls x c, WriterSpec.grow_cap x c ls = last (WriterSpec.grow_calls x c ls) c.
Proof.
induction ls as [|l rest IH]; intros x c; [reflexivity|].
cbn [WriterSpec.grow_cap WriterSpec.grow_calls].
destruct (c <? x + l + 1); [rewrite re_last_cons|]; apply IH.
Qed.
(* the model's final capacity of pj_write's text is grow_cap of the whole document from an empty writer *)
Lemma re_wcap_last : forall (t : PjTree.jv) (p : bool),
  WriterSpec.grow_cap (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 0 0))))
    (WriterApp.w_cap (WriterApp.w0 0 0)) (WriterSpec.piece_lens (WriterValue.wdpieces t p))
  = last (PresetReqAt.wcaps t p) 0.
Proof.
intros t p. unfold WriterApp.w0. cbn [WriterApp.w_text WriterApp.w_cap length].
rewrite re_grow_cap_last. reflexivity.
Qed.

(* ---- THE COUNTER, THE CALL COUNT AND THE GRANT of one writer run (image-free). g_count advances once per grow
   call whatever its outcome; a run from an unfailed writer makes at most the accepting run's grows; a run that ends
   unfailed granted every grow it made ---- *)
Lemma re_putN_cnt : forall P ok st, 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok st P) =
    (WriterApp.w_cnt st + Z.of_nat (PRH_FnWriter.prhWriter_k ok st P)) mod 2 ^ 64.
Proof.
induction P as [|b P IH]; intros ok st Hn.
- unfold PRH_FnWriter.prhWriter_k. cbn [PRH_FnWriter.prhWriter_putN]. rewrite Nat.sub_diag, Z.add_0_r, Z.mod_small by lia.
  reflexivity.
- rewrite PRH_Supply.prhWriter_k_cons. cbn [PRH_FnWriter.prhWriter_putN].
  destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G.
  + assert (Hc : WriterApp.w_cnt (PRH_FnWriter.prhWriter_put1 (hd true ok) st b) = (WriterApp.w_cnt st + 1) mod 2 ^ 64).
    { unfold PRH_FnWriter.prhWriter_put1. rewrite G. cbv zeta.
      destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [reflexivity|]. destruct (hd true ok); reflexivity. }
    rewrite IH by (rewrite Hc; apply Z.mod_pos_bound; lia). rewrite Hc, Zplus_mod_idemp_l. f_equal. lia.
  + destruct (PRH_Supply.sup_put1_keep st b G) as (_ & Hc & _).
    rewrite IH by (rewrite Hc; exact Hn). rewrite Hc. reflexivity.
Qed.

Lemma re_k_le : forall P ok st, WriterApp.w_failed st = 0 ->
  (PRH_FnWriter.prhWriter_k ok st P <= length (WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st)))
     (WriterApp.w_cap st) (WriterSpec.piece_lens P)))%nat.
Proof.
induction P as [|b P IH]; intros ok [f t c n fl cs] Hf;
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap] in *; subst f.
- unfold PRH_FnWriter.prhWriter_k. cbn [PRH_FnWriter.prhWriter_putN]. lia.
- rewrite PRH_Supply.prhWriter_k_cons. unfold WriterSpec.piece_lens. cbn [map]. fold (WriterSpec.piece_lens P).
  cbn [WriterSpec.grow_calls].
  unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap]. rewrite Z.eqb_refl. cbn [andb].
  destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  + cbn [length]. apply le_n_S.
    unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) Hg). cbn [andb]. cbv zeta.
    destruct (n =? fl); [|destruct (hd true ok)].
    * unfold PRH_FnWriter.prhWriter_k. rewrite re_putN_failed by (cbn [WriterApp.w_failed]; lia). lia.
    * etransitivity; [apply IH; reflexivity|].
      cbn [WriterApp.w_text WriterApp.w_cap]. rewrite length_app, Nat2Z.inj_add. lia.
    * unfold PRH_FnWriter.prhWriter_k. rewrite re_putN_failed by (cbn [WriterApp.w_failed]; lia). lia.
  + unfold WriterApp.put1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    cbn [negb Z.eqb]. cbv zeta. rewrite (proj2 (Z.leb_le _ _) Hg).
    etransitivity; [apply IH; reflexivity|].
    cbn [WriterApp.w_text WriterApp.w_cap]. rewrite length_app, Nat2Z.inj_add. lia.
Qed.

(* the two outcomes of pj_write's run from its empty writer w0 cnt fail *)
Lemma re_w0_succ : forall P ok cnt fail, 0 <= cnt < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) = 0 ->
  PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P =
    length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens P)) /\
  (forall i, (i < length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens P)))%nat -> nth i ok true = true) /\
  WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) =
    (cnt + Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens P)))) mod 2 ^ 64 /\
  WriterApp.w_fail (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) = fail /\
  WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) =
    WriterSpec.grow_cap 0 0 (WriterSpec.piece_lens P).
Proof.
intros P ok cnt fail Hn Hs.
destruct (re_wsucc P ok (WriterApp.w0 cnt fail) eq_refl Hn Hs) as (I1 & I2 & I3 & I4 & I5).
change (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 cnt fail)))) with 0 in I1, I2, I3, I5.
change (WriterApp.w_cap (WriterApp.w0 cnt fail)) with 0 in I1, I2, I3, I5.
change (WriterApp.w_cnt (WriterApp.w0 cnt fail)) with cnt in I3.
change (WriterApp.w_fail (WriterApp.w0 cnt fail)) with fail in I4.
change (WriterApp.w_calls (WriterApp.w0 cnt fail)) with (@nil Z) in I2. cbn [app] in I2.
split; [|split; [exact I1 | split; [exact I3 | split; [exact I4 | exact I5]]]].
unfold PRH_FnWriter.prhWriter_k. rewrite I2.
change (length (WriterApp.w_calls (WriterApp.w0 cnt fail))) with 0%nat. lia.
Qed.

Lemma re_w0_fail : forall P ok cnt fail, 0 <= cnt < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) <> 0 ->
  exists i, (i < length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens P)))%nat /\
    (i < PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P)%nat /\
    ((cnt + Z.of_nat i) mod 2 ^ 64 = fail \/ nth i ok true = false).
Proof. intros P ok cnt fail Hn Hf. exact (re_wfail P ok (WriterApp.w0 cnt fail) eq_refl Hn Hf). Qed.

Lemma re_w0_k_le : forall P ok cnt fail,
  (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P <=
     length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens P)))%nat.
Proof. intros P ok cnt fail. exact (re_k_le P ok (WriterApp.w0 cnt fail) eq_refl). Qed.

(* ---- the number of grows is at most the text's length plus one (each grow serves a strictly larger need) ---- *)
Lemma re_dbl_need : forall c need, 0 <= c -> 0 < need <= 2 ^ 62 -> need <= WriterSpec.newcap c need.
Proof.
intros c need Hc Hn. unfold WriterSpec.newcap.
set (c0 := if c =? 0 then 4096 else c).
assert (H0 : 1 <= c0) by (unfold c0; destruct (Z.eqb_spec c 0); lia).
assert (Hp : need <= c0 * 2 ^ Z.of_nat 64) by (change (2 ^ Z.of_nat 64) with (2 ^ 64); lia).
destruct (WriterSpecFacts.dbl_spec 64 c0 need ltac:(lia) Hp) as (j & _ & _ & Hge & _). exact Hge.
Qed.

Lemma re_gc_len : forall ls x c, 0 <= x -> 0 <= c -> Forall (fun l => 0 <= l) ls ->
  x + fold_right Z.add 0 ls + 1 <= 2 ^ 62 ->
  Z.of_nat (length (WriterSpec.grow_calls x c ls)) <= Z.max 0 (x + fold_right Z.add 0 ls + 1 - c).
Proof.
induction ls as [|l ls IH]; intros x c Hx Hc HF Hs; cbn [WriterSpec.grow_calls fold_right length] in *; [lia|].
apply Forall_cons_iff in HF as [Hl HF].
assert (Hsum : 0 <= fold_right Z.add 0 ls)
  by (clear -HF; induction HF as [|a l' Ha _ IH']; cbn [fold_right]; lia).
destruct (Z.ltb_spec c (x + l + 1)) as [Hg|Hg].
- cbn [length]. pose proof (re_dbl_need c (x + l + 1) Hc ltac:(lia)) as Hd.
  pose proof (IH (x + l) (WriterSpec.newcap c (x + l + 1)) ltac:(lia) ltac:(lia) HF ltac:(lia)) as I. lia.
- pose proof (IH (x + l) c ltac:(lia) Hc HF ltac:(lia)) as I. lia.
Qed.

Lemma re_sum_lens : forall P, fold_right Z.add 0 (WriterSpec.piece_lens P) = Z.of_nat (length (concat P)).
Proof.
induction P as [|b P IH]; [reflexivity|]. unfold WriterSpec.piece_lens in *. cbn [map fold_right concat].
rewrite length_app, Nat2Z.inj_add, IH. reflexivity.
Qed.

Lemma re_lens_nn : forall P, Forall (fun l => 0 <= l) (WriterSpec.piece_lens P).
Proof. intros P. unfold WriterSpec.piece_lens. rewrite Forall_map. apply Forall_forall. intros b _. lia. Qed.

Lemma re_wcalls_le : forall t p, PjWriteHyp.wlen t p + 1 <= 2 ^ 28 ->
  Z.of_nat (PresetReqAt.wcalls t p) <= PjWriteHyp.wlen t p + 1.
Proof.
intros t p H. unfold PresetReqAt.wcalls, PresetReqAt.wcaps, PjWriteHyp.wlen, WriterValue.wdoc in *.
pose proof (re_gc_len (WriterSpec.piece_lens (WriterValue.wdpieces t p)) 0 0 ltac:(lia) ltac:(lia) (re_lens_nn _))
  as G.
rewrite re_sum_lens in G. specialize (G ltac:(lia)). lia.
Qed.

(* WITH g_fail_at = SIZE_MAX AND g_count < 2 ^ 62 NO GROW OF pj_write IS THE ONE SET TO FAIL *)
Lemma re_cnt_ne : forall t p cnt, 0 <= cnt < 2 ^ 62 -> PjWriteHyp.wlen t p + 1 <= 2 ^ 28 ->
  forall j, (j < PresetReqAt.wcalls t p)%nat -> (cnt + Z.of_nat j) mod 2 ^ 64 <> SIZE_MAXZ.
Proof.
intros t p cnt Hc Hw j Hj. pose proof (re_wcalls_le t p Hw) as Hb. unfold SIZE_MAXZ.
rewrite Z.mod_small by lia. lia.
Qed.

(* the final capacity, in the form LIVE_pj_write counts *)
Lemma re_wcap_newcap : forall t p, PjWriteHyp.wlen t p + 1 <= 2 ^ 28 ->
  last (PresetReqAt.wcaps t p) 0 = WriterSpec.newcap 0 (PjWriteHyp.wlen t p + 1).
Proof.
intros t p H. rewrite PresetFlush.wcaps_last by lia. unfold PresetFlush.pow4k, WriterSpec.newcap.
rewrite PresetFlush.pow4k_dbl. reflexivity.
Qed.

(* ---- the bytes of the live blocks, as the sum the cut's blocks_bytes bound counts ---- *)
Lemma re_bsum_perm : forall (l l' : list (Z * Z)), Permutation l l' ->
  fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l'.
Proof. intros l l' P. induction P; cbn [fold_right]; lia. Qed.

(* a stored 8-byte value read back as a word (YCem.v:101 rdword_of_val_mem, copied body for body: YCem is not
   Required here because it pulls YCeh, red on #102) *)
Lemma re_rdword_of_vm : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B0 : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B0 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B0 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B0 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B0 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B0 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B0 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B0 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B0 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ======================================================================================================== *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
(* the image A' instance of the kit's PrhImg class: every kit name below (prh_most, prh_own, prh_ledger, ck_tree_ok,
   fpre, ...) takes PI := prh_img_A, the statement's own instance *)
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).

(* ---- image A': the walked offsets (DERIVED) ---- *)
Definition RE_PC : Z := 4 * Z.of_nat (A_prog_slot AS_round_trip_text).
Definition RE_A2_OFF : Z := 96.   (* A' 0x849cc: lw a2, 0(a2), the use-after-return flag *)
Definition RE_A3_OFF : Z := 100.  (* A' 0x849d0: ld s9, 0(a1), the shadow base *)
Definition RE_B_OFF : Z := 120.   (* A' 0x849e4: frame_alloc_1's return site, `mv s2, a0` *)

Lemma RE_PC_val : BASE + RE_PC = SIGMA AS_round_trip_text.
Proof. vm_compute. reflexivity. Qed.
Lemma RE_PJW_val : BASE + (RE_PC + RT_PJW) = SIGMA AS_round_trip_text + RT_PJW.
Proof. rewrite <- RE_PC_val. lia. Qed.
(* the image's object atoms lie below 2 ^ 31 *)
Lemma pa_hi_ok_A : @pa_hi _ A_prog_listing PA <= 2 ^ 31.
Proof. change (@pa_hi _ _ PA) with IMG_TOP. unfold IMG_TOP. lia. Qed.
(* round_trip_text's allowance covers frame_alloc_1's 4096 BELOW the realigned sp, which `andi sp, sp, -0x20`
   puts at most 176 under the entry sp (RT_R's range), and pj_write's below that *)
Lemma HSTK_A : 4096 + 176 <= STKR.
Proof. vm_compute. discriminate. Qed.
Lemma HSTKW_A : 0 <= @STK_pj_write prh_img_A DOC_D /\ @STK_pj_write prh_img_A DOC_D + 192 <= STKR.
Proof. split; vm_compute; discriminate. Qed.
Lemma pst_img_A : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_A. Qed.
Lemma pst_ro_A : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_A. Qed.

(* the realigned frame base `(sp0 - 160) & -32` = Rtt102Cut.RT_R *)
Lemma re_R_eq : forall sp0, RT_R sp0 = (sp0 - 160) / 32 * 32.
Proof.
intros sp0. unfold RT_R, RT_FRAME.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)). lia.
Qed.
Lemma re_R_range : forall sp0, sp0 mod 16 = 0 -> 176 <= sp0 ->
  sp0 - 176 <= RT_R sp0 <= sp0 - 160 /\ RT_R sp0 mod 32 = 0 /\ 0 <= RT_R sp0.
Proof.
intros sp0 Hal16 H. rewrite re_R_eq.
pose proof (Z.mul_div_le (sp0 - 160) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)).
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)). pose proof (Z.div_pos (sp0 - 160) 32 ltac:(lia) ltac:(lia)).
assert ((sp0 - 160) mod 32 = 0 \/ (sp0 - 160) mod 32 = 16) as [Hm|Hm]
  by (rewrite Z.mod_divide in Hal16 by lia; destruct Hal16 as [q ->]; lia).
all: split; [lia | split; [apply Z.mod_mul; lia | lia]].
Qed.
(* the engine's word for `andi sp, sp, -32` after `addi sp, sp, -160` *)
Lemma re_R_word : forall (regs : bvmap 5 word), 160 <= spZ regs ->
  alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (getr regs 2) + -160)) (Z_to_bv 64 (-32)) = w64 (RT_R (spZ regs)).
Proof.
intros regs H160. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr.
change (bv_modulus 64) with (2 ^ 64) in Hr. change (bv_unsigned (getr regs 2)) with (spZ regs) in *.
apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (spZ regs + -160)) by lia. change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32).
rewrite ts_land_m32 by lia. rewrite re_R_eq.
pose proof (Z.mul_div_le (spZ regs - 160) 32 ltac:(lia)).
pose proof (Z.div_pos (spZ regs - 160) 32 ltac:(lia) ltac:(lia)).
replace (spZ regs + -160) with (spZ regs - 160) by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma re_R_add0 : forall (regs : bvmap 5 word), 160 <= spZ regs ->
  alu64 ALU_ADD (alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (getr regs 2) + -160)) (Z_to_bv 64 (-32))) (Z_to_bv 64 0)
  = w64 (RT_R (spZ regs)).
Proof. intros regs H. rewrite re_R_word by exact H. apply ts_add0_word. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the world relation of every journal of this stretch (Rtt102Cut.v's RZW) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* ---- Section hypotheses. Each names its owner; none closes a goal of this stretch ---- *)
(* the allocator laws at the cf instance's head (engine fold, YCbqG.v: 25 fields at the batch kit's cut) - owner: the
   engine. AT THE A' BINDER (WalkRtt102's composition, B := AD2l.TfibB, ARx := YG0ncf.ARcf rsegs TfibB, cp :=
   CfParams_preset): palib_laws_A (PALibA.v) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the unit's image binding of B: PALib's fields (owned by the kit / the core's PALib), as S10TxString.v:166 takes it.
   AT THE A' BINDER: PAL := palib_A (the PALib prover's PALibA 88c72c8175cf, int102 83ac1a932a8d: every PALib field by
   vm_compute on AF0l dfca6bb1a8d7, pins102 rc=0).
   This stretch stays generic in B (WalkRtt102's ruling): PALibA.v's palib_A is on the batch kit's cut, and its discharge is
   the binder's, not this file's. *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* the listing's frame_alloc_1 is the code record's (owned by the kit / the core's PALib, as S10TxString.v:168 takes the
   class-0 twin). NOT A PALib FIELD. Discharge at the A' binder: `vm_compute; reflexivity` at B := AD2l.TfibB,
   PI_prog_A - AF0l dfca6bb1a8d7's pc_stack_malloc cid 1 and the A' twin bff8519bbe3ea0e4's .symtab
   __asan_stack_malloc_1 are both 0x3dcbc (WalkRtt102's measurement) *)
Hypothesis pal_stack_malloc1 : SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1.
(* the use-after-return flag cell lies in the image (owned by the kit / the core's PALib; S10TxString.v:170). NOT A PALib
   FIELD. Discharge at the A' binder: `split; apply Z.leb_le; vm_compute; reflexivity` at B := AD2l.TfibB (the
   cell's address is a constant of TfibB's record, IMG_LO / IMG_TOP are Img0's) *)
Hypothesis pal_uar_img : IMG_LO <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP.
(* alloc.c's statics are not the runtime's own statics and not errno, so a runtime call's image clause keeps them
   (owned by the kit, the image binding of B; S10TxString.v:220). NOT A PALib FIELD. Discharge at the A' binder: S1ImgA.v's
   pst_allb_sound applied to the boolean check `pst_allb (fun a => negb (existsb (fun r => (fst r <=? a) &&
   (a <? fst r + snd r)) (as_owned_static AD2l.TfibB)) && negb ((as_errno AD2l.TfibB <=? a) &&
   (a <? as_errno AD2l.TfibB + 4))) (@prh_pst prh_img_A) = true`, closed by `vm_compute; reflexivity` - the
   pin-generic pattern of S1ImgA's pst_img_b_A / pst_ro_b_A over PRH_Img's cells and the #102 segments *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* THE HEAD IS AT LEAST ONE SHADOW GRANULE WIDE, in the kit's one spelling (owned by the kit, PRH_Base.v:188-195, which
   says a walk takes it as a Section hypothesis `HW : prh_head_wide`; the preset instantiation discharges it
   by the cf instance owner's preset_head_wide, lib/A/CfParamsPreset.v:95). Needed here because a harness block's head
   WORD - the 8 bytes prh_hblock reads at a - cf_head - lies inside the block only when 8 <= kk + cf_head,
   and YGcfNames.v:91 allows cf_head = 0 at another harness *)
Hypothesis HW : prh_head_wide.
(* THE INSTANCE'S HEAD IS THE MODEL'S HEAD (owner: the preset instance CfParams_preset; WalkRtt102's ruling, the
   same spelling RttX and RttCmp carry, so the stretches unify at composition). The callee's run premise is
   cf_head-sized (PRH_FnWriter.v:203, prhWriter_pjw_evs) and rtt_pre's run is HEAD-sized (Rtt102Cut.v:186, the
   model's w_evs); PRH_Supply.prhWriter_pjw_evs_w_evs bridges them under exactly this. Closed at the real instance
   by `hhead_preset` at the end of this file. *)
Hypothesis HHEAD : cf_head = PresetReqAt.HEAD.
(* ---- frame class 1: exactly the hypotheses YGcallMxmn.v's aj_stack_malloc_at_xmR takes, as S10TxString.v:173-186
   takes them for class 0 (owner: the frame-class lane that discharges FCiface contracts at the instance) ---- *)
Hypothesis ASM1 : astack_malloc_realizes_xm SEGS B ARx RT_CID.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Variable CTX0 : list (list Z).

(* ---- THE CALLEE TEXT: the kit's pj_write text at nesting DOC_D (PRH_FnWriter.v tpj_write_specX at the batch kit's cut, blob
   d89d3c67b78c; owned by the kit), at every float state, as every callee text of the walk is taken (Rtt102CKA.v TSAME /
   TPJF, Rtt102CmpA.v TFF). It is the text the pre-cut file took as its explicit premise re_K0_REFUTE_PJW (DeadK1
   c753d960f56, blob 0bd195c1199a), keyed: rp_sm and its equation and DW gone (the comparison is in the file
   header). Its post's K0-DEAD-PJWRITE conjunct `prh_granted ok cnt fail (prhWriter_k ..)` refutes the failed arm
   (q = 0) at the call through the writer-model step re_refute_pj_write_failed below (DeadK1's
   PRH_Refute.prh_refute_pj_write_failed, blob 90e5bae6f73e, rebuilt here); its new entry premise
   `prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (prhWriter_pjw_evs [] ..))` is rtt_pre's
   prh_cons_from over ck_rtt_evs split by prh_cons_from_app_iff (re_at_B, HCONS'). ---- *)
Hypothesis TPJW : forall fx' : YK11.FPState,
  PRH_FnWriter.tpj_write_specX (fx := fx') (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK CTX0
    DOC_D.

(* the image facts a glue lemma leaves after eapply / edestruct *)
Ltac re_ctx := first [exact HSTK_A | exact HSTKW_A | exact pa_hi_ok_A | exact LAWS | exact PAL | exact pal_uar_img
  | exact pst_img_A | exact pst_ro_A | exact pal_pst_static | idtac].

(* ======================================================================================================== *)
(* ---- the three prologue segments. round_trip_text's prologue is the same instruction sequence as
   tx_string's, in the same registers, so the segment shapes are S10TxStrGlue.v's A1 / A2 / A3 ---- *)

(* E1: the entry to the flag's load. Regions: the 160-byte frame below sp0 (written), the two GOT words (read) *)
Definition re_E1_regions : smem :=
  [ stack_region 160; got_regionP;
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))] ].
Definition ss_E1 : sstate :=
  mkSS RE_PC sr_atoms re_E1_regions None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Lemma re_E1_entry : forall ly S Hp (W : world SEGS) regs mem md ch,
  afn_pre_x SEGS B ARx STKR ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (TE regs regs [w64 (as_uar_cell B)]) ss_E1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RE_PC)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regs [w64 (as_uar_cell B)]) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK_A as HSTK.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow (PI := PA) B PAL), (pal_cell (PI := PA) B PAL) in Kgot.
rewrite (pal_got_uar (PI := PA) B PAL) in Kgotu.
set (E := TE regs regs [w64 (as_uar_cell B)]).
assert (E2 : ew E 2 = getr regs 2) by (apply te_entry; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E64 : ew E 64 = w64 (as_uar_cell B)) by exact (te_more_lt regs regs [w64 (as_uar_cell B)] 0 ltac:(lia)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 1)) as R1.
pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
pose proof (ts_rdword_range _ _ _ _ Kgotu) as Ruar.
pose proof (@pa_obj_img _ _ PA 0 ltac:(lia)) as I0. pose proof (@pa_obj_img _ _ PA 1 ltac:(lia)) as I1.
pose proof pa_hi_ok_A as Hhi.
split.
- apply ts_st_ok.
  all: try change (TE regs regs [w64 (as_uar_cell B)]) with E.
  + unfold E, TE. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold re_E1_regions, stack_region, got_regionP. repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ 2 (spZ regs)); [exact Usp | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * apply (ts_rok E _ (A_OBJ 0) (VAL (A_OBJ 0)));
        [rewrite Eo0; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * apply (ts_rok E _ (A_OBJ 1) (VAL (A_OBJ 1)));
        [rewrite Eo1; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff 64 0) (as_uar_cell B));
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgotu).
  + apply pairwise_disjoint_of_extents. unfold re_E1_regions, stack_region, got_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
    rewrite Usp, Eo0, Eo1, !unsigned_lit_small by lia.
    pose proof (pal_got_uar_disj (PI := PA) B PAL) as (D01 & _).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* E2: the use-after-return flag's load (one instruction; the flag cell is the only region) *)
Definition ss_E2 : sstate :=
  mkSS (RE_PC + RE_A2_OFF) cur_atoms
    [YP09.mkRegion (Some (xr 12)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]] None (mkFacts [] [] []).
Lemma re_E2_entry : forall (regs regsc : bvmap 5 word) memc (Wc : world SEGS),
  getr regsc 12 = w64 (as_uar_cell B) -> rd32 (aview SEGS (w_H Wc) memc) (as_uar_cell B) 1 ->
  st_ok_pi SEGS VAL (TE regs regsc []) ss_E2
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (RE_PC + RE_A2_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc []) (mrestrict (w_H Wc) memc).
Proof.
intros regs regsc memc Wc R12 Hu. pose proof pal_uar_img as Huar. unfold IMG_LO, IMG_TOP in Huar.
set (E := TE regs regsc []).
assert (X12 : bv_unsigned (ew E (xr 12)) = as_uar_cell B).
{ unfold E, xr. rewrite (te_cur regs regsc [] 12%bv 12) by reflexivity. rewrite R12.
  apply unsigned_lit_small. lia. }
split.
- apply ts_st_ok.
  all: try change (TE regs regsc []) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 12) (as_uar_cell B)); [exact X12 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (ts_val_mem_rd32 _ _ _ _ Hu).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

(* E3: the shadow base's load, `mv s4, a0`, the flag test (not taken) and `li a0, 0x80`, to the frame call *)
Definition ss_E3 : sstate :=
  mkSS (RE_PC + RE_A3_OFF) cur_atoms
    [YP09.mkRegion (Some (xr 11)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))]] None
    (mkFacts [(xr 12, mkAF 1 1 0)] [] []).
Lemma re_E3_entry : forall (regs regsc : bvmap 5 word) memc (Wc : world SEGS),
  getr regsc 11 = w64 (VAL (A_OBJ 12)) -> getr regsc 12 = w64 1 ->
  rdword (aview SEGS (w_H Wc) memc) (VAL (A_OBJ 12)) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs regsc [w64 SHADOW_OFF]) ss_E3
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (RE_PC + RE_A3_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc [w64 SHADOW_OFF]) (mrestrict (w_H Wc) memc).
Proof.
intros regs regsc memc Wc R11 R12 Hc.
pose proof (@pa_obj_img _ _ PA 12 ltac:(lia)) as I12.
pose proof pa_hi_ok_A as Hhi. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12v.
set (E := TE regs regsc [w64 SHADOW_OFF]).
assert (X11 : bv_unsigned (ew E (xr 11)) = VAL (A_OBJ 12)).
{ unfold E, xr. rewrite (te_cur regs regsc _ 11%bv 11) by reflexivity. rewrite R11.
  apply unsigned_lit_small. lia. }
assert (X12 : bv_unsigned (ew E (xr 12)) = 1).
{ unfold E, xr. rewrite (te_cur regs regsc _ 12%bv 12) by reflexivity. rewrite R12. reflexivity. }
assert (E64 : ew E 64 = w64 SHADOW_OFF) by exact (te_more_lt regs regsc [w64 SHADOW_OFF] 0 ltac:(lia)).
split.
- apply ts_st_ok.
  all: try change (TE regs regsc [w64 SHADOW_OFF]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 11) (VAL (A_OBJ 12))); [exact X11 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 8 (SOff 64 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hc).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X12. cbn. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ======================================================================================================== *)
(* ---- THE CUT'S CARRIED STATE, re-spelled here with THE SAME BODIES as Rtt102Cut.v's rtt_fx / rtt_saved /
   rtt_frame / rtt_J / rtt_wild / rtt_cregs / rtt_room / rtt_pos / rtt_carry / rtt_led / rtt_wout / rtt_copy_kept /
   rtt_at_pjw at 80a1d52c32c7 (that file is NOT edited; these are copies, so each is convertible with the cut's and
   `exact` bridges the two in one step). They are re-spelled because this file's lemmas must mention them in their
   statements. re_AJ alone is NOT a copy: it is this stretch's own journal (below). ---- *)
#[local] Notation RIN := (@rtt_in rc A_prog_listing PA).

Definition re_fx (fxc : YK11.FPState) : Prop := frm_zero (@YK11.fp_csr fxc) /\ fregs_kept_x fx fxc.

Definition re_saved (D : RIN) (W : world SEGS) (mem : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
    val_mem SEGS (mrestrict (w_H W) mem) (ri_sp D - 8 * (Z.of_nat j + 1)) 8
      (bv_unsigned (getr (ri_regs D) (nth j RTT_SAVED 0%bv))).

Definition re_frame (D : RIN) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (pos : Z)
  : Prop :=
  frames S = (RT_CID, pos) :: frames (ri_S D) /\ ~ In (RT_CID, pos) (frames (ri_S D)) /\
  rdword (aview SEGS (w_H W) mem) (frame_addr ly RT_CID pos + RT_FLAGP) = Some (flag_addr ly RT_CID pos) /\
  (forall a, frame_addr ly RT_CID pos <= a < frame_addr ly RT_CID pos + fs_frame_bytes RT_CID ->
     apresent (w_H W) mem a).

(* the cut's journal: from the entry WITH THE ENTRY'S DEPOT MOVED TO THE CUT STATE'S (Rtt102Cut.rtt_J) *)
Definition re_J (D : RIN) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (md : Model) (k : Z) (pos : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B PST ARx RZW STKR (ri_sp D) (ri_FP D) (ri_ly D)
    (set_depot (st_depot S) (ri_S D)) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp W mem md k.
(* NOT a cut re-spelling: the journal FROM THE ENTRY ITSELF at the empty budget and at RZW, the form this stretch's two
   call rules compose (YGcallMxmn.aj_stack_malloc_at_xmR, YCbqGcall.aj_call_xF_spR, both at RZW; neither callee stores
   a wild trace). At RT_PJW it gives re_J (Rtt102Cut.rtt_J_of_AJ) and both wild facts (Rtt102Cut.rtt_wild_of_AJ at
   WS = []) *)
Definition re_AJ (D : RIN) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (md : Model) (k : Z) (pos : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B PST ARx RZW STKR (ri_sp D) (ri_FP D) (ri_ly D) (ri_S D) (ri_Hp D)
    (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp W mem md k.
(* the wild traces stored since the entry, within the entry's plus at most n fresh ones (Rtt102Cut.rtt_wild) *)
Definition re_wild (D : RIN) (S : astate) (n : nat) : Prop :=
  exists WS, incl (wild_part (as_universe B) (st_depot S)) (wild_part (as_universe B) (st_depot (ri_S D)) ++ WS) /\
    YCbqGwild.wbudget [] n WS.

Definition re_cregs (D : RIN) (ly : alayout) (regs : bvmap 5 word) (pos : Z) : Prop :=
  let F := frame_addr ly RT_CID pos in
  getr regs 2 = w64 (RT_R (ri_sp D)) /\ getr regs 8 = w64 (ri_sp D) /\ getr regs 9 = w64 (RT_R (ri_sp D)) /\
  getr regs 18 = w64 F /\ getr regs 19 = w64 (ri_copy D) /\ getr regs 20 = w64 (ri_doc D) /\
  getr regs 25 = w64 (shadow_addr F) /\ getr regs 26 = w64 F /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

(* the re-stated cut (base 4d768df1473): the room is room_live_cf ONLY, and the model-run POSITION is exact
   and carried separately, on the granted path only *)
Definition re_room (D : RIN) (S : astate) : Prop := room_live_cf S.
Definition re_pos (D : RIN) (S : astate) (k : nat) : Prop :=
  exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + k)%nat (ri_H0 D) hist S.

Definition re_carry (D : RIN) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  (* the entry float state: INSIDE this Section re_fx's body names the Section variable fx directly (re_fx is
     not yet generalised, so no class resolution happens here and fxc cannot be picked); the elaborated forms
     after the Section closes are printed at the end of the file (the text owner's 17:1xZ FPState rule) *)
  re_fx fxc /\ re_J D ly S Hp W mem md k pos /\ re_frame D ly S W mem pos /\ re_saved D W mem /\
  re_cregs D ly regs pos /\ (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  re_room D S /\
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin (ri_Lam D)) (ri_doc D) (ri_t D) (ri_D D) /\
  PRH_FnWriter.prhWriter_tree_vis W mem (ri_D D) /\
  re_wild D S (prh_wk F_round_trip_text).

Definition re_copy_kept (D : RIN) (W : world SEGS) (mem : word -> option byte) : Prop :=
  ri_copy D <> 0 -> forall a, ri_copy D <= a < ri_copy D + 56 ->
    aview SEGS (w_H W) mem a = aview SEGS (w_H (ri_W D)) (ri_mem D) a.

(* cut 6e2b5d75a77: the refusal arm is GONE from the cut - the writer outcome is the granted one only *)
Definition re_wout (D : RIN) (q : Z) (Lamw : list (Z * Z)) (cntw ranw : Z) (wab : list (Z * Z)) : Prop :=
  let t := ri_t D in let p := ri_p D in
  q <> 0 /\ cntw = ri_cnt D + PjWriteHyp.wcalls t p /\ ranw = ri_ran D /\
  exists capw, Lamw = (q, capw) :: ri_Lam D /\
    ~ In (q - cf_head, capw + cf_head) (ablocks B (ri_ly D) (ri_S D)) /\
    wab = (q - cf_head, capw + cf_head) :: ablocks B (ri_ly D) (ri_S D) /\
    Z.of_nat (length (ri_tb D)) < capw /\ capw + cf_head <= PRH_FnWriter.LIVE_pj_write t p /\
    capw = last (PresetReqAt.wcaps t p) 0.

(* base f9eda666dd9 (the ledger-field sweep): g_most and g_own_ran_out are LEDGER FIELDS, so the ledger at a cut
   names the entry's most and the cut's own *)
Definition re_led (D : RIN) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (Lamc : list (Z * Z)) (peakc cntc ranc ownc : Z) : Prop :=
  prh_ledger B ly S Hp W mem Lamc peakc cntc SIZE_MAXZ ranc (ri_most D) ownc /\ ri_peak D <= peakc.

Definition re_at_pjw (D : RIN) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  re_carry D fxc ly S Hp W regs mem md k pos /\ getr regs 21 = w64 (ri_pretty D) /\ re_copy_kept D W mem /\
  exists q Lamw peakw cntw ranw wab,
    getr regs 10 = w64 q /\ re_led D ly S Hp W mem Lamw peakw cntw ranw 0 /\ re_wout D q Lamw cntw ranw wab /\
    Permutation (ablocks B ly S) wab /\
    bytes_at W mem q (ri_tb D ++ [0]) /\
    blocks_bytes S <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) /\
    re_pos D S (RT_K_W D) /\ re_wild D S 0.

(* E's journal from the entry, at RT_PJW: the cut's journal and the wild traces (none fresh) *)
Lemma re_J_of_AJ : forall D ly S Hp W mem md k pos, re_AJ D ly S Hp W mem md k pos -> re_J D ly S Hp W mem md k pos.
Proof.
intros D ly S Hp W mem md k pos HJ. exact (rtt_J_of_AJ B ARx SK D [] ly S Hp W mem md k pos HJ).
Qed.
Lemma re_wild_of_AJ : forall D n ly S Hp W mem md k pos, re_AJ D ly S Hp W mem md k pos -> re_wild D S n.
Proof.
intros D n ly S Hp W mem md k pos HJ.
(* the entry head set occurs in no journal conjunct, so it is passed: unification cannot find it *)
refine (rtt_wild_of_AJ B ARx SK D n STKR (ri_sp D) (ri_FP D) (ri_ly D) (ri_Hp D) _ _ _ _ _ _ _ _ _ _ _ [] HJ _).
unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia.
Qed.

(* ---- THE SIDE FACTS this stretch carries from the entry to the pj_write call: everything the callee's text
   asks about the ledger, the tree and the room, at the walk's current state and memory.
   THE LAYOUT, THE WORLD AND THE HEAD SET ARE THE ENTRY'S THROUGHOUT THIS STRETCH: a run of the function's own
   code changes neither (YC1fPx's runners keep lyc / Sc / Wc / Hpc), and the one call it makes before the cut,
   frame_alloc_1, keeps lyc, Hpc and W too (YGcallMxmn.v aj_stack_malloc_at_xmR's post: `W2 = W` and the journal
   at the same lyc / Hpc). So only S (once, to set_fs with one more frame) and mem move, and re_side needs
   neither a layout nor a world nor a head-set argument. ---- *)
Definition re_side (D : RIN) (S : astate) (mem : word -> option byte) : Prop :=
  (* g_most and g_own_ran_out are LEDGER FIELDS on base f9eda666dd9: the entry's most and own = 0 ride inside *)
  prh_ledger B (ri_ly D) S (ri_Hp D) (ri_W D) mem (ri_Lam D) (ri_peak D) (ri_cnt D) SIZE_MAXZ (ri_ran D)
    (ri_most D) 0 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H (ri_W D)) mem) /\
  re_room D S /\
  (* the model-run position at the entry index: pj_write's text takes `iface_room_pos .. rp_i .. S` at its
     call state, so the stretch carries it from rtt_pre across its own runs and frame_alloc_1's set_fs *)
  re_pos D S 0 /\
  (* the tree's home stays named in the ENTRY state's frames: a frame this stretch adds is never its home *)
  ck_tree_ok (ri_ly D) (ri_S D) (ri_Lam D) (ri_W D) mem (ri_doc D) (ri_t D) (ri_D D) /\
  re_copy_kept D (ri_W D) mem /\
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem).

(* WHERE COPY LIVES, from the text's ck_out_ok: in a fake frame live at the entry. Carried beside re_side
   because re_copy_kept alone does not say it, and the frame clause of every keep below needs it. *)
Definition re_copy_home (D : RIN) : Prop :=
  ri_copy D <> 0 -> exists cid pos, In (cid, pos) (frames (ri_S D)) /\
    frame_addr (ri_ly D) cid pos <= ri_copy D /\
    ri_copy D + 56 <= frame_addr (ri_ly D) cid pos + fs_frame_bytes cid.

(* the addresses this stretch writes before the pj_write call: its own 160-byte frame below the entry sp, the
   fake frame frame_alloc_1 gave it and that frame's 16 shadow bytes. Before the call only the first disjunct
   is reached (re_wr_stk); the frame disjuncts need the pos the call returns *)
Definition re_wr_stk (D : RIN) (a : Z) : Prop := ri_sp D - STKR <= a < ri_sp D.
Definition re_wr (D : RIN) (pos : Z) (a : Z) : Prop :=
  let F := frame_addr (ri_ly D) RT_CID pos in
  re_wr_stk D a \/ (F <= a < F + fs_frame_bytes RT_CID) \/
  (shadow_addr F <= a < shadow_addr F + fs_frame_bytes RT_CID / 8).

(* ---- the three bands this stretch separates: the image (below kLowMemEnd), the client's blocks and fake
   frames with their shadow (below the allocator ceiling), and the function's own stack window (at or above
   the ceiling, by astk_ok). Everything the walk must KEEP lies in the first two; everything it WRITES before
   the frame call lies in the third ---- *)
Lemma re_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

Lemma re_stk_above : forall ly (sp0 a : Z), astk_ok STKR ly sp0 -> a < YM05.alloc_ceiling -> a < sp0 - STKR.
Proof.
intros ly sp0 a (Hal16 & HSTK0 & Hcl & Hlo & Hhi & H47 & Hbot & Htop & Htop2) Ha. lia.
Qed.

(* a live block, its tail granule and its shadow all end below the ceiling *)
Lemma re_blk_ceil : forall ly S Hp (W : world SEGS) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= YM05.alloc_ceiling /\
  (p + req_size n + 7) / 8 * 8 <= YM05.alloc_ceiling /\
  shadow_addr p + (req_size n + 7) / 8 < YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (H16 & H4096 & Hce & Happ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_val rc) as (Hcv & Hcm).
(* no sign of n is needed below: req_size n <= Z.max 1 n and the ceiling bound carries either way *)
assert (Hgr : (p + req_size n + 7) / 8 * 8 <= YM05.alloc_ceiling).
{ pose proof (Z.div_mod (p + req_size n + 7) 8 ltac:(lia)) as Dg.
  pose proof (Z.mod_pos_bound (p + req_size n + 7) 8 ltac:(lia)) as Mg.
  pose proof (Z.div_mod YM05.alloc_ceiling 4096 ltac:(lia)) as Dc. lia. }
split; [exact H4096|]. split; [exact Hce|]. split; [exact Hgr|].
unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.div_mod (req_size n + 7) 8 ltac:(lia)) as Dr.
pose proof (Z.mod_pos_bound (req_size n + 7) 8 ltac:(lia)) as Mr. lia.
Qed.

(* a live fake frame and its shadow end below the ceiling *)
Lemma re_frm_ceil : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= YM05.alloc_ceiling /\
  frame_addr ly cid pos mod 32 = 0 /\
  shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 < YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (H4096 & Hce & Happ).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (Hal32 & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact H4096|]. split; [exact Hce|]. split; [exact Hal32|].
unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as Dp.
pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)) as Mp.
pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as Dr.
pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as Mr. lia.
Qed.

(* ---- THE KEEP: a step that changes the state only by adding frames, and the memory only off the image, off
   every live block's bytes and off every frame live at the entry (its shadow included), carries every side
   fact. ITS THREE KEEPS ARE EXACTLY YGcallx.v acall_kept's image, block and frame clauses, so a call
   discharges them by projection and one of this function's own runs discharges them from its write set.
   NO BLOCK-SHADOW KEEP IS ASKED (acall_kept has no such clause): the tree's shadow facts are RE-DERIVED at
   the end memory from alx_hshadow - the ledger puts a tree block's base in Hp - and its bytes from
   alx_blocks / alx_blocks_tail. ---- *)
Lemma re_side_keep : forall (D : RIN) S S' mem mem' md',
  re_side D S mem -> re_copy_home D ->
  ARx (ri_ly D) S' (ri_Hp D) (ri_W D) mem' md' ->
  ablocks B (ri_ly D) S' = ablocks B (ri_ly D) S ->
  (forall cid pos, In (cid, pos) (frames S) -> In (cid, pos) (frames S')) ->
  (forall cid pos, In (cid, pos) (frames (ri_S D)) -> In (cid, pos) (frames S)) ->
  (room_live_cf S -> room_live_cf S') ->
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PresetRoomPos.iface_room_pos sm x os i H0 hist S') ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H (ri_W D)) mem' a = aview SEGS (w_H (ri_W D)) mem a) ->
  (forall p n i, In (p, n) (ablocks B (ri_ly D) S) -> 0 <= i < req_size n ->
     aview SEGS (w_H (ri_W D)) mem' (p + i) = aview SEGS (w_H (ri_W D)) mem (p + i)) ->
  (forall cid pos a, In (cid, pos) (frames (ri_S D)) ->
     (in_zr a (frame_rng (ri_ly D) (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr (ri_ly D) cid pos), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H (ri_W D)) mem' a = aview SEGS (w_H (ri_W D)) mem a) ->
  (* the keep is stated from the ENTRY memory, the form every runner phase and every call rule hands over *)
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem') ->
  re_side D S' mem'.
Proof.
intros D S S' mem mem' md' HSIDE HCH HAR' Eab Hfr Hfr0 Hroom Hpos Kimg Kblk Kfrm Kmn.
destruct HSIDE as (HLED & HROD & HROOM & HPOS & HTREE & HCPY & HMN).
pose proof (@cf_head_nonneg cp) as Hhn. pose proof (@cf_head_al cp) as Hal8.
pose proof HW as Hhw. unfold prh_head_wide in Hhw.
(* the statics of alloc.c, read through the image clause *)
assert (Kpst : forall a, Exists (in_zr a) PST ->
  aview SEGS (w_H (ri_W D)) mem' a = aview SEGS (w_H (ri_W D)) mem a).
{ intros a Ha. destruct (pal_pst_static a Ha) as [H1 H2]. exact (Kimg a (pst_img_A a Ha) H1 H2). }
(* a live block's bytes, by address rather than by offset *)
assert (Kblkv : forall p n a, In (p, n) (ablocks B (ri_ly D) S) -> p <= a < p + req_size n ->
  aview SEGS (w_H (ri_W D)) mem' a = aview SEGS (w_H (ri_W D)) mem a).
{ intros p n a Hin Ha. replace a with (p + (a - p)) by lia. apply (Kblk p n (a - p) Hin). lia. }
(* 1. the ledger: its seven cells (g_most and g_own_ran_out among them since the ledger-field sweep) are statics
   of alloc.c read through the image clause; its blocks' head words are block bytes *)
assert (HLED' : prh_ledger B (ri_ly D) S' (ri_Hp D) (ri_W D) mem'
  (ri_Lam D) (ri_peak D) (ri_cnt D) SIZE_MAXZ (ri_ran D) (ri_most D) 0).
{ destruct HLED as (HG & Hnd & HF & Hperm).
  split; [|split; [exact Hnd | split; [|exact Hperm]]].
  - unfold prh_glob in *. destruct HG as (G1 & G2 & G3 & G4 & G5 & (GM & GMr) & (GO & GOr) & GR).
    split; [|split; [|split; [|split; [|split; [|split; [split; [|exact GMr] | split; [split; [|exact GOr] | exact GR]]]]]]];
    (eapply ts_vm_av; [|eassumption]); intros j Hj; apply Kpst; unfold prh_pst;
    repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
  - rewrite Forall_forall in HF |- *. intros [a kk] Hin. specialize (HF _ Hin). cbn [fst snd] in *.
    unfold prh_hblock in *.
    destruct HF as (Hk & Hab & Hhp & Ha16 & Hv).
    split; [exact Hk|]. split; [rewrite Eab; exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
    eapply ts_vm_av; [|exact Hv]. intros j Hj.
    apply (Kblkv (a - cf_head) (kk + cf_head) (a - cf_head + Z.of_nat j) Hab).
    unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia. }
(* 3. the read-only view *)
assert (HROD' : arodata_okP SEGS RLO RHI B (aview SEGS (w_H (ri_W D)) mem')).
{ intros a Hro Hno Her. rewrite (Kimg a (re_ro_img a Hro) Hno Her). exact (HROD a Hro Hno Her). }
(* 4. the room: re-stated, it is room_live_cf alone (the model-run position is carried separately and only on
   the granted path) *)
assert (HROOM' : re_room D S') by exact (Hroom HROOM).
(* 5. copy's bytes: copy lives in a frame live at the entry *)
assert (HCPY' : re_copy_kept D (ri_W D) mem').
{ intros Hc0 a Ha. rewrite <- (HCPY Hc0 a Ha).
  destruct (HCH Hc0) as (cid & pos & Hin & Hlo & Hhi).
  apply (Kfrm cid pos a Hin). left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
split; [exact HLED'|]. split; [exact HROD'|].
split; [exact HROOM'|].
split; [destruct HPOS as (hist & Hip); exists hist; exact (Hpos _ _ _ _ _ _ Hip)|].
split; [|split; [exact HCPY' | exact Kmn]].
(* 6. the tree *)
destruct HTREE as (HND & HDL & HVIS & HHOME).
pose proof HHOME as (Hm8 & (hcid & hpos & Hhin & Hhlo & Hhhi) & HRA).
assert (Hhin' : In (hcid, hpos) (frames S)) by exact (Hfr0 hcid hpos Hhin).
assert (Kdoc : forall a, ri_doc D <= a < ri_doc D + 56 ->
  aview SEGS (w_H (ri_W D)) mem' a = aview SEGS (w_H (ri_W D)) mem a)
  by (intros a Ha; apply (Kfrm hcid hpos a Hhin); left; unfold in_zr, frame_rng; cbn [fst snd]; lia).
assert (Kdocsh : forall a, shadow_addr (ri_doc D) <= a <= shadow_addr (ri_doc D + 55) ->
  aview SEGS (w_H (ri_W D)) mem' a = aview SEGS (w_H (ri_W D)) mem a).
{ intros a Ha. apply (Kfrm hcid hpos a Hhin). right. unfold in_zr. cbn [fst snd].
  destruct (re_frm_ceil (ri_ly D) S' (ri_Hp D) (ri_W D) mem' md' hcid hpos HAR' (Hfr hcid hpos Hhin'))
    as (_ & _ & HFal & _).
  destruct (re_fs_div8 hcid ltac:(lia)) as (Hcid0 & Hfs8).
  unfold shadow_addr in Ha |- *.
  pose proof (Z.div_mod (ri_doc D) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (ri_doc D) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (ri_doc D + 55) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (ri_doc D + 55) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (frame_addr (ri_ly D) hcid hpos) 8 ltac:(lia)) as D3.
  pose proof (Z.div_mod (frame_addr (ri_ly D) hcid hpos) 32 ltac:(lia)) as D3b.
  pose proof (Z.div_mod (fs_frame_bytes hcid) 8 ltac:(lia)) as D4. lia. }
(* every block of the tree, as a harness block of the ledger *)
assert (HBLK : forall a kk, In (a, kk) (ri_D D) ->
  0 <= kk /\ In (a - cf_head, kk + cf_head) (ablocks B (ri_ly D) S) /\ In (a - cf_head) (ri_Hp D) /\
  req_size (kk + cf_head) = kk + cf_head).
{ intros a kk Hin. pose proof (HDL _ Hin) as HinL.
  destruct HLED as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF _ HinL) as (Hk & Hab & Hhp & _). cbn [fst snd] in Hk, Hab, Hhp.
  split; [exact Hk|]. split; [exact Hab|]. split; [exact Hhp|].
  unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia. }
split.
- (* pj_nodeR: the frame lemma over the tree's footprint *)
  eapply pj_nodeR_frame; [exact HND|]. intros x Hx.
  assert (Kx : aview SEGS (w_H (ri_W D)) mem' x = aview SEGS (w_H (ri_W D)) mem x /\
               apresent (w_H (ri_W D)) mem' x).
  { destruct Hx as [Hx | (bk & Hbk & Hh)].
    - split; [exact (Kdoc x Hx)|].
      destruct (alx_frames _ _ _ LAWS (ri_ly D) S' (ri_Hp D) (ri_W D) mem' md' hcid hpos HAR'
        (Hfr hcid hpos Hhin')) as (_ & _ & Hpr & _).
      exact (proj1 (Hpr x ltac:(lia))).
    - destruct bk as [a kk]. destruct (HBLK a kk Hbk) as (Hk & Hab & Hhp & Hrq).
      unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
      destruct (alx_blocks _ _ _ LAWS (ri_ly D) S' (ri_Hp D) (ri_W D) mem' md' _ _ HAR'
        ltac:(rewrite Eab; exact Hab)) as (_ & _ & _ & _ & Hpres & _).
      split; [apply (Kblkv (a - cf_head) (kk + cf_head) x Hab); lia|].
      exact (proj1 (Hpres x ltac:(lia))). }
  destruct Kx as [Kx1 Kx2]. split.
  + exact (mbyte_of_aview SEGS (w_H (ri_W D)) (w_H (ri_W D)) mem mem' x Kx1).
  + intros _. exact (apresent_writable SEGS _ _ _ Kx2).
- split; [exact HDL|]. split.
  + (* the tree's blocks stay visible: the shadow facts re-derived at the end memory *)
    intros a kk Hin. destruct (HVIS a kk Hin) as (V1 & V2 & V3 & V4 & _ & _ & V7).
    destruct (HBLK a kk Hin) as (Hk & Hab & Hhp & Hrq).
    destruct (alx_hshadow _ _ _ LAWS (ri_ly D) S' (ri_Hp D) (ri_W D) mem' md' (a - cf_head) (kk + cf_head)
      HAR' ltac:(rewrite Eab; exact Hab) Hhp) as (Hbs & Hhv).
    rewrite Hrq in Hbs, Hhv.
    replace (a - cf_head + cf_head) with a in Hbs, Hhv by lia.
    replace (kk + cf_head - cf_head) with kk in Hbs, Hhv by lia.
    split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|].
    split; [exact (block_shadow_range _ _ a kk a kk Hbs ltac:(lia) ltac:(lia))|].
    split; [intros Hk0; exact (Hhv ltac:(lia))|].
    intros x Hx. destruct (Z_lt_le_dec x (a + kk)) as [Hlt|Hge].
    * rewrite (Kblkv (a - cf_head) (kk + cf_head) x Hab ltac:(lia)). exact (V7 x ltac:(lia)).
    * refine (alx_blocks_tail _ _ _ LAWS (ri_ly D) S' (ri_Hp D) (ri_W D) mem' md' _ _ x HAR'
        ltac:(rewrite Eab; exact Hab) _). rewrite Hrq. lia.
  + (* the root's home and its shadow *)
    split; [exact Hm8|].
    split; [exists hcid, hpos; split; [exact Hhin | split; [exact Hhlo | exact Hhhi]]|].
    intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    unfold shadow_of_addr in Hs |- *. rewrite <- Hs. apply Kdocsh.
    unfold shadow_addr. pose proof (Z.div_mod (ri_doc D) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (ri_doc D) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod x 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
    pose proof (Z.div_mod (ri_doc D + 55) 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (ri_doc D + 55) 8 ltac:(lia)) as M3. lia.
Qed.

(* what frame_alloc_1 leaves, at the call's return site +120: the fake frame (RT_CID, pos), its shadow still
   zero, its flag pointer in the last word, its bytes present *)
Definition re_frame_out (D : RIN) (S2 : astate) (mem2 : word -> option byte) (pos : Z) : Prop :=
  let F := frame_addr (ri_ly D) RT_CID pos in
  frames S2 = (RT_CID, pos) :: frames (ri_S D) /\ ~ In (RT_CID, pos) (frames (ri_S D)) /\
  ablocks B (ri_ly D) S2 = ablocks B (ri_ly D) (ri_S D) /\ blocks_bytes S2 = blocks_bytes (ri_S D) /\
  zero_shadow (aview SEGS (w_H (ri_W D)) mem2) SHADOW_OFF F (fs_frame_bytes RT_CID) /\
  rdword (aview SEGS (w_H (ri_W D)) mem2) (F + RT_FLAGP) = Some (flag_addr (ri_ly D) RT_CID pos) /\
  (forall a, F <= a < F + fs_frame_bytes RT_CID -> apresent (w_H (ri_W D)) mem2 a).

(* the registers at +120, before `mv s2, a0` *)
Definition re_bregs_b (D : RIN) (rg : bvmap 5 word) (pos : Z) : Prop :=
  getr rg 10 = w64 (frame_addr (ri_ly D) RT_CID pos) /\
  getr rg 2 = w64 (RT_R (ri_sp D)) /\ getr rg 8 = w64 (ri_sp D) /\ getr rg 9 = w64 (RT_R (ri_sp D)) /\
  getr rg 19 = w64 (ri_copy D) /\ getr rg 20 = w64 (ri_doc D) /\ getr rg 21 = w64 (ri_pretty D) /\
  getr rg 25 = w64 SHADOW_OFF /\ getr rg 3 = w64 (as_gp B) /\ getr rg 4 = w64 (as_tp B).

(* ---- re_entry: the entry, the prologue, the two GOT loads (E1), the use-after-return flag (E2), the shadow base
   and the flag test (E3), and the frame_alloc_1 call, to its return site +120 ---- *)
Lemma re_entry : forall (D : RIN) (Q : world SEGS -> config -> Prop) ch,
  fpre B ARx STKR (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_regs D) (ri_mem D) (ri_md D) ch ->
  re_side D (ri_S D) (ri_mem D) -> re_copy_home D ->
  count_cid RT_CID (frames (ri_S D)) < fs_frames RT_CID ->
  getr (ri_regs D) 10 = w64 (ri_doc D) -> getr (ri_regs D) 11 = w64 (ri_pretty D) ->
  getr (ri_regs D) 12 = w64 (ri_copy D) ->
  (forall S2 mem2 md2 rg kj pos,
     re_AJ D (ri_ly D) S2 (ri_Hp D) (ri_W D) mem2 md2 kj pos ->
     re_side D S2 mem2 -> re_saved D (ri_W D) mem2 -> re_frame_out D S2 mem2 pos ->
     re_bregs_b D rg pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (ri_W D)
       (mkCfg (mkst rg (Z_to_bv 64 (BASE + (RE_PC + RE_B_OFF))) mem2 (seg_rom SEGS)) md2) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (ri_W D) (cfg_at SEGS (SIGMA AS_round_trip_text) (ri_regs D) (ri_mem D) (ri_md D))
    Q.
Proof.
intros D Q ch HFPRE HSIDE HCH HCNT H10 H11 H12 KONT.
pose proof HFPRE as (HPRE & HROD & HSPHI & HRACEIL).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs. pose proof HSTK_A as HSTK.
pose proof (@alloc_ceiling_val rc) as (Hcv & Hcm).
assert (H160 : 176 <= ri_sp D) by (unfold ri_sp in *; lia).
destruct (re_R_range (ri_sp D) Hal16 H160) as (HR1 & HR2 & HR3).
(* the entry journal, at RZW (YCbqG.ajournal_x_initR at the reflexive wle') *)
pose proof (ajournal_x_initR (SK := SK) SEGS B PST ARx RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) STKR (ri_FP D)
  (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_regs D) (ri_mem D) (ri_md D) ch HPRE) as HJ.
(* one name for the entry sp, so lia sees one atom: ri_sp D is spZ (ri_regs D) by definition *)
change (spZ (ri_regs D)) with (ri_sp D) in Hal16, Hstk0, Hceil, Hslo, Hshi, H47, Hbot, Htop, Htop2, Hpres, HSPHI, HJ.
(* the memory invariant this walk carries: memnorm from the entry *)
pose (PMN := fun m => YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS PMN)
  by exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (ri_mem D) (srr_inv_laws_memnorm_k SEGS)).
pose (RUNTO := @paj_run_to_x_invR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS PMN PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS PMN PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
assert (HPM : PMN (ri_mem D)) by (unfold PMN; intros H; exact H).
(* ---- E1 ---- *)
destruct (re_E1_entry (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_regs D) (ri_mem D) (ri_md D) ch HPRE) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)])) by apply te_env.
assert (Usp : bv_unsigned (ew (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)]) 2) = ri_sp D)
  by (rewrite (te_entry (ri_regs D) (ri_regs D) _ 2%bv 2) by reflexivity; reflexivity).
unfold cfg_at. rewrite <- RE_PC_val.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (0, 0) (RE_PC + RE_A2_OFF).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp; unfold ri_sp; lia | cbn; unfold ri_sp in *; lia | cbn; unfold ri_sp in *; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
pose proof (ajxR_ar HJ) as HAR1.
prreg HS (12%bv : bv 5) R12. prreg HS (11%bv : bv 5) R11. prreg HS (10%bv : bv 5) R10.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (2%bv : bv 5) R2.
prreg HS (19%bv : bv 5) R19. prreg HS (21%bv : bv 5) R21.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (ts_region_nth (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)]) _ _ 0 _ HS eq_refl) as HR0.
cbn [ms_mem restrict] in HR0.
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
assert (EE : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  ew (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)]) n = getr (ri_regs D) r)
  by (intros r n Hn; apply te_entry; exact Hn).
assert (EP2 : ew (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)]) 2 = getr (ri_regs D) 2)
  by (apply EE; reflexivity).
assert (H160' : 160 <= spZ (ri_regs D)) by (change (spZ (ri_regs D)) with (ri_sp D); lia).
assert (X2 : getr regs1 2 = w64 (RT_R (ri_sp D)))
  by (rewrite R2, EP2; exact (re_R_word (ri_regs D) H160')).
assert (X9 : getr regs1 9 = w64 (RT_R (ri_sp D)))
  by (rewrite R9, EP2; exact (re_R_add0 (ri_regs D) H160')).
assert (X8 : getr regs1 8 = getr (ri_regs D) 2) by (rewrite R8; exact EP2).
assert (X10 : getr regs1 10 = w64 (ri_doc D)) by (rewrite R10, (EE 10%bv 10%nat) by reflexivity; exact H10).
assert (X19 : getr regs1 19 = w64 (ri_copy D)) by (rewrite R19, (EE 12%bv 12%nat) by reflexivity; exact H12).
assert (X21 : getr regs1 21 = w64 (ri_pretty D)) by (rewrite R21, (EE 11%bv 11%nat) by reflexivity; exact H11).
assert (X3 : getr regs1 3 = getr (ri_regs D) 3) by (rewrite R3; apply EE; reflexivity).
assert (X4 : getr regs1 4 = getr (ri_regs D) 4) by (rewrite R4; apply EE; reflexivity).
assert (X11 : getr regs1 11 = w64 (VAL (A_OBJ 12)))
  by (rewrite R11, te_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); reflexivity).
assert (X12 : getr regs1 12 = w64 (as_uar_cell B))
  by (rewrite R12; exact (te_more_lt (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)] 0 ltac:(lia))).
(* the thirteen saves are in the frame now *)
assert (HSV : re_saved D (ri_W D) mem1).
{ intros j Hj. do 13 (destruct j as [|j]; [
    lazymatch goal with |- val_mem _ _ _ _ (bv_unsigned (getr _ (nth ?jj RTT_SAVED 0%bv))) =>
      let r := eval vm_compute in (nth jj RTT_SAVED 0%bv) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      let off := eval vm_compute in (- 8 * (Z.of_nat jj + 1)) in
      pose proof (ts_field (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)]) _ 2 (ri_sp D) _ _ _ _ _ off 8
        (SOff n 0) HR0 Usp ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; change (N.to_nat 8) with 8%nat in V;
      rewrite ts_U_atom_mod, (EE r n) in V by reflexivity;
      change (nth jj RTT_SAVED 0%bv) with r;
      replace (ri_sp D - 8 * (Z.of_nat jj + 1)) with (ri_sp D + off) by (cbn; lia); exact V
    end |]). lia. }
(* the side facts survive a step that writes only inside the function's own frame window: every byte the keep
   asks about - the image, a live block, a frame live at the entry and that frame's shadow - lies below the
   allocator ceiling, and astk_ok puts the whole window at or above it *)
assert (KSTK : forall (Sx : astate) (memx memy : word -> option byte) mdx,
  ARx (ri_ly D) Sx (ri_Hp D) (ri_W D) memy mdx -> re_side D Sx memx ->
  (forall cid pos, In (cid, pos) (frames (ri_S D)) -> In (cid, pos) (frames Sx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ re_wr_stk D a ->
     aview SEGS (w_H (ri_W D)) memy a = aview SEGS (w_H (ri_W D)) memx a) ->
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS memy) ->
  re_side D Sx memy).
{ intros Sx memx memy mdx HARx HSx Hfr0 K Kmn.
  refine (re_side_keep D Sx Sx memx memy mdx HSx HCH HARx eq_refl (fun c p H => H) Hfr0 (fun H => H)
    (fun sm x os i H0 hist H => H) _ _ _ Kmn).
  - intros a Hi _ _. pose proof (Hsegs a Hi) as Hl.
    apply K; [unfold kLowMemEnd in Hl; lia|]. unfold re_wr_stk, kLowMemEnd in *. lia.
  - intros p n i Hin Hi. destruct (re_blk_ceil (ri_ly D) Sx (ri_Hp D) (ri_W D) memy mdx p n HARx Hin)
      as (H4096 & Hce & Hgr & Hsh). apply K; [lia|]. unfold re_wr_stk. lia.
  - intros c p a Hin Ha. destruct (re_frm_ceil (ri_ly D) Sx (ri_Hp D) (ri_W D) memy mdx c p HARx (Hfr0 c p Hin))
      as (H4096 & Hce & Hal & Hsh).
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
    apply K; [unfold shadow_addr, SHADOW_OFF in *; lia|]. unfold re_wr_stk, shadow_addr, SHADOW_OFF in *. lia. }
(* the prologue's writes lie in that window *)
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ re_wr_stk D a ->
  aview SEGS (w_H (ri_W D)) mem1 a = aview SEGS (w_H (ri_W D)) (ri_mem D) a).
{ intros a Ha Hn.
  refine (ts_keep (ri_W D) (TE (ri_regs D) (ri_regs D) [w64 (as_uar_cell B)]) (ss_mem ss_E1) (ri_mem D) mem1
    (fun x => re_wr_stk D x) HFr _ a Ha Hn).
  intros x (r & Hr & Hx). cbv [ss_E1 ss_mem re_E1_regions stack_region got_regionP In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx;
    rewrite ts_bv_some in Hx; [rewrite Usp in Hx; unfold re_wr_stk; lia | lia | lia]. }
assert (HSIDE1 : re_side D (ri_S D) mem1)
  by exact (KSTK (ri_S D) (ri_mem D) mem1 _ HAR1 HSIDE (fun c p H => H) KW1 HPM).
clear HF HG HFr HR0 R2 R3 R4 R8 R9 R10 R11 R12 R19 R21.
(* ---- E2: the use-after-return flag's load. ARx_const_law fixes the flag at 1, so the `beqz` of E3 falls
   through to the frame call and the real-stack skip (+0x80) is dead ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR1) as (_ & Kuar1 & _ & _).
destruct (re_E2_entry (ri_regs D) regs1 mem1 (ri_W D) X12 Kuar1) as [HS2 SHOK2].
assert (HEI2 : img_env VAL A_LIM (TE (ri_regs D) regs1 [])) by apply te_env.
change (BASE + 13292) with (BASE + (RE_PC + RE_A2_OFF)).
paj_run_to_tok_x_inv RUNTO HS2 HJ SHOK2 HPM (0, 0) (RE_PC + RE_A3_OFF).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS2.
pose proof (ajxR_ar HJ) as HAR2.
prreg HS2 (12%bv : bv 5) Q12.
assert (Y : forall (r : bv 5), In r [2; 3; 4; 8; 9; 10; 11; 19; 21]%bv -> getr (ms_regs ms0) r = getr regs1 r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [tskeep HS2 |]). destruct Hr. }
(* E2 writes nothing *)
assert (Hnowr2 : forall a, ~ in_wrange (TE (ri_regs D) regs1 []) (ss_mem ss_E2) a).
{ intros a (r & Hr & Ha). cbv [ss_E2 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
assert (HSIDE2 : re_side D (ri_S D) (ms_mem ms0)).
{ refine (KSTK (ri_S D) mem1 (ms_mem ms0) _ HAR2 HSIDE1 (fun c p H => H) _ HPM).
  intros a Ha _. apply aview_eq_of. rewrite HFr by apply Hnowr2. reflexivity. }
clear HF HG. rename HFr into HFr2.
set (regs2 := ms_regs ms0) in *. set (mem2 := ms_mem ms0) in *.
(* ---- E3: the shadow base's load, `mv s4, a0`, the flag test and `li a0, 0x80`, to the frame call ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kcell2 & _ & _ & _).
rewrite (pal_cell (PI := PA) B PAL) in Kcell2.
destruct (re_E3_entry (ri_regs D) regs2 mem2 (ri_W D)
  ltac:(unfold regs2; rewrite (Y 11%bv) by (cbv; tauto); exact X11) Q12 Kcell2) as [HS3 SHOK3].
assert (HEI3 : img_env VAL A_LIM (TE (ri_regs D) regs2 [w64 SHADOW_OFF])) by apply te_env.
change (BASE + 13296) with (BASE + (RE_PC + RE_A3_OFF)).
paj_run_tok_x_inv RUN HS3 HJ SHOK3 HPM (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS3.
pose proof (ajxR_ar HJ) as HAR3.
assert (Y3 : forall (r : bv 5), In r [2; 3; 4; 8; 9; 19; 21]%bv -> getr (ms_regs ms1) r = getr regs2 r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [tskeep HS3 |]). destruct Hr. }
assert (Z20 : getr (ms_regs ms1) 20 = getr regs2 10) by tskeep HS3.
prreg HS3 (25%bv : bv 5) Z25. prreg HS3 (1%bv : bv 5) Z1.
assert (Hnowr3 : forall a, ~ in_wrange (TE (ri_regs D) regs2 [w64 SHADOW_OFF]) (ss_mem ss_E3) a).
{ intros a (r & Hr & Ha). cbv [ss_E3 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
assert (HSIDE3 : re_side D (ri_S D) (ms_mem ms1)).
{ refine (KSTK (ri_S D) mem2 (ms_mem ms1) _ HAR3 HSIDE2 (fun c p H => H) _ HPM).
  intros a Ha _. apply aview_eq_of. rewrite HFr by apply Hnowr3. reflexivity. }
assert (HSV3 : re_saved D (ri_W D) (ms_mem ms1)).
{ intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi. apply aview_eq_of.
  rewrite HFr by apply Hnowr3. rewrite HFr2 by apply Hnowr2. reflexivity. }
clear HF HG. rename HFr into HFr3.
set (regs3 := ms_regs ms1) in *. set (mem3 := ms_mem ms1) in *.
(* ---- the frame_alloc_1 call (YGcallMxmn.v aj_stack_malloc_at_xmR at class RT_CID, the journal at RZW; the rule
   concludes the plain SRr with W2 = W, lifted by YA0nH.SRr_SRr'). THE CAPACITY PREMISE is Rtt102Cut.rtt_capacity at
   the entry state, carried here by the journal's `frames Sc = own ++ frames S` at own = [] ---- *)
rewrite pal_stack_malloc1.
assert (R2' : getr regs3 2 = w64 (RT_R (ri_sp D))).
{ unfold regs3. rewrite (Y3 2%bv) by (cbv; tauto). unfold regs2. rewrite (Y 2%bv) by (cbv; tauto). exact X2. }
assert (Hsp3 : spZ regs3 = ri_sp D + (RT_R (ri_sp D) - ri_sp D)).
{ unfold spZ. rewrite R2'. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply YA0nH.SRr_SRr'.
  eapply (aj_stack_malloc_at_xmR SEGS B PST ARx LAWS pa_segs_low (pal_env (PI := PA) B PAL) OWNLOW SMX
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    RT_CID ASM1 ltac:(unfold RT_CID; lia)
    (ri_W D) regs3 mem3 STKR (ri_sp D) (ri_FP D) (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D)
    [] (ri_ly D) (ri_S D) (ri_Hp D) _ 0 (RT_R (ri_sp D) - ri_sp D) (getr regs3 1) HJ Hsp3).
  - rewrite Z.mod_divide in Hal16, HR2 by lia. destruct Hal16 as [q1 Hq1]. destruct HR2 as [q3 Hq3].
    apply Z.mod_divide; [lia|]. exists (2 * q3 - q1). lia.
  - lia.
  - unfold ESTACK. lia.
  - unfold regs3. rewrite (Y3 3%bv) by (cbv; tauto). unfold regs2. rewrite (Y 3%bv) by (cbv; tauto).
    rewrite X3. exact Hgp.
  - unfold regs3. rewrite (Y3 4%bv) by (cbv; tauto). unfold regs2. rewrite (Y 4%bv) by (cbv; tauto).
    rewrite X4. exact Htp.
  - reflexivity.
  - rewrite Z1. apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite (ajxR_frs HJ). exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & rgB & memB & mdB & pos & -> & HJ2 & HprB & H10B & EabB & HfrsB & HfreshB
  & HnevB & HbbB & HzB & HflB & HfpB & HkB & HJnilB & (fB & ES2) & HmnB).
pose proof (ajxR_ar HJ2) as HARB.
destruct HkB as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6).
assert (HSIDEB : re_side D S2 memB).
{ refine (re_side_keep D (ri_S D) S2 mem3 memB mdB HSIDE3 HCH HARB EabB _ (fun c p H => H) _ _ KB3 _ _
    (fun H => HmnB (HPM H))).
  - intros c p Hin. rewrite HfrsB. right. exact Hin.
  - intros Hk. rewrite ES2. apply RL_set_fs. exact Hk.
  - intros sm x os i H0 hist Hip. rewrite ES2. apply PresetRoomPosKeep.room_pos_set_fs. exact Hip.
  - intros p n i Hin Hi. exact (KB2 p n i Hin Hi ltac:(intros [])).
  - intros c p a Hin Ha. exact (KB4 c p a Hin Ha ltac:(intros [])). }
assert (HSVB : re_saved D (ri_W D) memB).
{ intros j Hj. eapply ts_vm_av; [|exact (HSV3 j Hj)]. intros i Hi.
  apply KB1; unfold ESTACK in *; lia. }
(* the fake frame the call gave: at F = frame_addr ly 1 pos, nonzero by the frames law, so the real-stack
   fallback at +0x8c .. +0xa4 and the `beqz s2` of the exit are both dead *)
assert (HFOUT : re_frame_out D S2 memB pos).
{ split; [exact HfrsB|]. split; [exact HfreshB|]. split; [exact EabB|]. split; [exact HbbB|].
  split; [exact HzB|]. split; [|exact HfpB].
  change RT_FLAGP with (fs_frame_bytes RT_CID - 8). rewrite Z.add_sub_assoc. exact HflB. }
rewrite Z1. change (BASE + 13316) with (BASE + (RE_PC + RE_B_OFF)).
refine (KONT S2 memB mdB rgB _ pos HJ2 HSIDEB HSVB HFOUT _).
assert (PB : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr rgB r = getr regs3 r).
{ intros r Hr. pose proof (HprB _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
assert (Y13 : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 21]%bv -> getr regs3 r = getr regs1 r).
{ intros r Hr. rewrite (Y3 r Hr). apply Y. cbv [In] in Hr |- *. tauto. }
unfold re_bregs_b.
split; [exact H10B|].
split; [rewrite (PB 2%bv ltac:(ts_cs)), (Y13 2%bv) by (cbv; tauto); exact X2|].
split; [rewrite (PB 8%bv ltac:(ts_cs)), (Y13 8%bv) by (cbv; tauto); rewrite X8;
        unfold w64, ri_sp, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (PB 9%bv ltac:(ts_cs)), (Y13 9%bv) by (cbv; tauto); exact X9|].
split; [rewrite (PB 19%bv ltac:(ts_cs)), (Y13 19%bv) by (cbv; tauto); exact X19|].
split; [rewrite (PB 20%bv ltac:(ts_cs)), Z20, (Y 10%bv) by (cbv; tauto); exact X10|].
split; [rewrite (PB 21%bv ltac:(ts_cs)), (Y13 21%bv) by (cbv; tauto); exact X21|].
split; [rewrite (PB 25%bv ltac:(ts_cs)), Z25;
        exact (te_more_lt (ri_regs D) regs2 [w64 SHADOW_OFF] 0 ltac:(lia))|].
split; [rewrite (PB 3%bv ltac:(ts_cs)), (Y13 3%bv) by (cbv; tauto); rewrite X3; exact Hgp
       | rewrite (PB 4%bv ltac:(ts_cs)), (Y13 4%bv) by (cbv; tauto); rewrite X4; exact Htp].
Unshelve. all: first [exact HSTK_A | exact LAWS | exact pst_img_A | exact pal_pst_static | exact 0].
Qed.

(* ---- E4: from frame_alloc_1's return site (+120) to the pj_write call (+0x12c): `mv s2, a0`, `mv s10, s2`, the
   `bnez s2` past the real-stack fallback (taken: a0 = F >= 4096), the spill `sd s10, 0x10(s1)`, the frame
   header F+0 / F+8 / F+16, s9 := (F >> 3) + s9 = shadow_addr F, the 16 shadow bytes, `mv a0, s4; mv a1, s5`.
   Regions: s1's spill slot [s1 + 16, s1 + 24), the header [F, F + 24), F's 16 shadow bytes (atom 64 = the
   shadow pointer, aliased to `(F >> 3) + s9` as S10TxString.v ss_B aliases it to `(F >> 3) + s8`) ---- *)
Definition ss_E4 : sstate := mkSS (RE_PC + RE_B_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 16 24 16 24 [];
    YP09.mkRegion (Some (xr 10)) 0 24 0 24 [];
    YP09.mkRegion (Some 64%nat) 0 16 0 16 [] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 10, mkAF 4096 (2 ^ 47) 5); (xr 25, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] []
           [(SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 10) 0) (SLit 3)) (SOff (xr 25) 0), SOff 64 0)]).

Lemma re_E4_entry : forall (regs0 : bvmap 5 word) lyc Sc Hpc (Wc : world SEGS) memc mdc pos rg sp1,
  ARx lyc Sc Hpc Wc memc mdc -> In (RT_CID, pos) (frames Sc) ->
  (forall a, frame_addr lyc RT_CID pos <= a < frame_addr lyc RT_CID pos + fs_frame_bytes RT_CID ->
     apresent (w_H Wc) memc a) ->
  (forall a, sp1 + 16 <= a < sp1 + 24 -> apresent (w_H Wc) memc a) ->
  YM05.alloc_ceiling <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr lyc RT_CID pos) -> getr rg 25 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs0 rg [w64 (shadow_addr (frame_addr lyc RT_CID pos))]) ss_E4
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (RE_PC + RE_B_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs0 rg [w64 (shadow_addr (frame_addr lyc RT_CID pos))]) (mrestrict (w_H Wc) memc).
Proof.
intros regs0 lyc Sc Hpc Wc memc mdc pos rg sp1 HAR Hin Hfp Hsp Hc Hc47' Hal R9 R10 R25.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc RT_CID pos HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc RT_CID pos HAR Hin) as (F32 & _ & _ & Fsh).
change (fs_frame_bytes RT_CID) with 128 in F2, F3, Fsh, Hfp.
set (F := frame_addr lyc RT_CID pos) in *.
set (E := TE regs0 rg [w64 (shadow_addr F)]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs0 rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs0 rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X25 : bv_unsigned (ew E (xr 25)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs0 rg _ 25%bv 25) by reflexivity. rewrite R25. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (Hsh2 : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs0 rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
unfold SHADOW_OFF in Hsh2.
split.
- apply ts_st_ok.
  all: try change (TE regs0 rg [w64 (shadow_addr F)]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hsp. lia.
    * apply (ts_rok E _ (xr 10) F); [exact X10 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hfp. lia.
    * apply (ts_rok E _ 64 (shadow_addr F)); [exact X64 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Fsh o ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X10, X64.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X10, X25, X64.
      change (2 ^ 5) with 32. change (2 ^ 0) with 1.
      unfold shadow_addr, SHADOW_OFF. repeat split; try lia.
    * cbn [f_alias alias_ok]. split; [|exact I].
      apply (ts_alias_shadow E (xr 10) (xr 25) 64 F X10 X25 X64). lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- E4's writes: s1's spill slot, the new frame's 24-byte header, the new frame's 16 shadow bytes ---- *)
Definition re_E4_wr (D : RIN) (pos a : Z) : Prop :=
  (RT_R (ri_sp D) + 16 <= a < RT_R (ri_sp D) + 24) \/
  (frame_addr (ri_ly D) RT_CID pos <= a < frame_addr (ri_ly D) RT_CID pos + 24) \/
  (shadow_addr (frame_addr (ri_ly D) RT_CID pos) <= a < shadow_addr (frame_addr (ri_ly D) RT_CID pos) + 16).

(* none of them is an image byte, a live block's byte, or a byte (or shadow byte) of a frame live at the entry *)
Lemma re_E4_disj : forall (D : RIN) S mem md pos a,
  ARx (ri_ly D) S (ri_Hp D) (ri_W D) mem md ->
  frames S = (RT_CID, pos) :: frames (ri_S D) -> ~ In (RT_CID, pos) (frames (ri_S D)) ->
  astk_ok STKR (ri_ly D) (ri_sp D) -> re_E4_wr D pos a ->
  ~ in_img SEGS a /\
  (forall p n, In (p, n) (ablocks B (ri_ly D) S) -> ~ (p <= a < p + req_size n)) /\
  (forall cid pos', In (cid, pos') (frames (ri_S D)) ->
     ~ in_zr a (frame_rng (ri_ly D) (cid, pos')) /\
     ~ in_zr a (shadow_addr (frame_addr (ri_ly D) cid pos'), fs_frame_bytes cid / 8)).
Proof.
intros D S mem md pos a HAR EF Hfresh Hstk Hwr.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HSTK_A as HSTK.
pose proof (@alloc_ceiling_val rc) as (Hcv & Hcm).
assert (H176 : 176 <= ri_sp D) by lia.
destruct (re_R_range (ri_sp D) Hal16 H176) as (HR1 & HR2 & HR3).
assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite EF; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR Hin) as (F32 & _ & _ & _).
change (fs_frame_bytes RT_CID) with 128 in F2, F3. unfold in_app in F3.
unfold re_E4_wr, shadow_addr in Hwr.
split; [|split].
- intros Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
  destruct Hwr as [Hw | [Hw | Hw]].
  + unfold kLowMemEnd in Hl. lia.
  + refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi).
    right; left. exists RT_CID, pos. split; [exact Hin|]. change (fs_frame_bytes RT_CID) with 128. lia.
  + unfold SHADOW_OFF, kLowMemEnd in *. lia.
- intros p n Hpn Hr.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hpn) as (_ & H4096 & Hce & Happ & _ & _).
  unfold in_app in Happ.
  destruct Hwr as [Hw | [Hw | Hw]].
  + lia.
  + pose proof (sep_block_frame_x _ _ _ LAWS _ _ _ _ _ _ p n RT_CID pos HAR Hpn Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes RT_CID) with 128 in Hd. lia.
  + unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- intros cid pos' Hin'.
  assert (Hin2 : In (cid, pos') (frames S)) by (rewrite EF; right; exact Hin').
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cid pos' HAR Hin2) as (G1 & G2 & G3).
  destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ cid pos' HAR Hin2) as (G32 & _ & _ & _).
  unfold in_app in G3.
  destruct (in_split _ _ Hin') as (l2 & l3 & El).
  pose proof (sep_frames_pos_x _ _ _ LAWS _ _ _ _ _ _ (RT_CID, pos) (cid, pos') [] l2 l3 HAR
    ltac:(rewrite EF, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes RT_CID) with 128 in Hd.
  unfold in_zr, frame_rng, shadow_addr. cbn [fst snd].
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  split; destruct Hwr as [Hw | [Hw | Hw]]; lia.
Qed.

(* ---- pj_write's run, named once: its pieces, its end writer and its grow count from g_count = cnt, g_fail_at =
   SIZE_MAX ---- *)
Definition re_P (D : RIN) : list (list Z) := WriterValue.wdpieces (ri_t D) (ri_p D).
Definition re_st (D : RIN) (ok : list bool) : WriterApp.wst :=
  PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D).
Definition re_k (D : RIN) (ok : list bool) : nat :=
  PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D).

(* the bytes of the live blocks are blocks_bytes *)
Lemma re_blocks_bytes : forall ly S, blocks_bytes S = fold_right (fun b acc => snd b + acc) 0 (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, YG01.blocks.
induction (st_chunks S) as [|k t IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc k); cbn [map fold_right snd]; rewrite IH; reflexivity.
Qed.

(* THE REFUTATION'S WRITER-MODEL STEP: a run of puts whose k calls are all granted (prh_granted) and below the pick
   (cnt + k <= fail) ends unfailed. The first disjunct of the kit's PRH_Refute.prh_refute_pj_write_failed (on the batch kit
   cut; the DeadK1 head c753d960f56, blob 90e5bae6f73e), proved here from re_w0_fail: requiring
   PRH_Refute.v would add PresetCfnA and the room-count files to this stretch's closure for a four-line case. *)
Lemma re_refute_pj_write_failed : forall ok cnt fail P,
  0 <= cnt -> fail < 2 ^ 64 ->
  cnt + Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P) <= fail ->
  prh_granted ok cnt fail (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) = 0.
Proof.
intros ok cnt fail P Hc Hf Hw G.
destruct (Z.eq_dec (WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P)) 0) as [E|E];
  [exact E|exfalso].
destruct (re_w0_fail P ok cnt fail ltac:(lia) E) as (i & _ & Hi2 & Hi3).
assert (Hlt : cnt + Z.of_nat i < fail) by lia.
destruct Hi3 as [H3 | H3].
- rewrite Z.mod_small in H3 by lia. lia.
- pose proof (G i Hi2 H3). lia.
Qed.

(* PEAK: THE ONE NAMED LEMMA FROM pj_write's PEAK EQUALITY, and the rest of pj_write's outcome processed into the
   cut's writer outcome. The dead conjunct (K0-DEAD-PJWRITE, prh_granted) refutes the failed arm through
   re_refute_pj_write_failed, so that arm's remaining facts (Rf) are never read *)
Lemma re_pjw_out : forall (D : RIN) Sc ly3 S3 (W3 : world SEGS) mem3 ok ran' q Lam' peak' (Rf : Prop),
  0 <= ri_cnt D < 2 ^ 62 -> PjWriteHyp.wlen (ri_t D) (ri_p D) + 1 <= 2 ^ 28 ->
  ablocks B (ri_ly D) Sc = ablocks B (ri_ly D) (ri_S D) ->
  prh_oks ok (ri_cnt D) SIZE_MAXZ (re_k D ok)
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D)) (ri_most D) (ri_ran D) ran' ->
  prh_granted ok (ri_cnt D) SIZE_MAXZ (re_k D ok) ->
  ((WriterApp.w_failed (re_st D ok) = 0 /\ q <> 0 /\
    ~ In (q - cf_head, WriterApp.w_cap (re_st D ok) + cf_head) (ablocks B (ri_ly D) Sc) /\
    Lam' = (q, WriterApp.w_cap (re_st D ok)) :: ri_Lam D /\
    peak' = Z.max (ri_peak D) (Ledger.lsum (ri_Lam D) + WriterApp.w_cap (re_st D ok)) /\
    Permutation (ablocks B ly3 S3) ((q - cf_head, WriterApp.w_cap (re_st D ok) + cf_head) :: ablocks B (ri_ly D) Sc) /\
    Z.of_nat (length (WriterValue.wdoc (ri_t D) (ri_p D))) < WriterApp.w_cap (re_st D ok) /\
    bytes_at W3 mem3 q (WriterValue.wdoc (ri_t D) (ri_p D) ++ [0]))
   \/
   (WriterApp.w_failed (re_st D ok) <> 0 /\ Rf)) ->
  ri_peak D <= peak' /\ WriterApp.w_fail (re_st D ok) = SIZE_MAXZ /\
  (exists wab, re_wout D q Lam' (WriterApp.w_cnt (re_st D ok)) ran' wab /\ Permutation (ablocks B ly3 S3) wab) /\
  bytes_at W3 mem3 q (ri_tb D ++ [0]) /\
  blocks_bytes S3 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D).
Proof.
intros D Sc ly3 S3 W3 mem3 ok ran' q Lam' peak' Rf Hcnt Hwl EabC HOKS HGR HOUT.
pose proof (@cf_head_nonneg cp) as Hhn.
pose proof (re_wcalls_le (ri_t D) (ri_p D) Hwl) as HWC.
change (Z.of_nat (PresetReqAt.wcalls (ri_t D) (ri_p D))) with
  (Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (re_P D))))) in HWC.
assert (EWC : PjWriteHyp.wcalls (ri_t D) (ri_p D) =
  Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (re_P D))))) by reflexivity.
pose proof (re_w0_k_le (re_P D) ok (ri_cnt D) SIZE_MAXZ) as HKle.
change (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D)) with (re_k D ok) in HKle.
pose proof (re_wfail_max (re_P D) ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) eq_refl) as HFM.
change (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D)) with (re_st D ok) in HFM.
assert (HLV : 0 <= WriterSpec.newcap 0 (PjWriteHyp.wlen (ri_t D) (ri_p D) + 1)).
{ unfold WriterSpec.newcap. cbn [Z.eqb].
  pose proof (PresetFlush.dbl_ge 64 4096 (PjWriteHyp.wlen (ri_t D) (ri_p D) + 1) ltac:(lia)). lia. }
assert (ELV : PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) =
  2 * (WriterSpec.newcap 0 (PjWriteHyp.wlen (ri_t D) (ri_p D) + 1) + cf_head)) by reflexivity.
(* THE REFUTATION: the run is unfailed, so the failed arm is dead *)
assert (Hwin : ri_cnt D + Z.of_nat (re_k D ok) <= SIZE_MAXZ) by (unfold SIZE_MAXZ; lia).
assert (Hs0 : WriterApp.w_failed (re_st D ok) = 0).
{ unfold re_st. apply (re_refute_pj_write_failed ok (ri_cnt D) SIZE_MAXZ (re_P D));
    [lia | unfold SIZE_MAXZ; lia | exact Hwin | exact HGR]. }
destruct HOUT as [(Hs & Hq & Hni & EL & EP & Hperm & Hlen & Hbytes) | (Hf & _)]; [|contradiction].
destruct HOKS as (O1 & O2 & O3).
destruct (re_w0_succ (re_P D) ok (ri_cnt D) SIZE_MAXZ ltac:(lia) Hs) as (EK & Hall & Ecnt & Efail & Ecap).
change (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D)) with (re_st D ok)
  in Ecnt, Efail, Ecap.
change (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ri_cnt D) SIZE_MAXZ) (re_P D)) with (re_k D ok) in EK.
(* no refusal (prh_granted), so g_ran_out is the entry's *)
assert (Hran' : ran' = ri_ran D).
{ destruct O2 as [O2 | (_ & i & Hi & Hn & _)]; [exact O2|]. exfalso.
  unfold prh_refused in Hn. apply andb_prop in Hn as [Hn1 Hn2].
  apply negb_true_iff in Hn1. apply negb_true_iff in Hn2. apply Z.eqb_neq in Hn2.
  exact (Hn2 (HGR i Hi Hn1)). }
assert (Hcntw : WriterApp.w_cnt (re_st D ok) =
  ri_cnt D + Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (re_P D))))).
{ rewrite Ecnt. apply Z.mod_small. lia. }
assert (Hcapl : WriterApp.w_cap (re_st D ok) = last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0)
  by (rewrite Ecap; exact (re_wcap_last (ri_t D) (ri_p D))).
assert (HcapN : WriterApp.w_cap (re_st D ok) = WriterSpec.newcap 0 (PjWriteHyp.wlen (ri_t D) (ri_p D) + 1))
  by (rewrite Hcapl; exact (re_wcap_newcap (ri_t D) (ri_p D) Hwl)).
assert (HcL : WriterApp.w_cap (re_st D ok) + cf_head <= PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D))
  by (rewrite ELV, HcapN; lia).
split; [rewrite EP; lia|].
split; [unfold SIZE_MAXZ; exact HFM|].
split.
{ exists ((q - cf_head, WriterApp.w_cap (re_st D ok) + cf_head) :: ablocks B (ri_ly D) (ri_S D)).
  split; [|rewrite <- EabC; exact Hperm].
  split; [exact Hq|]. split; [rewrite EWC; exact Hcntw|]. split; [exact Hran'|].
  exists (WriterApp.w_cap (re_st D ok)). split; [exact EL|]. split; [rewrite <- EabC; exact Hni|].
  split; [reflexivity|]. split; [exact Hlen|]. split; [exact HcL | exact Hcapl]. }
split; [exact Hbytes|].
rewrite (re_blocks_bytes ly3 S3), (re_bsum_perm _ _ Hperm). cbn [fold_right snd].
rewrite EabC, <- (re_blocks_bytes (ri_ly D) (ri_S D)). lia.
Qed.

(* the writer's live allowance is part of round_trip_text's *)
Lemma re_live_pjw_le : forall t p, PRH_FnWriter.LIVE_pj_write t p <= LIVE_round_trip_text t p.
Proof.
intros t p. unfold LIVE_round_trip_text, PRH_FnTx.LIVE_tx, PRH_FnPj.LIVE_pj_parse.
pose proof (@cf_head_nonneg cp) as Hh.
assert (0 <= hpeakR (PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t p)))
  by (destruct (PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t p)); cbn [hpeakR]; lia).
nia.
Qed.

(* ---- E4 AND THE pj_write CALL: from frame_alloc_1's return site (+120) through the frame's header and shadow to
   `jal pj_write` (+0x12c), the call through YCbqGcall.v's aj_call_xF_spR at RZW with the kit's tpj_write_specX at
   n := DOC_D (TPJW, which concludes YA0nH.SRr' SEGS RZ_cf with its post fpostFm at wle'), and pj_write's post
   processed into the cut RT_PJW (+304) ---- *)
Lemma re_at_B : forall (D : RIN) (Q : world SEGS -> config -> Prop) S2 mem2 md2 rg kj pos,
  rtt_pre B ARx CTX0 D -> re_copy_home D ->
  re_AJ D (ri_ly D) S2 (ri_Hp D) (ri_W D) mem2 md2 kj pos ->
  re_side D S2 mem2 -> re_saved D (ri_W D) mem2 -> re_frame_out D S2 mem2 pos -> re_bregs_b D rg pos ->
  (forall fxc ly S Hp W regs mem md k pos', re_at_pjw D fxc ly S Hp W regs mem md k pos' ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (SIGMA AS_round_trip_text + RT_PJW))
       mem (YK11.seg_rom SEGS)) md) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (ri_W D)
    (mkCfg (mkst rg (Z_to_bv 64 (BASE + (RE_PC + RE_B_OFF))) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros D Q S2 mem2 md2 rg kj pos HPRE HCH HJ HSD HSV HFO HBR KONT.
unfold rtt_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & HMN0 & HUC & HCTX & H10 & H11 & H12 & HP01 & HD0 & HTREE0 & HWF & HDEP & HWL & HCPY
  & HLED0 & HCNT & HRUN & HRAN & HRQA & HLIVE & HRQ & HFRL & HRL0 & HIRP & HFRM0 & HWR & HCONS & HUP0 & HOS4).
pose proof HFPRE as (HPRE0 & HROD0 & HSPHI & HRACEIL).
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
change (spZ (ri_regs D)) with (ri_sp D) in Hal16, Hslo, Hshi, Hbot, Htop, Hpres, HSPHI, Hch, Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK_A as HSTK. pose proof HSTKW_A as (HSTKW0 & HSTKW1).
pose proof (@alloc_ceiling_val rc) as (Hcv & Hcm).
pose proof (@pa_B_ok _ _ PA) as HBASE. pose proof pa_hi_ok_A as Hhi.
pose proof (@cf_head_nonneg cp) as Hhn.
assert (H176 : 176 <= ri_sp D) by lia.
destruct (re_R_range (ri_sp D) Hal16 H176) as (HR1 & HR2 & HR3).
pose proof HFO as (EfrB & HfreshB & EabB & HbbB & HzB & HflB & HfpB).
pose proof HBR as (R10 & R2 & R8 & R9 & R19 & R20 & R21 & R25 & R3 & R4).
pose proof HSD as (HLEDc & HRODc & HRLc & HPOSc & HTREEc & HCPYc & HMNc).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_pres HJ) as HPRc.
assert (Hin : In (RT_CID, pos) (frames S2)) by (rewrite EfrB; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HARc Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HARc Hin) as (F32 & _ & _ & _).
change (fs_frame_bytes RT_CID) with 128 in F2, F3. unfold in_app in F3.
assert (Hsh : 0 <= shadow_addr (frame_addr (ri_ly D) RT_CID pos) < 2 ^ 64)
  by (unfold shadow_addr, SHADOW_OFF in *; lia).
(* ---- E4: the run ---- *)
destruct (re_E4_entry (ri_regs D) (ri_ly D) S2 (ri_Hp D) (ri_W D) mem2 md2 pos rg (RT_R (ri_sp D)) HARc Hin HfpB
  ltac:(intros a Ha; apply HPRc; lia) ltac:(lia) ltac:(lia) HR2 R9 R10 R25) as [HS SHOK].
pose (PMN := fun m => YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS PMN)
  by exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (ri_mem D) (srr_inv_laws_memnorm_k SEGS)).
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS PMN PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
assert (HPM : PMN mem2) by exact HMNc.
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) rg [w64 (shadow_addr (frame_addr (ri_ly D) RT_CID pos))]))
  by apply te_env.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (0, 0).
{ cbv [ss_E4 ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (RT_R (ri_sp D) - ri_sp D));
    [reflexivity | | cbn; lia | cbn; lia |].
  { unfold xr. rewrite (te_cur (ri_regs D) rg _ 9%bv 9) by reflexivity. rewrite R9. unfold w64.
    rewrite unsigned_lit_small by lia. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 10) (frame_addr (ri_ly D) RT_CID pos)); [reflexivity | | |].
  { unfold xr. rewrite (te_cur (ri_regs D) rg _ 10%bv 10) by reflexivity. rewrite R10. unfold w64.
    apply unsigned_lit_small. lia. }
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists RT_CID, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes RT_CID) with 128. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 64%nat (shadow_addr (frame_addr (ri_ly D) RT_CID pos)));
    [reflexivity | | |].
  { rewrite (te_more_lt (ri_regs D) rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists RT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes RT_CID / 8) with 16.
    lia. }
  apply awr_ok_nil. }
pose proof (ajxR_ar HJ) as HARd. pose proof (ajxR_hi HJ) as HKCd.
assert (U9 : bv_unsigned (ew (TE (ri_regs D) rg [w64 (shadow_addr (frame_addr (ri_ly D) RT_CID pos))]) (xr 9))
  = RT_R (ri_sp D)).
{ unfold xr. rewrite (te_cur (ri_regs D) rg _ 9%bv 9) by reflexivity. rewrite R9. unfold w64.
  apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew (TE (ri_regs D) rg [w64 (shadow_addr (frame_addr (ri_ly D) RT_CID pos))]) (xr 10))
  = frame_addr (ri_ly D) RT_CID pos).
{ unfold xr. rewrite (te_cur (ri_regs D) rg _ 10%bv 10) by reflexivity. rewrite R10. unfold w64.
  apply unsigned_lit_small. lia. }
assert (U64 : bv_unsigned (ew (TE (ri_regs D) rg [w64 (shadow_addr (frame_addr (ri_ly D) RT_CID pos))]) 64)
  = shadow_addr (frame_addr (ri_ly D) RT_CID pos)).
{ rewrite (te_more_lt (ri_regs D) rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
(* the run's writes are E4's three regions *)
assert (KE4 : forall a, 0 <= a < 2 ^ 64 -> ~ re_E4_wr D pos a ->
  aview SEGS (w_H (ri_W D)) (ms_mem ms) a = aview SEGS (w_H (ri_W D)) mem2 a).
{ intros a Ha Hn.
  refine (ts_keep (ri_W D) (TE (ri_regs D) rg [w64 (shadow_addr (frame_addr (ri_ly D) RT_CID pos))])
    (ss_mem ss_E4) mem2 (ms_mem ms) (re_E4_wr D pos) HFr _ a Ha Hn).
  intros x (r & Hr & Hx). cbv [ss_E4 ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite ts_bv_some in Hx;
    unfold re_E4_wr; [rewrite U9 in Hx; left | rewrite U10 in Hx; right; left | rewrite U64 in Hx; right; right];
    lia. }
(* the side facts after E4 *)
assert (HSD4 : re_side D S2 (ms_mem ms)).
{ refine (re_side_keep D S2 S2 mem2 (ms_mem ms) _ HSD HCH HARd eq_refl (fun c p H => H)
    (fun c p H => ltac:(rewrite EfrB; right; exact H)) (fun H => H) (fun sm x os i H0 hist H => H) _ _ _ HPM).
  - intros a Hi _ _. pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
    apply KE4; [unfold kLowMemEnd in Hl; lia|]. intros Hw.
    exact (proj1 (re_E4_disj D S2 mem2 md2 pos a HARc EfrB HfreshB Hstk Hw) Hi).
  - intros p n i Hpn Hi.
    destruct (re_blk_ceil (ri_ly D) S2 (ri_Hp D) (ri_W D) mem2 md2 p n HARc Hpn) as (H4096 & Hce & Hgr & Hsh').
    apply KE4; [lia|]. intros Hw.
    exact (proj1 (proj2 (re_E4_disj D S2 mem2 md2 pos (p + i) HARc EfrB HfreshB Hstk Hw)) p n Hpn ltac:(lia)).
  - intros c p' a Hin' Ha.
    assert (Hin2 : In (c, p') (frames S2)) by (rewrite EfrB; right; exact Hin').
    destruct (re_frm_ceil (ri_ly D) S2 (ri_Hp D) (ri_W D) mem2 md2 c p' HARc Hin2) as (G4096 & Gce & Gal & Gsh).
    assert (Hr : 0 <= a < 2 ^ 64)
      by (destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha;
          unfold shadow_addr, SHADOW_OFF in *; lia).
    apply KE4; [exact Hr|]. intros Hw.
    destruct (proj2 (proj2 (re_E4_disj D S2 mem2 md2 pos a HARc EfrB HfreshB Hstk Hw)) c p' Hin') as (N1 & N2).
    destruct Ha as [Ha | Ha]; [exact (N1 Ha) | exact (N2 Ha)]. }
pose proof HSD4 as (HLED4 & HROD4 & HRL4 & HPOS4 & HTREE4 & HCPY4 & HMN4).
assert (HSV4 : re_saved D (ri_W D) (ms_mem ms)).
{ intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi. apply KE4; [lia|].
  unfold re_E4_wr, shadow_addr, SHADOW_OFF in *. lia. }
assert (HFL4 : rdword (aview SEGS (w_H (ri_W D)) (ms_mem ms)) (frame_addr (ri_ly D) RT_CID pos + RT_FLAGP)
  = Some (flag_addr (ri_ly D) RT_CID pos)).
{ rewrite <- HflB. apply ts_rdword_keep. intros j Hj. apply KE4; [unfold RT_FLAGP; lia|].
  unfold re_E4_wr, RT_FLAGP, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
(* the registers at the call *)
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by tskeep HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by tskeep HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by tskeep HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by tskeep HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by tskeep HS.
assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by tskeep HS.
assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by tskeep HS.
assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by tskeep HS.
assert (Z25 : getr (ms_regs ms) 25 = w64 (shadow_addr (frame_addr (ri_ly D) RT_CID pos))).
{ prreg HS (25%bv : bv 5) Q25. rewrite Q25. exact (te_more_lt (ri_regs D) rg _ 0 ltac:(lia)). }
assert (Z18 : getr (ms_regs ms) 18 = w64 (frame_addr (ri_ly D) RT_CID pos)).
{ prreg HS (18%bv : bv 5) Q18. rewrite Q18, <- R10. te_close. }
assert (Z26 : getr (ms_regs ms) 26 = w64 (frame_addr (ri_ly D) RT_CID pos)).
{ prreg HS (26%bv : bv 5) Q26. rewrite Q26, <- R10. te_close. }
assert (X10 : getr (ms_regs ms) 10 = w64 (ri_doc D)) by (rewrite Q10, <- R20; te_close).
assert (X11 : getr (ms_regs ms) 11 = w64 (ri_pretty D)) by (rewrite Q11, <- R21; te_close).
assert (Hspc : spZ (ms_regs ms) = ri_sp D + (RT_R (ri_sp D) - ri_sp D)).
{ unfold spZ. rewrite Z2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the frame chain at the call: s0 = sp0, the saved ra and s0 below it, the entry's chain above it *)
assert (HCH1 : exists ch1, achain (ri_ly D) (aview SEGS (w_H (ri_W D)) (ms_mem ms))
  (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) (s0Z (ms_regs ms)) ch1).
{ assert (Hs0 : s0Z (ms_regs ms) = ri_sp D).
  { unfold s0Z. rewrite Z8, R8. unfold w64. apply unsigned_lit_small. lia. }
  rewrite Hs0. destruct (Z_lt_le_dec (ri_sp D) (ly_top (ri_ly D) - 16)) as [Htl | Htl].
  - pose proof (HSV4 0%nat ltac:(lia)) as V0. pose proof (HSV4 1%nat ltac:(lia)) as V1.
    cbv [nth RTT_SAVED] in V0, V1.
    replace (ri_sp D - 8 * (Z.of_nat 0 + 1)) with (ri_sp D - 8) in V0 by lia.
    replace (ri_sp D - 8 * (Z.of_nat 1 + 1)) with (ri_sp D - 16) in V1 by lia.
    pose proof (bv_unsigned_in_range 64 (getr (ri_regs D) 1)) as Hr1.
    pose proof (bv_unsigned_in_range 64 (getr (ri_regs D) 8)) as Hr8.
    change (bv_modulus 64) with (2 ^ 64) in Hr1, Hr8.
    eexists. eapply (achain_push (ri_ly D) (aview SEGS (w_H (ri_W D)) (ri_mem D)) _ (ri_sp D) (s0Z (ri_regs D))
      (raZ (ri_regs D)) (ri_ch D) (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) Hch ltac:(lia)).
    + intros a Ha. apply HKCd; lia.
    + exact (re_rdword_of_vm SEGS (w_H (ri_W D)) (ms_mem ms) _ _ V0 Hr1).
    + exact (re_rdword_of_vm SEGS (w_H (ri_W D)) (ms_mem ms) _ _ V1 Hr8).
    + exact Hra4.
    + lia.
    + lia.
    + exact Htl.
    + lia.
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH1 as (ch1 & Hch1).
(* THE REQUEST BOUND AT THE CALL (the text owner's rule: library texts stand only where it is carried) *)
assert (HREQ : prh_most (ri_W D) (ms_mem ms) (ri_most D) /\ RQA_rtt (ri_t D) (ri_p D) <= ri_most D).
{ split; [|exact HRQA]. assert (HM := HLED4). eapply prh_ledger_most in HM. exact HM. }
assert (HBD := HLED4). eapply prh_ledger_bounds in HBD. destruct HBD as (_ & _ & (HC0 & _) & _).
(* pj_write's run premise: rtt_pre's run starts with the model's w_evs, which is pj_write's list at cf_head = HEAD *)
assert (HRUN' : prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D)
  (PRH_FnWriter.prhWriter_pjw_evs [] (ri_cnt D) SIZE_MAXZ (WriterValue.wdpieces (ri_t D) (ri_p D)))).
{ rewrite (PRH_Supply.prhWriter_pjw_evs_w_evs (ri_t D) (ri_p D) (ri_cnt D) SIZE_MAXZ HHEAD ltac:(lia)
    (re_cnt_ne (ri_t D) (ri_p D) (ri_cnt D) ltac:(lia) HWL)).
  unfold ck_rtt_evs, PresetReqAt.rt_text in HRUN. rewrite <- app_assoc in HRUN.
  apply prh_run_at_app_iff in HRUN. exact (proj1 HRUN). }
(* the call's consumer window: rtt_pre's window over ck_rtt_evs starts with pj_write's w_evs *)
assert (HCONS' : prh_cons_from ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D)
  (length (PRH_FnWriter.prhWriter_pjw_evs [] (ri_cnt D) SIZE_MAXZ (WriterValue.wdpieces (ri_t D) (ri_p D))))).
{ rewrite (PRH_Supply.prhWriter_pjw_evs_w_evs (ri_t D) (ri_p D) (ri_cnt D) SIZE_MAXZ HHEAD ltac:(lia)
    (re_cnt_ne (ri_t D) (ri_p D) (ri_cnt D) ltac:(lia) HWL)).
  unfold ck_rtt_evs, PresetReqAt.rt_text in HCONS. rewrite <- app_assoc, length_app in HCONS.
  apply prh_cons_from_app_iff in HCONS. exact (proj1 HCONS). }
destruct HPOS4 as (hist0 & Hip0). rewrite Nat.add_0_r in Hip0.
pose proof HTREE4 as (HND4 & HDL4 & HVIS4 & (Hm8 & (hcid & hpos & Hhin & Hhlo & Hhhi) & HRA4)).
(* the jal's return pc, +304 (DERIVED: RE_PC + RT_PJW = 13500), inside the image's low band *)
assert (HBs : 0 <= BASE + 13500 < 2 ^ 31) by (split; vm_compute; [intros Hc; discriminate Hc | reflexivity]).
assert (Hra1 : raZ (ms_regs ms) = BASE + 13500).
{ unfold raZ. rewrite Q1. apply unsigned_lit_small. lia. }
(* pj_write's fpre beyond afn_pre_x, and its tree's home, at the call state *)
assert (HSPHI1 : spZ (ms_regs ms) + 64 <= ly_stk_hi (ri_ly D)) by (rewrite Hspc; lia).
assert (HRAC1 : raZ (ms_regs ms) < YM05.alloc_ceiling) by (rewrite Hra1; lia).
assert (HhinS2 : In (hcid, hpos) (frames S2)) by (rewrite EfrB; right; exact Hhin).
(* pj_write's bounds at the call, each from rtt_pre *)
assert (HPR31 : 0 <= ri_pretty D < 2 ^ 31) by lia.
assert (HDEPN : (PjTree.depth (ri_t D) <= DOC_D)%nat) by (unfold DOC_D, PjGrammar.MAXD; lia).
assert (HDEP31 : Z.of_nat (PjTree.depth (ri_t D)) <= 2 ^ 31 - 1) by lia.
assert (HFR0 : Z.of_nat (length (frames S2)) < fs_frames 0).
{ rewrite EfrB. cbn [length].
  assert (E29 : ck_FRAMES_CAP - FR_round_trip_text = 29) by (vm_compute; reflexivity).
  assert (Hf0 : 30 < fs_frames 0) by (vm_compute; reflexivity). lia. }
assert (HWMAX : Z.of_nat (length (WriterValue.wdoc (ri_t D) (ri_p D))) + 1 <= PRH_FnWriter.prhWriter_WMAX)
  by (unfold PRH_FnWriter.prhWriter_WMAX; unfold PjWriteHyp.wlen in HWL; exact HWL).
assert (HWH : PRH_FnWriter.prhWriter_WMAX + cf_head < cf_malloc_max)
  by (unfold RQ_rtt, zmaxl in HRQ; cbn [fold_right] in HRQ; lia).
assert (HLV2 : blocks_bytes S2 + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) <= LIVE_MAX)
  by (rewrite HbbB; pose proof (re_live_pjw_le (ri_t D) (ri_p D)); lia).
(* ---- the call (YCbqGcall.aj_call_xF_spR at RZW: the caller's journal, pj_write's post and the continuation at RZW) ---- *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (aj_call_xF_spR SEGS B PST ARx LAWS pa_segs_low RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) (ri_W D) _ _ ms STKR (ri_sp D) (ri_FP D) (ri_ly D)
    (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] (ri_ly D) S2 (ri_Hp D) _ _
    (@STK_pj_write prh_img_A DOC_D) [] (RT_R (ri_sp D) - ri_sp D) (getr (ms_regs ms) 1) ch1 _ HS eq_refl HJ Hspc).
  - lia.
  - lia.
  - exact HSTKW0.
  - lia.
  - rewrite Z3. exact R3.
  - rewrite Z4. exact R4.
  - reflexivity.
  - rewrite Q1. apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - change (bv_unsigned (getr (ms_regs ms) 1)) with (raZ (ms_regs ms)). rewrite Hra1. lia.
  - exact Hch1.
  - intros HPRE1.
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
      replace (ss_pc s) with (SIGMA AS_pj_write) by (vm_compute; reflexivity) end.
    (* THE ACTUALS of pj_write's prh_oks (PRH_FnWriter.v:816-817, `prh_oks ok cnt fail (prhWriter_k ..)
       (prhWriter_reqs ..) most ran ran'`, its binders at :775-776): most := ri_most D (round_trip_text's g_most, the
       ledger field of its own prh_ledger), own := 0, cnt := ri_cnt D, fail := SIZE_MAXZ, ran := ri_ran D (g_ran_out at
       entry, = 0 by the text's `ran = 0`), ran' := pj_write's post binder (g_ran_out after the call); re_pjw_out reads
       them in that order (prh_oks .. (ri_most D) (ri_ran D) ran'). The run's call bound `(length rp_os <= 4)%nat` is
       rtt_pre's 29th conjunct (HOS4, Rtt102Cut.rtt_pre_os4) *)
    exact (TPJW fx (ri_x D) (ri_os D) (ri_i D) (ri_H0 D) hist0 (ri_most D) 0 (ri_ly D) S2 (ri_Hp D)
      (ri_W D) (ms_regs ms) (ms_mem ms) _ ch1 (ri_doc D) (ri_pretty D) (ri_t D) (ri_D D) (ri_Lam D) (ri_peak D)
      (ri_cnt D) SIZE_MAXZ (ri_ran D)
      (conj HPRE1 (conj HROD4 (conj HSPHI1 (conj HRAC1 HFRM0))))
      HUC HRL4 Hip0 HOS4 HCONS' X10 X11 HPR31 HLED4 HRUN' HND4
      (or_intror (or_intror (ex_intro _ hcid (ex_intro _ hpos
        (conj HhinS2 (conj Hhlo Hhhi))))))
      HRA4 HVIS4 (fun a kk Hk => HDL4 (a, kk) Hk) HDEPN HDEP31 HFR0 HWMAX HWH HLV2).
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (fx' & ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & -> & HFZ & HFK & HJ3 & HJ1 & HP3 & HQ3).
destruct HQ3 as (HQ & HMN3). cbv beta zeta in HQ.
destruct HQ as (ok & ran' & q & Lam' & peak' & HOKS & H10q & HRL3 & HGR & HPOS3 & HND3 & HVIS3 & HLED3 & HOUT).
pose proof (ajxR_ar HJ1) as HAR3. pose proof (ajxR_ly HJ1) as HLY3. pose proof (ajxR_frs HJ1) as HFR3.
pose proof (ajxR_hi HJ1) as HKC3. pose proof (ajxR_img HJ1) as HKI3. pose proof (ajxR_frm HJ1) as HKF3.
(* E's journal from the entry at RT_PJW: the cut's depot-moved journal, and no fresh wild trace (neither callee
   stores one) *)
pose proof (re_J_of_AJ D ly3 S3 Hp3 W3 mem3 md3 _ pos HJ3) as HJ3c.
assert (HWK : forall n, re_wild D S3 n) by (intros n; exact (re_wild_of_AJ D n ly3 S3 Hp3 W3 mem3 md3 _ pos HJ3)).
assert (ELF : ly_F ly3 = ly_F (ri_ly D)) by (destruct HLY3 as (_ & _ & _ & _ & _ & E6 & _); exact E6).
assert (EFA : frame_addr ly3 RT_CID pos = frame_addr (ri_ly D) RT_CID pos)
  by (unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly3 RT_CID pos = flag_addr (ri_ly D) RT_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
assert (PB3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms) r).
{ intros r Hr. pose proof (HP3 _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
destruct (re_pjw_out D S2 ly3 S3 W3 mem3 ok ran' q Lam' peak' _ (conj HC0 HCNT) HWL EabB HOKS HGR HOUT)
  as (HPK & HFAIL & (wab & HWO & HPERM) & HBYT & HBB).
(* return to the cut *)
rewrite Q1. change (BASE + 13500) with (BASE + (RE_PC + RT_PJW)). rewrite RE_PJW_val.
refine (KONT fx' ly3 S3 Hp3 W3 regs3 mem3 md3 _ pos _).
split.
{ (* the carry *)
  split; [split; [exact HFZ | exact HFK]|].
  split; [exact HJ3c|].
  split.
  { unfold re_frame. rewrite EFA, EFL.
    split; [rewrite HFR3, app_nil_l; exact EfrB|]. split; [exact HfreshB|]. split.
    - rewrite <- HFL4. apply ts_rdword_keep. intros j Hj.
      apply (HKF3 RT_CID pos _ Hin); [|apply inFP_nil].
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes RT_CID) with 128. unfold RT_FLAGP. lia.
    - intros a Ha. assert (Hin3 : In (RT_CID, pos) (frames S3)) by (rewrite HFR3; exact Hin).
      destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR3 Hin3) as (_ & _ & Hpr & _).
      rewrite EFA in Hpr. exact (proj1 (Hpr a Ha)). }
  split.
  { intros j Hj. eapply ts_vm_av; [|exact (HSV4 j Hj)]. intros i Hi. apply HKC3; lia. }
  split.
  { unfold re_cregs. cbv zeta. rewrite EFA.
    split; [rewrite (PB3 2%bv ltac:(ts_cs)), Z2; exact R2|].
    split; [rewrite (PB3 8%bv ltac:(ts_cs)), Z8; exact R8|].
    split; [rewrite (PB3 9%bv ltac:(ts_cs)), Z9; exact R9|].
    split; [rewrite (PB3 18%bv ltac:(ts_cs)); exact Z18|].
    split; [rewrite (PB3 19%bv ltac:(ts_cs)), Z19; exact R19|].
    split; [rewrite (PB3 20%bv ltac:(ts_cs)), Z20; exact R20|].
    split; [rewrite (PB3 25%bv ltac:(ts_cs)); exact Z25|].
    split; [rewrite (PB3 26%bv ltac:(ts_cs)); exact Z26|].
    split; [rewrite (PB3 3%bv ltac:(ts_cs)), Z3; exact R3 | rewrite (PB3 4%bv ltac:(ts_cs)), Z4; exact R4]. }
  split; [intros H0; exact (HMN3 (HPM H0))|].
  split.
  { intros a Hro Hno Her.
    assert (Hfs : fp_spares [] a) by (apply fp_spares_closed; intros (r & Hr & _); destruct Hr).
    rewrite (HKI3 a (re_ro_img a Hro) Hno Her (fun Hp => pst_ro_A a Hp Hro) Hfs).
    exact (HROD4 a Hro Hno Her). }
  split; [exact HRL3|].
  split; [exact HND3 | split; [exact HVIS3 | exact (HWK _)]]. }
split; [rewrite (PB3 21%bv ltac:(ts_cs)), Z21; exact R21|].
split.
{ intros Hc0 a Ha. rewrite <- (HCPY4 Hc0 a Ha). destruct (HCH Hc0) as (cid & pos' & Hin' & Hlo & Hhi').
  apply (HKF3 cid pos' a ltac:(rewrite EfrB; right; exact Hin')); [|apply inFP_nil].
  left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
exists q, Lam', peak', (WriterApp.w_cnt (re_st D ok)), ran', wab.
split; [exact H10q|].
split.
{ split; [|exact HPK]. unfold re_st, re_P, ri_p in HFAIL. rewrite HFAIL in HLED3. exact HLED3. }
split; [exact HWO|].
split; [exact HPERM|].
split; [exact HBYT|].
split; [exact HBB|].
split; [|exact (HWK 0%nat)].
destruct (HPOS3 HGR) as (hist' & Hip'). exists hist'.
assert (EV : length (PRH_FnWriter.prhWriter_pjw_evs ok (ri_cnt D) SIZE_MAXZ
              (WriterValue.wdpieces (ri_t D) (negb (ri_pretty D =? 0)))) = RT_K_W D).
{ rewrite (PRH_Supply.prhWriter_pjw_evs_granted (WriterValue.wdpieces (ri_t D) (negb (ri_pretty D =? 0))) ok
    (ri_cnt D) SIZE_MAXZ HC0 ltac:(unfold SIZE_MAXZ; lia) HGR).
  exact (f_equal (@length _) (PRH_Supply.prhWriter_pjw_evs_w_evs (ri_t D) (ri_p D) (ri_cnt D) SIZE_MAXZ HHEAD
    ltac:(lia) (re_cnt_ne (ri_t D) (ri_p D) (ri_cnt D) ltac:(lia) HWL))). }
rewrite EV in Hip'. exact Hip'.
Unshelve. all: first [exact HSTK_A | exact LAWS | exact pst_img_A | exact pal_pst_static | exact 0].
Qed.

(* ======================================================================================================== *)
(* ---- THE STRETCH: entry -> RT_PJW, UNCONDITIONAL (Rtt102Cut.RTT_SEG_E at image A'). pj_write's dead refusal arm
   comes from its own text (TPJW, the cut's tpj_write_specX, K0-DEAD-PJWRITE), so no withheld fact is left. The
   entry facts the side carry starts from are rtt_pre's own ---- *)
Theorem rtt_seg_e_A : @RTT_SEG_E fx rc ci cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK CTX0.
Proof.
intros HSEG D HPRE.
pose proof HPRE as HPRE'. unfold rtt_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFPRE & HMN0 & HUC & HCTX & H10 & H11 & H12 & HP01 & HD0 & HTREE0 & HWF & HDEP & HWL & HCPY
  & HLED0 & HCNT & HRUN & HRAN & HRQA & HLIVE & HRQ & HFRL & HRL0 & HIRP & HFRM0 & HWR & HCONS & _).
assert (HCH : re_copy_home D).
{ intros Hc0. destruct HCPY as [E0 | (_ & _ & (HIF & _) & _)]; [contradiction | exact HIF]. }
assert (HSIDE : re_side D (ri_S D) (ri_mem D)).
{ split; [exact HLED0|]. split; [exact (proj1 (proj2 HFPRE))|]. split; [exact HRL0|].
  split; [exists (ri_hist D); rewrite Nat.add_0_r; exact HIRP|]. split; [exact HTREE0|].
  split; [intros _ a _; reflexivity | intros H; exact H]. }
refine (re_entry D _ (ri_ch D) HFPRE HSIDE HCH (rtt_capacity_of_len _ HFRL) H10 H11 H12 _).
intros S2 mem2 md2 rg kj pos HJ HSD HSV HFO HBR.
refine (re_at_B D _ S2 mem2 md2 rg kj pos HPRE HCH HJ HSD HSV HFO HBR _).
intros fxc ly S Hp W regs mem md k pos' HAT.
exact (HSEG D HPRE fxc ly S Hp W regs mem md k pos' HAT).
Qed.
Print Assumptions rtt_seg_e_A.

End f.
End e.

(* ---- THE FPState ELABORATION CHECK (the text owner's 17:1xZ rule), checked in so it re-runs on every build. The
   copies re_fx / re_carry / re_at_pjw bind a second FPState fxc beside the contract's entry state; after the
   Section closes their entry state is an explicit (generalised) argument, and the BODIES must read it - not fxc.
   Expected in the printed bodies: `fregs_kept_x fx fxc` (re_fx) and `re_fx fx fxc` / `@re_fx fx fxc` (re_carry);
   NOT `fregs_kept_x fxc fxc`. The cut's rtt_fx / rtt_carry are printed beside them for comparison. ---- *)
(* the amended form (the RTT layer reviewer, relayed 17:5xZ): implicits ON, notations OFF, and `Print` - not `About` /
   `Check`, which show only the type - for every Prop-valued definition, so a second FPState hidden in a body
   is visible *)
Set Printing Implicit. Unset Printing Notations.
Print re_fx. Print re_carry. Print re_at_pjw.
Print rtt_fx. Print rtt_carry. Print rtt_at_pjw.
(* the proof-context variant (the text owner, relayed by WalkRtt102): the lemmas whose statement binds a second
   FPState (re_at_B's continuation binds fxc; the stretch's rtt_seg binds fxc) are printed as elaborated
   statements. The two proof-context sites that bring a later FPState into a context - re_at_B's fx' from
   aj_call_xF_spR's post and rtt_seg_e_A's fxc from the cut's continuation - state no assert / have
   with an implicit FPState after it: fx' is passed explicitly (KONT fx') and the float facts HFZ / HFK are
   matched by `exact` against re_fx's body, whose entry state is the Section's fx *)
Check @re_at_B. Check @rtt_seg_e_A.
Set Printing Notations. Unset Printing Implicit.

(* ---- THE INSTANCE WITNESS of the Section hypothesis HHEAD, closed at the real instance (the unit's
   instance-witness rule): CfParams_preset is a Definition, not an Instance (CfParamsPreset.v:4), so requiring it
   cannot change any inference above ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
Example hhead_preset : @cf_head CfParamsPreset.CfParams_preset = PresetReqAt.HEAD := eq_refl.

(* the top theorem with every Section hypothesis discharged into its statement: only Rocq primitives may appear *)
Print Assumptions rtt_seg_e_A.
