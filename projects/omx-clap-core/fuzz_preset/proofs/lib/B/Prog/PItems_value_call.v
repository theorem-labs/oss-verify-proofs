(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 1116 of its 1156 lines of code are new or changed and 156 lines of the source are left out. *)
(* Theorem Labs, 2026-10: segment VALUE of parse_items' image-B walk, the CALL block (rebound to the kit's
   a Theorem Labs lane, prover PvCall2; the batch kit's rebind PItemsB.K1Value). Proves no function (kind: segment lemma).
     pv_call_holds : forall N, pv_aftv_spec B ARx SK d CTX0 CW N -> pv_call_spec B ARx SK d CTX0 CW N
   (PItems_value_pres.v), at prh_img_B / B_prog_listing / PI_prog_B / PL_prog_B.
   The block is one instruction, PI_O_PVAL `jal parse_value`, with its return site PI_O_AFTV. parse_value's text is
   the batch kit's tparse_value_specX at S d (lib/A/PRH_FnParse.v ed236011cf99, the batch kit 240b06ed4fd4; Section hypothesis PV,
   the text's own): it takes the cursor set CW, prh_cw_entry, wild_room and the hull budget over its all-granted events
   at the call, and concludes YA0nH.SRr' pa_segs RZ_cf in the BUDGETED m-form window-float post fpostWFbm (wbudget CW 0)
   .. (fQmn mem Q), at wle'; Q is the text's tpvP_Q, read through tpvP_R_of and its fields. The specs take the journal at
   the walk's relation wle' pa_segs RZ_cf (pi_ajR) and conclude pi_goalR there, so the call rule is YCbqGwild.v
   aj_call_xWFb_spR at wle', under SRr'_bind, from the caller's journal at its budget WS0 (rebased for the jal's run,
   ajournal_xw_rebaseR, back by ajournal_xw_unbase0R), with
   STK1 = STK_parse_value (S d), e1 = e + 144, o = -(144 + e) below the journal's sp spZ regs0 + e, FP1 = rd_fp q slot,
   slot = pv_slot kids n; STK_parse_items d = 144 + STK_parse_value (S d) (pvc_stk). After it the caller's journal is
   at WS0 ++ WS1 with wbudget CW 0 (WS0's and parse_value's at the same CW: YCbqGwild.wbudget_app). The text's
   premises at the call: memnorm from pv_call_pre's travelling fact (the jal writes no memory); fpre's frm_zero from
   pi_fpok; the two live counts over prhPv_gtrace (S d) from pi_ent's over prhPi_gtrace d at the block's pi_live
   (PItems_value_model.v pvm_lc_call, the value's granted trace being the head of pi_val_k's: pvm_gt_split);
   prh_cw_entry at the call registers from pi_ent's (the word a cursor free reads at q - 8 / q + 8 is the entry's,
   XW); wild_room from pi_ent's across the prefix's journal (YCbqGwild.ajournal_xw_roomR, no fresh slot used); THE
   HULL BUDGET from pi_ent's over prhPi_gtrace d, split at the value as tr0 ++ the value's ++ the rest (HGTI), less the
   prefix's use (PItems_posb.pi_posb_budget). After it, pv_aftv_pre's memnorm is the m-form keep, its position and
   pi_live over tr0 ++ tr are the callee's position implication and live-request permutation composed on the block's
   (as PItems_posb.pi_posb_call / pi_live_call), and its hull use is per outcome: read, the value's all-granted list
   is its trace (pvm_granted_some), so the use extends over tr (PresetHullBudget.hull_used_app); refused, the post's
   use over the whole call's all-granted list (PItems_posb.pi_posb_hull_call).
   THE BATCH KIT PRE AFTER THE CALL (PItems_value_pres.v pv_aftv_pre): the ledger over the whole call's granted trace
   prhPi_gtrace = tr0 ++ the value's granted trace ++ the rest (pvm_gt_grant under pi_grant, pvm_gt_split), composed by
   pvm_ledger_app (the callee's move normalised to its consumed outcomes, pvc_move_agree); pi_ncaps / pi_forder across
   the call (pvm_ncaps_frame / pvm_forder_frame on the bytes the callee kept); the key's tie as before; per outcome:
   Some - pi_grant (the value's outcomes all granted, pvm_some_granted), the kid's pj_ncapR and ordered tie (parse_value's
   Some arm), the model pv_jfk from pi_fl_eqV past the value (the value's free list jfv at the normalised outcomes is
   prhPv_frees at the callee's own: pvm_jfv_det, PresetFreeFo.jfv_fuel); None - the post's OUTCOME clause from the
   refused value's own outcome clause at the position pi_posb names, under the run's split (prh_run_at_app_iff,
   prh_cons_from_sub) and the prefix's unchanged failure window (so the value's granted run refused too: the whole
   granted run is tr0 then that refusal), THE INJECTED READING (the post's clause at ok0 ++ okn / tr0 ++ tr: the prefix
   granted all, so the chosen failure is at or past its calls and the model's grant list there is ok0 then okk shifted
   by them; inside the value's window the value's own tpvP_injected, past it a contradiction by the value's OUTCOME),
   the partial kid's ordered tie, and the model (af ++ fv ++ lk) ++ arrz o cap.
   The callee's chain premises are PROVED here, not carried: its entry chain at the call view from s0 = q + 16 (one
   record, the cursor's end word over its p word, which lies below alloc_ceiling, so the chain stops: pvc_achain16);
   the cursor's chain-stop word (prh_cur_entry's sp - 16 arm) from the entry's; the partitioned cursor chain's right
   arm from prh_s0 F_parse_string q = q (pvc_achainq: the word at q - 16 is below alloc_ceiling by prh_cur_entry).
   No UBSan check and no shadow-check branch in this block (one jal; the brief's REPORT SITES).
   NUMERALS: no ADDRESS (PVC_K is computed from the listing's symbols B_prog_sigma AS_parse_items, A_TEXT and the
   offset PI_O_PVAL). LENGTH: 144 (the frame), 136 .. 40 (the frame's save slots), 32 .. 8 (pi_regs_body's cached
   slots), 24 (the cursor), 20, 16, 8 (the cursor's words, a frame record), 56 (a pj_value node), 4 (the jal).
   WORD: 4096 (the smallest chain return address, YG00.v fpchain), 0 and -1 (the result). DERIVED: 2 ^ 47, 2 ^ 64,
   and the fuel / count / peak arithmetic (1, 2, 3, 224, 512 from the kit's bounds). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres
PItems_value_pres PItems_value_model PItems_kept PItems_shape S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_ledk1.
(* the walk's world relation wle' pa_segs RZ_cf (YA0nH) and the bind over it (YSRrG); the hull budget and use *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).

(* ---- the block: one instruction, `jal parse_value` at PI_O_PVAL; its return site is PI_O_AFTV = PI_O_PVAL + 4 ---- *)
Definition PVC_K : Z := Eval vm_compute in (B_prog_sigma AS_parse_items - B_prog_val A_TEXT + PI_O_PVAL).
Definition ss_pvc : sstate := mkSS PVC_K sr_atoms [] None (mkFacts [] [] []).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pvc_st : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (@Eimg _ B_prog_listing PA (Ereg regs [])) ss_pvc
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PVC_K)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_pvc. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn. exact I.
Qed.
End e.

(* ================================================================================================== *)
(* pure helpers *)
Lemma pvc_fregs_trans : forall f0 f1 f2 : YK11.FPState, fregs_kept_x f0 f1 -> fregs_kept_x f1 f2 -> fregs_kept_x f0 f2.
Proof. intros f0 f1 f2 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* THE CURSOR'S p WORD AT THE CALL (0x87d94) below alloc_ceiling, which the kit's prh_cur_entry asks at F_parse_items
   (B: prh_s0 = q + 16, so the word at q): the cursor never passes the text's end, and the kit's rd_pre (fix (a) of
   02:44Z) bounds the text strictly below the ceiling *)
Section cl. Context {rc : YM05.RunCeil}.
Lemma pvc_cur_low : forall text len p, p <= text + len -> text + len < YM05.alloc_ceiling -> p < YM05.alloc_ceiling.
Proof. intros text len p H1 H2. lia. Qed.
End cl.

(* the batch kit ledger move (PRH_FnParse.v rd_ledger_move: prh_oks with g_most, the refusal peak over the granted trace gt)
   reads the outcome list only at the trace's own calls *)
Lemma pvc_move_agree : forall Lam peak cnt fail ran most (ok ok' : list bool) gt tr D Lam' peak' cnt' fail' ran',
  (forall i, (i < PjGrammar.calls tr)%nat -> nth i ok' true = nth i ok true) ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' ->
  rd_ledger_move Lam peak cnt fail ran most ok' gt tr D Lam' peak' cnt' fail' ran'.
Proof.
intros Lam peak cnt fail ran most ok ok' gt tr D Lam' peak' cnt' fail' ran' E ((O1 & O2 & O3) & C & F & P & S1 & N & K).
assert (RE : forall i, (i < PjGrammar.calls tr)%nat -> prh_refused ok' cnt fail i = prh_refused ok cnt fail i)
  by (intros i Hi; unfold prh_refused; rewrite (E i Hi); reflexivity).
split; [split; [|split]|].
- intros i Hi Hf. rewrite (E i Hi). exact (O1 i Hi Hf).
- destruct O2 as [O2 | (O2 & i & Hi & Hn & Hf)]; [left; exact O2 | right; split; [exact O2|]].
  exists i. split; [exact Hi|]. rewrite (RE i Hi). split; [exact Hn | exact Hf].
- intros i Hi Hn Hf. rewrite (RE i Hi) in Hn. exact (O3 i Hi Hn Hf).
- split; [exact C|]. split; [exact F|]. split; [exact P|]. split; [exact S1|]. split; [exact N|].
  rewrite K. f_equal. unfold prh_refused_peak. f_equal. apply map_ext_in. intros i Hi.
  apply List.in_seq in Hi. rewrite (RE i ltac:(lia)). reflexivity.
Qed.

Lemma pvc_rest_suffix : forall (tb : list Z) text len pc pre r,
  Z.of_nat (length tb) = len -> text <= pc <= text + len ->
  rest_atR tb text pc = pre ++ r -> rest_atR tb text (text + len - Z.of_nat (length r)) = r.
Proof.
intros tb text len pc pre r Hl Hp E. unfold rest_atR in *.
set (k := Z.to_nat (pc - text)) in E.
assert (Ht : tb = (firstn k tb ++ pre) ++ r) by (rewrite <- app_assoc, <- E; symmetry; apply firstn_skipn).
assert (HL : length tb = (length (firstn k tb ++ pre) + length r)%nat)
  by (rewrite Ht at 1; rewrite length_app; reflexivity).
replace (Z.to_nat (text + len - Z.of_nat (length r) - text)) with (length (firstn k tb ++ pre)) by lia.
rewrite Ht at 2. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

(* the callee's footprint rd_fp q sl, byte by byte *)
Lemma pvc_notfp : forall q sl x, ~ (q <= x < q + 8) -> ~ (q + 16 <= x < q + 20) -> ~ (sl <= x < sl + 56) ->
  ~ inFP (rd_fp q sl) x.
Proof.
intros q sl x H1 H2 H3 (r0 & Hin & Hr). destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
  [apply H1 | apply H2 | apply H3]; lia.
Qed.
Lemma pvc_notfp2 : forall q v sl x, ~ inFP (rd_fp q v) x -> ~ (sl <= x < sl + 56) -> ~ inFP (rd_fp q sl) x.
Proof.
intros q v sl x Hn Hs (r0 & Hin & Hr). destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
- apply Hn. exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
- apply Hn. exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
- apply Hs. lia.
Qed.
(* a shadow byte of an address below 2^47 is in the shadow gap: below the high memory and above the low memory *)
Section c00. Context {rc : YM05.RunCeil}.
Lemma pvc_shadow_notfp : forall q sl a, 0 <= a < 2 ^ 47 -> kHighMemBeg <= q -> in_app sl 56 ->
  ~ inFP (rd_fp q sl) (shadow_of_addr SHADOW_OFF a).
Proof.
intros q sl a Ha Hq Hs (r0 & Hin & Hr).
unfold shadow_of_addr, in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
Qed.
End c00.
(* NoDup is stdpp's (the ledger's); the list lemmas are Stdlib's List.NoDup ones, through NoDup_ListNoDup *)
Lemma pvc_nodup_sep : forall (l1 l2 : list (Z * Z)) x, NoDup (map fst (l1 ++ l2)) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x H. apply NoDup_ListNoDup in H. revert H.
induction l1 as [|b l1 IH]; intros H H1 H2; [destruct H1|].
cbn [app map] in H. apply List.NoDup_cons_iff in H as (Hn & Hd).
destruct H1 as [<- | H1].
- apply Hn. rewrite map_app. apply in_or_app. right. apply in_map. exact H2.
- exact (IH Hd H1 H2).
Qed.
Lemma pvc_nodup_app_l : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
intros A l l' H. induction l as [|a l IH]; [constructor|]. cbn [app] in H.
apply List.NoDup_cons_iff in H as (Hn & Hd).
constructor; [intros Hi; apply Hn; apply in_or_app; left; exact Hi | exact (IH Hd)].
Qed.

Section c0. Context {rc : YM05.RunCeil}.

(* the frame chain from s0 = q + 16 (parse_items' s0 at the call): its first record is the cursor's end word (a data
   word of the run, at least 4096) over the cursor's p word, which lies below q + 16, so the chain stops there *)
Lemma pvc_achain16 : forall ly (rd : reader) sp q w0 w8,
  rdword rd q = Some w0 -> rdword rd (q + 8) = Some w8 -> 4096 <= w8 -> w0 <= q + 16 -> sp + 16 <= q + 16 ->
  exists ch, achain ly rd sp (q + 16) ch.
Proof.
intros ly rd sp q w0 w8 H0 H8 Hw8 Hw0 Hsp.
destruct (Z_lt_le_dec (q + 16) YM05.alloc_ceiling) as [Hc|Hc]; [exists []; left; split; [left; exact Hc | reflexivity]|].
destruct (Z_le_gt_dec (ly_top ly - 16) (q + 16)) as [Ht|Ht]; [exists []; left; split; [right; left; exact Ht | reflexivity]|].
destruct (Z.eq_dec ((q + 16) mod 8) 0) as [Hm|Hm]; [|exists []; left; split; [right; right; exact Hm | reflexivity]].
exists [(q + 16, w8, w0)]. right. split; [exact Hsp|]. split; [lia|]. split; [exact Hm|]. split.
- cbn [fpchain]. split; [reflexivity|]. split; [exact Hm|].
  replace (q + 16 - 8) with (q + 8) by lia. replace (q + 16 - 16) with q by lia.
  split; [exact H8|]. split; [exact H0|]. split; [exact Hw8|].
  unfold bad_next. replace (w0 <=? q + 16) with true by (symmetry; apply Z.leb_le; exact Hw0). exact eq_refl.
- constructor; [cbn; lia | constructor].
Qed.

(* the frame chain from q (parse_string's s0 = prh_s0 F_parse_string q): one record at most, its next word below q *)
Lemma pvc_achainq : forall ly (rd : reader) sp q w8 w16,
  rdword rd (q - 8) = Some w8 -> 0 <= w8 -> rdword rd (q - 16) = Some w16 -> w16 <= q -> sp + 16 <= q ->
  exists ch, achain ly rd sp q ch.
Proof.
intros ly rd sp q w8 w16 H8 Hw8 H16 Hw16 Hsp.
destruct (Z_lt_le_dec q YM05.alloc_ceiling) as [Hc|Hc]; [exists []; left; split; [left; exact Hc | reflexivity]|].
destruct (Z_le_gt_dec (ly_top ly - 16) q) as [Ht|Ht]; [exists []; left; split; [right; left; exact Ht | reflexivity]|].
destruct (Z.eq_dec (q mod 8) 0) as [Hm|Hm]; [|exists []; left; split; [right; right; exact Hm | reflexivity]].
destruct (Z_lt_le_dec w8 4096) as [Hs|Hs].
- exists []. right. split; [exact Hsp|]. split; [lia|]. split; [exact Hm|].
  split; [cbn [fpchain]; exists w8; split; [exact H8 | lia] | constructor].
- exists [(q, w8, w16)]. right. split; [exact Hsp|]. split; [lia|]. split; [exact Hm|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hm|].
    split; [exact H8|]. split; [exact H16|]. split; [exact Hs|].
    unfold bad_next. replace (w16 <=? q) with true by (symmetry; apply Z.leb_le; exact Hw16). exact eq_refl.
  + constructor; [cbn; lia | constructor].
Qed.

Lemma pvc_rdword_some : forall (rd : reader) a,
  (forall k, 0 <= k < 8 -> exists b, rd (a + k) = Some b /\ 0 <= b) -> exists w, rdword rd a = Some w /\ 0 <= w.
Proof.
intros rd a H.
destruct (H 0 ltac:(lia)) as (b0 & E0 & P0). destruct (H 1 ltac:(lia)) as (b1 & E1 & P1).
destruct (H 2 ltac:(lia)) as (b2 & E2 & P2). destruct (H 3 ltac:(lia)) as (b3 & E3 & P3).
destruct (H 4 ltac:(lia)) as (b4 & E4 & P4). destruct (H 5 ltac:(lia)) as (b5 & E5 & P5).
destruct (H 6 ltac:(lia)) as (b6 & E6 & P6). destruct (H 7 ltac:(lia)) as (b7 & E7 & P7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7.
eexists. split; [reflexivity | lia].
Qed.

End c0.

Section c1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma pvc_aview_present : forall segs H (m : word -> option byte) a,
  apresent H m a -> exists b, aview segs H m a = Some b /\ 0 <= b.
Proof.
intros segs H m a [Hh [b Hb]]. exists (bv_unsigned b). split.
- unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
- pose proof (bv_unsigned_in_range _ b). lia.
Qed.

Lemma pvc_rdword_of_val : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* a byte outside the image that two views read alike is the same byte, and stays writable, in the restricted memories *)
Lemma pvc_same : forall (H H' : word -> bool) (m m' : word -> option byte) x,
  0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  aview SEGS H' m' x = aview SEGS H m x -> pis_same SEGS (mrestrict H m) (mrestrict H' m') x.
Proof.
intros H H' m m' x Hx Hn E. pose proof (mbyte_of_aview SEGS H H' m m' x E) as Em. split; [exact Em|].
intros Hw. unfold writable_at in *.
assert (Hf : find_segment SEGS (bv_unsigned (Z_to_bv 64 x)) 1 = None)
  by (rewrite unsigned_lit_small by lia; exact (find_segment_none SEGS x Hn)).
unfold mbyte in Em. rewrite (seg_rom_none SEGS x Hx Hn) in Em.
unfold wview in *. rewrite Hf in *.
destruct (mrestrict H' m' (Z_to_bv 64 x)) as [b'|]; [discriminate|].
destruct (mrestrict H m (Z_to_bv 64 x)) as [b|]; [discriminate Em | exact Hw].
Qed.
Lemma pvc_val_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall kk, (kk < n)%nat -> aview SEGS H' m' (a + Z.of_nat kk) = aview SEGS H m (a + Z.of_nat kk)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v E Hv kk Hk. rewrite (mbyte_of_aview SEGS H H' m m' _ (E kk Hk)). exact (Hv kk Hk). Qed.

Lemma pvc_rdfp_closed : forall q v, 0 < q -> 0 < v -> ~ YI16.sink_open_fp (rd_fp q v).
Proof. intros q v Hq Hv (r0 & Hin & Hr). destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. Qed.

(* the container and the key read only their footprint bytes and their blocks (PItems_shape.v's transfers) *)
Lemma pvc_cont_xfer : forall (m m' : word -> option byte) (Lamc Lam' : list (Z * Z)) (o : bool) v kids keys n cap acc Di,
  pi_cont (L := B_prog_listing) (PA := PA) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  (forall a kk, In (a, kk) Lamc -> In (a, kk) Lam') ->
  (forall x, v <= x < v + 56 -> pis_same SEGS m m' x) ->
  (forall x, kids <= x < kids + 56 * Z.of_nat n -> pis_same SEGS m m' x) ->
  (o = true -> forall x, keys <= x < keys + 8 * Z.of_nat n -> pis_same SEGS m m' x) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same SEGS m m' x) ->
  pi_cont (L := B_prog_listing) (PA := PA) m' (prh_lin Lam') o v kids keys n cap acc Di.
Proof.
intros m m' Lamc Lam' o v kids keys n cap acc Di (Hh & Hn & Hnc & Hc54 & Hsl & Hk0 & HND & HAP & HIT) HLam Hv Hkd Hky HDi.
split; [exact (pis_hdr_frame SEGS m m' v _ _ _ _ _ _ _ Hh Hv)|].
split; [exact Hn|]. split; [exact Hnc|]. split; [exact Hc54|].
split.
{ destruct Hsl as [Hsl | (Hc & Hk & Hy)]; [left; exact Hsl|].
  right. split; [exact Hc|]. split; [apply HLam; exact Hk | intros Ho; apply HLam; exact (Hy Ho)]. }
split; [exact Hk0|]. split; [exact HND|]. split; [exact HAP|].
assert (PI : pis_items SEGS m (prh_lin Lamc) o kids keys (map snd acc) (map fst acc) Di).
{ destruct o; unfold pis_items;
    [split; [rewrite !length_map; reflexivity | rewrite pis_combine_map; exact HIT] | exact HIT]. }
assert (Hlen : length (map snd acc) = n) by (rewrite length_map; symmetry; exact Hn).
assert (PI' : pis_items SEGS m' (prh_lin Lam') o kids keys (map snd acc) (map fst acc) Di).
{ apply (pis_items_xfer SEGS m (prh_lin Lamc) m' (prh_lin Lam') o kids keys kids keys (map snd acc) (map fst acc) Di PI).
  - intros a kk Hak. apply HLam. exact (pis_items_lblk SEGS m (prh_lin Lamc) o kids keys _ _ Di PI a kk Hak).
  - exact HDi.
  - intros i Hi. rewrite Hlen in Hi. exact (proj1 (Hkd (kids + i) ltac:(lia))).
  - intros i Hi Hw. rewrite Hlen in Hi. exact (proj2 (Hkd (kids + i) ltac:(lia)) Hw).
  - intros Hl. exact (pis_items_mod8 SEGS m (prh_lin Lamc) o kids keys _ _ Di PI Hl).
  - left. reflexivity.
  - intros Ho i Hi. rewrite Hlen in Hi. exact (proj1 (Hky Ho (keys + i) ltac:(lia))). }
destruct o; unfold pis_items in PI'; [destruct PI' as (_ & PI'); rewrite pis_combine_map in PI'; exact PI' | exact PI'].
Qed.

Lemma pvc_key_xfer : forall (m m' : word -> option byte) (Lamc Lam' : list (Z * Z)) (o : bool) keys n nm Dk,
  pi_key (L := B_prog_listing) (PA := PA) m (prh_lin Lamc) o keys n nm Dk ->
  (forall a kk, In (a, kk) Lamc -> In (a, kk) Lam') ->
  (o = true -> forall x, keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8 -> mbyte SEGS m' x = mbyte SEGS m x) ->
  (forall x, (exists b, In b Dk /\ pj_holdsR b x) -> mbyte SEGS m' x = mbyte SEGS m x) ->
  pi_key (L := B_prog_listing) (PA := PA) m' (prh_lin Lam') o keys n nm Dk.
Proof.
intros m m' Lamc Lam' o keys n nm Dk HK HLam Hky HDk. unfold pi_key in *. destruct o; [|exact HK].
destruct HK as (x & kx & -> & Hu & Hc). exists x, kx. split; [reflexivity|]. split.
- apply (pis_u64_frame SEGS m m'); [exact Hu|]. intros y Hy. apply Hky; [reflexivity | lia].
- apply (pis_cstr_frame SEGS m (prh_lin Lamc) m' (prh_lin Lam')); [exact Hc | apply HLam; exact (proj1 Hc)|].
  intros y Hy. apply HDk. exists (x, kx). split; [left; reflexivity | exact Hy].
Qed.

End c1.

(* ================================================================================================== *)
Section w. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable d : nat.
Variable CTX0 : list (list Z).
(* the cursor set of the walk (the batch kit 240b06ed4fd4): parse_items' own CW, handed on to parse_value unchanged *)
Variable CW : list (list Z).
(* the callee: the kit's record text of parse_value at depth S d (lib/A/PRH_FnParse.v ed236011cf99 tparse_value_specX,
   the batch kit 240b06ed4fd4: CW, prh_cw_entry, wild_room, the budgeted post at wbudget CW 0), owner PValueB *)
Hypothesis PV : (d < PjGrammar.MAXD)%nat -> forall (fy : YK11.FPState) (CTX' : list (list Z)),
  tparse_value_specX (fx := fy) (L := B_prog_listing) (PA := PA) B ARx SK (Nat.succ d) CTX' CTX0 CW.
(* the harness-block shadow law, PItems_defs.v's one text (discharged at ARcf by YGcfHeadSh.v) *)
Hypothesis HSH : pi_hshadow_law (L := B_prog_listing) (PA := PA) B ARx cf_head.
(* PItems_kept.v's statement, taken by name, over a world relation R (the callee journal of the R call rule is at
   wle'): pi_cur's five memory conjuncts across a call, the form for parse_value's REFUSED arm, whose return cursor is
   only pj_in_afterR *)
Hypothesis CURM : pi_curmem_kept_callR_stmt (L := B_prog_listing) (PA := PA) (SKq := SK) B ARx.

Lemma pvc_pc_pval : pa_val (PAImg := PA) A_TEXT + PI_AT (L := B_prog_listing) (PI := PA) PI_O_PVAL = BASE + PVC_K.
Proof. vm_compute. reflexivity. Qed.
Lemma pvc_pc_aftv : pa_val (PAImg := PA) A_TEXT + PI_AT (L := B_prog_listing) (PI := PA) PI_O_AFTV = BASE + (PVC_K + 4).
Proof. vm_compute. reflexivity. Qed.

Lemma pvc_stk : (d < PjGrammar.MAXD)%nat -> STK_parse_items d = 144 + STK_parse_value (Nat.succ d).
Proof.
intros Hd. assert (E : (PjGrammar.MAXD - d)%nat = S (PjGrammar.MAXD - S d)) by lia.
unfold STK_parse_items, STK_parse_value. change (Nat.succ d) with (S d). rewrite E.
change (PRH_Base.pi_frame F_parse_items) with 144. lia.
Qed.
Lemma pvc_stk_lo : 144 <= STK_parse_items d /\ 0 <= STK_parse_value (Nat.succ d).
Proof.
unfold STK_parse_items, STK_parse_value. change (Nat.succ d) with (S d).
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)). pose proof (Nat2Z.is_nonneg (S (PjGrammar.MAXD - S d))).
assert (EL : LEAF_pv_pi = 16560) by (vm_compute; reflexivity). rewrite EL.
change (PRH_Base.pi_frame F_parse_items) with 144. change (PRH_Base.pi_frame F_parse_value) with 176. lia.
Qed.

(* the arodata view survives a journal (over any world relation R) whose footprint does not open the sink (image
   clause; the statics are RW) *)
Lemma pvc_rod_kept : forall R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS,
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc).
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS HJ Hsk HR a Hro Hns He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]).
rewrite (ajxR_img HJ a Himg Hns He (fun Hx => pst_not_ro_B a Hx Hro) (fp_spares_closed FP a Hsk)). exact (HR a Hro Hns He).
Qed.

(* a harness block's bytes: an allocator block of the state, present, not runtime-owned, outside the image *)
Lemma pvc_hb_blk : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a kk x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, kk) Lam ->
  a <= x < a + kk ->
  In (a - cf_head, kk + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp /\ req_size (kk + cf_head) = kk + cf_head /\
  a mod 16 = 0 /\ 4096 <= a - cf_head /\ a + kk <= YM05.alloc_ceiling /\ in_app (a - cf_head) (kk + cf_head) /\
  apresent (w_H W) mem x /\ ~ aowned B ly S x /\ ~ in_img SEGS x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a kk x HAR HLg Hin Hx.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLg) as HF.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (proj1 (Forall_forall _ _) HF (a, kk) Hin) as (Hk0 & Hab & Hhp & H16 & _). cbn [fst snd] in *.
assert (Hreq : req_size (kk + cf_head) = kk + cf_head) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hceil & Happ & Hpres & _).
rewrite Hreq in Hceil, Happ, Hpres.
destruct (Hpres x ltac:(lia)) as [Hp1 Hp2].
assert (Hc' : a + kk <= YM05.alloc_ceiling) by lia.
assert (Hi' : ~ in_img SEGS x) by exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab ltac:(rewrite Hreq; lia)).
exact (conj Hab (conj Hhp (conj Hreq (conj H16 (conj H4096 (conj Hc' (conj Happ (conj Hp1 (conj Hp2 Hi'))))))))).
Qed.

(* a byte of a harness block of the call state, outside the callee's footprint, is kept by the callee's journal (over
   any world relation R) *)
Lemma pvc_hb_same : forall R STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1
  Lamc peakc cntc failc ranc mostc ownc a kk x,
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  (forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) ->
  In (a, kk) Lamc -> a <= x < a + kk -> ~ inFP FP1 x ->
  pis_same SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) x.
Proof.
intros R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 Lamc peakc cntc failc ranc mostc ownc a kk x
  HJ1 HAR HLg Hkeep Hin Hx Hfp.
destruct (pvc_hb_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a kk x HAR HLg Hin Hx)
  as (Hab & _ & Hreq & _ & H4096 & Hceil & _ & _ & _ & Himg).
pose proof asan_consts as (C1 & _). pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_blk HJ1) as F2.
apply pvc_same; [lia | exact Himg|].
replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
apply (F2 (a - cf_head) (kk + cf_head) (x - (a - cf_head)) Hab (Hkeep _ Hab)); [rewrite Hreq; lia|].
replace (a - cf_head + (x - (a - cf_head))) with x by lia. exact Hfp.
Qed.

(* the node v of the container: a live harness block, a live allocator block or a live fake frame of the call state
   (prhReader_at's window case is excluded by rd_pre); its bytes outside the callee's footprint are kept *)
Lemma pvc_v_place : forall R STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1
  Lamc peakc cntc failc ranc mostc ownc (regs0 : bvmap 5 word) e v,
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  (forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  (forall x, v <= x < v + 56 -> ~ inFP FP1 x) ->
  4096 <= v /\ v + 56 <= YM05.alloc_ceiling /\
  forall x, v <= x < v + 56 -> pis_same SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) x.
Proof.
intros R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 Lamc peakc cntc failc ranc mostc ownc regs0 e v
  HJ1 HAR HLg Hkeep Hat Hvw Hfp.
pose proof asan_consts as (C1 & _). pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_blk HJ1) as F2. pose proof (ajxR_frm HJ1) as F4.
destruct Hat as [(a & kk & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct (pvc_hb_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a kk v HAR HLg Hin ltac:(lia))
    as (_ & _ & _ & _ & H4096 & Hceil & _).
  split; [lia|]. split; [lia|]. intros x Hx.
  exact (pvc_hb_same R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 Lamc peakc cntc failc ranc mostc
    ownc a kk x HJ1 HAR HLg Hkeep Hin ltac:(lia) (Hfp x Hx)).
- destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc b m HAR Hin) as (_ & H4096 & Hceil & _).
  assert (Hreq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  rewrite Hreq in Hceil. split; [lia|]. split; [lia|]. intros x Hx.
  apply pvc_same; [lia | exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc b m x HAR Hin ltac:(rewrite Hreq; lia)) |].
  replace x with (b + (x - b)) by lia. apply (F2 b m (x - b) Hin (Hkeep _ Hin)); [rewrite Hreq; lia|].
  replace (b + (x - b)) with x by lia. exact (Hfp x Hx).
- destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR Hin) as (G1 & G2 & _).
  split; [lia|]. split; [lia|]. intros x Hx.
  apply pvc_same; [lia | exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos x HAR Hin ltac:(lia)) |].
  apply (F4 cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (Hfp x Hx)].
- lia.
Qed.

(* a harness block of the return ledger that holds a byte of the text or of the node keeps its harness status: a
   block the callee added is new, and a block of the call state cannot share its base with a new one *)
Lemma pvc_hp_kept : forall lyc Sc Hpc (Wc : world SEGS) memc ly2 S2 Hp2 W2 mem2 md2 Lamc peakc cntc failc ranc mostc
  ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 D b m,
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  Permutation Lam2 (D ++ Lamc) ->
  (forall a kk, In (a, kk) D -> ~ In (a - cf_head, kk + cf_head) (ablocks B lyc Sc)) ->
  (forall bb, In bb (ablocks B lyc Sc) -> In bb (ablocks B ly2 S2)) ->
  In (b, m) (ablocks B lyc Sc) -> 0 < m ->
  (In b Hpc <-> In b Hp2).
Proof.
intros lyc Sc Hpc Wc memc ly2 S2 Hp2 W2 mem2 md2 Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2
  own2 D b m HLc0 HLc2 HAR2 HPL HDnew Hkeep Hb Hm.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HLc0) as HPc.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLc2) as HF2.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HLc2) as HP2.
pose proof (@cf_head_nonneg cp) as Hh0.
split; intros Hin.
- apply (Permutation_in _ (Permutation_sym HP2)). apply (Permutation_in _ HPc) in Hin.
  apply in_map_iff in Hin as ((a & kk) & Ea & Hak). apply in_map_iff. exists (a, kk). split; [exact Ea|].
  apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. exact Hak.
- apply (Permutation_in _ HP2) in Hin. apply in_map_iff in Hin as ((a & kk) & Ea & Hak). cbn [fst] in Ea.
  pose proof (Permutation_in _ HPL Hak) as Hak'. apply in_app_or in Hak' as [HaD | HaL].
  + exfalso. pose proof (proj1 (Forall_forall _ _) HF2 (a, kk) Hak) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
    assert (Hne : (b, m) <> (a - cf_head, kk + cf_head)) by (intros E; apply (HDnew a kk HaD); rewrite <- E; exact Hb).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 (Hkeep _ Hb) Hab2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    assert (R1 : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    assert (R2 : 1 <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    lia.
  + apply (Permutation_in _ (Permutation_sym HPc)). apply in_map_iff. exists (a, kk). split; [exact Ea | exact HaL].
Qed.

(* two different harness blocks of one ledger hold no byte in common *)
Lemma pvc_lam_apart : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a kk a' kk' x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, kk) Lam -> In (a', kk') Lam -> (a, kk) <> (a', kk') -> a <= x < a + kk -> ~ (a' <= x < a' + kk').
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a kk a' kk' x HAR HLg H1 H2 Hne Hx Hx'.
destruct (pvc_hb_blk ly S Hp W mem md Lam peak cnt fail ran most own a kk x HAR HLg H1 Hx) as (Hab & _ & Hreq & _).
destruct (pvc_hb_blk ly S Hp W mem md Lam peak cnt fail ran most own a' kk' x HAR HLg H2 Hx') as (Hab' & _ & Hreq' & _).
assert (Hne' : (a - cf_head, kk + cf_head) <> (a' - cf_head, kk' + cf_head))
  by (intros E; injection E as E1 E2; apply Hne; f_equal; lia).
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne') as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hreq' in Hd. pose proof (@cf_head_nonneg cp). lia.
Qed.

Lemma pvc_items_calls : forall dd (o : bool) x ok, x <> [] ->
  (PjGrammar.calls (snd (fst (jr_items prh_jr_strtod dd o x ok))) <= 2 * length x)%nat.
Proof. intros dd o [|b y] ok H; [contradiction|]. apply G7_4_items. Qed.

Lemma pvc_cont_lblk : forall (m : word -> option byte) (Lamc : list (Z * Z)) (o : bool) v kids keys n cap acc Di,
  pi_cont (L := B_prog_listing) (PA := PA) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  forall a kk, In (a, kk) Di -> In (a, kk) Lamc.
Proof.
intros m Lamc o v kids keys n cap acc Di (_ & _ & _ & _ & _ & _ & _ & _ & HIT) a kk Hak.
assert (PI : pis_items SEGS m (prh_lin Lamc) o kids keys (map snd acc) (map fst acc) Di).
{ destruct o; unfold pis_items;
    [split; [rewrite !length_map; reflexivity | rewrite pis_combine_map; exact HIT] | exact HIT]. }
exact (pis_items_lblk SEGS m (prh_lin Lamc) o kids keys _ _ Di PI a kk Hak).
Qed.

(* split a right-nested conjunction into its conjuncts, syntactically (no definition is unfolded) *)
Ltac pvc_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "TLa" in let H2 := fresh "TLb" in destruct H as [H1 H2]; pvc_split H2
  | _ => idtac
  end.

Ltac pvc_reg HS EL r rn H :=
  prreg HS r H; rewrite (EL rn) in H by (cbv; lia); rewrite (ew_Ereg_nat _ _ rn r eq_refl) in H.

(* ================================================================================================== *)
(* THE SEGMENT LEMMA: pv_call_spec d from pv_aftv_spec d and parse_value's text at S d *)
Lemma pv_call_holds : forall N,
  pv_aftv_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW N ->
  pv_call_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW N.
Proof.
intros N AFTV. unfold pv_call_spec.
intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc
  mdc k regs WS0 HJw HWS HPRE.
pose proof HPRE as (HFP & HENT & HMN & HFR & HREG & HRB & H21 & H10 & f & n & cap & acc & kids & keys & Di & nm &
  Dk & pc & ok0 & tr0 & D0 & Lamc & peakc & cntc & failc & ranc & HVD & H11 & HZERO).
clear HPRE.
pose proof HVD as (HCUR & HNb & Hncap & HCONT & HDEP & HAPART & HKEY & HD0 & HFUEL & HEQ & HLED & HBM & HPOSB & HLIVE &
  HBB & HLEN & HLSUM & HROOM & HGR & HCAPN & HNC & af & lk & HFO & HLK & HFLV).
(* pi_ent and its rd_pre: the fixed prefix by position, every conjunct after it BY TYPE (robust to a conjunct the kit owner adds
   there, e.g. the strict text ceiling of fix (a)) *)
pose proof HENT as (HMN0 & HLC1 & HLC2 & HCTX & HUNIV & HCURE & HCH0 & HCCH & R10e & R11e & R12e & Rgp0 & Rtp0 & HRD0 &
  Hplt & Hopen & HROOM0 & HCHf & HFRM0 & HRO0 & HENTT).
pvc_split HENTT.
match goal with H : prh_cw_entry B CW W mem regs0 q |- _ => rename H into HCWe end.
match goal with H : YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) |- _ => rename H into HWRe end.
(* the entry's hull budget over the whole call's all-granted list (pi_ent's last conjunct, PItems_defs.pi_ent_hull) *)
match goal with H : PresetHullBudget.hull_budget S _ |- _ => rename H into HHB end.
pose proof HRD0 as (Hfrm0 & Hmu & Hrl1 & Hrl2 & HIN0 & HFW0 & Hsq & Hqs & Hqra0 & Hsrc0 & Hhome0 & HRDT).
pvc_split HRDT.
match goal with H : Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 |- _ => rename H into Hmaxrun end.
match goal with H : prhPv_node _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hnode0 end.
match goal with H : q + 24 <= v \/ v + 56 <= q |- _ => rename H into Hqv end.
match goal with H : 0 < len -> text + len <= v \/ v + 56 <= text |- _ => rename H into Htv end.
match goal with H : v + 56 <= spZ regs0 \/ spZ regs0 + e <= v |- _ => rename H into Hvwin end.
match goal with H : prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own |- _ => rename H into HLED0 end.
match goal with H : (d <= PjGrammar.MAXD)%nat |- _ => rename H into HdM end.
match goal with H : cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 |- _ => rename H into Hcnt0 end.
pose proof HCUR as (HIN & Hqra & Hsrc & Hhome & Hat & Hvra & HLEDc & Hcntc).
pose proof HIN as (Mp & Mend & Mdep & Hqrw & Hq8 & Htx0 & Htx62 & Hpcr & Hlen & Hgarr & Hqtx & Hdep).
pose proof HIN0 as (_ & _ & _ & _ & _ & _ & _ & Hp0r & _).
pose proof HFR as (Hsp & Hgp & Htp & S136 & S128 & S120 & S112 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 &
  Hwin & Hret0 & He0 & He16).
pose proof HREG as (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
pose proof HRB as (R22 & R24 & M0 & M32 & M24 & M16 & M8).
pose proof HFP as (HFZc & HFKc).
pose proof HCONT as (HHDR & Hnacc & Hncap' & Hcap54 & Hslots & Hkeys0 & HNDi & HDiap & HITEMS).
pose proof Hsrc as (Hbytes & Htx4096 & Htxceil & Htxamr & Htxra & Htxhull).
pose proof HBM as (HBnew & HBperm & HBfr & HBpk).
pose proof HFW0 as (Hfe0 & Hfe16 & Hfetop & Hfepres).
pose proof Hnode0 as (Hv4096 & _).
unfold PI_FRAME in Hsp.
(* THE BUDGETED JOURNAL at the walk's relation wle' pa_segs RZ_cf (PItems_pres.v pi_ajR): the run takes the
   empty-budget journal at the block's depot (YCbqGwild.ajournal_xw_rebaseR); HWD is the cover the step back needs
   (ajournal_xw_unbase0R) *)
unfold pi_ajR in HJw. pose proof HJw as HJ0.
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof (ajxR_ar HJw) as HARc. pose proof (ajxR_ly HJw) as Hlyc. pose proof (ajxR_frs HJw) as Hfrc.
pose proof (ajxR_hi HJw) as HJstk. pose proof (ajxR_blk HJw) as HJblk. pose proof (ajxR_img HJw) as HJimg.
pose proof (ajxR_frm HJw) as HJfrm. pose proof (ajxR_gone HJw) as HJgone. pose proof (ajxR_pres HJw) as HJpres.
pose proof (ajxR_stk HJw) as HJastk. pose proof (ajxR_extra HJw) as HJext. pose proof (ajxR_qt HJw) as HJqt.
(* the room for CW at this block's state: the entry's (pi_ent), across the prefix's journal, whose wild traces are all
   CW's (the pre's budget), so no fresh slot is used (YCbqGwild.ajournal_xw_roomR) *)
pose proof (YCbqGwild.ajournal_xw_roomR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CW 0 HJw HWRe HWS) as HWRc.
change (0 - YCbqGwild.wfresh CW WS0)%nat with 0%nat in HWRc.
pose proof HJastk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop).
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & Eloc & Ehic & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Hd : (d < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
pose proof (pvc_stk Hd) as Hstk. pose proof pvc_stk_lo as (Hstk1 & Hstk2).
assert (Hsp0 : YM05.alloc_ceiling + 144 <= spZ regs0) by lia.
assert (Hq47 : q + 24 <= 2 ^ 47) by lia.
assert (Hlen0 : 0 < len) by lia.
(* SRC-CEIL (the kit's PRH_Base.v src_rd): the ceiling bounds the text's own bytes, no `+ 8` *)
assert (Htxc : text + len <= YM05.alloc_ceiling) by lia.
(* the cursor's p word below alloc_ceiling, which prh_cur_entry's arm at F_parse_items asks at the call (pvc_cur_low),
   from rd_pre's strict text ceiling (the batch kit's tip 03fcabb582d0 / c23331281d07, rd_pre's last conjunct) *)
assert (HTXS : text + len < YM05.alloc_ceiling)
  by (match goal with H : text + len < YM05.alloc_ceiling |- _ => exact H end).
pose proof (pvc_cur_low text len pc ltac:(lia) HTXS) as HPCC.
(* ---- the kid array: a harness block of the call ledger, new since the entry ---- *)
destruct Hslots as [(Hc0 & _ & _) | (Hcpos & Hkblk & Hkyblk)]; [lia|].
destruct (pvc_hb_blk lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) kids HARc HLEDc
  Hkblk ltac:(lia)) as (Hkab & Hkhp & Hkreq & Hk16 & Hk4096 & Hkceil & Hkapp & _).
assert (Hkin : In (kids, 56 * Z.of_nat cap) (pi_sblk o kids keys cap)).
{ unfold pi_sblk. apply in_or_app. left. unfold kids_blkR.
  replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
assert (HkD0 : In (kids, 56 * Z.of_nat cap) D0).
{ apply (Permutation_in _ (Permutation_sym HD0)). apply in_or_app. left. exact Hkin. }
pose proof (HBnew _ _ HkD0) as Hknew.
set (sl := pv_slot kids n) in *. assert (Hsl : sl = kids + 56 * Z.of_nat n) by reflexivity.
(* the text is apart from the kid slot: its entry home is a block of the entry state (the kid array is new) or the
   read-only image (the kid array is off the image) *)
assert (TS : text + len <= sl \/ sl + 56 <= text).
{ assert (BLK : forall b m0, In (b, m0) (ablocks B ly S) -> b <= text -> text + len <= b + req_size m0 ->
    text + len <= sl \/ sl + 56 <= text).
  { intros b m0 Hb H1 H2.
    assert (Hbc : In (b, m0) (ablocks B lyc Sc))
      by (apply (Permutation_in _ (Permutation_sym HBperm)); apply in_or_app; right; exact Hb).
    assert (Hne : (b, m0) <> (kids - cf_head, 56 * Z.of_nat cap + cf_head)) by (intros E; rewrite E in Hb; exact (Hknew Hb)).
    pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hbc Hkab Hne) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Hkreq in Hdj. lia. }
  assert (RO : (forall a, text <= a < text + len -> in_roP SEGS RLO RHI a) -> text + len <= sl \/ sl + 56 <= text).
  { intros Hro.
    destruct (Z_le_gt_dec (text + len) sl) as [Hl1|Hl1]; [left; exact Hl1|].
    destruct (Z_le_gt_dec (sl + 56) text) as [Hl2|Hl2]; [right; exact Hl2|]. exfalso.
    pose proof (Hro (Z.max text sl) ltac:(lia)) as Hra.
    assert (Hia : in_img SEGS (Z.max text sl))
      by (destruct Hra as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA _ Hr)]).
    assert (Hrg : kids - cf_head <= Z.max text sl < kids - cf_head + req_size (56 * Z.of_nat cap + cf_head)) by (rewrite Hkreq; lia).
    exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ HARc Hkab Hrg Hia). }
  destruct Hhome0 as [[(b & m0 & Hb & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m0 & Hb & _ & H1 & H2)].
  - pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED0) as HF0.
    pose proof (proj1 (Forall_forall _ _) HF0 (b, m0) Hb) as (Hm0 & Hab0 & _).
    cbn [fst snd] in Hm0, Hab0.
    apply (BLK (b - cf_head) (m0 + cf_head) Hab0); [lia | unfold req_size; destruct (Z.eqb_spec (m0 + cf_head) 0); lia].
  - apply RO. intros a Ha. exact (proj1 (Hro a Ha)).
  - apply RO. intros a Ha. exact (proj1 (Hro a Ha)).
  - apply (BLK b m0 Hb H1). unfold req_size. destruct (Z.eqb_spec m0 0); lia. }
(* ---- the GRANTED PREFIX (pi_grant) makes the whole call's all-granted run the prefix then pi_val_k at [] (its
   granted trace: the value's, then the rest pvm_gafter) ---- *)
assert (HGT : fst (jr_items prh_jr_strtod d o (rest_atR tb text p) []) =
  (fst (fst (pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) [])),
   tr0 ++ snd (fst (pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) []))))
  by exact (pvm_gt_grant d o (rest_atR tb text p) ok0 tr0 _ HEQ HGR).
assert (HGTI : prhPi_gtrace d o (rest_atR tb text p) =
  tr0 ++ prhPv_gtrace (Nat.succ d) (rest_atR tb text pc) ++
  pvm_gafter f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc)).
{ unfold prhPi_gtrace. rewrite HGT. cbn [snd].
  rewrite (pvm_gt_split f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) HFUEL). reflexivity. }
(* THE HULL BUDGET at the call (route (b)): parse_value's all-granted events follow the prefix's in the entry's list
   (HGTI), so its budget is the entry's less the prefix's use (PItems_posb.pi_posb_budget) *)
assert (HHBv : PresetHullBudget.hull_budget Sc
  (PresetReqAt.rd_hevs (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc)))).
{ pose proof HHB as HB. rewrite HGTI, !PresetReqAt.rd_hevs_app in HB.
  exact (PItems_posb.pi_posb_budget S Sc tr0 _ _ _ HB HPOSB eq_refl). }
(* ---- the symbolic state at PI_O_PVAL and the run of `jal parse_value` ---- *)
pose proof (pvc_st (fx := fxc) Wc regs memc) as HS.
remember (@Eimg _ B_prog_listing PA (Ereg regs [])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall rn : nat, (rn < A_TEXT)%nat -> ew E rn = ew (Ereg regs []) rn)
  by (intros rn Hrn; rewrite HE; apply Eimg_low; exact Hrn).
clear HE.
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
unfold pi_goalR, cfg_at. rewrite pvc_pc_pval. change (w64 (BASE + PVC_K)) with (Z_to_bv 64 (BASE + PVC_K)).
pose (RUN := PI_RUNR (fx := fxc) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PA)
  B (@prh_pst prh_img_B) ARx LAWS).
pi_run RUN HS HJ SHOK.
all: try (cbn; apply awr_ok_nil).
(* the block writes nothing: the memory after the jal is the memory before *)
assert (MEQ : ms_mem ms = memc).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hin & _). cbn in Hin. destruct Hin. }
subst memc.
pose proof HJ as (HARc2 & _).
pvc_reg HS EL (2%bv : bv 5) 2%nat Q2. pvc_reg HS EL (3%bv : bv 5) 3%nat Q3. pvc_reg HS EL (4%bv : bv 5) 4%nat Q4.
pvc_reg HS EL (8%bv : bv 5) 8%nat Q8. pvc_reg HS EL (9%bv : bv 5) 9%nat Q9.
pvc_reg HS EL (10%bv : bv 5) 10%nat Q10. pvc_reg HS EL (11%bv : bv 5) 11%nat Q11.
pvc_reg HS EL (18%bv : bv 5) 18%nat Q18. pvc_reg HS EL (19%bv : bv 5) 19%nat Q19.
pvc_reg HS EL (20%bv : bv 5) 20%nat Q20. pvc_reg HS EL (21%bv : bv 5) 21%nat Q21.
pvc_reg HS EL (22%bv : bv 5) 22%nat Q22. pvc_reg HS EL (23%bv : bv 5) 23%nat Q23.
pvc_reg HS EL (24%bv : bv 5) 24%nat Q24. pvc_reg HS EL (25%bv : bv 5) 25%nat Q25.
pvc_reg HS EL (26%bv : bv 5) 26%nat Q26. pvc_reg HS EL (27%bv : bv 5) 27%nat Q27.
prreg HS (1%bv : bv 5) Q1.
assert (Ush : spZ (ms_regs ms) = spZ regs0 - 144) by (unfold spZ in *; rewrite Q2; exact Hsp).
assert (Us0 : s0Z (ms_regs ms) = q + 16)
  by (unfold s0Z; rewrite Q8, R8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Q1' : getr (ms_regs ms) 1 = w64 (pa_val (PAImg := PA) A_TEXT + PI_AT (L := B_prog_listing) (PI := PA) PI_O_AFTV))
  by (rewrite Q1; unfold w64; f_equal; vm_compute; reflexivity).
assert (Hsp8 : spZ regs0 mod 8 = 0) by lia.
(* ---- the call chain at the call: from s0 = q + 16, one record (the cursor's end over its p word) ---- *)
assert (RWq : rdword (aview SEGS (w_H Wc) (ms_mem ms)) q = Some pc) by (apply pvc_rdword_of_val; [exact Mp | lia]).
assert (RWq8 : rdword (aview SEGS (w_H Wc) (ms_mem ms)) (q + 8) = Some (text + len))
  by (apply pvc_rdword_of_val; [exact Mend | lia]).
destruct (pvc_achain16 lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ (ms_regs ms)) q pc (text + len) RWq RWq8
  ltac:(lia) ltac:(lia) ltac:(lia)) as (ch1 & Hch1).
rewrite <- Us0 in Hch1.
(* ---- the two cursor words at the call state (prh_cur_entry), from the entry's: a word at or above the entry sp
   outside the cursor's cells is the entry view's; the saved ra / s0 slots hold the entry ra / s0 ---- *)
assert (XW : forall a w, (a = spZ regs0 - 8 \/ a = spZ regs0 - 16 \/
     (spZ regs0 <= a /\ a + 8 <= spZ regs0 + e /\ (a + 8 <= q \/ (q + 8 <= a /\ a + 8 <= q + 16)))) ->
   rdword (aview SEGS (w_H Wc) (ms_mem ms)) a = Some w -> prh_word_entry W mem regs0 a w).
{ intros a w Ha Hw. unfold prh_word_entry.
  destruct Ha as [-> | [-> | (Ha1 & Ha2 & Ha3)]].
  - rewrite Z.eqb_refl.
    assert (E1 : rdword (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs0 - 8) = Some (raZ regs0)).
    { replace (spZ regs0 - 8) with (spZ regs + 136) by lia. apply pvc_rdword_of_val; [exact S136|].
      unfold raZ. pose proof (bv_unsigned_in_range _ (getr regs0 1)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
      exact Hb. }
    rewrite E1 in Hw. injection Hw as <-. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (spZ regs0 - 16) (spZ regs0 - 8))) by lia. rewrite Z.eqb_refl.
    assert (E1 : rdword (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs0 - 16) = Some (s0Z regs0)).
    { replace (spZ regs0 - 16) with (spZ regs + 128) by lia. apply pvc_rdword_of_val; [exact S128|].
      unfold s0Z. pose proof (bv_unsigned_in_range _ (getr regs0 8)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
      exact Hb. }
    rewrite E1 in Hw. injection Hw as <-. reflexivity.
  - rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 8))) by lia. rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 16))) by lia.
    rewrite <- Hw. apply rdword_ext. intros kk Hkk. symmetry. apply Hwin; [lia|].
    intros (r0 & Hin & Hr). destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
assert (Hqc : q = spZ regs0 \/ q = spZ regs0 + 8 \/ spZ regs0 + 16 <= q) by lia.
(* a word at or above the entry sp - 16 that the callee's entry form names is the call view's word *)
assert (WE : forall a w, spZ regs0 - 16 <= a -> prh_word_entry Wc (ms_mem ms) (ms_regs ms) a w ->
               rdword (aview SEGS (w_H Wc) (ms_mem ms)) a = Some w).
{ intros a w Ha Hw. unfold prh_word_entry in Hw. rewrite Ush in Hw.
  rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 144 - 8))) in Hw by lia.
  rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 144 - 16))) in Hw by lia. exact Hw. }
assert (HCE : prh_cur_entry Wc (ms_mem ms) (ms_regs ms) q).
{ split.
  { (* no call-view chain from s0 = q + 16 has a record at q + 8: the kit's case 3 (every record at or above s0) *)
    apply (prh_cur_entry_cases Wc (ms_mem ms) (ms_regs ms) q); [lia | right; right; rewrite Us0; lia]. }
  (* The batch kit: prh_cur_entry keeps only the sp - 16 arm (prh_cur_low); the sp - 8 arm's slot is CW's (prh_cw_entry) *)
  intros F HFc. pose proof (proj2 HCURE F HFc) as E2.
  assert (Hkv : prh_s0 F q = q \/ prh_s0 F q = q + 16)
    by (destruct HFc as [-> | ->]; unfold prh_s0; cbn; lia).
  destruct Hkv as [Es | Es]; rewrite Es in E2 |- *.
  - intros w Hw. apply E2. apply WE in Hw; [|lia]. apply (XW _ w); [|exact Hw].
    destruct Hqc as [Hqc | [Hqc | Hqc]]; [right; left; lia | left; lia | right; right; lia].
  - intros w Hw. apply WE in Hw; [|lia]. replace (q + 16 - 16) with q in Hw by lia.
    rewrite RWq in Hw. injection Hw as <-. exact HPCC. }
(* THE CURSOR SET at the call (the batch kit, PRH_Base.prh_cw_entry): the word a cursor free reads at prh_s0 F q - 8 (q - 8 or
   q + 8, at or above the entry sp - 8) is the entry's (XW), so its trace is CW's by pi_ent's prh_cw_entry *)
assert (HCW : prh_cw_entry B CW Wc (ms_mem ms) (ms_regs ms) q).
{ intros F0 r0 w HF0 Hr0 Hw. apply (HCWe F0 r0 w HF0 Hr0).
  assert (Hkv : prh_s0 F0 q = q \/ prh_s0 F0 q = q + 16)
    by (destruct HF0 as [-> | ->]; unfold prh_s0; cbn; lia).
  apply WE in Hw; [|destruct Hkv as [Es | Es]; rewrite Es; lia].
  apply (XW _ w); [|exact Hw].
  destruct Hkv as [Es | Es]; rewrite Es;
    [destruct Hqc as [Hqc | [Hqc | Hqc]]; [left; lia | right; right; lia | right; right; lia] | right; right; lia]. }
(* ---- the chain at the cursor for parse_string (s0 = q): one record at most, its next word low ---- *)
assert (HCC : exists ch', achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ (ms_regs ms)) (prh_s0 F_parse_string q) ch').
{ assert (Es : prh_s0 F_parse_string q = q) by (unfold prh_s0; cbn; lia).
  assert (PR : forall a, q - 16 <= a < q -> exists b, aview SEGS (w_H Wc) (ms_mem ms) a = Some b /\ 0 <= b).
  { intros a Ha. apply pvc_aview_present. apply HJpres. lia. }
  destruct (pvc_rdword_some (aview SEGS (w_H Wc) (ms_mem ms)) (q - 8) (fun kk Hkk => PR (q - 8 + kk) ltac:(lia)))
    as (w8 & Hw8 & Hw8p).
  destruct (pvc_rdword_some (aview SEGS (w_H Wc) (ms_mem ms)) (q - 16) (fun kk Hkk => PR (q - 16 + kk) ltac:(lia)))
    as (w16 & Hw16 & _).
  pose proof (proj2 HCE F_parse_string (or_introl eq_refl)) as L16.
  assert (Hlow : w16 < YM05.alloc_ceiling).
  { apply L16. rewrite Es. unfold prh_word_entry. rewrite Ush.
    rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regs0 - 144 - 8))) by lia.
    rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regs0 - 144 - 16))) by lia. exact Hw16. }
  rewrite Es. exact (pvc_achainq lyc _ (spZ (ms_regs ms)) q w8 w16 Hw8 Hw8p Hw16 ltac:(lia) ltac:(rewrite Ush; lia)). }
(* ---- the live counts at the call (form (b)): the callee's two peak premises over its own granted events, from pi_ent's
   over the whole call's at the block's pi_live (PItems_value_model.v pvm_lc_call; the value's granted trace is the
   head of the block continuation's, pvm_gt_split) ---- *)
assert (LC : forall (f0 : Z -> bool) b,
  Z.of_nat (PresetRun.pkR f0 (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= b ->
  Z.of_nat (PresetRun.pkR f0 (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (PresetReqAt.rd_hevs (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc)))) <= b).
{ intros f0 b Hb.
  apply (pvm_lc_call f0 _ _ d o (rest_atR tb text p) ok0 tr0
    (pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc)) _ b HEQ HLEN HLIVE); [|exact Hb].
  exists (pvm_gafter f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc)).
  exact (pvm_gt_split f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) HFUEL). }
(* ---- the call: the BUDGETED window-float call rule at the walk's relation, YCbqGwild.aj_call_xWFb_spR at
   wle' pa_segs RZ_cf, at window e + 144 below the journal's sp (o = -(144 + e)), from the caller's journal at WS0
   (back from the run's empty-budget one); parse_value's text concludes SRr' pa_segs RZ_cf with its post at wle' and
   at wbudget CW 0 with the SAME CW ---- *)
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) as HJb.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (YCbqGwild.aj_call_xWFb_spR (fx := fxc) (SK := SK) SEGS B prh_pst ARx LAWS Hsegs
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    Wc E _ ms (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly S Hp W mem md [] lyc Sc Hpc _ k WS0
    (STK_parse_value (Nat.succ d)) (e + 144) (rd_fp q sl) (- (144 + e))
    (w64 (pa_val (PAImg := PA) A_TEXT + PI_AT (L := B_prog_listing) (PI := PA) PI_O_AFTV)) ch1
    (YCbqGwild.wbudget CW 0) _ HS eq_refl HJb).
  - rewrite Ush. lia.
  - lia.
  - lia.
  - exact Hstk2.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Q3, Hgp. exact Rgp0.
  - rewrite Q4, Htp. exact Rtp0.
  - exact Q1'.
  - rewrite pvc_pc_aftv. unfold w64. apply (ret_ok_codeptr_v (PI := PA)); [unfold PVC_K; lia | reflexivity].
  - rewrite pvc_pc_aftv. unfold w64. apply Z.leb_le. vm_compute. reflexivity.
  - replace (spZ regs0 + e + - (144 + e)) with (spZ (ms_regs ms)) by lia. exact Hch1.
  - (* the callee: the parse_value text at S d, at CTX' := the spine at the call; its hull budget HHBv *)
    intros HPRE1 HWIN1. cbn [ss_pc setpc].
    refine (PV Hd fxc [raZ (ms_regs ms) :: spine ch1] lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (e + 144) q text len
      pc tb sl Lamc peakc cntc failc ranc most own _ HMN _ HUNIV HCE HCW _ _ _ _ _ _ HWRc (LC _ _ HLC1) (LC _ _ HLC2)
      HHBv _).
    + split; [exact HPRE1|]. split.
      { apply (pvc_rod_kept _ _ _ _ ly S Hp W mem md [] lyc Sc Hpc Wc (ms_mem ms) mdc k WS0 HJ0
          (pvc_rdfp_closed q v ltac:(lia) ltac:(lia)) HRO0). }
      split; [rewrite Ush, Ehic; lia|].
      (* fpre's frm_zero at the call (FRM0-ENTRY): the block's own float state, pi_fpok *)
      split; [|exact HFZc].
      (* fpre's return address below the ceiling: the jal's own return pc, PI_O_AFTV, a text address *)
      unfold raZ. rewrite Q1', pvc_pc_aftv.
      assert (Hra : bv_unsigned (w64 (BASE + (PVC_K + 4))) < kLowMemEnd) by (apply Z.ltb_lt; vm_compute; reflexivity).
      lia.
    + left. reflexivity.
    + exists ch1. split; [exact Hch1 | reflexivity].
    + right. split; [rewrite Ush; lia | exact HCC].
    + rewrite Q10. exact H10.
    + rewrite Q11. exact H11.
    + split; [exact HFZc|]. split; [exact Hmu|]. split; [exact Hrl1|]. split; [exact Hrl2|].
      split; [rewrite Nat2Z.inj_succ; unfold Z.succ; exact HIN|].
      split; [exact HWIN1|].
      split; [rewrite Ush; lia|]. split; [rewrite Ush; lia|].
      split; [exact Hqra|]. split; [exact Hsrc|]. split; [exact Hhome|]. split; [exact Hmaxrun|].
      split.
      { assert (Hsl8 : sl mod 8 = 0) by lia.
        assert (SLB : forall x, sl <= x < sl + 56 -> apresent (w_H Wc) (ms_mem ms) x /\ ~ aowned B lyc Sc x).
        { intros x Hx. destruct (pvc_hb_blk lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own kids
            (56 * Z.of_nat cap) x HARc2 HLEDc Hkblk ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
          exact (conj Hp1 Hp2). }
        split; [lia|]. split; [exact Hsl8|].
        split; [split; [exact Hsl8 | intros x Hx; apply (apresent_writable SEGS); exact (proj1 (SLB x Hx))]|].
        split; [exact HZERO|].
        split; [left; exists kids, (56 * Z.of_nat cap); split; [exact Hkblk | lia]|].
        split; [unfold amem_range; unfold in_app, kLowShadowBeg, ASAN_CEIL in Hkapp; lia|].
        split; [intros x Hx; split; [exact (proj2 (SLB x Hx)) | rewrite Ush; lia]|].
        destruct (HSH lyc Sc Hpc Wc (ms_mem ms) _ (kids - cf_head) (56 * Z.of_nat cap + cf_head) HARc2 Hkab Hkhp)
          as (Hbs & _).
        rewrite Hkreq in Hbs. replace (kids - cf_head + cf_head) with kids in Hbs by lia.
        replace (56 * Z.of_nat cap + cf_head - cf_head) with (56 * Z.of_nat cap) in Hbs by lia.
        exact (block_shadow_range _ SHADOW_OFF kids (56 * Z.of_nat cap) sl 56 Hbs ltac:(lia) ltac:(lia)). }
      split; [right; lia|]. split; [intros _; exact TS|]. split; [left; rewrite Ush; lia|].
      split; [exact HLEDc|]. split; [change (Nat.succ d) with (Datatypes.S d); lia|].
      (* the strict text ceiling, rd_pre's last conjunct: the text and its length are the entry's *)
      split; [exact Hcntc | exact HTXS].
    + pose proof HROOM as RM.
      rewrite (pvm_gt_split f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) HFUEL) in RM.
      exact (pvm_room_pre Sc _ _ RM).
    + rewrite Hfrc. cbn [app].
      change (Nat.succ (PjGrammar.MAXD - Nat.succ d)) with (Datatypes.S (PjGrammar.MAXD - Datatypes.S d)).
      assert (Efr : (PjGrammar.MAXD - d)%nat = Datatypes.S (PjGrammar.MAXD - Datatypes.S d)) by lia.
      rewrite <- Efr. exact HFRM0.
  - intros a (r0 & Hin & Hr). destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + left. exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    + left. exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
    + right. left. exists (kids - cf_head), (56 * Z.of_nat cap + cf_head).
      split; [exact Hkab|]. split; [exact Hknew|]. rewrite Hkreq. lia. }
cbv beta. intros W2 c2 Hwle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW1 & HJ2 & HJ1 &
  HWIN & HPRES & HK).
(* the m-form post: the callee's own Q and the memnorm keep from the call state's memory; the Q is the text's tpvP_Q,
   read through its named layer (tpvP_R_of and the fields) *)
unfold fQmn in HK. cbv beta in HK. destruct HK as (HK & HKMN).
change (tpvP_Q (L := B_prog_listing) (PA := PA) B (Nat.succ d) lyc Sc q text len pc tb sl Lamc peakc cntc failc ranc
  most own ly2 S2 Hp2 W2 regs2 mem2 md2) in HK.
destruct (tpvP_R_of HK) as (okc & res & tr & okr & Dv & Lam2 & peak2 & cnt2 & fail2 & ran2 & HPV). clear HK.
pose proof (tpvP_run HPV) as HJV. pose proof (tpvP_ledger HPV) as HLED2. pose proof (tpvP_room HPV) as HRL2.
pose proof (tpvP_hull HPV) as HHU2. pose proof (tpvP_live HPV) as HLV2. pose proof (tpvP_pos HPV) as HPOS2.
pose proof (tpvP_outcome HPV) as HOUT2. pose proof (tpvP_injected HPV) as HINJ2.
pose proof (tpvP_ledger_move HPV) as HLM. pose proof (tpvP_blocks_move HPV) as HBM2.
pose proof (tpvP_bytes HPV) as HBB2. pose proof (tpvP_lsum HPV) as HLS2. pose proof (tpvP_arm HPV) as HRES.
clear HPV.
(* The batch kit's post states the run over ReaderRes.jr_strtod; the model lemmas use PRH_Reader.prh_jr_strtod, the same term *)
assert (HJVp : jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) okc = (res, tr, okr)) by exact HJV.
clear HJV. rename HJVp into HJV.
replace (spZ regs0 + e + - (144 + e)) with (spZ regs0 - 144) in HJ1, HWIN by lia.
pose proof HJ2 as (HAR2 & HLy2 & _).
pose proof HLy2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
pose proof HLM as (_ & HLc & _ & HLp & _).
pose proof HBM2 as (HBn2 & HBp2 & _).
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLEDc) as (_ & _ & Hcnc & _).
pose proof (prh_ledger_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLEDc) as HNDc.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED0) as (_ & _ & Hcn0 & Hfl0 & _).
pose proof HLED as (_ & _ & _ & HLp0 & _).
destruct (pvc_hb_blk lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) kids HARc2
  HLEDc Hkblk ltac:(lia)) as (_ & _ & _ & _ & _ & Hkc & _).
assert (KEEPB : forall bb, In bb (ablocks B lyc Sc) -> In bb (ablocks B ly2 S2))
  by (intros bb Hbb; apply (Permutation_in _ (Permutation_sym HBp2)); apply in_or_app; right; exact Hbb).
assert (LSUB : forall a kk, In (a, kk) Lamc -> In (a, kk) Lam2)
  by (intros a kk H; apply (Permutation_in _ (Permutation_sym HLp)); apply in_or_app; right; exact H).
assert (NFPlo : forall x, x < YM05.alloc_ceiling -> ~ (sl <= x < sl + 56) -> ~ inFP (rd_fp q sl) x)
  by (intros x Hx Hs; apply pvc_notfp; lia).
assert (KW : forall a, spZ regs0 - 144 <= a < spZ regs0 ->
   aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a)
  by (intros a Ha; apply HWIN; [lia | apply pvc_notfp; lia]).
assert (HND0 : NoDup (map fst (pi_sblk o kids keys cap ++ Di ++ Dk))).
{ apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst HD0)).
  apply (pvc_nodup_app_l _ _ (map fst Lam)). rewrite <- map_app.
  apply (Permutation_NoDup (Permutation_map fst HLp0)). apply NoDup_ListNoDup. exact HNDc. }
assert (Hslapp : in_app sl 56).
{ apply (in_app_sub (kids - cf_head) (56 * Z.of_nat cap + cf_head)); [exact Hkapp | lia | lia | lia]. }
assert (Hqhi : kHighMemBeg <= q) by lia.
(* ---- the node v: its bytes are kept (outside the callee's footprint: apart from the cursor and the kid array) ---- *)
assert (VNF : forall x, v <= x < v + 56 -> ~ inFP (rd_fp q sl) x).
{ intros x Hx. apply pvc_notfp; [lia | lia|]. intros Hs.
  apply (HAPART (kids, 56 * Z.of_nat cap) x Hkin); [unfold pj_holdsR; cbn [fst snd]; lia | exact Hx]. }
destruct (pvc_v_place _ _ _ _ lyc Sc Hpc Wc (ms_mem ms) _ ly2 S2 Hp2 W2 mem2 md2 k1 WS1 Lamc peakc cntc failc ranc most
  own regs0 e v HJ1 HARc2 HLEDc KEEPB Hat Hvwin VNF) as (Hv4096' & Hvceil & SV).
(* ---- the caller's cursor / text / node memory facts at the return state (PItems_kept.v's statement at wle') ---- *)
destruct (CURM (wle' SEGS YGcfRehidePost.RZ_cf) regs0 e q v text len tb d lyc Sc Hpc Wc (ms_mem ms) _ pc Lamc peakc
  cntc failc ranc most own (STK_parse_value (Nat.succ d)) (spZ regs0 - 144) (e + 144) (rd_fp q sl) [] ly2 S2 Hp2 W2
  mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most own WS1 HCUR HJ1) as (Rq2 & Src2 & Home2 & At2 & Rv2).
{ intros a Ha Hn. apply HWIN; [lia | exact Hn]. }
{ lia. }
{ lia. }
{ lia. }
{ rewrite Elo2. lia. }
{ rewrite Ehi2. lia. }
{ destruct Hhome as [[(b & m0 & Hb & H1 & H2) | [Hro | Hki]] | (b & m0 & Hb & _ & H1 & H2)].
  + right; right. destruct (pvc_hb_blk lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own b m0 text HARc2
      HLEDc Hb ltac:(lia)) as (Hab & _). exists (b - cf_head), (m0 + cf_head). split; [exact Hab | lia].
  + left. exact Hro.
  + right; left. exact Hki.
  + right; right. exists b, m0. split; [exact Hb | lia]. }
{ intros b m Hb Hcov. split; [exact (KEEPB _ Hb)|].
  apply (pvc_hp_kept lyc Sc Hpc Wc (ms_mem ms) ly2 S2 Hp2 W2 mem2 md2 Lamc peakc cntc failc ranc most own
    Lam2 peak2 cnt2 fail2 ran2 most own Dv b m HLEDc HLED2 HAR2 HLp HBn2 KEEPB Hb). destruct Hcov; lia. }
{ intros a Ha. apply pvc_notfp; lia. }
{ intros a Ha. apply pvc_shadow_notfp; [lia | exact Hqhi | exact Hslapp]. }
{ intros a Ha. apply pvc_shadow_notfp; [lia | exact Hqhi | exact Hslapp]. }
{ exact (pvc_rdfp_closed q sl ltac:(lia) ltac:(lia)). }
{ exact HLED2. }
{ left. reflexivity. }
{ intros a kk H _. exact (LSUB a kk H). }
(* the cursor in the caller's window (rd_pre at the entry) *)
{ exact Hsq. }
{ exact Hqs. }
(* the ledger entries the callee adds are blocks the call state did not have (its rd_blocks_move) *)
{ intros a kk Hin. apply (Permutation_in _ HLp) in Hin. apply in_app_or in Hin as [HD | HLm];
    [right; exact (HBn2 a kk HD) | left; exact HLm]. }
(* the call state's invariant: the journal's first conjunct *)
{ exact HARc2. }
(* ---- the container's bytes: the kid array before the slot, the keys array, the members' blocks, the key ---- *)
assert (SKD : forall x, kids <= x < kids + 56 * Z.of_nat n ->
   pis_same SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H W2) mem2) x).
{ intros x Hx. eapply pvc_hb_same; [exact HJ1 | exact HARc2 | exact HLEDc | exact KEEPB | exact Hkblk | lia |].
  apply NFPlo; lia. }
assert (APK : forall a kk x, In (a, kk) Lamc -> (a, kk) <> (kids, 56 * Z.of_nat cap) -> a <= x < a + kk ->
   pis_same SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H W2) mem2) x).
{ intros a kk x Hb Hne Hx.
  destruct (pvc_hb_blk lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own a kk x HARc2 HLEDc Hb Hx)
    as (_ & _ & _ & _ & _ & Hc & _).
  pose proof (pvc_lam_apart lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own a kk kids
    (56 * Z.of_nat cap) x HARc2 HLEDc Hb Hkblk Hne Hx) as Hap.
  eapply pvc_hb_same; [exact HJ1 | exact HARc2 | exact HLEDc | exact KEEPB | exact Hb | exact Hx |].
  apply NFPlo; lia. }
assert (SKY : o = true -> forall x, keys <= x < keys + 8 * Z.of_nat cap ->
   pis_same SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H W2) mem2) x).
{ intros Ho x Hx. apply (APK keys (8 * Z.of_nat cap) x (Hkyblk Ho)); [intros Hq0; injection Hq0 as E1 E2; lia | lia]. }
assert (SDI : forall x, (exists b, In b Di /\ pj_holdsR b x) ->
   pis_same SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H W2) mem2) x).
{ intros x ((a & kk) & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  apply (APK a kk x (pvc_cont_lblk _ _ _ _ _ _ _ _ _ _ HCONT a kk Hb)); [|exact Hx].
  intros Hq0. rewrite Hq0 in Hb. exact (pvc_nodup_sep _ _ _ HND0 Hkin (in_or_app _ _ _ (or_introl Hb))). }
assert (SDK : forall x, (exists b, In b Dk /\ pj_holdsR b x) ->
   mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H Wc) (ms_mem ms)) x).
{ intros x ((a & kk) & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  assert (HbL : In (a, kk) Lamc).
  { unfold pi_key in HKEY. destruct o.
    - destruct HKEY as (x0 & kx & EDk & _ & Hcs). rewrite EDk in Hb. destruct Hb as [Hq0 | []].
      injection Hq0 as <- <-. exact (proj1 Hcs).
    - destruct HKEY as (_ & EDk). rewrite EDk in Hb. destruct Hb. }
  apply (APK a kk x HbL); [|exact Hx].
  intros Hq0. rewrite Hq0 in Hb.
  exact (pvc_nodup_sep _ _ _ HND0 Hkin (in_or_app _ _ _ (or_intror Hb))). }
(* ---- the registers after the call: the callee-saved ones are the call state's, so the caller's ---- *)
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HPRES 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (HPRES 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (HPRES 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (HPRES 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (HPRES 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (HPRES 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (HPRES 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (HPRES 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (HPRES 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HPRES 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (HPRES 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (HPRES 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (HPRES 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (HPRES 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HPRES 27 ltac:(unfold acallee_saved; lia)).
assert (Esp2 : spZ regs2 = spZ regs) by (unfold spZ; rewrite P2, Q2; reflexivity).
(* ---- the model: the callee's ok list normalised, the run through the value, the traces' facts ---- *)
destruct (pvm_jr_value_norm _ _ _ _ _ _ HJV) as (okn & Hokn & Hnth & HJVn).
pose proof (pvc_move_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnth HLM) as HLMn.
assert (HVK : forall ok1, pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) (okn ++ ok1) =
   jbind (fun ok => (res, tr, ok)) (pv_kont f (Nat.succ d) o n cap (rev acc) nm) ok1).
{ intros ok1. rewrite pvm_val_k_eq. unfold jbind. rewrite (pvm_jrv_value _ _ _ HFUEL). rewrite (HJVn ok1). reflexivity. }
assert (Hx0ne : rest_atR tb text p <> []).
{ unfold rest_atR. intros E0.
  assert (Hk : (Z.to_nat (p - text) < length tb)%nat) by (apply nth_error_Some; rewrite Hopen; discriminate).
  apply (f_equal (@length Z)) in E0. rewrite length_skipn in E0. cbn [length] in E0. lia. }
assert (RUNF : exists r' t2 ok2', jr_items prh_jr_strtod d o (rest_atR tb text p) (ok0 ++ okn) = (r', tr0 ++ tr ++ t2, ok2')).
{ pose proof (HVK []) as E1. rewrite app_nil_r in E1. unfold jbind in E1.
  destruct res as [a|]; cbv beta iota in E1.
  - exists (fst (fst (pv_kont f (Nat.succ d) o n cap (rev acc) nm a []))),
      (snd (fst (pv_kont f (Nat.succ d) o n cap (rev acc) nm a []))), (snd (pv_kont f (Nat.succ d) o n cap (rev acc) nm a [])).
    apply HEQ. rewrite E1. destruct (pv_kont f (Nat.succ d) o n cap (rev acc) nm a []) as [[r2 t2] ok2]. reflexivity.
  - exists None, [], []. rewrite app_nil_r. exact (HEQ okn None tr [] E1). }
destruct RUNF as (r' & t2 & ok2' & Ei).
assert (Wtr0 : pvm_wf tr0).
{ pose proof (pvm_wf_items d o (rest_atR tb text p) (ok0 ++ okn)) as Wi. rewrite Ei in Wi. cbn [fst snd] in Wi.
  unfold pvm_wf in Wi |- *. apply pvm_wf_from_app in Wi as (Wi & _). exact Wi. }
assert (Wtr : pvm_wf tr) by (pose proof (pvm_wf_value (Nat.succ d) (rest_atR tb text pc) okc) as Wv; rewrite HJV in Wv; exact Wv).
assert (CB : (PjGrammar.calls tr0 + PjGrammar.calls tr <= 2 * length (rest_atR tb text p))%nat).
{ pose proof (pvc_items_calls d o (rest_atR tb text p) (ok0 ++ okn) Hx0ne) as Hc. rewrite Ei in Hc.
  cbn [fst snd] in Hc. rewrite !calls_app in Hc. lia. }
assert (HHP : hpeakR (tr0 ++ tr) <= 224 * Z.of_nat (length (rest_atR tb text p)) + 512 * Z.of_nat (PjGrammar.MAXD - d)).
{ pose proof (pvm_hpeak_items d o (rest_atR tb text p) (ok0 ++ okn) _ _ _ Hx0ne Ei) as Hh.
  rewrite app_assoc in Hh. pose proof (pvm_hpeak_prefix (tr0 ++ tr) t2). lia. }
(* ---- the ledger move composes over prhPi_gtrace (HGTI: the prefix, the value's granted trace, the rest) ---- *)
assert (HGRANT0 : prh_granted ok0 cnt fail (calls tr0)) by (rewrite HGR; apply pik1_grant_granted).
assert (HCLE : (calls tr <= calls (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc)))%nat)
  by exact (pvm_calls_le_granted _ (jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc)) okc res tr okr
    (agrees_jr_value prh_jr_strtod _ _) HJV).
assert (HLEDv : rd_ledger_move Lam peak cnt fail ran most (ok0 ++ okn) (prhPi_gtrace d o (rest_atR tb text p))
  (tr0 ++ tr) (Dv ++ D0) Lam2 peak2 cnt2 fail2 ran2).
{ rewrite HGTI.
  apply (pvm_ledger_app Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc okn _ tr Dv Lam2 peak2 cnt2
    fail2 ran2 _ Wtr0 Wtr HLEN ltac:(lia)); [unfold SIZE_MAXZ; lia | lia | exact HGRANT0 | exact HCLE | exact HLED | exact HLMn]. }
(* ---- The batch kit: the value's run at the normalised outcome list, and its free list (jfv depends only on the outcomes of the
   calls the run makes: pvm_jfv_det; the fuel: PresetFreeFo.jfv_fuel) ---- *)
assert (HJVR : forall ok', jrv ReaderRes.jr_strtod f (Datatypes.S d) (rest_atR tb text pc) (okn ++ ok') = (res, tr, ok')).
{ intros ok'. rewrite (jr_value_fuel ReaderRes.jr_strtod f (Datatypes.S d) _ _ HFUEL). exact (HJVn ok'). }
assert (HFV : forall ok1, PresetReqAt.jfv ReaderRes.jr_strtod f (Datatypes.S d) (rest_atR tb text pc) (okn ++ ok1) =
  prhPv_frees (Nat.succ d) (rest_atR tb text pc) okc).
{ intros ok1. unfold prhPv_frees.
  transitivity (PresetReqAt.jfv ReaderRes.jr_strtod f (Datatypes.S d) (rest_atR tb text pc) okc).
  - apply (pvm_jfv_det ReaderRes.jr_strtod f (Datatypes.S d) (rest_atR tb text pc) okc (okn ++ ok1) res tr okr).
    + rewrite (jr_value_fuel ReaderRes.jr_strtod f (Datatypes.S d) _ okc HFUEL). exact HJV.
    + intros i Hi. rewrite app_nth1 by (rewrite Hokn; exact Hi). exact (Hnth i Hi).
  - exact (PresetFreeFo.jfv_fuel ReaderRes.jr_strtod f (Datatypes.S d) (rest_atR tb text pc) okc HFUEL). }
(* ---- The batch kit: the container's capacities and completed slots' free order at the return state (the callee kept pi_cont's
   read bytes: SV / SKD / SKY / SDI) ---- *)
assert (AGc : pj_agreeR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H W2) mem2) (pvm_cont_ufoot o v kids keys n Di)).
{ intros x [Hx | [(i & Hi & Hx) | [(Ho & i & Hi & Hx) | Hx]]].
  - exact (SV x Hx).
  - apply SKD. clear - Hi Hx. lia.
  - apply (SKY Ho). clear - Hi Hx Hncap. lia.
  - exact (SDI x Hx). }
pose proof (pvm_ncaps_frame (w_H Wc) (ms_mem ms) (mrestrict (w_H W2) mem2) (prh_lin Lamc) o v kids keys n cap acc Di HCONT
  HNC AGc)
  as HNC2.
pose proof (pvm_forder_frame _ _ (prh_lin Lamc) (prh_lin Lam2) o v kids keys n Di acc af HFO (fun x kk H => LSUB x kk H) AGc)
  as HFO2.
(* ---- The kit's pv_aftv_spec at the callee's float state fx', from the caller's journal at WS0 ++ WS1: WS0's traces are
   CW's (the pre) and parse_value's WS1 is at wbudget CW 0 with the same CW (YCbqGwild.wbudget_app) ---- *)
assert (HBUD : YCbqGwild.wbudget CW 0 (WS0 ++ WS1)).
{ change 0%nat with (0 + 0)%nat. apply YCbqGwild.wbudget_app; [exact HWS | exact HPW1]. }
refine (AFTV fx' fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  ly2 S2 Hp2 W2 mem2 md2 (k + k1) regs2 (WS0 ++ WS1) HJ2 HBUD _).
split; [split; [exact HFZ | exact (pvc_fregs_trans fx0 fxc fx' HFKc HFK)]|].
split; [exact HENT|].
(* memnorm at the return state by the callee's m-form keep (the jal wrote nothing, so the call state's memory is the
   pre's); the position and the live requests are composed on below (PItems_posb.pi_posb_call / pi_live_call) *)
split; [exact (HKMN HMN)|].
split.
{ (* pi_frame at the return state *)
  split; [rewrite Esp2; exact Hsp|]. split; [rewrite P3, Q3; exact Hgp|]. split; [rewrite P4, Q4; exact Htp|].
  rewrite Esp2.
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S136]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S128]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S120]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S112]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S104]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S96]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S88]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S80]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S72]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S64]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S56]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S48]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact S40]|].
  split; [|exact (conj Hret0 (conj He0 He16))].
  intros a Ha Hn. rewrite (HWIN a ltac:(lia) (pvc_notfp2 q v sl a Hn ltac:(lia))). exact (Hwin a Ha Hn). }
split.
{ (* pi_regs *)
  split; [rewrite P9, Q9; exact R9|]. split; [rewrite P19, Q19; exact R19|]. split; [rewrite P18, Q18; exact R18|].
  split; [rewrite P8, Q8; exact R8|]. split; [rewrite P20, Q20; exact R20|].
  split; [rewrite P26, Q26; exact R26|]. split; [rewrite P27, Q27; exact R27|].
  split; [rewrite P25, Q25; exact R25 | rewrite P23, Q23; exact R23]. }
split.
{ (* pi_regs_body *)
  split; [rewrite P22, Q22; exact R22|]. split; [rewrite P24, Q24; exact R24|]. rewrite Esp2.
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact M0]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact M32]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact M24]|].
  split; [eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact M16]|].
  eapply pvc_val_xfer; [intros kk Hk; apply KW; lia | exact M8]. }
split; [rewrite P21, Q21; exact H21|].
exists f, n, cap, acc, kids, keys, Di, nm, Dk, res, Dv, (ok0 ++ okn), (tr0 ++ tr), (Dv ++ D0), Lam2, peak2, cnt2, fail2, ran2.
split.
{ destruct res as [[t r]|]; cbv beta iota in HRES;
    [exact (tpvPs_ret (tpvP_RSome_of HRES)) | exact (tpvPn_ret (tpvP_RNone_of HRES))]. }
split; [exact Hncap|].
split; [exact (pvc_cont_xfer _ _ Lamc Lam2 o v kids keys n cap acc Di HCONT LSUB SV SKD
  (fun Ho x Hx => SKY Ho x ltac:(lia)) SDI)|].
split; [exact HDEP|]. split; [exact HAPART|].
split.
{ apply (pvc_key_xfer _ _ Lamc Lam2 o keys n nm Dk HKEY LSUB); [|exact SDK].
  intros Ho x Hx. exact (proj1 (SKY Ho x ltac:(lia))). }
split.
{ apply Permutation_trans with (D0 ++ Dv); [apply Permutation_app_comm|].
  replace (pi_sblk o kids keys cap ++ Di ++ Dk ++ Dv) with ((pi_sblk o kids keys cap ++ Di ++ Dk) ++ Dv)
    by (rewrite <- !app_assoc; reflexivity).
  apply Permutation_app_tail. exact HD0. }
split.
{ (* the run through the value *)
  unfold pv_run_after. pose proof HVK as HV. unfold jbind in HV. destruct res as [[t r]|].
  - intros ok1 r2 t2' ok2 Ek. rewrite <- !app_assoc. apply HEQ. rewrite (HV ok1). cbv beta iota. rewrite Ek. reflexivity.
  - intros ok1. rewrite <- app_assoc. apply HEQ. rewrite (HV ok1). reflexivity. }
split; [exact HLEDv|].
split; [exact (pvm_blocks_move_app B ly S lyc Sc ly2 S2 D0 tr0 Dv tr _ d _ HBM HBM2 HHP)|].
(* the travelling position and live requests through the value: parse_value's post transfer (its position implication
   over rd_hevs tr from Sc to S2, and its live-request permutation) composed on the block's own over tr0 *)
split.
{ intros osm ox oos oi oH0 ohist OP OR. rewrite PresetReqAt.rd_hevs_app in OR |- *.
  apply prh_run_at_app_iff in OR as [OR0 OR1].
  destruct (PItems_posb.pi_posb_post S Sc tr0 HPOSB osm ox oos oi oH0 ohist OP OR0) as (ohist1 & OP1).
  destruct (HPOS2 osm ox oos _ oH0 ohist1 OP1 OR1) as (ohist2 & OP2).
  exists ohist2. rewrite length_app, Nat.add_assoc. exact OP2. }
(* THE HULL USE (route (b)): parse_value's post bounds its use by its ALL-GRANTED list; read, that list is its trace
   tr (pvm_granted_some), so the block's use extends over tr (PresetHullBudget.hull_used_app); refused, the post's
   conjunct over the whole call's all-granted list (PItems_posb.pi_posb_hull_call, the list split by HGTI) *)
split.
{ destruct res as [[t r]|].
  - change (PresetHullBudget.hull_used S S2 (PresetReqAt.rd_hevs (tr0 ++ tr))).
    assert (Egs : prhPv_gtrace (Nat.succ d) (rest_atR tb text pc) = tr)
      by (unfold prhPv_gtrace; rewrite (pvm_granted_some _ _ _ _ _ _ _ HJV); reflexivity).
    rewrite Egs in HHU2. rewrite PresetReqAt.rd_hevs_app.
    exact (PresetHullBudget.hull_used_app _ _ _ _ _ (PItems_posb.pi_posb_hull S Sc tr0 HPOSB) HHU2).
  - change (PresetHullBudget.hull_used S S2 (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))).
    rewrite HGTI, !PresetReqAt.rd_hevs_app.
    exact (PItems_posb.pi_posb_hull_call S Sc S2 tr0 _ _ _ HPOSB eq_refl HHU2). }
split; [exact (PItems_posb.pi_live_call _ _ _ tr0 tr HLIVE HLV2)|].
split; [rewrite pvm_prh_held_app; lia|].
split; [rewrite length_app, calls_app, HLEN, Hokn; reflexivity|].
split; [rewrite pvm_lsum_app, PjGrammar.held_app, HLS2, HLSUM; lia|].
split; [exact HRL2|].
split; [exact Rq2|]. split; [exact Src2|]. split; [exact Home2|]. split; [exact At2|]. split; [exact Rv2|].
split; [exact HLED2|].
destruct res as [[t r]|].
- cbv beta iota in HRES. pose proof (tpvP_RSome_of HRES) as HRS. clear HRES.
  pose proof (tpvPs_freeord HRS) as HFOv. pose proof (tpvPs_in_ok HRS) as HI2. pose proof (tpvPs_node HRS) as HN2.
  pose proof (tpvPs_ncap HRS) as HNCv.
  pose proof (vspec_jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) okc) as VS. rewrite HJV in VS.
  destruct VS as (_ & _ & VS). destruct (VS t r eq_refl) as (Vl & Vc & _). cbn [fst snd] in Vc.
  split.
  { split; [exact HN2|].
    split; [exact (jr_value_depth prh_jr_strtod _ _ _ _ _ _ _ HJV)|].
    exists (text + len - Z.of_nat (length r)).
    split; [rewrite Nat2Z.inj_succ in HI2; unfold Z.succ in HI2; exact HI2|].
    split.
    { destruct (pvm_value_suffix _ _ _ _ _ _ _ HJV) as (pre & Hy). exact (pvc_rest_suffix tb text len pc pre r Hlen Hpcr Hy). }
    split; [rewrite HLc, Z.mod_small by lia; lia|].
    split; [change (Nat.succ (length r)) with (Datatypes.S (length r)); lia|]. split; [lia|].
    pose proof HROOM as RM. rewrite pvm_val_k_eq in RM. unfold jbind in RM.
    rewrite (pvm_jrv_value _ _ _ HFUEL), (pvm_granted_some _ _ _ _ _ _ _ HJV) in RM. cbv beta iota in RM.
    revert RM. destruct (pv_kont f (Nat.succ d) o n cap (rev acc) nm (t, r) []) as [[r3 t3] ok3].
    cbv beta iota. cbn [fst snd]. intros RM.
    exact (pvm_room_after Sc S2 tr t3 RM HRL2 HLV2). }
  (* THE BATCH KIT'S TAIL, the value READ: its outcomes were all granted (pvm_some_granted), so the prefix stays granted; the
     kid's capacities and free order are parse_value's Some arm; the model is pi_fl_eqV past the value *)
  split; [exact HCAPN|]. split; [exact HNC2|].
  exists af, lk, (prhPv_frees (Nat.succ d) (rest_atR tb text pc) okc).
  split; [exact HFO2|]. split; [exact HLK|].
  split.
  { unfold pi_grant. rewrite HGR, calls_app, repeat_app. f_equal.
    apply pvm_repeat_of_nth; [exact Hokn|]. intros i Hi. rewrite (Hnth i Hi).
    exact (pvm_some_granted _ (jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc)) okc _ tr okr
      (agrees_jr_value prh_jr_strtod _ _) HJV i Hi). }
  split; [exact HNCv|]. split; [exact HFOv|].
  intros ok1. rewrite <- app_assoc, (HFLV (okn ++ ok1)). unfold pi_jfv_k. cbv zeta.
  rewrite (HJVR ok1), (HFV ok1). reflexivity.
- cbv beta iota in HRES. pose proof (tpvP_RNone_of HRES) as HRN. clear HRES.
  pose proof (tpvPn_freeord HRN) as HFOv. pose proof (tpvPn_in_after HRN) as HA2. pose proof (tpvPn_fd HRN) as HF2.
  split; [split; [exact HF2|]; rewrite Nat2Z.inj_succ in HA2; unfold Z.succ in HA2; exact HA2|].
  split; [exact HCAPN|]. split; [exact HNC2|].
  exists af, lk, (prhPv_frees (Nat.succ d) (rest_atR tb text pc) okc).
  split; [exact HFO2|]. split; [exact HLK|].
  split.
  { (* THE OUTCOME (the post's clause at this state): the refused value's own outcome clause, at the position the
       granted prefix advanced to (pi_posb), under the run's split (prh_run_at_app_iff / prh_cons_from_sub); its
       failure window is the call's (the prefix made no refusal); so the value's granted run refused too, and the whole
       granted run is the prefix then that refusal *)
    intros osm ox oos oi oH0 ohist OP OR OC OF.
    rewrite HGTI in OR, OC, OF |- *.
    rewrite !PresetReqAt.rd_hevs_app in OR, OC |- *.
    apply prh_run_at_app_iff in OR as [OR0 OR1]. apply prh_run_at_app_iff in OR1 as [ORv _].
    destruct (PItems_posb.pi_posb_post S Sc tr0 HPOSB osm ox oos oi oH0 ohist OP OR0) as (ohist1 & OP1).
    rewrite !length_app in OC.
    pose proof (fun Hk => prh_cons_from_sub osm ox oos oi _ (length (PresetReqAt.rd_hevs tr0))
      (length (PresetReqAt.rd_hevs (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc)))) Hk OC) as OCv.
    specialize (OCv ltac:(clear; lia)).
    pose proof HLED as (_ & OEcc & (OFa & OFb) & _).
    rewrite !calls_app in OF.
    assert (OEcc' : cntc = cnt + Z.of_nat (calls tr0)).
    { rewrite OEcc. apply Z.mod_small. clear - Hcn0 Hcnt0 CB. lia. }
    assert (OEfc : failc = fail) by (apply OFb; clear - OF; lia).
    assert (OFv : failc < cntc \/ cntc + Z.of_nat (calls (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc))) <= failc)
      by (rewrite OEfc, OEcc'; clear - OF; lia).
    destruct (HOUT2 osm ox oos (oi + length (PresetReqAt.rd_hevs tr0))%nat oH0 ohist1 OP1 ORv OCv OFv)
      as (OEran & OEjv & ohist2 & OP2).
    assert (OEjv' : fst (jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) []) = (None, tr)) by exact OEjv.
    assert (OEgv : prhPv_gtrace (Nat.succ d) (rest_atR tb text pc) = tr)
      by (unfold prhPv_gtrace; rewrite OEjv'; reflexivity).
    assert (OEgaf : pvm_gafter f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) = [])
      by (unfold pvm_gafter; rewrite OEjv'; reflexivity).
    assert (OEK0 : pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) [] = (None, tr, [])).
    { rewrite pvm_val_k_eq. unfold jbind. rewrite (pvm_jrv_value _ _ _ HFUEL []).
      rewrite (agrees_nil _ _ (agrees_jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc))), OEjv'. reflexivity. }
    split; [rewrite OEran; exact (pik1_move_ran _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGRANT0 HLED)|].
    split; [rewrite OEK0 in HGT; exact HGT|].
    exists ohist2. rewrite OEgv in OP2.
    match goal with |- PresetRoomPos.iface_room_pos _ _ _ ?I _ _ _ =>
      replace I with (oi + length (PresetReqAt.rd_hevs tr0) + length (PresetReqAt.rd_hevs tr))%nat; [exact OP2|] end.
    rewrite OEgv, OEgaf, !length_app. cbn [PresetReqAt.rd_hevs flat_map length]. lia. }
  split.
  { (* THE INJECTED READING (the post's clause at ok0 ++ okn / tr0 ++ tr): the prefix granted all, so the chosen
       failure lies at or past the prefix's calls (the prefix's prh_oks), and the model's grant list there is ok0 then
       okk shifted by the prefix's calls: the model run is tr0, then the value's run under that shifted list, then the
       rest. A chosen failure inside the value's window: the value's own clause (tpvP_injected). Past it: the value's
       model run is its all-granted one (PjGrammar.agrees), so its OUTCOME says the all-granted value refuses too,
       the whole call's all-granted list ends with it, and the failure lies outside the call's window *)
    intros osm ox oos oi oH0 ohist IP IR IC IW.
    change ReaderRes.jr_strtod with prh_jr_strtod in IR, IC.
    pose proof HLED as ((IO1 & _ & _) & IEcc & (_ & IFb) & _).
    assert (IK0 : (calls tr0 <= Z.to_nat (fail - cnt))%nat).
    { destruct (le_lt_dec (calls tr0) (Z.to_nat (fail - cnt))) as [Hk|Hk]; [exact Hk|exfalso].
      pose proof (IO1 (Z.to_nat (fail - cnt)) Hk ltac:(lia)) as Hn.
      rewrite HGR, nth_repeat in Hn. discriminate Hn. }
    remember (Z.to_nat (fail - cnt) - calls tr0)%nat as j eqn:Hj.
    assert (IOK : PresetReqAt.okk (Z.to_nat (fail - cnt)) = ok0 ++ PresetReqAt.okk j).
    { unfold PresetReqAt.okk. rewrite HGR. replace (Z.to_nat (fail - cnt)) with (calls tr0 + j)%nat by lia.
      rewrite repeat_app, <- app_assoc. reflexivity. }
    rewrite IOK in IR, IC.
    destruct (jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) (PresetReqAt.okk j)) as [[rv tv] okv] eqn:IEV.
    assert (IEI : exists t'', snd (fst (jr_items prh_jr_strtod d o (rest_atR tb text p) (ok0 ++ PresetReqAt.okk j))) =
      tr0 ++ tv ++ t'').
    { destruct rv as [av|].
      - destruct (pv_kont f (Nat.succ d) o n cap (rev acc) nm av okv) as [[r9 t9] ok9] eqn:IEK.
        exists t9. rewrite (HEQ (PresetReqAt.okk j) r9 (tv ++ t9) ok9); [reflexivity|].
        rewrite pvm_val_k_eq. unfold jbind. rewrite (pvm_jrv_value _ _ _ HFUEL), IEV. cbv beta iota.
        rewrite IEK. reflexivity.
      - exists []. rewrite (HEQ (PresetReqAt.okk j) None tv okv); [rewrite app_nil_r; reflexivity|].
        rewrite pvm_val_k_eq. unfold jbind. rewrite (pvm_jrv_value _ _ _ HFUEL), IEV. reflexivity. }
    destruct IEI as (t'' & IEI). rewrite IEI in IR, IC.
    rewrite !PresetReqAt.rd_hevs_app in IR, IC. rewrite !length_app in IC.
    apply prh_run_at_app_iff in IR as [IR0 IR1]. apply prh_run_at_app_iff in IR1 as [IRv _].
    destruct (PItems_posb.pi_posb_post S Sc tr0 HPOSB osm ox oos oi oH0 ohist IP IR0) as (ohist1 & IP1).
    pose proof (fun Hk => prh_cons_from_sub osm ox oos oi _ (length (PresetReqAt.rd_hevs tr0))
      (length (PresetReqAt.rd_hevs tv)) Hk IC) as ICv.
    specialize (ICv ltac:(clear; lia)).
    assert (IEcc' : cntc = cnt + Z.of_nat (calls tr0)).
    { rewrite IEcc. apply Z.mod_small. clear - Hcn0 Hcnt0 CB. lia. }
    assert (IEfc : failc = fail) by (apply IFb; clear - IK0 IW; lia).
    assert (IG : prh_granted okc cntc failc (calls tr)).
    { destruct (Nat.lt_ge_cases j (calls (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc)))) as [Hjin|Hjout].
      - (* inside the value's window: the value's own clause *)
        assert (EJ : Z.to_nat (failc - cntc) = j) by (rewrite IEfc, IEcc'; lia).
        apply (HINJ2 osm ox oos (oi + length (PresetReqAt.rd_hevs tr0))%nat oH0 ohist1 IP1).
        + rewrite EJ. change ReaderRes.jr_strtod with prh_jr_strtod. rewrite IEV. exact IRv.
        + rewrite EJ. change ReaderRes.jr_strtod with prh_jr_strtod. rewrite IEV. exact ICv.
        + rewrite IEfc, IEcc'. lia.
      - (* past the value's window: a contradiction *)
        exfalso.
        assert (IEtv : tv = prhPv_gtrace (Nat.succ d) (rest_atR tb text pc)).
        { assert (IU : ok_upto (PresetReqAt.okk j)
            (calls (snd (fst (jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) []))))).
          { intros ii Hii. unfold PresetReqAt.okk.
            rewrite app_nth1 by (rewrite repeat_length; unfold prhPv_gtrace in Hjout; lia). apply nth_repeat. }
          pose proof (proj1 (agrees_jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) (PresetReqAt.okk j)) IU)
            as IA.
          rewrite IEV in IA. injection IA as _ IEt _. exact IEt. }
        assert (IWv : failc < cntc \/
          cntc + Z.of_nat (calls (prhPv_gtrace (Nat.succ d) (rest_atR tb text pc))) <= failc)
          by (right; rewrite IEfc, IEcc'; lia).
        rewrite IEtv in IRv, ICv.
        destruct (HOUT2 osm ox oos (oi + length (PresetReqAt.rd_hevs tr0))%nat oH0 ohist1 IP1 IRv ICv IWv)
          as (_ & IEjv & _).
        assert (IEjv' : fst (jr_value prh_jr_strtod (Nat.succ d) (rest_atR tb text pc) []) = (None, tr)) by exact IEjv.
        assert (IEga : pvm_gafter f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) = [])
          by (unfold pvm_gafter; rewrite IEjv'; reflexivity).
        rewrite HGTI, IEga, app_nil_r, calls_app in IW. lia. }
    intros ii Hii Hn. rewrite calls_app in Hii.
    destruct (Nat.lt_ge_cases ii (calls tr0)) as [Hi0|Hi0].
    - rewrite app_nth1 in Hn by (rewrite HLEN; exact Hi0). rewrite HGR, nth_repeat in Hn. discriminate Hn.
    - rewrite app_nth2 in Hn by (rewrite HLEN; exact Hi0). rewrite HLEN in Hn.
      rewrite (Hnth (ii - calls tr0)%nat ltac:(lia)) in Hn.
      pose proof (IG (ii - calls tr0)%nat ltac:(lia) Hn) as IE. rewrite IEcc', IEfc in IE. lia. }
  split; [exact HFOv|].
  intros ok1. rewrite <- app_assoc, (HFLV (okn ++ ok1)). unfold pi_jfv_k. cbv zeta.
  rewrite (HJVR ok1), (HFV ok1). reflexivity.
Qed.

End w.
