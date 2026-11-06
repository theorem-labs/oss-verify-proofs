(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 848 of its 915 lines of code are new or changed and 447 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece C of
   SEG_N: S 0x8676c -> M 0x86778, the
   fuzz_malloc call. Proves PvB_NCut.v's pnC_stmt as pnC_holds.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search (04:10Z, `proof-index
   parse_value`, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in the delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (04:21Z): no released srealizes-form proof of this program's parse_value.
   WHAT THE CODE DOES (listing lines 254-256): `sub s9, s6, a0` (s9 := m, the token length), `addi a0, s9, 1`
   (a0 := m + 1), `jal fuzz_malloc` (the PCall slot AS_fuzz_malloc), back at 0x86778 with a0 = res.
   HOW IT IS PROVED: one run of YC80x / YC1fPx's listing engine from S (no memory region: the stretch reads and writes
   no memory) to the PCall; then PRW_CallerJ.v's aj_call_xW over the fuzz_malloc text tfuzz_malloc_specX (a Section
   hypothesis, the call text) through fpostW_x_of_apost; then M's facts from (a) the call's widened journal (the
   caller's), (b) the callee's journal from the call state (its stack clause keeps every byte at or above the call's
   sp: the real frame, the caller window, the cursor q; its frame clause keeps the fake frame and its shadow; its
   block and image clauses keep the text and a node in a block), (c) fuzz_malloc's post (prh_alloc_post, the room
   invariant room_live_cf S', a0 = res), (d) the allocator laws at M for the node's and the text's shadow (alx_shadow,
   alx_zshadow_byte, alx_const_cells, and the CUTFIX laws below for a harness block, a registered read-only global and
   the shadow hull of an image string).
   The call's premises: the room invariant room_live_cf Sc from the call state's rd_room (pv_reader0); the request
   bound (prh_maxreq, the largest single request) and the live bound from the entry's rd_room over the granted trace,
   which for a number token with a leading digit is [EAlloc (S L)] with m <= L (PvB_Model.v pvm_unfold /
   pvm_number); the frame chain at the call is the entry chain behind the frame record parse_value saved at sp0 - 16
   (pnc_fpchain: the only word above sp0 that may differ from the entry's is the cursor's p field, a text address
   below alloc_ceiling, so a chain step that reads it stops the chain both before and after).
   KIT: the #102 kit (A/PRH_FnAlloc.v 740f4d11d144, A/PRH_Base.v (sha256 da55cb740765; internal record)):
   tfuzz_malloc_specX posts through fpostm (YCbqGmn's apost_base_xm), whose Q is PRH_Base's fQmn mem Q (Q and the keep
   `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'`); its fpre's `raZ regs < YM05.alloc_ceiling` is the
   jal's return pc, a listing slot (pnc_slot_lt_ceil), and its last conjunct frm_zero is the entry's (rd_pre's first:
   the stretch from the entry runs no float instruction, so the call's float state is fx0). The ledger carries the
   #102 statics most / own, the entry's, unchanged by the stretch.
   MEMNORM: S's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` holds at the call memory (the stretch writes no
   memory: the run's frame gives ms_mem = mem), and fuzz_malloc's keep gives it at M's memory (M's last conjunct).
   LIVE COUNTS AND ROOM (the post-implication form): fuzz_malloc's sec_cnt / ccnt24 premises at the call state Sc are
   pv_pre's two live-count premises (record premises 12 and 13): Sc's live list is the entry's (pv_reader0's rp_keep,
   PvB_Room.rp_keep_cnt), sec_cnt / ccnt24 are cnt of the live list by conversion (CfRoomLivePreset.rs_live_blocks is
   reflexivity), and cnt is below pkR at its first state (PresetRun.pkR_prefix at j = 0: pnc_cnt_pkR). The post's
   two position implications and prh_alloc_post's blocks give M's room conjunct (PvB_NCut.v): res = 0, the NULL arms
   keep ablocks, so the live list (pnc_live_ab), and E = [] keeps the position: rp_keep from the entry
   (PvB_Room.rp_keep_trans); res <> 0, the success arm appends (res - cf_head, m + 1 + cf_head), so the live list is
   Sc's with that request added, and E = [HMal (m + 1 + cf_head)] moves the position: PvB_Room.rp_call gives
   rp_post [EAlloc (S m)] from the entry, HHD turning rd_hev's HMal (S m + HEAD) into the call's request.
   SECTION HYPOTHESES: LAWS (AR_laws_x at the harness block's head length hl, a Section Context, as YCbqG.v states
   it), FMALLOC (the kit's call text tfuzz_malloc_specX: room invariant room_live_cf and the two live counts at
   entry, the room post as two position implications, no position at entry), CUTFIX_hshadow and CUTFIX_zs
   (reported: the shadow of a harness block / of a registered read-only global at any ARx state, which
   neither AR_laws_x nor a journal gives), CUTFIX_kimg (reported: the shadow hull of an image string,
   kept_at's third arm kept_img, at any ARx state), PA_BOX (MARKED instance fact: the kit's per-instance kept_img /
   kept_at bounds pa_lo / pa_hi lie inside the B' image box CUTFIX_zs is stated over; PvB_Inst.v pvI_pa_box), PSTRO
   (MARKED image fact: alloc.c's statics are not read-only), HHD (instance fact: the kit's head length is the model's,
   cf_head = PresetReqAt.HEAD; CfParams_preset).
   Numerals: listing offsets 20640 / 20652 (DERIVED: AF_pn_scan / AF_pn_mret of PvB_NCut.v); 8 16 24 32 56 64 160
   176, -8 -16 -104 (LENGTH: word, granule, alignment, node, fake-frame and real-frame sizes and saved-register
   offsets); 4096 (LENGTH: the low page); 2 ^ 40 / 2 ^ 44 / 2 ^ 47 / 2 ^ 62 / 2 ^ 64 (LENGTH: address widths); 0 .. 27
   as register numbers (WORD: RISC-V register indices); -1 / 18446744073709551615 (WORD: the multiplier the
   listing's `sub` lowers to, read off the engine's symbolic registers); 16400 / 16880 / 320 / 16560 (DERIVED:
   STK_fuzz_malloc, the least STK_parse_value, the two frames and LEAF_pv_pi at prh_img_B, by computation); 45 48
   123 91 34 116 102 110 (WORD: ASCII, PvB_NCut's); 1 / 256 (LENGTH: a one-byte shadow cell and its value range,
   pnc_kimg_shadow). No ADDRESS (the internal file port_addr_check.py on the old-base revision lib/B/Prog/PvB_NC.v (sha256 f98c75ade53e; internal record): 462 numerals,
   NON-ADDRESS-SAME 457, SAME-GEOMETRY 5, no flag; the re-point onto the moved base adds only the LENGTH numerals
   1 and 256 and repeats 0 8 64; the kit rebind adds the LENGTH numeral 2 ^ 40 (pnc_slot_lt_ceil, the
   listing's slot-offset width as pa_B_ok states it) and 4 (a slot's byte length, find_segment's width)). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut PvB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_NQ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIBc : PrhImg := prh_img_B.

(* ---- the stretch's symbolic state: every register an atom, no memory region, no fact ---- *)
Definition PNC_Bx : sv := SLit SHADOW_OFF.
Definition PNC_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pnc_ss : sstate := mkSS AF_pn_scan sr_atoms [] None (mkFacts [] [] []).

(* ---- pure: the granted trace of a number token with a leading digit is one allocation of at least m + 1 ---- *)
Lemma pnc_span_len : forall k z a r, PjGrammar.span PjGrammar.numch z = (a, r) ->
  Forall (fun b => PjGrammar.numch b = true) (firstn k z) -> (k <= length z)%nat -> (k <= length a)%nat.
Proof.
induction k as [|k IH]; intros z a r Hs Hf Hk; [lia|].
destruct z as [|b z]; [cbn in Hk; lia|].
cbn [firstn] in Hf. apply Forall_cons_iff in Hf as [Hb Hf].
cbn [PjGrammar.span] in Hs. rewrite Hb in Hs.
destruct (PjGrammar.span PjGrammar.numch z) as [a1 r1] eqn:E. injection Hs as <- <-.
cbn [length] in Hk |- *. specialize (IH z a1 r1 E Hf ltac:(lia)). lia.
Qed.

Lemma pnc_gt : forall d rest c y (m : nat), PjGrammar.skip rest = c :: y ->
  c <> 123 -> c <> 91 -> c <> 34 -> c <> 116 -> c <> 102 -> c <> 110 ->
  pn_lead (c :: y) (pn_sg c) -> (pn_sg c < m <= length (c :: y))%nat -> pn_span (c :: y) (pn_sg c) m ->
  exists L, prhPv_gtrace d rest = [PjGrammar.EAlloc (S L)] /\ (m <= L)%nat.
Proof.
intros d rest c y m Hsk H1 H2 H3 H4 H5 H6 (Hl0 & Hdig & Hlz) Hm Hsp. unfold pn_span in Hsp.
unfold prhPv_gtrace. rewrite pvm_unfold, Hsk.
rewrite (proj2 (Z.eqb_neq c 123) H1), (proj2 (Z.eqb_neq c 91) H2), (proj2 (Z.eqb_neq c 34) H3),
  (proj2 (Z.eqb_neq c 116) H4), (proj2 (Z.eqb_neq c 102) H5), (proj2 (Z.eqb_neq c 110) H6).
rewrite pvm_number. cbv beta iota zeta.
change (if c =? 45 then 1%nat else 0%nat) with (pn_sg c).
set (j := pn_sg c) in *. set (x := c :: y) in *.
pose proof (length_skipn j x) as Lsk.
destruct (skipn j x) as [|c' z] eqn:Esk; [cbn [length] in Lsk; lia|].
assert (Ec' : nth j x 0 = c').
{ rewrite <- (firstn_skipn j x) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Esk. replace (j - Nat.min j (length x))%nat with 0%nat by lia. reflexivity. }
rewrite Ec' in Hdig, Hlz. cbv beta iota. rewrite Hdig. cbn [negb].
assert (Hz : (c' =? 48) && match z with c1 :: _ => PjGrammar.digit c1 | [] => false end = false).
{ destruct (Z.eqb_spec c' 48) as [E48|E48]; [|reflexivity]. cbn [andb].
  destruct z as [|c1 z]; [reflexivity|]. destruct (PjGrammar.digit c1) eqn:Ed; [|reflexivity].
  exfalso. apply Hlz. split; [exact E48|]. cbn [length] in Lsk. split; [lia|].
  rewrite <- (firstn_skipn j x) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Esk. replace (S j - Nat.min j (length x))%nat with 1%nat by lia. exact Ed. }
rewrite Hz.
destruct (PjGrammar.span PjGrammar.numch z) as [a r] eqn:Es.
cbn [PjGrammar.take].
destruct (PjGrammar.whole prh_jr_strtod (firstn j x ++ c' :: a));
  (eexists; split; [reflexivity|]);
  (rewrite length_app, length_firstn; cbn [length];
   destruct (m - j)%nat as [|k] eqn:Ek; [lia|]; cbn [firstn] in Hsp; apply Forall_cons_iff in Hsp as [_ Hsp];
   cbn [length] in Lsk; pose proof (pnc_span_len k z a r Es Hsp ltac:(lia)); lia).
Qed.

(* ---- the stretch's register arithmetic (the engine lowers `sub` to an add of a times -1) ---- *)
Lemma pnc_U_sub : forall E a b, ew E 10 = w64 a -> ew E 22 = w64 b -> 0 <= a <= b -> b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit (-1))) (SOff 22 0)) = w64 (b - a).
Proof.
intros E a b Ha Hb H1 H2. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 10 a Ha) by lia. rewrite (U_atom E 22 b Hb) by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
rewrite Zplus_mod_idemp_l. replace (a * (2 ^ 64 - 1) + b) with ((b - a) + a * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma pnc_U_sub1 : forall E a b, ew E 10 = w64 a -> ew E 22 = w64 b -> 0 <= a <= b -> b + 1 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 18446744073709551615)) (SLit 1)) (SOff 22 0))
  = w64 (b - a + 1).
Proof.
intros E a b Ha Hb H1 H2. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !U_SAlu, U_SMd, !U_SLit, (U_atom E 10 a Ha) by lia. rewrite (U_atom E 22 b Hb) by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
replace (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (1 mod 2 ^ 64) with 1 by reflexivity.
rewrite Zplus_mod_idemp_l, <- Z.add_assoc, Zplus_mod_idemp_l.
replace (a * (2 ^ 64 - 1) + (1 + b)) with ((b - a + 1) + a * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* ---- the frame-pointer chain: a chain survives a change of words that each hold, before and after, a value in
   [4096, alloc_ceiling): such a word read as a frame record's saved s0 ends the chain (it is below the frame) and
   read as its saved ra is still a return address ---- *)
Lemma pnc_fpchain : forall (load load' : Z -> option Z) top ch bp lo,
  fpchain load bp top ch -> lo <= bp -> bp mod 8 = 0 -> bp < top - 16 ->
  (forall a, a mod 8 = 0 -> bp - 16 <= a -> a + 8 <= top -> load' a = load a \/
     (exists v v', load a = Some v /\ load' a = Some v' /\ 4096 <= v < lo /\ 4096 <= v' < lo)) ->
  exists ch', fpchain load' bp top ch'.
Proof.
intros load load' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp lo Hc Hbp H8 Htp Hw.
- exists []. cbn [fpchain] in Hc |- *. destruct Hc as (r & Hr & Hr4).
  destruct (Hw (bp - 8) ltac:(lia) ltac:(lia) ltac:(lia)) as [E | (v & v' & Ev & _ & Hv & _)].
  + exists r. rewrite E. exact (conj Hr Hr4).
  + rewrite Hr in Ev. injection Ev as <-. lia.
- cbn [fpchain] in Hc. destruct Hc as (-> & Hal & Hra & Hnf & Hra4 & Hrest).
  assert (Ha8 : exists ra', load' (bp - 8) = Some ra' /\ 4096 <= ra').
  { destruct (Hw (bp - 8) ltac:(lia) ltac:(lia) ltac:(lia)) as [E | (v & v' & Ev & Ev' & _ & Hv')].
    - exists ra. rewrite E. exact (conj Hra Hra4).
    - exists v'. split; [exact Ev' | lia]. }
  destruct Ha8 as (ra' & Hra' & Hra4').
  destruct (Hw (bp - 16) ltac:(lia) ltac:(lia) ltac:(lia)) as [E | (v & v' & Ev & Ev' & Hv & Hv')].
  + destruct (bad_next bp top nfp) eqn:Hb.
    * exists [(bp, ra', nfp)]. cbn [fpchain]. rewrite Hb.
      repeat split; try lia; try reflexivity; [exact Hra' | rewrite E; exact Hnf].
    * unfold bad_next in Hb. apply orb_false_iff in Hb as [Hb Hm]. apply orb_false_iff in Hb as [Hb1 Hb2].
      apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply negb_false_iff, Z.eqb_eq in Hm.
      destruct (IH nfp lo Hrest ltac:(lia) Hm ltac:(lia)) as (ch'' & Hch'').
      { intros a Ha Hlo Hhi. apply Hw; [exact Ha | lia | exact Hhi]. }
      exists ((bp, ra', nfp) :: ch''). cbn [fpchain].
      replace (bad_next bp top nfp) with false
        by (unfold bad_next; rewrite (proj2 (Z.leb_gt _ _) Hb1), (proj2 (Z.leb_gt _ _) Hb2), (proj2 (Z.eqb_eq _ _) Hm);
            reflexivity).
      repeat split; try lia; try reflexivity; [exact Hra' | rewrite E; exact Hnf | exact Hch''].
  + rewrite Hnf in Ev. injection Ev as <-.
    exists [(bp, ra', v')]. cbn [fpchain].
    replace (bad_next bp top v') with true
      by (unfold bad_next; rewrite (proj2 (Z.leb_le v' bp) ltac:(lia)); reflexivity).
    repeat split; try lia; try reflexivity; [exact Hra' | exact Ev'].
Qed.

(* ---- fpre's return-address bound (the kit's PRH_Base.v (sha256 586b1b19f7ad; internal record), fpre's last conjunct `raZ regs <
   YM05.alloc_ceiling`): a listing slot's pc is below the run's allocation ceiling. The slot's word is fetched from an
   image segment (pa_cert, pa_tbl_ok), so the pc is in_img, so below kLowMemEnd (pa_segs_low), which is below
   CEIL_MIN <= YM05.alloc_ceiling (YM05.alloc_ceiling_value). The proof is PRW_StepKit.pa_slot_lt_ceil's
   (lib/A/Prog/PRW_StepKit.v:235); the same steps as YC1fP.v
   pa_slot_img, with pa_segs_low in place of pa_img_range. ---- *)
Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Lemma pnc_slot_lt_ceil : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_segs_low _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia.
pose proof (@YM05.alloc_ceiling_value rc) as [[HC _] _]. unfold kLowMemEnd in HR. lia.
Qed.
End pc.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PSTX := (@prh_pst prh_img_B).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- Section hypotheses ---- *)
(* the kit's allocator laws (YCbqG.v AR_laws_x), at the harness block's head length hl *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the call text: the fuzz_malloc text of the kit (lib/A/PRH_FnAlloc.v (sha256 06329535a22a; internal record)), at the arm's float
   state; it takes and gives the room invariant room_live_cf, and takes the run position iface_room_pos and gives it
   back at the call's own event *)
Hypothesis FMALLOC : tfuzz_malloc_specX (fx := fx0) (cp := cp) (PI := prh_img_B) (PA := PA) B ARx SK.
(* CUTFIX (reported 05:4xZ): a harness block's user range, past its hidden head, has a block shadow and
   a visible hull at every ARx state (YGcfHeadSh.v ARx_hshadow_law_cf at hl = cf_head; ARx_hshadow_law_cf_ok proves it
   at ARcf). AR_laws_x's alx_shadow excludes a block whose base is in Hp, its alx_hshadow is at the Section's head
   length hl (not cf_head), and no journal keeps a block's shadow, so the node and the text in a harness block lose
   their shadow facts across fuzz_malloc without it. *)
Hypothesis CUTFIX_hshadow : forall ly S Hp W mem md b n, ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) ->
  In b Hp -> block_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (b + cf_head) (req_size n - cf_head) /\
  (cf_head < req_size n -> shadow_hull_vis (aview SEGS (w_H W) mem) (b + cf_head) (req_size n - cf_head)).
(* CUTFIX (reported with the one above): a text in a registered read-only global (kept_at's second arm) has its
   shadow facts at every ARx state (FuzzStrdupB.v sd_src_shadow's in_zs arm at ARcf: AR_zshadow_law_cf with the
   granule-aligned as_zero_shadow entries, and the image's shadow hull img_shadow_vis_cf of the start-up). *)
Hypothesis CUTFIX_zs : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> in_zs B p n ->
  IMG_LO_B + 64 <= p -> p + n + 64 <= IMG_TOP_B ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n).
(* CUTFIX (reported 07:2xZ, on the rebase onto this walk's moved base): the shadow hull of an image
   string under kept_at's third arm (kept_img, PRH_Base.v route (a)) is visible at every ARx state. The moved cut's
   text home (pv_reader0's prhReader_home, through kept_at) now admits such a string. AR_laws_x's alx_const_cells
   keeps the shadow byte of each of its granules, so pnc_kimg_shadow below derives its addressable range; but the hull
   also reads the shadow bytes of the image around the string (up to 64 bytes each side, inside kept_img's 64-byte
   margins), which no law states and no journal keeps (at ARcf: the image's shadow hull img_shadow_vis_cf of
   the start-up, as for CUTFIX_zs). *)
Hypothesis CUTFIX_kimg : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> kept_img (PA := PA) B p n -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
(* MARKED instance fact, discharged at PI_prog_B (PAImg_prog.v: pa_lo := IMG_LO_B, pa_hi := IMG_TOP_B; PvB_Inst.v
   pvI_pa_box): the per-instance image bounds of the kit's kept_img / kept_at (PRH_Base.v (sha256 da55cb740765; internal record), `pa_lo + 64 <= p
   /\ p + n + 64 <= pa_hi`) lie inside the B' image box CUTFIX_zs is stated over (PvB_A_Home.v PA_BOX, same text) *)
Hypothesis PA_BOX : IMG_LO_B <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= IMG_TOP_B.
(* MARKED image fact, discharged at PI_prog_B (S1ImgB.v pst_not_ro_B): alloc.c's statics are not read-only *)
Hypothesis PSTRO : forall a, Exists (in_zr a) PSTX -> ~ in_roP SEGS RLO RHI a.
(* instance fact (CfParams_preset: 16 = fuzz/alloc.c's HEAD): the kit's head length is the model's, so the call's
   request m + 1 + cf_head is rd_hev's HMal (S m + HEAD), the model's event of the number's allocation *)
Hypothesis HHD : cf_head = PresetReqAt.HEAD.

(* the live list is the block sizes of ablocks (ablocks renames the bases only; CfRoomLivePreset.rs_live_blocks) *)
Lemma pnc_live_ab : forall ly S, map snd (ablocks B ly S) = PresetRoom.rs_live (YGcfRoom.room_of_cf S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.

(* a count of the live list is at most its peak along any events (PresetRun.pkR_prefix at j = 0) *)
Lemma pnc_cnt_pkR : forall f s es, (PresetReqAt.cnt f s <= PresetRun.pkR f s es)%nat.
Proof. intros f s es. exact (PresetRun.pkR_prefix f es s 0). Qed.

(* ---- byte transports ---- *)
Lemma pnc_vm : forall H H' (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> aview SEGS H' m' z = aview SEGS H m z) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v E V k Hk.
rewrite (mbyte_of_aview SEGS H H' m m' _ (E (a + Z.of_nat k) ltac:(lia))). exact (V k Hk).
Qed.

Lemma pnc_garr : forall H H' (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> aview SEGS H' m' z = aview SEGS H m z) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l E G j Hj. destruct (G j Hj) as [Hv Hb]. split; [|exact Hb].
apply (pnc_vm H H' m m'); [|exact Hv]. intros z Hz. apply E. cbn in Hz. lia.
Qed.

(* two memories that both hold v at [a, a + n) agree there *)
Lemma pnc_vm_eq : forall H H' (m m' : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v ->
  forall z, a <= z < a + Z.of_nat n -> aview SEGS H' m' z = aview SEGS H m z.
Proof.
intros H H' m m' a n v V V' z Hz. unfold aview.
replace z with (a + Z.of_nat (Z.to_nat (z - a))) by lia.
rewrite (V (Z.to_nat (z - a)) ltac:(lia)), (V' (Z.to_nat (z - a)) ltac:(lia)). reflexivity.
Qed.

Lemma pnc_wr_present : forall H (m : word -> option byte) z, 0 <= z < 2 ^ 64 -> ~ in_img SEGS z ->
  writable_at SEGS (mrestrict H m) z -> apresent H m z.
Proof.
intros H m z Hz Hni Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent.
assert (Hseg : find_segment SEGS (bv_unsigned (Z_to_bv 64 z)) 1 = None).
{ destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 z)) 1) as [seg|] eqn:Ef; [|reflexivity].
  exfalso. apply Hni. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by lia. exists seg. split; [exact Hin|lia]. }
destruct (H (Z_to_bv 64 z)).
- rewrite Hseg in Hw. exfalso. apply Hw. reflexivity.
- split; [reflexivity|]. destruct (m (Z_to_bv 64 z)) as [b|].
  + exists b. reflexivity.
  + rewrite Hseg in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma pnc_wr : forall H H' (m m' : word -> option byte) z, 0 <= z < 2 ^ 64 -> ~ in_img SEGS z ->
  aview SEGS H' m' z = aview SEGS H m z -> writable_at SEGS (mrestrict H m) z -> writable_at SEGS (mrestrict H' m') z.
Proof.
intros H H' m m' z Hz Hni E Hw. apply (apresent_writable SEGS).
exact (apresent_transfer SEGS H H' m m' z Hz Hni E (pnc_wr_present H m z Hz Hni Hw)).
Qed.

Lemma pnc_rdword : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a E. pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. unfold rdword.
rewrite E0, (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7) by lia. reflexivity.
Qed.

Lemma pnc_rdword_val : forall H (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ---- shadow facts ---- *)
Lemma pnc_hull_sub : forall (rd : Z -> option Z) p mm d n, shadow_hull_vis rd p mm -> p <= d -> d + n <= p + mm ->
  0 < n -> shadow_hull_vis rd d n.
Proof.
intros rd p mm d n H Hpd Hdn Hn s Hs. apply H.
assert (M : forall x y, x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8).
{ intros x y Hxy. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
pose proof (M p d Hpd). pose proof (M (d + n - 1) (p + mm - 1) ltac:(lia)). lia.
Qed.

Lemma pnc_fs8 : forall c, 56 <= fs_frame_bytes c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z.le_gt_cases 0 c) as [Hc|Hc].
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z.mod_mul. lia.
- exfalso. assert (En : c = - (- c)) by lia. remember (- c) as n eqn:Hn. rewrite En in H.
  rewrite Z.shiftl_div_pow2 in H by lia. rewrite ?Z.opp_involutive in H.
  assert (H2 : 2 <= 2 ^ n).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (H3 : 64 / 2 ^ n <= 64 / 2) by (apply Z.div_le_compat_l; lia).
  change (64 / 2) with 32 in H3. lia.
Qed.

Lemma pnc_sh_in : forall fa fs x, fa mod 8 = 0 -> fs mod 8 = 0 -> fa <= x < fa + fs ->
  fa / 8 <= x / 8 < fa / 8 + fs / 8.
Proof.
intros fa fs x Ha Hs Hx. pose proof (Z.div_mod fa 8 ltac:(lia)) as Da. pose proof (Z.div_mod fs 8 ltac:(lia)) as Ds.
rewrite Ha, Z.add_0_r in Da. rewrite Hs, Z.add_0_r in Ds.
split; [apply Z.div_le_mono; lia|].
apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_add_distr_l. rewrite <- Da, <- Ds. lia.
Qed.

(* under the ledger, a live block whose base is not in Hp holds no base of Hp *)
Lemma pnc_hp_apart : forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR (_ & _ & HF & HP) Hin Hnb h Hh Hr.
pose proof (Permutation_in _ HP Hh) as Hh'.
apply in_map_iff in Hh' as ([a' k] & Eh & Hak). cbn [fst] in Eh.
destruct (proj1 (Forall_forall _ _) HF (a', k) Hak) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
rewrite Eh in Hblk.
assert (Hne : (b, m) <> (h, k + cf_head)).
{ intros E. injection E as E1 _. rewrite E1 in Hnb. exact (Hnb Hh). }
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m h (k + cf_head) HAR Hin Hblk Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (H1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.

(* a range inside a live harness block of the ledger is addressable, with a visible hull when non-empty *)
Lemma pnc_lam_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own b m a len,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) Lam -> b <= a -> a + len <= b + m -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len /\
  (0 < len -> shadow_hull_vis (aview SEGS (w_H W) mem) a len).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m a len HAR HLED Hin Hba Hab Hlen.
destruct (Z.eq_dec len 0) as [->|Hl0]; [split; [apply range_addressable_nil; lia | intros; lia]|].
destruct HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & Hhp & _).
cbn [fst snd] in Hm0, Hblk, Hhp.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (CUTFIX_hshadow ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk Hhp) as [Hbs Hhv].
assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
rewrite Hrq in Hbs, Hhv.
replace (b - cf_head + cf_head) with b in Hbs, Hhv by lia. replace (m + cf_head - cf_head) with m in Hbs, Hhv by lia.
split.
- eapply block_shadow_range; [exact Hbs | exact Hba | exact Hab].
- intros Hl. apply (pnc_hull_sub _ b m); [apply Hhv; lia | lia | lia | lia].
Qed.

(* a range inside a live allocator block whose base is not a hidden head *)
Lemma pnc_blk_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own b m a len,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp -> b <= a -> a + len <= b + m -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len /\
  (0 < len -> shadow_hull_vis (aview SEGS (w_H W) mem) a len).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m a len HAR HLED Hin Hb Hba Hab Hlen.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md b m HAR Hin
  (pnc_hp_apart ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hb)) as [Hbs Hhv].
split.
- destruct (Z.eq_dec len 0) as [->|Hl0]; [apply range_addressable_nil; lia|].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- intros Hl. apply (pnc_hull_sub _ b (req_size m)); [exact Hhv | lia | lia | lia].
Qed.

(* a text under kept_at's third arm (kept_img, an image string): addressable at every ARx state, each byte by its
   granule's zero-shadow range (CUTFIX_zs over the granule, inside kept_img's 64-byte margins) or by its granule's
   const-shadow cell (alx_const_cells: the shadow byte reads 0 or a value above the byte's offset in the granule); its
   hull by CUTFIX_kimg *)
Lemma pnc_kimg_shadow : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> kept_img (PA := PA) B p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n).
Proof.
intros ly S Hp W mem md p n HAR HK. split; [|exact (CUTFIX_kimg ly S Hp W mem md p n HAR HK)].
pose proof HK as (Hlo & Hhi & Hro).
intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hcell & Hv)]).
- pose proof PA_BOX as (HB1 & HB2).
  assert (Hg1 : IMG_LO_B + 64 <= x - x mod 8) by (clear - Hlo HB1 Hx; unfold IMG_LO_B in *; lia).
  assert (Hg2 : x - x mod 8 + 8 + 64 <= IMG_TOP_B) by (clear - Hhi HB2 Hx; unfold IMG_TOP_B in *; lia).
  destruct (CUTFIX_zs ly S Hp W mem md (x - x mod 8) 8 HAR Hzs Hg1 Hg2) as [Hra _].
  exact (Hra x ltac:(lia)).
- pose proof (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) as HC.
  rewrite Forall_forall in HC. specialize (HC _ (Hcell ly)).
  cbn [cell_holds c_at c_val c_w z1 c1 aeval] in HC. specialize (HC 0%nat ltac:(lia)).
  change (Z.of_nat 0) with 0 in HC. rewrite Z.add_0_r in HC. unfold shadow_addr in HC.
  assert (Ev : le_byte v 1 0 = v).
  { unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia. }
  rewrite Ev in HC. exists v. split; [unfold shadow_of_addr; exact HC | unfold saddr_ok; lia].
Qed.

(* ---- fuzz_malloc's three arms, as M uses them: a ledger at M over a list that holds the entry's, the blocks kept, and
   no old block's base newly hidden ---- *)
Lemma pnc_post : forall n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' md', 0 <= n ->
  ARx ly' S' Hp' W' mem' md' ->
  prh_alloc_post B n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' ->
  exists Lam' peak' cnt' fail' ran', prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\
  (forall x, In x Lam -> In x Lam') /\ (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) /\
  (forall b mm, In (b, mm) (ablocks B ly S) -> 0 <= mm -> ~ In b Hp -> ~ In b Hp').
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' md' Hn HAR HAP.
destruct HAP as [(_ & _ & EHp & Eab & HL) | [(_ & _ & EHp & Eab & _ & _ & HL) |
  (_ & H16 & _ & _ & EHp & Eab & _ & _ & _ & HL)]].
- do 5 eexists. split; [exact HL|]. split; [intros x Hx; exact Hx|]. rewrite Eab, EHp.
  split; [intros x Hx; exact Hx|]. intros b mm _ _ Hb; exact Hb.
- do 5 eexists. split; [exact HL|]. split; [intros x Hx; exact Hx|]. rewrite Eab, EHp.
  split; [intros x Hx; exact Hx|]. intros b mm _ _ Hb; exact Hb.
- do 5 eexists. split; [exact HL|]. split; [intros x Hx; right; exact Hx|].
  split; [intros x Hx; rewrite Eab; apply in_or_app; left; exact Hx|].
  intros b mm Hin Hmm Hb. rewrite EHp. intros [Eb | Hb']; [|exact (Hb Hb')].
  assert (Hnew : In (res - cf_head, n + cf_head) (ablocks B ly' S'))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W' mem' md' _ _ HAR Hnew) as (_ & _ & _ & _ & _ & Hpw).
  destruct (in_split _ _ Hin) as (l1 & l2 & El).
  set (f := fun b0 : Z * Z => (fst b0, req_size (snd b0))) in Hpw.
  assert (Eq : map f (ablocks B ly' S') = map f l1 ++ f (b, mm) :: map f l2 ++ f (res - cf_head, n + cf_head) :: []).
  { rewrite Eab, El, !map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
  pose proof (pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw Eq) as D. unfold f, zdisjoint in D. cbn [fst snd] in D.
  pose proof (@cf_head_nonneg cp) as Hh0.
  assert (R1 : 1 <= req_size mm) by (unfold req_size; destruct (Z.eqb_spec mm 0); lia).
  assert (R2 : 1 <= req_size (n + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (n + cf_head) 0); lia).
  lia.
Qed.

(* a block of the ledger's state whose user range is not a harness block's has no hidden head at its base *)
Lemma pnc_nl_nhp : forall ly S Hp W mem md Lam peak cnt fail ran most own b mm,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, mm) (ablocks B ly S) -> 0 < mm -> ~ In (b + cf_head, mm - cf_head) Lam -> ~ In b Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b mm HAR (_ & _ & HF & HP) Hin Hmm Hnl Hb.
pose proof (Permutation_in _ HP Hb) as Hb'. apply in_map_iff in Hb' as ([a' k] & Eb & Hak). cbn [fst] in Eb.
destruct (proj1 (Forall_forall _ _) HF (a', k) Hak) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
rewrite Eb in Hblk.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (Z.eq_dec mm (k + cf_head)) as [Em | Ne].
- apply Hnl. replace (b + cf_head) with a' by lia. replace (mm - cf_head) with k by lia. exact Hak.
- assert (Hne : (b, mm) <> (b, k + cf_head)) by (intros E; injection E as E; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b mm b (k + cf_head) HAR Hin Hblk Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (1 <= req_size mm) by (unfold req_size; destruct (Z.eqb_spec mm 0); lia).
  assert (1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  lia.
Qed.

Lemma pnc_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

Lemma pnc_bad : forall fp top nfp, bad_next fp top nfp = true <-> (nfp <= fp \/ top - 16 <= nfp \/ nfp mod 8 <> 0).
Proof.
intros fp top nfp. unfold bad_next. rewrite !orb_true_iff, !Z.leb_le, negb_true_iff, Z.eqb_neq. tauto.
Qed.

Lemma pnc_fp3 : forall q v z,
  (q <= z < q + 8) \/ (q + 16 <= z < q + 20) \/ (v <= z < v + 56) \/
  ~ inFP [(q, q + 8); (q + 16, q + 20); (v, v + 56)] z.
Proof.
intros q v z.
destruct (Z_le_gt_dec q z); destruct (Z_lt_le_dec z (q + 8)); [left; lia| | |];
(destruct (Z_le_gt_dec (q + 16) z); destruct (Z_lt_le_dec z (q + 20)); [right; left; lia| | |]);
(destruct (Z_le_gt_dec v z); destruct (Z_lt_le_dec z (v + 56)); [right; right; left; lia| | |]);
right; right; right; intros (r & Hr & Hz); cbn in Hr; destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hz; lia.
Qed.

(* the register of a stopped symbolic state at a call, read off the engine's register list *)
Ltac pnc_reg HS r H :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
  pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H end.
(* a callee-saved register across the call: the callee keeps it (HPk), the stretch kept it (Q), S held it (R) *)
Ltac pnc_kr HPk Q R n r :=
  etransitivity; [apply (HPk n r); [unfold acallee_saved; lia | reflexivity] | etransitivity; [exact Q | exact R]].

Lemma pnc_ereg : forall E regs (n : nat) (r : bv 5), (forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs []) i) ->
  (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> sv_denot E (SOff n 0) = getr regs r.
Proof.
intros E regs n r EL Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EL n Hn).
exact (ew_Ereg_nat regs [] n r Hr).
Qed.

(* the granule arithmetic the walk below needs, proved here so that its lia calls run without the euclidean
   expansion of every div / mod in its large context *)
Lemma pnc_mod16 : forall a b c, a mod 32 = 0 -> b mod 16 = 0 -> c mod 16 = 0 -> (a - (b + c)) mod 16 = 0.
Proof. intros a b c Ha Hb Hc. lia. Qed.
Lemma pnc_m32 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof. intros x Hx. lia. Qed.
Lemma pnc_word_apart : forall a q z, a mod 8 = 0 -> q mod 8 = 0 -> a <> q -> a <= z < a + 8 -> ~ (q <= z < q + 8).
Proof. intros a q z Ha Hq Hne Hz Hz'. lia. Qed.
Lemma pnc_m16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x Hx. lia. Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- the segment ---- *)
Theorem pnC_holds : pnC_stmt (fx0 := fx0) (SK := SK) B ARx.
Proof.
intros en HPRE HKM W' ms mdc HAT.
destruct HAT as (regs & mem & Y & fa & fl & pos & lyc & Sc & k & c & y & m & Ems & HBASE & HBODY & HRD0 & HV24 &
  R21 & R10 & R12 & Hlead & Hm & Hspan & Hstop & R22 & HMN).
pose proof HBASE as (HKR & R9 & R19 & R20 & R24 & Hskip & Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6).
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
pose proof HRD0 as (Hfrs & Hab & Hbb & HRKr & Hcur1 & Hsrc1 & Hhome1 & Hnode1 & HvRA1 & HLED1 & HRP1 & HSEC1).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs0.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk0. pose proof (ajx_hi HJ) as J1.
pose proof (ajx_blk HJ) as J2. pose proof (ajx_img HJ) as J3. pose proof (ajx_frm HJ) as J4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstk.
pose proof (ajx_extra HJ) as J5. pose proof (ajx_qt HJ) as HQT.
pose proof HPRE as (HFPRE & HCTX & _ & _ & HCHE & HCUR & Hq10 & Hv11 & HRDP & HROOMp & HFRB & _ & HPKS & HPK24 & _ & _).
pose proof HFPRE as (HAFN & HRO & H64).
pose proof HAFN as (HAR0 & Hra_ok & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hchain & HQT0).
pose proof HRDP as (Hfrm0 & Hmuniv & Hruniv1 & Hruniv2 & Hcur & Hwin & Hqlo & Hqhi & Hqra & Hsrc & Hhome &
  Hmaxrun & Hnode & Hqv & Htv & Hvwin & HLED0 & Hdmax & Hcntb & Htxc).
pose proof HROOMp as (HRL0 & Hhpk & Hlive).
pose proof Hwin as (He0 & He16 & Hetop & Hepres).
pose proof Hstk0 as (Hsp16 & HSTKn & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop20 & Htop0).
pose proof Hnode as (Hv4096 & Hv8 & Hvrw & Hvzero & Hvat & Hvam & Hvown & HvRA).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
change (spZ (pe_regs en)) with (pe_sp en) in *.
set (sp0 := pe_sp en) in *. set (ee := pe_e en) in *.
(* the stack numbers: parse_value's bound and fuzz_malloc's *)
assert (HSTK : 16880 <= pe_STK en).
{ unfold pe_STK. generalize (pe_d en) as d. intros d. unfold STK_parse_value.
  match goal with |- context [Z.of_nat (S ?n) * ?f + ?l] =>
    assert (Ef : f = 320) by reflexivity; assert (El : l = 16560) by reflexivity; rewrite Ef, El;
    assert (1 <= Z.of_nat (S n)) by lia end. nia. }
assert (FFM : @STK_fuzz_malloc prh_img_B = 16400) by (vm_compute; reflexivity).

(* ---- the run from S to the call ---- *)
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall i : nat, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs []) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (HS : st_ok_pi SEGS VAL E pnc_ss (restrict (w_H W') ms)).
{ rewrite Ems. unfold pn_ms. rewrite restrict_mkst_fx. unfold pnc_ss.
  replace (Z_to_bv 64 (BASE + AF_pn_scan)) with (Z_to_bv 64 (VAL A_TEXT + AF_pn_scan)) by reflexivity.
  apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat split. }
assert (SHOK : sh_ok SEGS PNC_Bx [] E (rdW W' (ms_mem ms))) by (constructor).
subst ms. unfold pn_ms in *.
pose (RUN := @paj_run_x fx0 rc SK B_prog_listing PL_prog_B PA B PSTX ARx _ LAWS).
paj_run_tok_x RUN HS HJ SHOK PNC_Bspan; [intros a (r & Hr & _); unfold pnc_ss in Hr; cbn in Hr; destruct Hr|].
(* ---- at the call: the memory is S's (the stretch wrote nothing), the registers are read off the engine ---- *)
assert (Emem : ms_mem ms = mem).
{ apply functional_extensionality. intros z. apply HF. intros (r & Hr & _). unfold pnc_ss in Hr. cbn in Hr. exact Hr. }
rewrite Emem in HJ. clear HFr HG SHOK.
pmkst HS. rewrite Emem.
set (md' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
pnc_reg HS (1%bv : bv 5) Q1. pnc_reg HS (10%bv : bv 5) Q10. pnc_reg HS (25%bv : bv 5) Q25.
pnc_reg HS (2%bv : bv 5) Q2. rewrite (pnc_ereg E regs 2 2%bv EL ltac:(cbv; lia) eq_refl) in Q2.
pnc_reg HS (3%bv : bv 5) Q3. rewrite (pnc_ereg E regs 3 3%bv EL ltac:(cbv; lia) eq_refl) in Q3.
pnc_reg HS (4%bv : bv 5) Q4. rewrite (pnc_ereg E regs 4 4%bv EL ltac:(cbv; lia) eq_refl) in Q4.
pnc_reg HS (8%bv : bv 5) Q8. rewrite (pnc_ereg E regs 8 8%bv EL ltac:(cbv; lia) eq_refl) in Q8.
pnc_reg HS (9%bv : bv 5) Q9. rewrite (pnc_ereg E regs 9 9%bv EL ltac:(cbv; lia) eq_refl) in Q9.
pnc_reg HS (18%bv : bv 5) Q18. rewrite (pnc_ereg E regs 18 18%bv EL ltac:(cbv; lia) eq_refl) in Q18.
pnc_reg HS (19%bv : bv 5) Q19. rewrite (pnc_ereg E regs 19 19%bv EL ltac:(cbv; lia) eq_refl) in Q19.
pnc_reg HS (20%bv : bv 5) Q20. rewrite (pnc_ereg E regs 20 20%bv EL ltac:(cbv; lia) eq_refl) in Q20.
pnc_reg HS (21%bv : bv 5) Q21. rewrite (pnc_ereg E regs 21 21%bv EL ltac:(cbv; lia) eq_refl) in Q21.
pnc_reg HS (22%bv : bv 5) Q22. rewrite (pnc_ereg E regs 22 22%bv EL ltac:(cbv; lia) eq_refl) in Q22.
pnc_reg HS (23%bv : bv 5) Q23. rewrite (pnc_ereg E regs 23 23%bv EL ltac:(cbv; lia) eq_refl) in Q23.
pnc_reg HS (24%bv : bv 5) Q24. rewrite (pnc_ereg E regs 24 24%bv EL ltac:(cbv; lia) eq_refl) in Q24.
pnc_reg HS (26%bv : bv 5) Q26. rewrite (pnc_ereg E regs 26 26%bv EL ltac:(cbv; lia) eq_refl) in Q26.
pnc_reg HS (27%bv : bv 5) Q27. rewrite (pnc_ereg E regs 27 27%bv EL ltac:(cbv; lia) eq_refl) in Q27.
set (regsc := ms_regs ms) in *.
set (p1 := pn_p1 en (c :: y)) in *.
pose proof Hcur1 as (Vq1 & Vq81 & Vq161 & Hrw1 & Hq8 & Ht0 & Htl & Hp1r & Hlen & Gtb1 & Hqt & Hd).
pose proof Hcur as (Vq0 & _ & Vq160 & _ & _ & _ & _ & Hp0r & _ & _ & _ & _).
pose proof Hsrc as (_ & Ht4096 & Htc & _).
pose proof (@pa_B_ok _ _ PA) as HBOK.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Ep1 : p1 = pe_text en + pe_len en - Z.of_nat (length (c :: y))) by reflexivity.
assert (Ra0 : getr regsc 10 = w64 (Z.of_nat m + 1)).
{ rewrite Q10, (pnc_U_sub1 E p1 (p1 + Z.of_nat m)).
  - f_equal. lia.
  - rewrite (EL 10%nat ltac:(cbv; lia)), (ew_Ereg_nat regs [] 10 10%bv eq_refl). exact R10.
  - rewrite (EL 22%nat ltac:(cbv; lia)), (ew_Ereg_nat regs [] 22 22%bv eq_refl). exact R22.
  - lia.
  - lia. }
assert (Rs9 : getr regsc 25 = w64 (Z.of_nat m)).
{ rewrite Q25, (pnc_U_sub E p1 (p1 + Z.of_nat m)).
  - f_equal. lia.
  - rewrite (EL 10%nat ltac:(cbv; lia)), (ew_Ereg_nat regs [] 10 10%bv eq_refl). exact R10.
  - rewrite (EL 22%nat ltac:(cbv; lia)), (ew_Ereg_nat regs [] 22 22%bv eq_refl). exact R22.
  - lia.
  - lia. }
assert (Rra : getr regsc 1 = Z_to_bv 64 (BASE + AF_pn_mret)) by (rewrite Q1; apply codeptr_val; exact HEI).

(* ---- the frame chain at the call: the entry chain behind parse_value's frame record ---- *)
assert (HCH : exists ch1, achain lyc (aview SEGS (w_H W') mem) Y sp0 ch1).
{ pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ETOP1 & _).
  destruct (Z_le_gt_dec (ly_top lyc - 16) sp0) as [Hhi|Hlo].
  - exists []. left. split; [right; left; exact Hhi | reflexivity].
  - pose proof (proj1 (Forall_forall _ _) Vsav (-8, 1) ltac:(cbn; tauto)) as V8.
    pose proof (proj1 (Forall_forall _ _) Vsav (-16, 8) ltac:(cbn; tauto)) as V16.
    cbn [fst snd] in V8, V16.
    assert (HSV8 : rdword (aview SEGS (w_H W') mem) (sp0 - 8) = Some (raZ (pe_regs en))).
    { replace (sp0 - 8) with (sp0 + -8) by lia. apply pnc_rdword_val; [exact V8|].
      pose proof (bv_unsigned_in_range 64 (getr (pe_regs en) 1)) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
      exact Hr. }
    assert (HSV16 : rdword (aview SEGS (w_H W') mem) (sp0 - 16) = Some (s0Z (pe_regs en))).
    { replace (sp0 - 16) with (sp0 + -16) by lia. apply pnc_rdword_val; [exact V16|].
      pose proof (bv_unsigned_in_range 64 (getr (pe_regs en) 8)) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
      exact Hr. }
    set (s0e := s0Z (pe_regs en)) in *. set (rae := raZ (pe_regs en)) in *.
    rewrite ETOP1 in Hlo.
    destruct Hchain as [(Hc0 & Ech) | (Hn1 & Hn2 & Hn3 & Hn4 & Hn5)].
    + exists [(sp0, rae, s0e)]. right. rewrite ETOP1. split; [lia|]. split; [lia|].
      split; [exact (pnc_m16 _ Hsp16)|]. split.
      * cbn [fpchain]. replace (bad_next sp0 (ly_top (pe_ly en)) s0e) with true
          by (symmetry; apply pnc_bad; lia).
        repeat split; try lia; try exact (pnc_m16 _ Hsp16); [exact HSV8 | exact HSV16].
      * constructor; [cbn; lia | constructor].
    + assert (WORDS : forall a, a mod 8 = 0 -> s0e - 16 <= a -> a + 8 <= ly_top (pe_ly en) ->
        rdword (aview SEGS (w_H W') mem) a = rdword (aview SEGS (w_H (pe_W en)) (pe_mem en)) a \/
        (exists v v', rdword (aview SEGS (w_H (pe_W en)) (pe_mem en)) a = Some v /\
           rdword (aview SEGS (w_H W') mem) a = Some v' /\ 4096 <= v < alloc_ceiling /\ 4096 <= v' < alloc_ceiling)).
      { intros a Ha8 Hlo2 Hhi2.
        destruct (Z.eq_dec a (pe_q en)) as [-> | Hne].
        - (* the cursor word: p before, p1 after, both inside the text and so below the ceiling (SRC-CEIL: the
             text ends at or below alloc_ceiling, and p <= p1 < text + len since the number's first byte is there) *)
          assert (Hpp1 : pe_p en <= p1 < pe_text en + pe_len en).
          { destruct (PvB_Model.pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen Hp0r) as [_ Hb].
            change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hb. rewrite Hskip in Hb.
            assert (Hl1 : 1 <= Z.of_nat (length (c :: y))) by (cbn [length]; lia).
            rewrite Ep1. clear - Hb Hl1. lia. }
          right. exists (pe_p en), p1. split; [|split].
          + apply pnc_rdword_val; [exact Vq0 | lia].
          + apply pnc_rdword_val; [exact Vq1 | lia].
          + split; split; lia.
        - left. apply pnc_rdword. intros i Hi.
          destruct (Z_lt_le_dec (a + i) (sp0 + ee)) as [Hw|Hw].
          + destruct (pnc_fp3 (pe_q en) (pe_v en) (a + i)) as [Hz|[Hz|[Hz|Hz]]].
            * exfalso. exact (pnc_word_apart a (pe_q en) (a + i) Ha8 Hq8 Hne ltac:(lia) Hz).
            * apply (pnc_vm_eq (w_H (pe_W en)) (w_H W') (pe_mem en) mem (pe_q en + 16) 4 (Z.of_nat (pe_d en)));
                [exact Vq160 | exact Vq161 | cbn; lia].
            * exact (Hnode1 (a + i) Hz).
            * exact (HWIN (a + i) ltac:(lia) Hz).
          + apply J1; lia. }
      assert (Hcs : alloc_ceiling <= s0e) by lia.
      destruct (pnc_fpchain _ _ (ly_top (pe_ly en)) (pe_ch en) s0e alloc_ceiling Hn4 Hcs Hn3 Hn2 WORDS)
        as (ch'' & Hch'').
      exists ((sp0, rae, s0e) :: ch''). right. rewrite ETOP1. split; [lia|]. split; [lia|].
      split; [exact (pnc_m16 _ Hsp16)|]. split.
      * cbn [fpchain]. replace (bad_next sp0 (ly_top (pe_ly en)) s0e) with false.
        2:{ symmetry. destruct (bad_next sp0 (ly_top (pe_ly en)) s0e) eqn:Hb; [|reflexivity].
            apply pnc_bad in Hb. lia. }
        repeat split; try lia; try exact (pnc_m16 _ Hsp16); [exact HSV8 | exact HSV16 | exact Hch''].
      * constructor; [cbn; lia|]. pose proof (fpchain_fps_increase _ _ _ _ Hch'') as Hinc.
        eapply Forall_impl; [|exact Hinc]. intros r Hr. cbn beta in Hr. lia. }
destruct HCH as (ch1 & HCH).

(* ---- fuzz_malloc's premises ---- *)
destruct (pnc_gt (pe_d en) (pe_rest en) c y m Hskip Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hlead Hm Hspan) as (L & EgtL & HmL).
assert (Egt : pe_gt en = [PjGrammar.EAlloc (S L)]) by exact EgtL.
(* the room invariant at the call state: pv_reader0's rd_room *)
pose proof HRKr as (HRL & _ & _).
assert (Hhp1 : hpeakR (pe_gt en) = Z.of_nat (S L)) by (rewrite Egt; cbn [hpeakR PjGrammar.held_ev]; lia).
assert (Hmr : prh_maxreq (pe_gt en) = Z.of_nat (S L))
  by (rewrite Egt; unfold prh_maxreq; cbn [map fold_right PjGrammar.esize]; lia).
assert (Hcalls : PjGrammar.calls (pe_gt en) = 1%nat) by (rewrite Egt; reflexivity).
assert (HMAX : Z.of_nat m + 1 + cf_head < cf_malloc_max) by (rewrite Hmr in Hhpk; lia).
(* The batch kit's per-event live room (rd_room's third conjunct at 03fcabb582d0): the call's request is the FIRST event of the
   call's request is the FIRST event of the entry's grant-all trace, so PvB_Defs.rd_room_first gives the
   bound on the entry's live bytes, and the call state's are the entry's (pv_reader0's blocks keep) *)
assert (HLIVE : pe_cnt en <> pe_fail en -> blocks_bytes Sc + (Z.of_nat m + 1 + cf_head) <= LIVE_MAX).
{ intros _. rewrite Hbb.
  assert (Hev : PresetReqAt.rd_hevs (pe_gt en) = [PresetReqAt.HMal (Z.of_nat (S L) + PresetReqAt.HEAD)])
    by (rewrite Egt; reflexivity).
  pose proof (rd_room_first (pe_S en) (pe_gt en) _ _ HROOMp Hev) as HL1.
  cbn [prh_ev_req] in HL1. rewrite HHD. clear - HL1 HmL. lia. }
assert (HROD : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W') mem)).
{ intros a Hro Hno Her. rewrite (J3 a (pnc_ro_img a Hro) Hno Her (fun Hp => PSTRO a Hp Hro)).
  - exact (HRO a Hro Hno Her).
  - apply fp_spares_closed. apply sink_closed_pos. unfold pe_FP.
    repeat constructor; cbn [fst]; lia. }
(* fpre's stack-top margin at the call (the kit's fpre third conjunct, lib/A/PRH_Base.v (sha256 15f329a07919; internal record)):
   the callee's sp is Y <= sp0 - 160 and the layout's stack top is the entry's *)
assert (H64c : spZ regsc + 64 <= ly_stk_hi lyc).
{ assert (ESPc : spZ regsc = Y) by (unfold spZ; rewrite Q2, R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EHIc & _).
  rewrite ESPc. unfold pe_sp in *. lia. }
(* fpre's return-address bound at the call (the kit's fpre fourth conjunct): the return pc is the jal's own,
   the listing slot BASE + AF_pn_mret (pnc_slot_lt_ceil) *)
assert (Hrac : raZ regsc < YM05.alloc_ceiling).
{ unfold raZ. rewrite Rra, unsigned_lit_small by (unfold AF_pn_mret; lia).
  destruct (plookup (@pl_tpi _ PL_prog_B) AF_pn_mret) as [e|] eqn:Hk.
  - exact (pnc_slot_lt_ceil (PI := PA) AF_pn_mret e ltac:(unfold AF_pn_mret; lia) Hk).
  - vm_compute in Hk. discriminate Hk. }
(* fuzz_malloc's two live counts at the call state: pv_pre's live-count premises (record premises 12 and 13) at their
   first state (pnc_cnt_pkR), the call state's live list being the entry's (pv_reader0's rp_keep); sec_cnt / ccnt24
   are cnt of the live list by conversion *)
assert (HSEC : YGcfRoomLive.sec_cnt Sc <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ change (YGcfRoomLive.sec_cnt Sc) with
    (Z.of_nat (PresetReqAt.cnt YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)))).
  rewrite (rp_keep_cnt _ _ _ HRP1).
  pose proof (pnc_cnt_pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (pe_S en)))
    (PresetReqAt.rd_hevs (pe_gt en))) as Hc.
  clear - Hc HPKS. lia. }
assert (HC24 : YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ change (YGcfRoomLive.ccnt24 Sc) with
    (Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)))).
  rewrite (rp_keep_cnt _ _ _ HRP1).
  pose proof (pnc_cnt_pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (pe_S en)))
    (PresetReqAt.rd_hevs (pe_gt en))) as Hc.
  clear - Hc HPK24. lia. }
(* fuzz_malloc's hull budget at the call state: pv_pre's over parse_value's events, which at the stopped token ARE the
   one allocation EAlloc (S m) (PvB_NQ.pnq_gt_go), the meters kept from the entry (pv_reader0's secs_same), HHD turning
   rd_hev's HMal (S m + HEAD) into the call's request *)
assert (EgtM : pe_gt en = [PjGrammar.EAlloc (S m)]).
{ unfold pe_gt, prhPv_gtrace.
  rewrite (PvB_NQ.pnq_value prh_jr_strtod (pe_d en) (pe_rest en) c y [] Hskip Hc1 Hc2 Hc3 Hc4 Hc5 Hc6).
  exact (proj1 (PvB_NQ.pnq_gt_go prh_jr_strtod c y m Hlead Hm Hspan Hstop)). }
assert (HHULLc : PresetHullBudget.hull_budget Sc [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)]).
{ assert (HB0 : PresetHullBudget.hull_budget (pe_S en) (PresetReqAt.rd_hevs (pe_gt en)))
    by (unfold pv_pre in HPRE; tauto).
  rewrite EgtM in HB0.
  change (PresetReqAt.rd_hevs [PjGrammar.EAlloc (S m)]) with [PresetReqAt.HMal (Z.of_nat (S m) + PresetReqAt.HEAD)]
    in HB0.
  rewrite <- HHD in HB0. replace (Z.of_nat m + 1 + cf_head) with (Z.of_nat (S m) + cf_head) by (clear; lia).
  exact (PresetHullBudget.hull_budget_same (pe_S en) Sc _ HSEC1 HB0). }

(* ---- the call ---- *)
eapply SRr_bind.
{ eapply (@aj_call_xW fx0 rc SK SEGS B PSTX ARx hl LAWS pa_segs_low W' regsc mem (SIGMA AS_fuzz_malloc)
    (pe_STK en + ee) (sp0 + ee) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en)
    [(0, pos)] lyc Sc (pe_Hp en) md' k (@STK_fuzz_malloc prh_img_B) 0 [] (Y - (sp0 + ee)) (getr regsc 1) ch1
    (fQmn mem (fun ly' S' Hp' W2 regs' mem' md2 => exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
       PresetHullBudget.hull_used Sc S' [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)] /\
       (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> PRH_Base.prh_run_at sm x os i [] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
       (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)])%nat H0 hist' S') /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)] ->
          PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)]) ->
          pe_cnt en <> pe_fail en ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)])%nat
            H0 hist' S') /\
       prh_alloc_post B (Z.of_nat m + 1) lyc Sc (pe_Hp en) W' (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en)
         (pe_ran en) (pe_most en) (pe_own en) res ly' S' Hp' W2 mem')) HJ).
  - unfold spZ. rewrite Q2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (pnc_mod16 Y sp0 ee HY32 Hsp16 He16).
  - lia.
  - rewrite FFM. lia.
  - rewrite FFM. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite Q3, R3. exact Hgp.
  - rewrite Q4, R4. exact Htp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [unfold AF_pn_mret; lia | reflexivity].
  - rewrite Rra, unsigned_lit_small by (unfold AF_pn_mret; lia). unfold AF_pn_mret. lia.
  - replace (sp0 + ee + (Y - (sp0 + ee))) with Y by lia. unfold s0Z. rewrite Q8, R8. unfold w64.
    rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1 HWIN1. assert (Hn0 : 0 <= Z.of_nat m + 1) by lia. eapply SRr_mono.
    + exact (FMALLOC lyc Sc (pe_Hp en) W' regsc mem md' ch1 (Z.of_nat m + 1) (pe_Lam en) (pe_peak en) (pe_cnt en)
        (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (conj HPRE1 (conj HROD (conj H64c (conj Hrac Hfrm0))))
        HRL Hmuniv HSEC HC24 HHULLc Ra0 Hn0 HMAX HLED1 HLIVE).
    + intros W2 c2 _ Hcc. eapply fpostW_x_of_apost. exact Hcc.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP &
  (res & Hres & HRK2 & Hhull2 & HRPn & HRPs & HOUTC & HAP) & HMK).
apply HKM.

(* ---- M: what the call keeps, and the laws at M ---- *)
pose proof HJ1 as (HAR2 & HLY2 & _ & _ & _ & Hfrs2 & _ & _ & K1 & K2 & K3 & K4 & _ & _ & _ & _ & _).
pose proof HLY2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & ETOP2 & ELO2 & EHI2 & _).
pose proof Hly as (_ & _ & _ & _ & _ & ELF1 & _ & _ & ETOP1 & ELO1 & EHI1 & _).
destruct (pnc_post (Z.of_nat m + 1) lyc Sc (pe_Hp en) W' (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en)
  (pe_ran en) (pe_most en) (pe_own en) res ly2 S2 Hp2 W2 mem2 md2 ltac:(lia) HAR2 HAP)
  as (Lam2 & pk2 & cn2 & fl2 & rn2 & HLED2 & HLam2 & Habl2 & Hhp2).
(* the stack at or above the call's sp: the callee's stack clause *)
assert (KS : forall a, Y <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W') mem a).
{ intros a Ha. apply K1; lia. }
(* a block of the call state: the callee's block clause (fuzz_malloc frees nothing) *)
assert (KB : forall b mm z, In (b, mm) (ablocks B lyc Sc) -> b <= z < b + req_size mm ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros b mm z Hin Hz. replace z with (b + (z - b)) by lia.
  apply (K2 b mm (z - b) Hin (Habl2 _ Hin)); [lia | apply inFP_nil]. }
(* a fake frame of the call state, and its shadow: the callee's frame clause *)
assert (KF : forall cid p z, In (cid, p) (frames Sc) ->
  frame_addr lyc cid p <= z < frame_addr lyc cid p + fs_frame_bytes cid ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros cid p z Hin Hz. apply (K4 cid p z Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil]. }
assert (KFS : forall cid p z, In (cid, p) (frames Sc) ->
  shadow_addr (frame_addr lyc cid p) <= z < shadow_addr (frame_addr lyc cid p) + fs_frame_bytes cid / 8 ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros cid p z Hin Hz. apply (K4 cid p z Hin); [right; unfold in_zr; cbn [fst snd]; lia | apply inFP_nil]. }
(* a read-only image byte: the callee's image clause *)
assert (KI : forall z, in_roP SEGS RLO RHI z -> ~ Exists (in_zr z) (as_owned_static B) ->
  ~ (as_errno B <= z < as_errno B + 4) -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros z Hro Hno Her.
  apply K3; [exact (pnc_ro_img z Hro) | exact Hno | exact Her | intros Hp; exact (PSTRO z Hp Hro) |].
  apply fp_spares_closed. exact sink_closed_nil. }
assert (KFa : forall z, fa <= z < fa + 64 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros z Hz. apply (KF 0 pos z HinF). rewrite <- Efa. change (fs_frame_bytes 0) with 64. lia. }
assert (KFsh : forall z, SHADOW_OFF + fa / 8 <= z < SHADOW_OFF + fa / 8 + 8 ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros z Hz. apply (KFS 0 pos z HinF). rewrite <- Efa. change (fs_frame_bytes 0 / 8) with 8. unfold shadow_addr.
  lia. }
assert (Hfa_img : forall z, fa <= z < fa + 64 -> ~ in_img SEGS z).
{ intros z Hz. apply (frm_img_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc 0 pos z HAR HinF).
  rewrite <- Efa. change (fs_frame_bytes 0) with 64. lia. }
assert (Hlen0 : 0 <= pe_len en) by lia.
(* the text: its bytes by its home, its shadow by the laws at M *)
assert (KT : forall z, pe_text en <= z < pe_text en + pe_len en ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros z Hz.
  destruct Hhome1 as [[(b & mm & Hin & Hb1 & Hb2) | [(Hzs & Hlo & Hhi & Hro) | (_ & _ & Hro)]] |
    (b & mm & Hin & Hnb & Hb1 & Hb2)].
  - destruct HLED1 as (_ & _ & HF1 & _).
    destruct (proj1 (Forall_forall _ _) HF1 (b, mm) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
    apply (KB _ _ z Hblk). unfold req_size. destruct (Z.eqb_spec (mm + cf_head) 0); lia.
  - destruct (Hro z Hz) as (H1 & H2 & H3). exact (KI z H1 H2 H3).
  - destruct (Hro z Hz) as (H1 & H2 & H3 & _). exact (KI z H1 H2 H3).
  - apply (KB b mm z Hin). unfold req_size. destruct (Z.eqb_spec mm 0); lia. }
assert (KTS : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (pe_text en) (pe_len en) /\
  (0 < pe_len en -> shadow_hull_vis (aview SEGS (w_H W2) mem2) (pe_text en) (pe_len en))).
{ destruct Hhome1 as [[(b & mm & Hin & Hb1 & Hb2) | [(Hzs & Hlo & Hhi & Hro) | Hki]] |
    (b & mm & Hin & Hnb & Hb1 & Hb2)].
  - exact (pnc_lam_shadow ly2 S2 Hp2 W2 mem2 md2 Lam2 pk2 cn2 fl2 rn2 (pe_most en) (pe_own en) b mm (pe_text en)
      (pe_len en)
      HAR2 HLED2 (HLam2 _ Hin) Hb1 Hb2 Hlen0).
  - pose proof PA_BOX as (HB1 & HB2).
    exact (CUTFIX_zs ly2 S2 Hp2 W2 mem2 md2 (pe_text en) (pe_len en) HAR2 Hzs ltac:(clear - Hlo HB1; lia)
      ltac:(clear - Hhi HB2; lia)).
  - exact (pnc_kimg_shadow ly2 S2 Hp2 W2 mem2 md2 (pe_text en) (pe_len en) HAR2 Hki).
  - exact (pnc_blk_shadow ly2 S2 Hp2 W2 mem2 md2 Lam2 pk2 cn2 fl2 rn2 (pe_most en) (pe_own en) b mm (pe_text en)
      (pe_len en)
      HAR2 HLED2 (Habl2 _ Hin) (Hhp2 b mm Hin ltac:(lia) Hnb) Hb1 Hb2 Hlen0). }
(* the node: its bytes by its home, its shadow by the laws at M or by the frame clause *)
assert (KV : forall z, pe_v en <= z < pe_v en + 56 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W') mem z).
{ intros z Hz.
  destruct Hvat as [(a & kk & Hin & Ha1 & Ha2) | [(b & mm & Hin & Hnl & Hb1 & Hb2) |
    [(cid & p & Hin & Hf1 & Hf2) | (Hw1 & Hw2)]]].
  - destruct HLED1 as (_ & _ & HF1 & _).
    destruct (proj1 (Forall_forall _ _) HF1 (a, kk) Hin) as (Hkk0 & Hblk & _). cbn [fst snd] in Hkk0, Hblk.
    apply (KB _ _ z Hblk). unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia.
  - rewrite <- Hab in Hin. apply (KB b mm z Hin). unfold req_size. destruct (Z.eqb_spec mm 0); lia.
  - apply (KF cid p z); [rewrite Hfrs; right; exact Hin|]. unfold frame_addr in Hf1, Hf2 |- *. rewrite ELF1. lia.
  - change (spZ (pe_regs en)) with sp0 in Hw1, Hw2. apply KS. lia. }
assert (KVS : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (pe_v en) 56).
{ destruct Hvat as [(a & kk & Hin & Ha1 & Ha2) | [(b & mm & Hin & Hnl & Hb1 & Hb2) |
    [(cid & p & Hin & Hf1 & Hf2) | (Hw1 & Hw2)]]].
  - exact (proj1 (pnc_lam_shadow ly2 S2 Hp2 W2 mem2 md2 Lam2 pk2 cn2 fl2 rn2 (pe_most en) (pe_own en) a kk
      (pe_v en) 56
      HAR2 HLED2 (HLam2 _ Hin) Ha1 Ha2 ltac:(lia))).
  - rewrite <- Hab in Hin.
    pose proof (pnc_nl_nhp lyc Sc (pe_Hp en) W' mem mdc (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en)
      (pe_ran en) (pe_most en) (pe_own en) b mm HAR HLED1 Hin ltac:(lia) Hnl) as Hnb.
    exact (proj1 (pnc_blk_shadow ly2 S2 Hp2 W2 mem2 md2 Lam2 pk2 cn2 fl2 rn2 (pe_most en) (pe_own en) b mm
      (pe_v en) 56
      HAR2 HLED2 (Habl2 _ Hin) (Hhp2 b mm Hin ltac:(lia) Hnb) Hb1 Hb2 ltac:(lia))).
  - assert (HinC : In (cid, p) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
    destruct (alx_frames _ _ _ LAWS lyc Sc (pe_Hp en) W' mem mdc cid p HAR HinC) as (Hal32 & _).
    assert (EFA : frame_addr lyc cid p = frame_addr (pe_ly en) cid p)
      by (unfold frame_addr; rewrite ELF1; reflexivity).
    rewrite EFA in Hal32.
    assert (Hfs8 : fs_frame_bytes cid mod 8 = 0) by (apply pnc_fs8; lia).
    apply (range_addressable_agree (aview SEGS (w_H W') mem) (aview SEGS (w_H W2) mem2) SHADOW_OFF (pe_v en) 56);
      [|exact HvRA1].
    intros x Hx. apply (KFS cid p); [exact HinC|]. rewrite EFA. unfold shadow_of_addr, shadow_addr.
    pose proof (pnc_sh_in (frame_addr (pe_ly en) cid p) (fs_frame_bytes cid) x (pnc_m32 _ Hal32) Hfs8 ltac:(lia)).
    lia.
  - change (spZ (pe_regs en)) with sp0 in Hw1, Hw2.
    intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    apply (alx_zshadow_byte _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2). rewrite ELO2, EHI2, ELO1, EHI1. lia. }
(* the registers the callee keeps *)
assert (HPk : forall (n : Z) (r : bv 5), acallee_saved n -> bv_unsigned r = n -> getr regs2 r = getr regsc r).
{ intros n r Hn Hr. pose proof (HP n Hn) as H. rewrite <- Hr, Z_to_bv_bv_unsigned in H. exact H. }

(* ---- M ---- *)
exists regs2, mem2, Y, fa, fl, pos, ly2, S2, Hp2, (k + k1), c, y, m, res, lyc, Sc, W', mem.
cbv zeta.
split. { unfold pn_ms. rewrite Rra. reflexivity. }
split.
{ unfold pn_base, pv_keep_regs.
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) (conj _ (conj _ (conj _ (conj _
    (conj Hskip (conj Hc1 (conj Hc2 (conj Hc3 (conj Hc4 (conj Hc5 Hc6)))))))))));
  [ pnc_kr HPk Q2 R2 2 (2%bv : bv 5) | pnc_kr HPk Q8 R8 8 (8%bv : bv 5) | pnc_kr HPk Q18 R18 18 (18%bv : bv 5)
  | pnc_kr HPk Q26 R26 26 (26%bv : bv 5) | pnc_kr HPk Q27 R27 27 (27%bv : bv 5) | pnc_kr HPk Q23 R23 23 (23%bv : bv 5)
  | pnc_kr HPk Q3 R3 3 (3%bv : bv 5) | pnc_kr HPk Q4 R4 4 (4%bv : bv 5) | pnc_kr HPk Q9 R9 9 (9%bv : bv 5)
  | pnc_kr HPk Q19 R19 19 (19%bv : bv 5) | pnc_kr HPk Q20 R20 20 (20%bv : bv 5)
  | pnc_kr HPk Q24 R24 24 (24%bv : bv 5) ]. }
split.
{ split; [|split; [|split; [|split; [|split]]]].
  - unfold pv_frame. split; [exact HY1|]. split; [exact HY32|].
    split.
    { intros a Ha. apply (apresent_transfer SEGS (w_H W') (w_H W2) mem mem2 a); [lia | | apply KS; lia | exact (HPR0 a Ha)].
      intros Him. pose proof (pa_segs_low a Him). lia. }
    split.
    { rewrite Forall_forall in Vsav |- *. intros oc Hin.
      assert (Hb : -104 <= fst oc <= -8).
      { cbn in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
      apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KS; lia | exact (Vsav oc Hin)]. }
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KS; lia | exact Vfa48]|].
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KFa; cbn in Hz; lia | exact Vmagic]|].
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KFa; cbn in Hz; lia | exact Vdesc]|].
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KFa; cbn in Hz; lia | exact Vpc]|].
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KFa; cbn in Hz; lia | exact Vfl]|].
    split.
    { intros a Ha.
      destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc 0 pos HAR HinF) as (Hf0 & Hf1 & _).
      rewrite <- Efa in Hf0, Hf1. change (fs_frame_bytes 0) with 64 in Hf1.
      apply (apresent_transfer SEGS (w_H W') (w_H W2) mem mem2 a);
        [lia | exact (Hfa_img a Ha) | apply KFa; lia | exact (HPRfa a Ha)]. }
    split; [exact Hshlen|].
    apply (pnc_garr (w_H W') (w_H W2) mem mem2); [|exact Gsh]. intros z Hz. rewrite Hshlen in Hz. apply KFsh. cbn in Hz.
    lia.
  - rewrite Hfrs2. exact HinF.
  - rewrite Efa. unfold frame_addr. rewrite ELF2. reflexivity.
  - rewrite Efl. unfold flag_addr. rewrite ELF2. reflexivity.
  - exact HJ2.
  - intros a Ha Hnf. rewrite KS by lia. exact (HWIN a Ha Hnf). }
split; [exact HRD0|].
split; [exact HAP|].
split; [exact HRK2|].
split; [rewrite Hfrs2; reflexivity|].
split.
{ unfold pn_reader. split; [|split; [|split]].
  - unfold pj_in_okR.
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KS; lia | exact Vq1]|].
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KS; lia | exact Vq81]|].
    split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KS; cbn in Hz; lia | exact Vq161]|].
    split.
    { intros z Hz. apply (pnc_wr (w_H W') (w_H W2) mem mem2 z); [lia | | apply KS; lia | exact (Hrw1 z Hz)].
      intros Him. pose proof (pa_segs_low z Him). lia. }
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hp1r|]. split; [exact Hlen|].
    split; [|split; [exact Hqt | exact Hd]].
    apply (pnc_garr (w_H W') (w_H W2) mem mem2); [|exact Gtb1]. intros z Hz. apply KT. lia.
  - pose proof Hsrc1 as (Gb & Ht4096' & Htc' & Ham & _ & _). destruct KTS as (KTS1 & KTS2).
    unfold src_rd. split; [|split; [exact Ht4096' | split; [exact Htc' | split; [exact Ham|]]]].
    + unfold bytes_at in *. apply (pnc_garr (w_H W') (w_H W2) mem mem2); [|exact Gb]. intros z Hz. apply KT. lia.
    + rewrite Hlen. split; [exact KTS1 | exact KTS2].
  - intros a Ha _. rewrite (KV a Ha). exact (Hnode1 a Ha).
  - exact KVS. }
split; [apply (pnc_vm (w_H W') (w_H W2) mem mem2); [intros z Hz; apply KS; lia | exact HV24]|].
split; [exact Hres|].
split; [etransitivity; [apply (HPk 25 (25%bv : bv 5)); [unfold acallee_saved; lia | reflexivity] | exact Rs9]|].
split; [pnc_kr HPk Q22 R22 22 (22%bv : bv 5)|].
split; [pnc_kr HPk Q21 R21 21 (21%bv : bv 5)|].
split; [exact Hlead|]. split; [exact Hm|]. split; [exact Hspan|]. split; [exact Hstop|].
(* M's room (PvB_NCut.v): fuzz_malloc's two position implications and prh_alloc_post's blocks, composed with the
   entry's keep at the call state (pv_reader0's rp_keep): a NULL keeps the blocks and E = [] keeps the position; a
   block appends its request to the live list and E = [HMal (m + 1 + cf_head)] is rd_hev's event of EAlloc (S m) *)
split.
{ assert (Eab0 : res = 0 -> ablocks B ly2 S2 = ablocks B lyc Sc).
  { intros E0. destruct HAP as [(_ & _ & _ & Eab & _) | [(_ & _ & _ & Eab & _) | (_ & H16 & _)]];
      [exact Eab | exact Eab | clear - E0 H16 Hh0; lia]. }
  assert (Eab1 : res <> 0 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res - cf_head, Z.of_nat m + 1 + cf_head)]).
  { intros E1. destruct HAP as [(_ & E0 & _) | [(_ & E0 & _) | (_ & _ & _ & _ & _ & Eab & _)]];
      [exfalso; exact (E1 E0) | exfalso; exact (E1 E0) | exact Eab]. }
  (* the hull use from the entry, either outcome: the meters kept to the call state, then fuzz_malloc's use (HHD
     turning its request into rd_hev's event of EAlloc (S m)) *)
  assert (HHU : pn_hull en m S2).
  { unfold pn_hull.
    change (PresetReqAt.rd_hevs [PjGrammar.EAlloc (S m)]) with [PresetReqAt.HMal (Z.of_nat (S m) + PresetReqAt.HEAD)].
    rewrite <- HHD. replace (Z.of_nat (S m) + cf_head) with (Z.of_nat m + 1 + cf_head) by (clear; lia).
    exact (PresetHullBudget.hull_used_app (pe_S en) Sc S2 [] _
      (PresetHullBudget.hull_used_same (pe_S en) Sc [] HSEC1) Hhull2). }
  split.
  - intros E0. split; [|split; [|exact HHU]].
    + apply (rp_keep_trans _ Sc _ HRP1). split.
      * transitivity (map snd (ablocks B ly2 S2)); [symmetry; apply pnc_live_ab|].
        rewrite (Eab0 E0). apply pnc_live_ab.
      * intros sm x os i H0 hist P. destruct (HRPn E0 sm x os i H0 hist P eq_refl) as (h & Ph).
        exists h. cbn [length] in Ph. rewrite Nat.add_0_r in Ph. exact Ph.
    + (* the NULL is off the grant-all run: the post's OUTCOME clause at Sc, reached from the entry by the keep *)
      intros Ecf sm x os i H0 hist P R C. destruct (proj2 HRP1 sm x os i H0 hist P) as (h1 & P1).
      assert (R1 : PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)]).
      { change (PresetReqAt.rd_hevs [PjGrammar.EAlloc (S m)])
          with [PresetReqAt.HMal (Z.of_nat (S m) + PresetReqAt.HEAD)] in R.
        rewrite <- HHD in R. replace (Z.of_nat m + 1 + cf_head) with (Z.of_nat (S m) + cf_head)
          by (clear - Hh0; lia). exact R. }
      destruct (HOUTC sm x os i H0 h1 P1 R1 C Ecf) as (Hne & _). exact (Hne E0).
  - intros E1. unfold pn_rp1. split; [|exact HHU].
    apply (rp_call [PjGrammar.EAlloc (S m)] [PresetReqAt.HMal (Z.of_nat m + 1 + cf_head)] (pe_S en) Sc S2 S2).
    + change (PresetReqAt.rd_hevs [PjGrammar.EAlloc (S m)])
        with [PresetReqAt.HMal (Z.of_nat (S m) + PresetReqAt.HEAD)].
      rewrite <- HHD. do 2 f_equal. clear - Hh0. lia.
    + exact HRP1.
    + rewrite <- (pnc_live_ab ly2 S2), <- (pnc_live_ab lyc Sc), (Eab1 E1), map_app.
      cbn [map snd PresetReqAt.hlive_from fold_left PresetReqAt.hstep].
      apply Permutation_sym, Permutation_cons_append.
    + exact (HRPs E1).
    + apply rp_keep_refl. }
(* M's memory normal form: S's (the stretch wrote nothing), kept by fuzz_malloc's m-form post (fQmn) *)
exact (HMK HMN).
Qed.

End c.
