(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlIdentityPollBlock.v, with its module paths and module names changed; 2273 of its 2322 lines of code are new or changed and 374 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): PIECE 6 of the walk
   of ex_value, `ev_items_open` (the internal file PIECES.md:94), CLOSED: ev_items_open_holds (the last lemma of this file) proves
   S8aIface.v:345's ev_items_open_spec verbatim, at L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A,
   cp := CfParams_preset (the instances of pieces 9 / 10 in S8aClose.v and of WalkS8a's composition), under LAWS
   only. The walk itself (ev_items_open_holds_zb) takes the per-byte stack zero-shadow law as its one premise
   (Section f's EV_ZSH_BYTE; S8aClose.v's s8c_ZB, verbatim):
     forall ly S Hp (W : world SEGS) mem md z, ARx ly S Hp W mem md -> ly_stk_lo ly <= z < ly_stk_hi ly ->
       aview SEGS (w_H W) mem (SHADOW_OFF + z / 8) = Some 0.
   That premise is AR_laws_x's field `alx_zshadow_byte` (YCbqG.v 219748197d6b, :317), so ev_items_open_holds cites
   `alx_zshadow_byte SEGS B ARx LAWS` for it. The journal cannot give it: shadow_addr q is about 0x1000_7fef_0000,
   below alloc_ceiling, outside YCbqG.v's clause. No Admitted, Axiom, Parameter, admit or timeout tactic.
   From P_KIND with '{' / '[' (ev_at_kind) to P_STEP 0x837ec (item 0: n = 0, cap = 0, acc = []), to P_END 0x83cec
   (the empty container, as ev_at_end; piece 10 is not called here), or to P_EXIT 0x83d48 (the grammar's depth
   refusal above PjGrammar.MAXD). Instructions walked: 0x834bc-0x834c8, 0x83654-0x83744, 0x83768-0x837e8 (122 with
   the report arms, the internal file PIECES.md); every report arm is a branch the token machinery shows not taken. The conclusion is
   `SRr` (srealizes, YA0n.v:35-38); no second form of any interface predicate is written here.
   The walk, by cut (offsets from ex_value's entry):
   - evo_head, 0x834bc (EV_ITEMS): the seated state evo_ss (evo_entry) with the measured branch outcomes as facts
     (evo_add_cond): (R) 31 < dep, the refusal -> P_EXIT (evo_refuse_post); dep <= 31 with (J0) v = 0, (J1) v's tag
     the container's, (J2) another tag (s7 := 0, in->differs := 1) -> 0x836d4 (evo_head_post). One obligation when
     v <> 0: the 4 bytes of v's type word, from prhex_tree's range_addressable.
   - evo_join, 0x836d4 (EVO_J): in->p := x0 + i1 + 1, then BC_GEU (the end of the text) -> 0x83768 (evo_tail), or
     BC_LTU -> 0x836fc with a0 = a3 = in->p, a1 = 32, a4 = EV_WSMASK (evo_from_ws).
   - evo_wsl, 0x836fc (EVO_WS): this piece's own whitespace loop (WalkS8a's S8aWs.v loop has other registers), by
     induction on len - i in the shape of S8aWs.v's ws_loop_raw; one obligation per iteration (the text byte's
     shadow); exit 0x83768 with skipn i' x = skip (skipn i x). evo_from_ws: evo_wsl, then evo_tail.
   - evo_tail, 0x83768 (EVO_AFT): (1) end of text -> P_STEP; (2) the closer -> P_END; (3) another byte -> P_STEP;
     the GO stretch's spills come from the final state: ev_spills' nine slots and s1 + 104 = v' (S8aIface.v:221).
   - evo_core is the carrier record of every cut from 0x836d4 on; evo_mid_keep carries ev_mid along a stretch (the
     stretches write only evo_W4: in->p, in->depth, in->differs, the spill area at s1).
   - MEMNORM (S8aIface.v's header): ev_mid's last conjunct `YAkMemnorm.memnorm SEGS mem` crosses every run by the
     `*_inv` runners of YC1fPx.v at P := YAkMemnorm.memnorm SEGS (laws YSRrMemnorm.srr_inv_laws_memnorm_k SEGS);
     evo_mid_keep, evo_wsl, evo_join's HPOST, evo_refuse_post and evo_head_post take it at the end memory. The piece
     makes no call, so no callee's m-form post is used.
   The model step (ev_V_open_at) is COPIED as pure spec from the released plain ex_value_m.v:77-116, :270-292 (no
   plain or UBSan file is Required or cited); evo_mask_bit is COPIED from WalkS8a's S8aWs.v ws_mask_bit.
   #102 (the port to image A', a working branch on the cut 7cdbb61b5fa0): ported from the old-pin proof of
   a working branch 8f1571cb9e13 (image A d83eb25d, twin f0d2e8d4, ex_value 0x82f30) BY SYMBOL: every pc in a
   comment is A' ex_value 0x832a4 + the same offset (+0x374; checked against the A' listing of pin 1be0f53d, the
   stacknarrow neutral disassembly); the EV_* / EVO_* offsets and every stepped word are unchanged, so the runs need no
   edit. 9 of the 122 words walked differ, all untaken report arms' `jal __asan_report_*`; the CHANGED frame string
   (+0xa8 / +0xc4; the 15:33Z #102 ruling) is outside them. The proofs changed in two places: (1) the kit's prh_ledger
   carries #102's two cells g_most / g_own_ran_out (PRH_Base.v prh_glob / prh_most / prh_own, ev_act's ea_most /
   ea_own), so evo_foot_rng takes `most own` and evo_mid_keep keeps the two cells along a stretch as it keeps the other
   five; (2) the kit's src_rd bounds the text by `x0 + len <= alloc_ceiling` (PRH_Base.v K0-SRC-CEIL: the old `+ 8`
   covered no access), so evo_wsl asks that bound, not `x0 + len + 8`: the loop reads the bytes [x0 + i, x0 + len) only.
   BUILD: the targeted route, the internal file zfb-targets.e5b8f1f4ec31aa52.sh (the internal file zfactsbuild.sh passing env
   TARGETS to the internal file ows.sh start) with TARGETS = this file's and S8aClose.v's .vo, PAU=pau-preset-102 (the 4 #102 pins;
   asan 1be0f53d), FACTS 8f3e7e1a07f1, at a pushed commit: the two files and their Require closure only. *)
(* The engine is the one of preset's lib/A/Prog/FuzzStrdup.v (c-omx-alloc-preset-s1): YC80x / YC1fPx over YCbqG's
   ajournal_x, with the float state fxc of the cut (the internal file PIECES.md house rule 4).
   Numerals here, classified (brief rule 4): ADDRESS - none is typed: every pc is `ev_pc <offset>` of S8aIface.v or
   `EVO_PC <offset>`, whose offsets are LENGTHs of the bff8519b listing, equal to the f0d2e8d4 listing's (EVO_J
   0x430, EVO_WS 0x458, EVO_AFT 0x4c4), and every image address is pa_sigma / pa_val / a segment field, read by
   computation. LENGTH: the struct ex offsets 0, 8, 16, 24, 32 and its size 40; the spill offsets 24..160 at s1
   (24..104 the GO stretch's slots, 152 the spill area's extent); access widths 1, 4, 8; the granule 8 and its log 3;
   v's node size 56; 4096 (a page, the lowest mapped address of the model); 104, 256, 287 (the prologue's save area
   and the 32-alignment). DERIVED:
   Z.of_nat PjGrammar.MAXD (the depth bound) and 31 = PjGrammar.MAXD - 1 (the depth test's immediate), 2 ^ 47 (the
   model's address-space bound), 2 ^ 64 / 2 ^ 32 (word ranges), 0x7fff7f800000 (the lower bound of ASAN_CEIL,
   YG0f.v:16), 2 ^ 44 (the shadow band, FuzzStrdup.v:84), 512 (A_LIM, YC4aP.v:20), the atom indices of the symbolic
   states (the engine's numbering: registers 0..31, extra values from 32), the region positions 0..6 of a state's
   region list. WORD: the byte constants 123 '{', 91 '[', 125 '}', 93 ']', 32 (the largest blank), 255, the tags
   5 (JArr) / 6 (JObj) of PjTree.v:22-23 (all tags in 0..6), EV_WSMASK 4294977024, 0, 1, -1.
   The memory-checking runtime's words are the stream's internal file asan-wording.md's (the internal file asan-wording.md). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== the pure model: the grammar at an opener ========
   COPIED (house rule 2 of the internal file PIECES.md: pure spec only) from the released plain lib/Prog/ex_value_m.v:77-109,
   :111-116 and :270-292, restated over S8aIface's prhex_V / ev_L (that is, over ReaderRes.jr_strtod instead of the
   plain file's ex_sm). No plain file is Required and no plain lemma is cited. *)

Definition evm_sm : list Z -> Z * Z := ReaderRes.jr_strtod.

Lemma ev_run0_bind : forall A B (m : PjGrammar.M A) (k : A -> PjGrammar.M B), PjGrammar.agrees m ->
  ev_run0 (PjGrammar.jbind m k) = match ev_run0 m with Some a => ev_run0 (k a) | None => None end.
Proof.
  intros A B m k H. unfold ev_run0, PjGrammar.jbind.
  destruct (m []) as [[r t] o] eqn:E.
  pose proof (PjGrammar.agrees_nil A m H) as N. rewrite E in N. cbn [fst snd] in N.
  inversion N; subst; clear N.
  destruct r as [a|]; cbn [fst snd]; [|reflexivity].
  destruct (k a []) as [[r1 t1] o1]; reflexivity.
Qed.

Lemma ev_run0_grow : forall o n cap,
  ev_run0 (PjGrammar.grow o n cap) = Some (if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat).
Proof.
  intros o n cap. unfold PjGrammar.grow.
  destruct (Nat.ltb n cap); [reflexivity|]. destruct o; reflexivity.
Qed.

Lemma ev_skip_nws : forall b y, PjGrammar.ws b = false -> PjGrammar.skip (b :: y) = b :: y.
Proof. intros b y H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.

Lemma ev_maxd : forall d, 0 <= d -> Nat.ltb PjGrammar.MAXD (S (Z.to_nat d)) = (Z.of_nat PjGrammar.MAXD <? d + 1).
Proof.
  intros d Hd. change (Z.of_nat PjGrammar.MAXD) with 32. unfold PjGrammar.MAXD.
  destruct (Nat.ltb 32%nat (S (Z.to_nat d))) eqn:E1; destruct (32 <? d + 1) eqn:E2; try reflexivity.
  - apply Nat.ltb_lt in E1. apply Z.ltb_ge in E2. lia.
  - apply Nat.ltb_ge in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma ev_jrl_nil : forall f d o n cap acc, ev_run0 (PjGrammar.jrl evm_sm f d o n cap acc []) = None.
Proof.
  intros [|f] d o n cap acc; [reflexivity|]. cbn [PjGrammar.jrl].
  rewrite ev_run0_bind by apply PjGrammar.agrees_grow. rewrite ev_run0_grow. cbv beta iota.
  destruct o; [reflexivity|]. destruct f; reflexivity.
Qed.

Lemma ev_V_cons : forall d b y, PjGrammar.ws b = false -> prhex_V d (b :: y) = ev_run0 (
  if b =? 123 then PjGrammar.jr_cont (PjGrammar.jrl evm_sm (2 * length (b :: y))) (Z.to_nat d) true (b :: y)
  else if b =? 91 then PjGrammar.jr_cont (PjGrammar.jrl evm_sm (2 * length (b :: y))) (Z.to_nat d) false (b :: y)
  else if b =? 34 then PjGrammar.jbind (PjGrammar.jr_string y) (fun '(s, r) => PjGrammar.jret (JStr s, r))
  else if b =? 116 then PjGrammar.lit PjGrammar.w_true JTrue (b :: y)
  else if b =? 102 then PjGrammar.lit PjGrammar.w_false JFalse (b :: y)
  else if b =? 110 then PjGrammar.lit PjGrammar.w_null JNull (b :: y)
  else PjGrammar.jr_number evm_sm (b :: y)).
Proof.
  intros d b y H. unfold prhex_V, PjGrammar.jr_value, ev_run0. cbn [PjGrammar.jrv].
  rewrite (ev_skip_nws b y H). reflexivity.
Qed.

(* the one model step of piece 6 (plain ex_value_m.v:270-292, restated): at an opener, the grammar refuses above
   PjGrammar.MAXD, else it skips the blanks after the opener and either closes an empty container or enters the
   item loop at ev_L *)
Lemma ev_V_open : forall d b y, 0 <= d -> (b = 123 \/ b = 91) ->
  prhex_V d (b :: y) =
    if Z.of_nat PjGrammar.MAXD <? d + 1 then None
    else match PjGrammar.skip y with
         | c :: r => if c =? PjGrammar.closer (b =? 123) then Some (PjGrammar.mk (b =? 123) [], r)
                     else ev_L (S (Z.to_nat d)) (b =? 123) 0 0 [] (c :: r)
         | [] => None
         end.
Proof.
  intros d b y Hd Hb.
  assert (Hc : prhex_V d (b :: y) =
    ev_run0 (PjGrammar.jr_cont (PjGrammar.jrl evm_sm (2 * length (b :: y))) (Z.to_nat d) (b =? 123) (b :: y))).
  { destruct Hb as [-> | ->]; rewrite ev_V_cons by reflexivity; reflexivity. }
  rewrite Hc. set (o := b =? 123).
  unfold PjGrammar.jr_cont. rewrite (ev_maxd d Hd).
  destruct (Z.of_nat PjGrammar.MAXD <? d + 1); cbv beta iota zeta; [reflexivity|].
  cbn [tl].
  destruct (PjGrammar.skip y) as [|c r] eqn:Ey; cbv beta iota.
  - apply ev_jrl_nil.
  - pose proof (PjGrammar.skip_len y) as Ly. rewrite Ey in Ly.
    destruct (c =? PjGrammar.closer o); cbv beta iota; [reflexivity|].
    unfold ev_L, ev_run0.
    rewrite (proj2 (PjGrammar.fuel_mono evm_sm (2 * length (c :: r) + 2)) (S (Z.to_nat d)) o 0%nat 0%nat [] (c :: r)
      (2 * length (b :: y))%nat []) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* the same step at a cursor whose blanks are not yet skipped: the reader skips them first (this is the form
   ev_at_kind gives: skip (x from i0) = x from i1, with x[i1] the opener) *)
Lemma ev_V_open_at : forall d (xs y : list Z) b, 0 <= d -> PjGrammar.skip xs = b :: y -> (b = 123 \/ b = 91) ->
  prhex_V d xs =
    if Z.of_nat PjGrammar.MAXD <? d + 1 then None
    else match PjGrammar.skip y with
         | c :: r => if c =? PjGrammar.closer (b =? 123) then Some (PjGrammar.mk (b =? 123) [], r)
                     else ev_L (S (Z.to_nat d)) (b =? 123) 0 0 [] (c :: r)
         | [] => None
         end.
Proof.
  intros d xs y b Hd Hskip Hb.
  assert (Hc : prhex_V d xs =
    ev_run0 (PjGrammar.jr_cont (PjGrammar.jrl evm_sm (2 * length xs)) (Z.to_nat d) (b =? 123) (b :: y))).
  { unfold prhex_V, PjGrammar.jr_value, ev_run0. cbn [PjGrammar.jrv]. rewrite Hskip.
    destruct Hb as [-> | ->]; reflexivity. }
  rewrite Hc. set (o := b =? 123).
  pose proof (PjGrammar.skip_len xs) as Lxs. rewrite Hskip in Lxs. cbn [length] in Lxs.
  unfold PjGrammar.jr_cont. rewrite (ev_maxd d Hd).
  destruct (Z.of_nat PjGrammar.MAXD <? d + 1); cbv beta iota zeta; [reflexivity|].
  cbn [tl].
  destruct (PjGrammar.skip y) as [|c r] eqn:Ey; cbv beta iota.
  - apply ev_jrl_nil.
  - pose proof (PjGrammar.skip_len y) as Ly. rewrite Ey in Ly.
    destruct (c =? PjGrammar.closer o); cbv beta iota; [reflexivity|].
    unfold ev_L, ev_run0.
    rewrite (proj2 (PjGrammar.fuel_mono evm_sm (2 * length (c :: r) + 2)) (S (Z.to_nat d)) o 0%nat 0%nat [] (c :: r)
      (2 * length xs)%nat []) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* ======== the symbolic state at P_KIND with an opener (0x834bc) ======== *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

(* the cut's slot, as a byte offset from the listing's base (DERIVED: the generated A_prog_sigma / A_prog_base) *)
Definition EVO_PC (off : Z) : Z := A_prog_sigma AS_ex_value + off - A_prog_base.

(* the shadow band the token machinery works in (FuzzStrdup.v:84) *)
Definition EVO_Bx : sv := SOff 24 0.
Definition EVO_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the lower bound of ASAN_CEIL (YG0f.v:16): every stack byte is at or above it *)
Definition EVO_CEIL : Z := 0x7fff7f800000.
(* the model's address-space bound less the struct (astk_ok: ly_stk_hi <= 2 ^ 47, and q + 40 <= ly_stk_hi) *)
Definition EVO_TOP : Z := 2 ^ 47 - 40.

(* s10 = shadow (q): the engine reads the four 8-byte checks of `in` through this form (YCbn.v:66-85 match_x) *)
Definition EVO_SHQ : sv := SAlu ALU_SRL (SOff 19 0) (SLit 3).
Definition EVO_S10 : sv := SAlu ALU_ADD EVO_SHQ EVO_Bx.

Definition evo_regs (cz : Z) (s7v : sv) : list sv :=
  sr_set (sr_set (sr_set sr_atoms 21%bv (SLit cz)) 26%bv EVO_S10) 23%bv s7v.

(* `in` at q, one region per field, so that the engine's write windows are EXACTLY the cells piece 6 writes and
   every one of them is in the text's footprint ea_FP (in->p, in->depth, in->differs): in->end and in->scratch are
   read-only here, and ev_mid's "the caller's window outside FP is kept" then follows from the stretch's frame *)
Definition evo_Rp : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 11 0))].
Definition evo_Re : YP09.region := YP09.mkRegion (Some 19%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 12 0))].
Definition evo_Rd : YP09.region := YP09.mkRegion (Some 19%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 32 0))].
Definition evo_Rs : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition evo_Rl : YP09.region := YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 34 0))].
Definition evo_Rin : smem := [evo_Rp; evo_Re; evo_Rd; evo_Rs; evo_Rl].
(* the body's spill area at s1: the 19 slots below the prologue's save area (which starts at sp0 - 104) *)
Definition evo_Rf : YP09.region := YP09.mkRegion (Some 9%nat) 0 152 0 152 [].
(* v's type word (read-only here): atom 35 is PjTree.tag of the activation's tree *)
Definition evo_Rv : YP09.region := YP09.mkRegion (Some 23%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].

Definition evo_atoms (vf : list (nat * afact)) : list (nat * afact) :=
  [(9%nat, mkAF EVO_CEIL EVO_TOP 5); (11%nat, mkAF 4096 EVO_TOP 0); (12%nat, mkAF 4096 EVO_TOP 0);
   (19%nat, mkAF EVO_CEIL EVO_TOP 3); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF 0 (Z.of_nat PjGrammar.MAXD) 0)] ++ vf.
Definition evo_G (vf : list (nat * afact)) : facts := mkFacts (evo_atoms vf) [] [].

Definition evo_ss (cz : Z) (s7v : sv) (rs : smem) (vf : list (nat * afact)) : sstate :=
  mkSS (EVO_PC EV_ITEMS) (evo_regs cz s7v) (evo_Rin ++ evo_Rf :: rs) None (evo_G vf).

Definition evo_E (a : ev_act) (regs : bvmap 5 word) : env :=
  @Eimg _ A_prog_listing PI_prog_A
    (Ereg regs [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))]).

(* the shadow of `in`'s 40 bytes, the one SH entry of every run of the piece (the token machinery discharges in's
   ASan checks through it); v's type word and the tree's tag as atom facts (tags 0..6, PjTree.v) *)
Definition evo_SH : list shent := [mkSHE 19%nat 0 40].
Definition evo_vf23 : list (nat * afact) := [(23%nat, mkAF 4096 EVO_TOP 0); (35%nat, mkAF 0 6 0)].

(* the piece's internal cuts, as offsets from ex_value's entry (LENGTH, the bff8519b listing; = f0d2e8d4's) *)
Definition EVO_WS : Z := 0x458.     (* 0x836fc: the head of the inlined ex_ws loop *)
Definition EVO_AFT : Z := 0x4c4.    (* 0x83768: after the blanks: the closer test *)
(* the whitespace mask, EV_WSMASK of S8aIface.v:57 *)
Definition evo_WSM : Z := 4294977024.

(* ---- the state at the tail cut 0x83768 (after the blanks): `in` field by field with the cursor at atom 36, the
   depth already dep + 1, the differs value atom 41, the three spill slots piece 6 has written by then (q + 16 at 48,
   its shadow atom 43 at 56, the closer atom 40 at 64) and the text byte at the cursor (atom 37) ---- *)
Definition evo_Tp : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
Definition evo_Td : YP09.region := YP09.mkRegion (Some 19%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 32 1))].
Definition evo_Tl : YP09.region := YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 41 0))].
Definition evo_Tin : smem := [evo_Tp; evo_Re; evo_Td; evo_Rs; evo_Tl].
Definition evo_Tf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 152 0 152
    [YP09.mkChunk 48 (CVal 8 (SOff 19 16)); YP09.mkChunk 56 (CVal 8 (SOff 43 0));
     YP09.mkChunk 64 (CVal 8 (SOff 40 0))].
Definition evo_Ttext : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition evo_Tatoms : list (nat * afact) :=
  [(9%nat, mkAF EVO_CEIL EVO_TOP 5); (12%nat, mkAF 4096 EVO_TOP 0); (19%nat, mkAF EVO_CEIL EVO_TOP 3);
   (23%nat, mkAF 0 EVO_TOP 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (Z.of_nat PjGrammar.MAXD) 0);
   (36%nat, mkAF 4096 EVO_TOP 0); (37%nat, mkAF 0 255 0); (40%nat, mkAF 93 125 0); (41%nat, mkAF 0 1 0)].
(* the cursor is at the end of the text: no byte to read, the loop head is entered with n = 0 *)
Definition evo_ssTe : sstate :=
  mkSS (EVO_PC EVO_AFT) (sr_set sr_atoms 26%bv EVO_S10)
    (evo_Tin ++ [evo_Tf]) None (mkFacts evo_Tatoms [mkAC BC_GEU (SOff 36 0) (SOff 12 0)] []).

(* ======== the walk ======== *)

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* The per-byte law `alx_zshadow_byte` of AR_laws_x, stated as a hypothesis of this Section: it says that every byte
   of the REAL STACK reads shadow 0. The journal cannot give it: shadow_addr q is about 0x1000_7fef_0000, below
   alloc_ceiling 0x7fff_7f80_0000, so ajournal_x's "at or above alloc_ceiling" clause (YCbqG.v:357, ajournal_xb) does
   not cover it. Section z's ev_items_open_holds discharges it by the citation `alx_zshadow_byte SEGS B ARx LAWS`. *)
Hypothesis EV_ZSH_BYTE : forall ly S Hp (W : world SEGS) mem md z,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= z < ly_stk_hi ly ->
  aview SEGS (w_H W) mem (SHADOW_OFF + z / 8) = Some 0.

#[local] Notation EV_PRE := (@ev_pre fx rc cp prh_img_A A_prog_listing PI_prog_A B ARx).
#[local] Notation EV_MID := (@ev_mid rc cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
#[local] Notation EV_KIND := (@ev_at_kind rc cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
#[local] Notation EV_STEPAT := (@ev_at_step rc cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
#[local] Notation EV_ENDAT := (@ev_at_end rc cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
#[local] Notation EV_TOEXIT := (@ev_to_exit fx rc cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK).

(* the frame of a stretch: what it did not write, it kept (FuzzStrdup.v:189-197) *)
Lemma evo_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* ex_value's own stack need is at least its frame (prh_img_A: pi_frame F_ex_value = 272) plus a runtime window *)
Lemma evo_stk : forall n : nat, 4096 <= @STK_ex_value prh_img_A n.
Proof.
intros n. unfold STK_ex_value.
match goal with |- _ <= _ * ?f + ?z =>
  assert (Hf : (0 <=? f) = true) by (vm_compute; reflexivity);
  assert (Hz : (4096 <=? z) = true) by (vm_compute; reflexivity) end.
apply Z.leb_le in Hf. apply Z.leb_le in Hz.
pose proof (Z.mul_nonneg_nonneg (Z.of_nat (S n)) _ ltac:(lia) Hf). lia.
Qed.

(* the shadow of a byte window of the REAL STACK: every byte of it reads 0 *)
Lemma evo_qzero : forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> ly_stk_lo ly <= p -> p + n <= ly_stk_hi ly ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n.
Proof.
intros ly S Hp W mem md p n HAR Hlo Hhi x Hx.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (EV_ZSH_BYTE ly S Hp W mem md x HAR). lia.
Qed.

(* the numbers every stretch of the piece needs: `in` and the spill area are inside the journal's stack window,
   both are at or above the memory-checking runtime's ceiling, and `in`'s 40 bytes are addressable *)
Lemma evo_bnd : forall a ly S Hp W mem md k p dep dl,
EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl ->
ARx ly S Hp W mem md /\
ea_q a mod 8 = 0 /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\
EVO_CEIL <= ea_q a /\ ea_q a <= EVO_TOP /\
ea_S1 a mod 32 = 0 /\ EVO_CEIL <= ea_S1 a /\ ea_S1 a + 160 <= ea_sp0 a /\ ea_S1 a <= EVO_TOP /\
ea_sp0 a - 287 <= ea_S1 a /\
(forall z, ea_sp0 a - ea_STK (PI := prh_img_A) a <= z < ea_sp0 a + ea_d a -> apresent (w_H W) mem z) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_q a) 40.
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID.
pose proof (proj1 (proj1 HPRE)) as HPRE0.
destruct HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & Hpres0 & _ & _).
destruct HPRE as (_ & _ & _ & _ & _ & _ & Hq8 & _ & Hsq & Hqd & Hfw & _).
destruct HMID as (HJ & _).
pose proof HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
unfold ea_sp0 in *.
pose proof (@ASAN_CEIL_range rc) as (CR & _).
pose proof (evo_stk (ea_n a)) as HSTK.
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & Hlo & Hhi & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hlosp & Hsphi & Hhi47 & _ & Hsptop & Htophi).
assert (HSTKa : 4096 <= ea_STK a) by (unfold ea_STK; exact HSTK).
unfold ASAN_CEIL in CR.
assert (HS1a : ea_S1 a mod 32 = 0).
{ unfold ea_S1.
  pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)) as Hm.
  pose proof (Z.div_mod (ea_SA a) 32 ltac:(lia)) as Hdm.
  assert (Heq : ea_SA a - ea_SA a mod 32 = 32 * (ea_SA a / 32)) by lia.
  rewrite Heq, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HS1b : spZ (ea_regs a) - 287 <= ea_S1 a <= spZ (ea_regs a) - 256).
{ unfold ea_S1, ea_SA, ea_sp0. pose proof (Z.mod_pos_bound (spZ (ea_regs a) - 256) 32 ltac:(lia)) as Hm. lia. }
assert (HLOQ : ly_stk_lo ly <= ea_q a) by (rewrite Hlo; lia).
assert (HHIQ : ea_q a + 40 <= ly_stk_hi ly) by (rewrite Hhi; lia).
assert (HQ : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_q a) 40)
  by (exact (evo_qzero ly S Hp W mem md (ea_q a) 40 HAR HLOQ HHIQ)).
assert (HQTOP : ea_q a + 40 <= 2 ^ 47) by (rewrite Hhi in HHIQ; lia).
split; [exact HAR|]. split; [exact Hq8|]. split; [exact Hsq|]. split; [exact Hqd|].
unfold EVO_CEIL, EVO_TOP.
rewrite Hlo in HLOQ.
split; [lia|]. split; [lia|]. split; [exact HS1a|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold ea_sp0; lia|].
split; [|exact HQ].
intros z Hz. replace z with (z - ea_d a + ea_d a) by lia. apply Hpres. lia.
Qed.

(* the entry sp is above the ceiling by the stack the activation may use *)
Lemma evo_sp_lo : forall a ly S Hp W mem md k p dep dl,
EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl ->
alloc_ceiling + 4096 <= ea_sp0 a /\ ea_sp0 a + ea_d a <= 2 ^ 47.
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID.
pose proof HMID as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hlosp & Hsphi & Hhi47 & _).
pose proof (evo_stk (ea_n a)) as HSTK.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; exact HSTK).
unfold ea_sp0 in *. clear - Hceil Hlosp HSTKa Hsphi Hhi47. lia.
Qed.

(* ---- the environment of the piece: registers below 32, then dep, scr, differs, the tree's tag ---- *)
Lemma evo_Ereg : forall a regs (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
ew (evo_E a regs) n = getr regs r.
Proof.
intros a regs n r Hn Hr. unfold evo_E. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma evo_Eex : forall a regs (j : nat), (j < 4)%nat ->
ew (evo_E a regs) (32 + j) =
  nth j [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))] (Z_to_bv 64 0).
Proof.
intros a regs j Hj. unfold evo_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
Lemma evo_Uoff : forall (E : env) (n : nat) (z v : Z), ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
sv_denot E (SOff n z) = Z_to_bv 64 (v + z).
Proof.
intros E n z v He Hv Hvz. cbn [sv_denot]. rewrite He. unfold w64.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma evo_atom_ok : forall (E : env) (n : nat) (v lo hi al : Z),
ew E n = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al He Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He. unfold w64. rewrite unsigned_lit_small by lia. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* ---- the regions of the piece: `in` field by field, and the spill area at s1 ---- *)
Lemma evo_Rin_ok : forall a ly S Hp W mem md k i1 c regs,
EV_PRE a -> EV_KIND a W regs mem md ly S Hp k i1 c ->
Forall (YP09.region_ok SEGS (evo_E a regs) (mrestrict (w_H W) mem)) evo_Rin.
Proof.
intros a ly S Hp W mem md k i1 c regs HPRE HKIND.
pose proof (evo_bnd a ly S Hp W mem md k _ _ _ HPRE (proj1 HKIND)) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & _ & _ & _ & _ & _ & Hpres & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hcur0 & _ & _ & _ & _ & _ & Hsrc & _ & Hlen & Hi0 & Hdep & _ & Hdl & Hwd & _).
pose proof HKIND as (HMID & HREG & _ & _ & _ & _ & _ & H11 & H12 & Hi1 & _).
pose proof HMID as (_ & _ & _ & _ & _ & Hcur & Hsrc' & _).
pose proof HREG as (_ & _ & _ & _ & H9 & _ & H19 & _).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2).
unfold ASAN_CEIL in CR1, CR2.
pose proof Hsrc' as (_ & Hx0lo & Hx0hi & _).
pose proof Hwd as (Hscr0 & Hscrhi & _).
destruct Hcur as (Hc0 & Hc8 & Hc16 & Hc24 & Hc32).
assert (EQ19 : ew (evo_E a regs) 19 = w64 (ea_q a)) by (rewrite (evo_Ereg a regs 19 19%bv ltac:(lia) eq_refl); exact H19).
assert (EQ11 : ew (evo_E a regs) 11 = w64 (ea_x0 a + Z.of_nat i1))
  by (rewrite (evo_Ereg a regs 11 11%bv ltac:(lia) eq_refl); exact H11).
assert (EQ12 : ew (evo_E a regs) 12 = w64 (ea_x0 a + ea_len a))
  by (rewrite (evo_Ereg a regs 12 12%bv ltac:(lia) eq_refl); exact H12).
assert (EQ32 : ew (evo_E a regs) 32 = w64 (ea_dep a)) by (exact (evo_Eex a regs 0%nat ltac:(lia))).
assert (EQ33 : ew (evo_E a regs) 33 = w64 (ea_scr a)) by (exact (evo_Eex a regs 1%nat ltac:(lia))).
assert (EQ34 : ew (evo_E a regs) 34 = w64 (ea_dl a)) by (exact (evo_Eex a regs 2%nat ltac:(lia))).
assert (Hi1len : Z.of_nat i1 <= ea_len a) by (unfold ea_len; lia).
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
unfold EVO_CEIL, EVO_TOP in Hqlo, Hqhi.
unfold evo_Rin, evo_Rp, evo_Re, evo_Rd, evo_Rs, evo_Rl.
repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite EQ19; unfold w64; rewrite !unsigned_lit_small by lia.
- split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_x0 a + Z.of_nat i1));
      [rewrite (evo_Uoff _ 11 0 (ea_x0 a + Z.of_nat i1) EQ11) by lia; f_equal; lia
      | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hc0].
- split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_x0 a + ea_len a));
    [rewrite (evo_Uoff _ 12 0 (ea_x0 a + ea_len a) EQ12) by lia; f_equal; lia
    | cbn; lia | cbn; lia | exact Hc8].
- split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 4%N _ (ea_dep a));
      [rewrite (evo_Uoff _ 32 0 (ea_dep a) EQ32) by lia; f_equal; lia
      | cbn; lia | cbn; lia | exact Hc16].
- split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_scr a));
    [rewrite (evo_Uoff _ 33 0 (ea_scr a) EQ33) by lia; f_equal; lia
    | cbn; lia | cbn; lia | exact Hc24].
- split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 4%N _ (ea_dl a));
      [rewrite (evo_Uoff _ 34 0 (ea_dl a) EQ34) by lia; f_equal; lia
      | cbn; lia | cbn; lia | exact Hc32].
Qed.

Lemma evo_Rf_ok : forall a ly S Hp W mem md k i1 c regs,
EV_PRE a -> EV_KIND a W regs mem md ly S Hp k i1 c ->
YP09.region_ok SEGS (evo_E a regs) (mrestrict (w_H W) mem) evo_Rf.
Proof.
intros a ly S Hp W mem md k i1 c regs HPRE HKIND.
pose proof (evo_bnd a ly S Hp W mem md k _ _ _ HPRE (proj1 HKIND)) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & _).
pose proof HKIND as (HMID & HREG & _).
pose proof HREG as (_ & _ & _ & _ & H9 & _).
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
assert (EQ9 : ew (evo_E a regs) 9 = w64 (ea_S1 a)) by (rewrite (evo_Ereg a regs 9 9%bv ltac:(lia) eq_refl); exact H9).
unfold EVO_CEIL, EVO_TOP in *.
unfold YP09.region_ok, evo_Rf.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EQ9. unfold w64. rewrite !unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.

(* v's type word: PRH_Reader's rd_u32 is a bound and YI04's val_mem *)
Lemma evo_u32_val : forall m p v, PRH_Reader.rd_u32 SEGS m p v -> val_mem SEGS m p 4 v.
Proof. intros m p v [_ Hv]. exact Hv. Qed.

(* every block a tree node's footprint names is a block of the reader's list (it is `lblk` of the node) *)
Lemma evo_items_lblk : forall (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l,
(forall a u D1, In u l -> P a u D1 -> forall x y, In (x, y) D1 -> lblk x y) ->
forall a D, PRH_Reader.pj_itemsR P a l D -> forall x y, In (x, y) D -> lblk x y.
Proof.
intros lblk P l. induction l as [|u l IH]; intros HP a D H x y Hin; cbn [PRH_Reader.pj_itemsR] in H.
- subst D. destruct Hin.
- destruct H as (D1 & D2 & -> & H1 & H2). apply in_app_or in Hin as [Hin|Hin].
  + exact (HP a u D1 ltac:(left; reflexivity) H1 x y Hin).
  + apply (IH ltac:(intros a' u' D' Hu'; apply HP; right; exact Hu') (a + 56) D2 H2 x y Hin).
Qed.
Lemma evo_mems_lblk : forall (lblk : Z -> Z -> Prop) m (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l,
(forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> forall x y, In (x, y) D1 -> lblk x y) ->
forall a ka D, PRH_Reader.pj_memsR SEGS m lblk P a ka l D -> forall x y, In (x, y) D -> lblk x y.
Proof.
intros lblk m P l. induction l as [|[nm u] l IH]; intros HP a ka D H x y Hin; cbn [PRH_Reader.pj_memsR] in H.
- subst D. destruct Hin.
- destruct H as (x0 & k0 & D1 & D2 & -> & _ & (Hl & _) & H1 & H2).
  destruct Hin as [E|Hin]; [injection E as <- <-; exact Hl|].
  apply in_app_or in Hin as [Hin|Hin].
  + exact (HP a u D1 ltac:(exists nm; left; reflexivity) H1 x y Hin).
  + apply (IH ltac:(intros a' u' D' (nm' & Hu'); apply HP; exists nm'; right; exact Hu') (a + 56) (ka + 8) D2 H2 x y Hin).
Qed.
Lemma evo_node_lblk : forall t m lblk p D, PRH_Reader.pj_nodeR SEGS m lblk p t D ->
forall x y, In (x, y) D -> lblk x y.
Proof.
intros t. induction t as [| | | txt bits | sx | items IH | members IH] using PjTree.jv_ind';
intros m lblk p D H x y Hin; cbn [PRH_Reader.pj_nodeR] in H;
destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb).
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & (k0 & (Hl & _) & ->)).
  destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct Hb as (_ & _ & _ & _ & (k0 & (Hl & _) & ->)).
  destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct Hb as (_ & _ & _ & _ & Hcap & (Di & -> & Hi)).
  apply in_app_or in Hin as [Hin|Hin].
  + destruct (cap =? 0) eqn:Ec; [destruct Hin|].
    destruct Hin as [E|[]]. injection E as <- <-.
    destruct Hcap as [(Hc0 & _)|(_ & Hl)]; [apply Z.eqb_neq in Ec; contradiction | exact Hl].
  + rewrite Forall_forall in IH.
    refine (evo_items_lblk lblk (PRH_Reader.pj_nodeR SEGS m lblk) items
      (fun a' u' D' Hu' HP x' y' Hin' => IH u' Hu' m lblk a' D' HP x' y' Hin') kids Di Hi x y Hin).
- destruct Hb as (_ & _ & _ & Hcap & (Di & -> & Hi)).
  apply in_app_or in Hin as [Hin|Hin].
  + destruct (cap =? 0) eqn:Ec; [destruct Hin|].
    destruct Hcap as [(Hc0 & _)|(_ & Hl1 & Hl2)]; [apply Z.eqb_neq in Ec; contradiction|].
    destruct Hin as [E|[E|[]]]; injection E as <- <-; [exact Hl1 | exact Hl2].
  + rewrite Forall_forall in IH.
    refine (evo_mems_lblk lblk m (PRH_Reader.pj_nodeR SEGS m lblk) members _ kids keys Di Hi x y Hin).
    intros a' u' D' (nm' & Hu') HP x' y' Hin'. exact (IH (nm', u') Hu' m lblk a' D' HP x' y' Hin').
Qed.

Lemma evo_node_hdr : forall m lblk p t D, PRH_Reader.pj_nodeR SEGS m lblk p t D ->
  PRH_Reader.rd_u32 SEGS m p (PjTree.tag t).
Proof.
intros m lblk p t D H.
destruct t; cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & (_ & Hu & _) & _);
  exact Hu.
Qed.

Lemma evo_Rv_ok : forall a ly S Hp W mem md k i1 c regs,
EV_PRE a -> EV_KIND a W regs mem md ly S Hp k i1 c -> ea_v a <> 0 ->
YP09.region_ok SEGS (evo_E a regs) (mrestrict (w_H W) mem) evo_Rv /\ 0 <= PjTree.tag (ea_t a) < 2 ^ 32 /\
4096 <= ea_v a <= EVO_TOP.
Proof.
intros a ly S Hp W mem md k i1 c regs HPRE HKIND Hv0.
pose proof HKIND as (HMID & HREG & _ & _ & _ & H23 & _).
pose proof HMID as (HJ & _ & _ & _ & HLED & _ & _ & _ & HT & _).
destruct HT as [HT | HT]; [contradiction|].
destruct HT as (Hnode & Hhome & Hra & _).
pose proof (evo_node_hdr _ _ _ _ _ Hnode) as Hu32.
pose proof (evo_u32_val _ _ _ Hu32) as Hval.
destruct Hu32 as [Htag _].
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhi & _).
destruct Hstk as (_ & _ & Hceil & Hlosp & _ & Hhi47 & _).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof (@cf_head_nonneg cp) as Hch.
assert (Hvr : 4096 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47).
{ destruct Hhome as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hb & Hm) | (Hsp & Hhi')]].
  - destruct HLED as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hm0 & Hab & _).
    cbn [fst snd] in Hm0, Hab.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
    assert (Hrq : m + cf_head <= req_size (m + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
    lia.
  - destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [_ HF].
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (H4096 & Hc). cbn [fst snd] in H4096, Hc. lia.
  - pose proof HPRE as (HPRE0 & _).
    pose proof (proj1 HPRE0) as (_ & _ & _ & _ & _ & Hstk0' & _).
    destruct Hstk0' as (_ & _ & Hceil0 & Hlo0 & _).
    pose proof (evo_stk (ea_n a)) as HSTK.
    rewrite Hhi in Hhi'. unfold ea_STK in Hlo0. lia. }
assert (EQ23 : ew (evo_E a regs) 23 = w64 (ea_v a)) by (rewrite (evo_Ereg a regs 23 23%bv ltac:(lia) eq_refl); exact H23).
assert (EQ35 : ew (evo_E a regs) 35 = w64 (PjTree.tag (ea_t a))) by (exact (evo_Eex a regs 3%nat ltac:(lia))).
split; [|split; [exact Htag | unfold EVO_TOP; lia]].
unfold YP09.region_ok, evo_Rv.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EQ23. unfold w64. rewrite !unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val _ _ _ _ _ 4%N _ (PjTree.tag (ea_t a)));
  [rewrite (evo_Uoff _ 35 0 (PjTree.tag (ea_t a)) EQ35) by lia; f_equal; lia
  | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hval].
Qed.

(* s10 = shadow (q), as the token machinery reads it: (q >> 3) + s8 *)
Lemma evo_S10_den : forall (E : env) q, ew E 19 = w64 q -> 0 <= q < 2 ^ 47 -> ew E 24 = w64 SHADOW_OFF ->
sv_denot E EVO_S10 = w64 (shadow_addr q).
Proof.
intros E q H19 Hq H24. apply bv_eq.
change (bv_unsigned (sv_denot E EVO_S10)) with (U E EVO_S10).
unfold EVO_S10, EVO_SHQ, EVO_Bx. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 19 q H19) by lia. rewrite (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)) as Hd0.
assert (Hd1 : q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold w64, shadow_addr, SHADOW_OFF in *.
rewrite (zcanon_id (q / 8)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia).
rewrite unsigned_lit_small by lia. lia.
Qed.

Lemma evo_regs_ok : forall a regs cz s7v,
getr regs 21 = w64 cz -> getr regs 23 = sv_denot (evo_E a regs) s7v ->
getr regs 26 = sv_denot (evo_E a regs) EVO_S10 ->
regs_ok (evo_E a regs) (evo_regs cz s7v) regs.
Proof.
intros a regs cz s7v H21 H23 H26. unfold evo_regs.
apply regs_ok_pin; [|intros X; discriminate X | exact H23].
apply regs_ok_pin; [|intros X; discriminate X | exact H26].
apply regs_ok_pin; [|intros X; discriminate X | exact H21].
apply regs_ok_Eimg_Ereg.
Qed.

Lemma evo_atoms_ok : forall a W regs mem md ly S Hp k i1 c vf,
EV_PRE a -> EV_KIND a W regs mem md ly S Hp k i1 c -> atoms_ok (evo_E a regs) vf ->
atoms_ok (evo_E a regs) (evo_atoms vf).
Proof.
intros a W regs mem md ly S Hp k i1 c vf HPRE HKIND Hvf.
pose proof (evo_bnd a ly S Hp W mem md k _ _ _ HPRE (proj1 HKIND)) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & Hi0 & Hdep & _).
pose proof HKIND as (HMID & HREG & _ & _ & _ & _ & _ & H11 & H12 & Hi1 & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & Hsrc' & _).
pose proof HREG as (_ & _ & _ & _ & H9 & _ & H19 & H24 & _).
pose proof Hsrc' as (_ & Hx0lo & Hx0hi & _).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
assert (Hi1len : Z.of_nat i1 <= ea_len a) by (unfold ea_len; lia).
unfold ea_len in Hx0hi, Hi1len.
unfold evo_atoms, EVO_CEIL, EVO_TOP in *. cbn [app atoms_ok].
split; [apply (evo_atom_ok _ 9 (ea_S1 a)); [rewrite (evo_Ereg a regs 9 9%bv ltac:(lia) eq_refl); exact H9 | lia | lia | exact HS32 | lia]|].
split; [apply (evo_atom_ok _ 11 (ea_x0 a + Z.of_nat i1));
  [rewrite (evo_Ereg a regs 11 11%bv ltac:(lia) eq_refl); exact H11 | lia | lia | apply Z.mod_1_r | lia]|].
split; [apply (evo_atom_ok _ 12 (ea_x0 a + ea_len a)); unfold ea_len;
  [rewrite (evo_Ereg a regs 12 12%bv ltac:(lia) eq_refl); exact H12 | lia | lia | apply Z.mod_1_r | lia]|].
split; [apply (evo_atom_ok _ 19 (ea_q a)); [rewrite (evo_Ereg a regs 19 19%bv ltac:(lia) eq_refl); exact H19 | lia | lia | exact Hq8 | lia]|].
split; [apply (evo_atom_ok _ 24 SHADOW_OFF);
  [rewrite (evo_Ereg a regs 24 24%bv ltac:(lia) eq_refl); exact H24 | unfold SHADOW_OFF; lia | lia | apply Z.mod_1_r | lia]|].
split; [apply (evo_atom_ok _ 32 (ea_dep a)); [exact (evo_Eex a regs 0%nat ltac:(lia)) | lia
  | change (Z.of_nat PjGrammar.MAXD) with 32; lia | apply Z.mod_1_r | lia]|].
exact Hvf.
Qed.

(* THE SET-UP: the symbolic state at the cut 0x834bc holds of the machine state P_KIND describes *)
Lemma evo_entry : forall a fxc W regs mem md ly S Hp k i1 c s7v rs vf,
EV_PRE a -> EV_KIND a W regs mem md ly S Hp k i1 c ->
getr regs 23 = sv_denot (evo_E a regs) s7v ->
regions_wf rs = true -> Forall (YP09.region_ok SEGS (evo_E a regs) (mrestrict (w_H W) mem)) rs ->
pairwise_disjoint (evo_E a regs) (evo_Rin ++ evo_Rf :: rs) ->
atoms_ok (evo_E a regs) vf ->
st_ok_pi (fx := fxc) SEGS VAL (evo_E a regs) (evo_ss c s7v rs vf)
  (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (@ev_pc rc A_prog_listing PI_prog_A EV_ITEMS)) mem
    (YK11.seg_rom SEGS))).
Proof.
intros a fxc W regs mem md ly S Hp k i1 c s7v rs vf HPRE HKIND H23 Hwf Hrs Hpd Hvf.
pose proof (evo_bnd a ly S Hp W mem md k _ _ _ HPRE (proj1 HKIND)) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & _).
pose proof HKIND as (HMID & HREG & _ & H21 & _).
pose proof HREG as (_ & _ & _ & _ & _ & _ & H19 & H24 & _ & H26).
rewrite restrict_mkst_fx.
replace (@ev_pc rc A_prog_listing PI_prog_A EV_ITEMS) with (BASE + EVO_PC EV_ITEMS) by (vm_compute; reflexivity).
unfold evo_ss. apply pa_entry_st_ok_full.
- apply evo_regs_ok; [exact H21 | exact H23 |].
  rewrite H26. symmetry. apply evo_S10_den.
  + rewrite (evo_Ereg a regs 19 19%bv ltac:(lia) eq_refl). exact H19.
  + unfold EVO_CEIL, EVO_TOP in *. lia.
  + rewrite (evo_Ereg a regs 24 24%bv ltac:(lia) eq_refl). exact H24.
- unfold evo_Rin, evo_Rp, evo_Re, evo_Rd, evo_Rs, evo_Rl, evo_Rf. cbn [app regions_wf].
  rewrite Hwf. vm_compute (region_wf _). reflexivity.
- apply Forall_app. split; [exact (evo_Rin_ok a ly S Hp W mem md k i1 c regs HPRE HKIND)|].
  apply Forall_cons; [exact (evo_Rf_ok a ly S Hp W mem md k i1 c regs HPRE HKIND)|].
  exact Hrs.
- exact Hpd.
- split; [|split; [exact I | exact I]].
  exact (evo_atoms_ok a W regs mem md ly S Hp k i1 c vf HPRE HKIND Hvf).
Qed.

(* reading a cell's value back out of the engine's symbolic memory *)
Lemma evo_region_val : forall (E : env) (m : word -> option byte) (rs : smem) (r : YP09.region) off (w : N) (e : sv) v,
mem_ok SEGS E m rs -> In r rs -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
val_mem SEGS m (base_val E (YP09.r_base r) + off) (N.to_nat w) v.
Proof.
intros E m rs r off w e v (_ & Hrs & _) Hin Hch He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hrs _ Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hch) as Hc.
exact (val_of_chunk_ok SEGS E m (base_val E (YP09.r_base r)) off w e v Hc He Hv Hw).
Qed.

(* ---- the tail cut's state holds of the machine state the invariant describes ---- *)
(* ---- the environment of the tail cut: the twelve extra values (32..43) ---- *)
Definition evo_ETx (a : ev_act) (iw byte clo dln : Z) : list word :=
  [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a));
   w64 (ea_x0 a + iw); w64 byte; w64 0; w64 0; w64 clo; w64 dln; w64 0; w64 (shadow_addr (ea_q a + 16))].
Definition evo_ET (a : ev_act) (regs : bvmap 5 word) (iw byte clo dln : Z) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs (evo_ETx a iw byte clo dln)).
Lemma evo_ETreg : forall a regs iw byte clo dln (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
ew (evo_ET a regs iw byte clo dln) n = getr regs r.
Proof.
intros a regs iw byte clo dln n r Hn Hr. unfold evo_ET. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma evo_ETex : forall a regs iw byte clo dln (j : nat), (j < 12)%nat ->
ew (evo_ET a regs iw byte clo dln) (32 + j) = nth j (evo_ETx a iw byte clo dln) (Z_to_bv 64 0).
Proof.
intros a regs iw byte clo dln j Hj. unfold evo_ET. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_extra.
Qed.


Lemma evo_Tstate : forall a ly S Hp W mem md k (iw : nat) dln (o : bool) regs,
EV_PRE a -> EV_MID a ly S Hp W mem md k (ea_x0 a + Z.of_nat iw) (ea_dep a + 1) dln ->
ev_regs (PA := PI_prog_A) a regs -> getr regs 12 = w64 (ea_x0 a + ea_len a) ->
getr regs 23 = w64 (ev_v' (ea_v a) o (ea_t a)) ->
val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 48) 8 (ea_q a + 16) ->
val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 56) 8 (shadow_addr (ea_q a + 16)) ->
val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 64) 8 (PjGrammar.closer o) ->
(dln = 0 \/ dln = 1) -> (iw <= length (ea_x a))%nat ->
0 <= ev_v' (ea_v a) o (ea_t a) <= EVO_TOP ->
Forall (YP09.region_ok SEGS (evo_ET a regs (Z.of_nat iw) (nth iw (ea_x a) 0) (PjGrammar.closer o) dln)
          (mrestrict (w_H W) mem)) (evo_Tin ++ [evo_Tf]) /\
((iw < length (ea_x a))%nat ->
  YP09.region_ok SEGS (evo_ET a regs (Z.of_nat iw) (nth iw (ea_x a) 0) (PjGrammar.closer o) dln)
    (mrestrict (w_H W) mem) evo_Ttext) /\
atoms_ok (evo_ET a regs (Z.of_nat iw) (nth iw (ea_x a) 0) (PjGrammar.closer o) dln) evo_Tatoms /\
regs_ok (evo_ET a regs (Z.of_nat iw) (nth iw (ea_x a) 0) (PjGrammar.closer o) dln)
  (sr_set sr_atoms 26%bv EVO_S10) regs.
Proof.
intros a ly S Hp W mem md k iw dln o regs HPRE HMID HREG H12 H23v H48 H56 H64 Hdln Hiw Hv'.
pose proof (evo_bnd a ly S Hp W mem md k _ _ _ HPRE HMID) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & HQA).
pose proof HMID as (_ & _ & _ & _ & _ & Hcur & Hsrc & Hwd & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlenb & Hi0 & Hdepb & _).
pose proof Hsrc as (Hga & Hx0lo & Hx0hi & _).
pose proof Hwd as (Hscr0 & Hshi & _).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
pose proof HREG as (_ & _ & _ & _ & H9 & _ & H19 & H24 & _ & H26).
destruct Hcur as (C0 & C8 & C16 & C24 & C32).
set (byte := nth iw (ea_x a) 0) in *.
assert (Hiwlen : Z.of_nat iw <= ea_len a) by (unfold ea_len; apply inj_le; exact Hiw).
unfold ea_len in Hx0hi, Hiwlen.
assert (EQ9 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 9 = w64 (ea_S1 a)) by (rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 9 9%bv ltac:(lia) eq_refl); exact H9).
assert (EQ12 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 12 = w64 (ea_x0 a + Z.of_nat (length (ea_x a))))
  by (rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 12 12%bv ltac:(lia) eq_refl); unfold ea_len in H12; exact H12).
assert (EQ19 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 19 = w64 (ea_q a)) by (rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 19 19%bv ltac:(lia) eq_refl); exact H19).
assert (EQ23 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 23 = w64 (ev_v' (ea_v a) o (ea_t a)))
  by (rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 23 23%bv ltac:(lia) eq_refl); exact H23v).
assert (EQ24 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 24 = w64 SHADOW_OFF) by (rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 24 24%bv ltac:(lia) eq_refl); exact H24).
assert (EQ32 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 32 = w64 (ea_dep a)) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 0%nat ltac:(lia))).
assert (EQ33 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 33 = w64 (ea_scr a)) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 1%nat ltac:(lia))).
assert (EQ36 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 36 = w64 (ea_x0 a + Z.of_nat iw)) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 4%nat ltac:(lia))).
assert (EQ37 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 37 = w64 byte) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 5%nat ltac:(lia))).
assert (EQ40 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 40 = w64 (PjGrammar.closer o)) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 8%nat ltac:(lia))).
assert (EQ41 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 41 = w64 dln) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 9%nat ltac:(lia))).
assert (EQ43 : ew (evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) 43 = w64 (shadow_addr (ea_q a + 16))) by (exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 11%nat ltac:(lia))).
set (E := evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) in *.
assert (Hbyte : 0 <= byte < 256).
{ destruct (Nat.lt_ge_cases iw (length (ea_x a))) as [Hlt|Hge].
  - exact (proj2 (Hga iw Hlt)).
  - subst byte. rewrite nth_overflow by exact Hge. lia. }
assert (Hclo : 93 <= PjGrammar.closer o <= 125) by (unfold PjGrammar.closer; destruct o; lia).
assert (HSH : 0 <= shadow_addr (ea_q a + 16) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. unfold EVO_TOP in Hqhi.
  pose proof (Z.div_pos (ea_q a + 16) 8 ltac:(clear - Hqlo; unfold EVO_CEIL in Hqlo; lia) ltac:(lia)) as D1.
  assert (D2 : (ea_q a + 16) / 8 <= ea_q a + 16) by (apply Z.div_le_upper_bound; clear - Hqlo Hqhi; unfold EVO_CEIL in Hqlo; lia).
  clear - D1 D2 Hqhi. lia. }
unfold EVO_CEIL in Hqlo, HSlo. unfold EVO_TOP in Hqhi, HShi, Hv'.
split; [|split; [|split]].
- unfold evo_Tin, evo_Tp, evo_Re, evo_Td, evo_Rs, evo_Tl, evo_Tf. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite EQ19. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_x0 a + Z.of_nat iw));
      [rewrite (evo_Uoff _ 36 0 _ EQ36) by lia; f_equal; lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact C0].
  + rewrite EQ19. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_x0 a + Z.of_nat (length (ea_x a))));
      [rewrite (evo_Uoff _ 12 0 _ EQ12) by lia; f_equal; lia | cbn; lia | cbn; lia | unfold ea_len in C8; exact C8].
  + rewrite EQ19. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 4%N _ (ea_dep a + 1));
      [rewrite (evo_Uoff _ 32 1 _ EQ32) by lia; f_equal; lia | cbn; lia | cbn; lia | exact C16].
  + rewrite EQ19. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_scr a));
      [rewrite (evo_Uoff _ 33 0 _ EQ33) by lia; f_equal; lia | cbn; lia | cbn; lia | exact C24].
  + rewrite EQ19. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 4%N _ dln);
      [rewrite (evo_Uoff _ 41 0 _ EQ41) by lia; f_equal; lia | cbn; lia | cbn; lia | exact C32].
  + rewrite EQ9. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; apply (apresent_writable SEGS); apply Hpres; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_q a + 16));
        [rewrite (evo_Uoff _ 19 16 _ EQ19) by lia; f_equal; lia | cbn; lia | cbn; lia | exact H48].
    * apply (chunk_ok_val _ _ _ _ _ 8%N _ (shadow_addr (ea_q a + 16)));
        [rewrite (evo_Uoff _ 43 0 _ EQ43) by lia; f_equal; lia | cbn; lia | cbn; lia | exact H56].
    * apply (chunk_ok_val _ _ _ _ _ 8%N _ (PjGrammar.closer o));
        [rewrite (evo_Uoff _ 40 0 _ EQ40) by lia; f_equal; lia | cbn; lia | cbn; lia | exact H64].
- intros Hlt. unfold evo_Ttext, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EQ36. unfold w64. rewrite !unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val _ _ _ _ _ 1%N _ byte);
    [rewrite (evo_Uoff _ 37 0 _ EQ37) by lia; f_equal; lia | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. replace (ea_x0 a + Z.of_nat iw) with (ea_x0 a + Z.of_nat iw) by lia.
  exact (proj1 (Hga iw Hlt)).
- unfold evo_Tatoms, EVO_CEIL, EVO_TOP. cbn [atoms_ok].
  split; [apply (evo_atom_ok _ 9 (ea_S1 a)); [exact EQ9 | lia | lia | exact HS32 | lia]|].
  split; [apply (evo_atom_ok _ 12 (ea_x0 a + Z.of_nat (length (ea_x a)))); [exact EQ12 | lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 19 (ea_q a)); [exact EQ19 | lia | lia | exact Hq8 | lia]|].
  split; [apply (evo_atom_ok _ 23 (ev_v' (ea_v a) o (ea_t a))); [exact EQ23 | lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 24 SHADOW_OFF); [exact EQ24 | unfold SHADOW_OFF; lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 32 (ea_dep a)); [exact EQ32 | lia | change (Z.of_nat PjGrammar.MAXD) with 32; lia
    | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 36 (ea_x0 a + Z.of_nat iw)); [exact EQ36 | lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 37 byte); [exact EQ37 | lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 40 (PjGrammar.closer o)); [exact EQ40 | lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (evo_atom_ok _ 41 dln); [exact EQ41 | lia | lia | apply Z.mod_1_r | lia]|]. exact I.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H26. symmetry. apply evo_S10_den; [exact EQ19 | lia | exact EQ24].
Qed.

(* the piece's post, as the interface states it (o = the opener's kind) *)
Definition evo_post (a : ev_act) (fxc : YK11.FPState) (o : bool) : world SEGS -> config -> Prop :=
  fun W' c' => EV_TOEXIT a W' c' \/
    exists fx' regs' mem' md' ly' S' Hp' k' (i : nat) dln',
      @ev_fx fx fx' /\
      ((c' = ev_cfg (PA := PI_prog_A) fx' regs' EV_STEP mem' md' /\
        EV_STEPAT a W' regs' mem' md' ly' S' Hp' k' o 0 0 [] i dln') \/
       (c' = ev_cfg (PA := PI_prog_A) fx' regs' EV_END mem' md' /\
        EV_ENDAT a W' regs' mem' md' ly' S' Hp' k' o [] i dln')).

(* ======== what a stretch of piece 6 writes, and what it therefore keeps ======== *)

(* the four byte windows the engine may write in this piece: in->p, in->depth, in->differs (all three in the
   text's footprint ea_FP) and the spill area at s1 (below the prologue's save area, which starts at sp0 - 104) *)
Definition evo_W4 (a : ev_act) (z : Z) : Prop :=
  (ea_q a <= z < ea_q a + 8) \/ (ea_q a + 16 <= z < ea_q a + 20) \/
  (ea_q a + 32 <= z < ea_q a + 36) \/ (ea_S1 a <= z < ea_S1 a + 152).

Lemma evo_keep_mbyte : forall a (W : world SEGS) mem mem' z,
(forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
0 <= z < 2 ^ 64 -> ~ evo_W4 a z ->
mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z.
Proof.
intros a W mem mem' z HK Hz Hn. unfold mbyte.
rewrite (HK (Z_to_bv 64 z)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma evo_keep_aview : forall a (W : world SEGS) mem mem' z,
(forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
0 <= z < 2 ^ 64 -> ~ evo_W4 a z ->
aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z.
Proof.
intros a W mem mem' z HK Hz Hn. unfold aview. f_equal. exact (evo_keep_mbyte a W mem mem' z HK Hz Hn).
Qed.
Lemma evo_keep_val : forall a (W : world SEGS) mem mem' p (n : nat) v,
(forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> (forall z, p <= z < p + Z.of_nat n -> ~ evo_W4 a z) ->
val_mem SEGS (mrestrict (w_H W) mem) p n v -> val_mem SEGS (mrestrict (w_H W) mem') p n v.
Proof.
intros a W mem mem' p n v HK Hp Hn Hout H j Hj.
assert (Hjz : 0 <= Z.of_nat j < Z.of_nat n) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt; exact Hj]).
assert (H1 : 0 <= p + Z.of_nat j < 2 ^ 64) by lia.
assert (H2 : ~ evo_W4 a (p + Z.of_nat j)) by (apply Hout; lia).
rewrite (evo_keep_mbyte a W mem mem' (p + Z.of_nat j) HK H1 H2). exact (H j Hj).
Qed.

(* every address at or below the memory-checking runtime's ceiling (the text, the scratch, a tree node, a block's
   head, alloc.c's statics and EVERY shadow byte) is outside the four windows, as is the prologue's save area *)
Lemma evo_W4_low : forall a ly S Hp W mem md k p dep dl z,
EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl -> z < alloc_ceiling + 8 -> ~ evo_W4 a z.
Proof.
intros a ly S Hp W mem md k p dep dl z HPRE HMID Hz.
pose proof (evo_bnd a ly S Hp W mem md k p dep dl HPRE HMID) as
  (_ & _ & Hsq & _ & _ & _ & _ & _ & _ & _ & HS287 & _).
pose proof HMID as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hlosp & _).
pose proof (evo_stk (ea_n a)) as HSTK.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; exact HSTK).
unfold evo_W4, ea_sp0 in *. clear HPRE HMID HJ HSTK.
intros [H|[H|[H|H]]]; lia.
Qed.
Lemma evo_W4_save : forall a ly S Hp W mem md k p dep dl z,
EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl -> ea_sp0 a - 104 <= z -> z < ea_sp0 a -> ~ evo_W4 a z.
Proof.
intros a ly S Hp W mem md k p dep dl z HPRE HMID Hlo Hhi.
pose proof (evo_bnd a ly S Hp W mem md k p dep dl HPRE HMID) as
  (_ & _ & Hsq & _ & _ & _ & _ & _ & _ & _ & HS287 & _).
pose proof HMID as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & _ & Hlosp & _).
assert (HS256 : ea_S1 a <= ea_sp0 a - 256).
{ unfold ea_S1, ea_SA, ea_sp0. pose proof (Z.mod_pos_bound (spZ (ea_regs a) - 256) 32 ltac:(lia)) as Hm. lia. }
unfold evo_W4. clear HPRE HMID HJ. intros [H|[H|[H|H]]]; lia.
Qed.

(* a tree's footprint lies below 2 ^ 47: its root by the premise, every other block of it is a live harness block
   (evo_node_lblk), inside an allocator block below alloc_ceiling (alx_blocks) *)
Lemma evo_foot_rng : forall ly S Hp W mem md Lam peak cnt fail ran most own m p t D,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_Reader.pj_nodeR SEGS m (prh_lin Lam) p t D -> 0 <= p -> p + 56 <= 2 ^ 47 ->
  forall x, PRH_Reader.pj_footR p D x -> 0 <= x < 2 ^ 47.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own m p t D HAR HL Hpj Hp0 Hp1 x [Hx | ([b k] & Hin & Hx)]; [lia|].
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof (@cf_head_nonneg cp) as Hch.
pose proof (evo_node_lblk t m (prh_lin Lam) p D Hpj b k Hin) as Hl. unfold prh_lin in Hl.
destruct HL as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF _ Hl) as (Hk0 & Hab & _).
cbn [fst snd] in Hk0, Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head)).
{ unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0) as [He|He]; clear - Hk0 Hch He; lia. }
unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx. clear - Hx H4096 Hc Hrq Hch Hk0 CR1. lia.
Qed.

(* ev_mid travels along a stretch of piece 6: the journal is the engine's, the three cells of `in` the stretch may
   write are given by their new values, and every other byte the invariant reads is kept, because the stretch
   writes only the four windows (all of which are in ea_FP or below the prologue's save area) *)
Lemma evo_mid_keep : forall a ly S Hp W mem md k p dep dl mem' md' k' p' dep' dl',
EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl ->
ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_A)) ARx
  (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
  (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k' ->
(forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 p' ->
val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 16) 4 dep' ->
val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 32) 4 dl' ->
YAkMemnorm.memnorm SEGS mem' ->
EV_MID a ly S Hp W mem' md' k' p' dep' dl'.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' k' p' dep' dl' HPRE HMID HJ' HK HGR Hp' Hdep' Hdl' HMN'.
pose proof (evo_bnd a ly S Hp W mem md k p dep dl HPRE HMID) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & HQA).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
unfold EVO_CEIL in Hqlo, HSlo. unfold EVO_TOP in Hqhi, HShi.
pose proof HMID as (HJ0 & _).
pose proof HJ0 as (_ & HLE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
destruct HLE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhi_eq & _).
destruct Hstk0 as (_ & _ & Hceil & Hlosp & Hsphi & Hhi47 & _).
assert (HSPHI : ea_sp0 a + ea_d a <= 2 ^ 47) by (unfold ea_sp0 in *; clear - Hsphi Hhi47; lia).
pose proof (evo_stk (ea_n a)) as HSTK0.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; exact HSTK0).
assert (HSPLO : alloc_ceiling + 4096 <= ea_sp0 a) by (unfold ea_sp0 in *; clear - Hceil Hlosp HSTKa; lia).
pose proof (fun z => evo_W4_low a ly S Hp W mem md k p dep dl z HPRE HMID) as HLOW.
pose proof (fun z => evo_W4_save a ly S Hp W mem md k p dep dl z HPRE HMID) as HSAVEW.
pose proof HMID as (HJ & Hwin & HHp & HBL & HLED & Hcur & Hsrc & Hwd & HT & HSAV & HFLAG & HRL & HRP & _).
assert (KEEPV : forall z (n : nat) v, 0 <= z -> z + Z.of_nat n <= alloc_ceiling + 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) z n v -> val_mem SEGS (mrestrict (w_H W) mem') z n v).
{ intros z n v Hz0 Hzn Hv. apply (evo_keep_val a W mem mem' z n v HK Hz0);
  [clear - Hz0 Hzn CR1 CR2; lia | intros y Hy; apply HLOW; clear - Hy Hzn; lia | exact Hv]. }
assert (KEEPA : forall z, 0 <= z -> z < alloc_ceiling + 8 ->
  aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z).
{ intros z Hz0 Hz. apply (evo_keep_aview a W mem mem' z HK); [clear - Hz0 Hz CR1 CR2; lia | apply HLOW; exact Hz]. }
assert (KEEPS : forall z (n : nat) v, ea_sp0 a - 104 <= z -> z + Z.of_nat n <= ea_sp0 a ->
  val_mem SEGS (mrestrict (w_H W) mem) z n v -> val_mem SEGS (mrestrict (w_H W) mem') z n v).
{ intros z n v Hz0 Hzn Hv. apply (evo_keep_val a W mem mem' z n v HK);
  [clear - Hz0 Hzn HSPLO CR1; lia | clear - Hz0 Hzn Hsq Hqhi; lia
  | intros y Hy; apply HSAVEW; clear - Hy Hz0 Hzn; lia | exact Hv]. }
split; [exact HJ'|]. split.
- intros z Hz1 Hz2. rewrite <- (Hwin z Hz1 Hz2).
  apply (evo_keep_aview a W mem mem' z HK); [clear - Hz1 HSPLO HSPHI CR1; lia|].
  unfold evo_W4. intros [H|[H|[H|H]]].
  + apply Hz2. exists (ea_q a, ea_q a + 8). split; [unfold ea_FP; cbn [In]; tauto | cbn [fst snd]; clear - H; lia].
  + apply Hz2. exists (ea_q a + 16, ea_q a + 20). split; [unfold ea_FP; cbn [In]; tauto | cbn [fst snd]; clear - H; lia].
  + apply Hz2. exists (ea_q a + 32, ea_q a + 36). split; [unfold ea_FP; cbn [In]; tauto | cbn [fst snd]; clear - H; lia].
  + clear - H Hz1 HSsp. lia.
- split; [exact HHp|]. split; [exact HBL|].
  assert (HGLO : forall z, z = @pi_g_live prh_img_A \/ z = @pi_g_peak prh_img_A \/ z = @pi_g_count prh_img_A \/
    z = @pi_g_fail prh_img_A \/ z = @pi_g_ran_out prh_img_A \/ z = @pi_g_most prh_img_A \/
    z = @pi_g_own_ran_out prh_img_A -> 0 <= z /\ z + 8 <= alloc_ceiling + 8).
  { intros z Hzc.
    assert (Hv : 0 <= z <= 2147450880).
    { destruct Hzc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; subst z; split; vm_compute; discriminate. }
    clear - Hv CR1 CR2. lia. }
  split.
  + pose proof HLED as (HG & HND & HF & HPM).
    split; [|split; [exact HND | split; [|exact HPM]]].
    * (* #102: prh_glob carries g_most / g_own_ran_out (PRH_Base.v prh_most / prh_own), kept as the five are *)
      unfold prh_glob, prh_most, prh_own in HG |- *.
      pose proof HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Grest).
      pose proof (HGLO (@pi_g_live prh_img_A) ltac:(tauto)) as L1.
      pose proof (HGLO (@pi_g_peak prh_img_A) ltac:(tauto)) as L2.
      pose proof (HGLO (@pi_g_count prh_img_A) ltac:(tauto)) as L3.
      pose proof (HGLO (@pi_g_fail prh_img_A) ltac:(tauto)) as L4.
      pose proof (HGLO (@pi_g_ran_out prh_img_A) ltac:(tauto)) as L5.
      pose proof (HGLO (@pi_g_most prh_img_A) ltac:(tauto)) as L6.
      pose proof (HGLO (@pi_g_own_ran_out prh_img_A) ltac:(tauto)) as L7.
      split; [apply (KEEPV _ 8%nat); [clear - L1; lia | cbn [Z.of_nat]; clear - L1; lia | exact G1]|].
      split; [apply (KEEPV _ 8%nat); [clear - L2; lia | cbn [Z.of_nat]; clear - L2; lia | exact G2]|].
      split; [apply (KEEPV _ 8%nat); [clear - L3; lia | cbn [Z.of_nat]; clear - L3; lia | exact G3]|].
      split; [apply (KEEPV _ 8%nat); [clear - L4; lia | cbn [Z.of_nat]; clear - L4; lia | exact G4]|].
      split; [apply (KEEPV _ 1%nat); [clear - L5; lia | cbn [Z.of_nat]; clear - L5; lia | exact G5]|].
      split; [split; [apply (KEEPV _ 8%nat); [clear - L6; lia | cbn [Z.of_nat]; clear - L6; lia | exact G6]
        | exact G6r]|].
      split; [split; [apply (KEEPV _ 1%nat); [clear - L7; lia | cbn [Z.of_nat]; clear - L7; lia | exact G7]
        | exact G7r]|].
      exact Grest.
    * eapply Forall_impl; [|exact HF]. intros [a0 k0] (Hk0 & Hab & Hhp & Hal & Hval). cbn [fst snd] in *.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem' md' _ _ (proj1 HJ') Hab) as (_ & H4096 & Hc & _).
      pose proof (@cf_head_nonneg cp) as Hch.
      assert (Hrq : 1 <= req_size (k0 + cf_head)).
      { unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0) as [He|He]; clear - Hk0 Hch He; lia. }
      split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Hal|].
      apply (KEEPV _ 8%nat); [clear - H4096; lia | clear - H4096 Hc Hrq; cbn [Z.of_nat]; lia | exact Hval].
  + pose proof Hcur as (C0 & C8 & C16 & C24 & C32).
    split.
    * split; [exact Hp'|]. split.
      { apply (evo_keep_val a W mem mem' (ea_q a + 8) 8%nat _ HK); [clear - Hqlo CR1; lia | clear - Hqhi; lia
        | intros y Hy; unfold evo_W4; clear - Hy HSsp Hsq; intros [H|[H|[H|H]]]; lia | exact C8]. }
      split; [exact Hdep'|]. split.
      { apply (evo_keep_val a W mem mem' (ea_q a + 24) 8%nat _ HK); [clear - Hqlo CR1; lia | clear - Hqhi; lia
        | intros y Hy; unfold evo_W4; clear - Hy HSsp Hsq; intros [H|[H|[H|H]]]; lia | exact C24]. }
      exact Hdl'.
    * (* the text, the scratch, the tree, the save area and the frame's flag word *)
      pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlenb & _ & _ & _ & _ & _ & _ & _ & _ &
        Htree0 & _).
      pose proof Hsrc as (Hga & Hx0lo & Hx0hi & Hamr & Hra & Hhull).
      pose proof Hwd as (Hscr0 & Hshi & Hsamr & Hsw & Hsra & Hshull).
      assert (SHLOW : forall y n0, 0 <= y -> y + n0 <= 2 ^ 47 -> 0 < n0 ->
        forall s0, shadow_addr y / 8 * 8 <= s0 < shadow_addr (y + n0 - 1) / 8 * 8 + 8 ->
        0 <= s0 /\ s0 < alloc_ceiling + 8).
      { intros y n0 Hy0 Hyn Hn0 s0 Hs0. unfold shadow_addr, SHADOW_OFF in Hs0.
        pose proof (Z.div_pos y 8 ltac:(clear - Hy0; lia) ltac:(lia)) as D1.
        assert (D3 : (y + n0 - 1) / 8 <= 17592186044416)
          by (apply Z.div_le_upper_bound; [lia | clear - Hy0 Hn0 Hyn; lia]).
        pose proof (Z.div_mod (2147450880 + y / 8) 8 ltac:(lia)) as E1.
        pose proof (Z.mod_pos_bound (2147450880 + y / 8) 8 ltac:(lia)) as M1.
        pose proof (Z.div_mod (2147450880 + (y + n0 - 1) / 8) 8 ltac:(lia)) as E2.
        pose proof (Z.mod_pos_bound (2147450880 + (y + n0 - 1) / 8) 8 ltac:(lia)) as M2.
        clear - Hs0 D1 D3 E1 M1 E2 M2 Hyn Hy0 Hn0 CR1. lia. }
      assert (SHA : forall y n0, 0 <= y -> y + n0 <= 2 ^ 47 ->
        forall x0, y <= x0 < y + n0 -> 0 <= shadow_of_addr SHADOW_OFF x0 /\ shadow_of_addr SHADOW_OFF x0 < alloc_ceiling + 8).
      { intros y n0 Hy0 Hyn x0 Hx0. unfold shadow_of_addr, SHADOW_OFF.
        pose proof (Z.div_pos x0 8 ltac:(clear - Hy0 Hx0; lia) ltac:(lia)) as D1.
        assert (D2 : x0 / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia | clear - Hx0 Hy0 Hyn; lia]).
        clear - D1 D2 Hx0 Hyn Hy0 CR1. lia. }
      split.
      { (* the text *)
        split; [|split; [exact Hx0lo | split; [exact Hx0hi | split; [exact Hamr | split]]]].
        - intros j Hj. destruct (Hga j Hj) as [Hv Hb]. split; [|exact Hb].
          apply (KEEPV _ 1%nat); [clear - Hx0lo; lia
            | apply inj_lt in Hj; cbn [Z.of_nat]; clear - Hx0hi Hj Hx0lo CR1 CR2; lia | exact Hv].
        - apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem') SHADOW_OFF (ea_x0 a) (Z.of_nat (length (ea_x a)))); [|exact Hra].
          intros y Hy. destruct (SHA (ea_x0 a) (Z.of_nat (length (ea_x a))) ltac:(clear - Hx0lo; lia)
            ltac:(clear - Hx0hi CR1; lia) y Hy) as [S1' S2']. exact (KEEPA _ S1' S2').
        - intros Hn s0 Hs0. rewrite KEEPA; [apply Hhull; [exact Hn | exact Hs0] | |];
          destruct (SHLOW (ea_x0 a) (Z.of_nat (length (ea_x a))) ltac:(clear - Hx0lo; lia)
            ltac:(clear - Hx0hi CR1; lia) Hn s0 Hs0) as [T1 T2]; [exact T1 | exact T2]. }
      split.
      { (* the scratch *)
        split; [exact Hscr0|]. split; [exact Hshi|]. split; [exact Hsamr|]. split.
        - intros z Hz. destruct (Hsw z Hz) as (Hw & Ho & Hst). split; [|split; [exact Ho | exact Hst]].
          exact (writable_at_grows SEGS _ _ _ HGR Hw).
        - split.
          + apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem') SHADOW_OFF (ea_scr a) (ea_len a + 1)); [|exact Hsra].
            intros y Hy. destruct (SHA (ea_scr a) (ea_len a + 1) ltac:(clear - Hscr0; lia)
              ltac:(clear - Hshi CR1; lia) y Hy) as [S1' S2']. exact (KEEPA _ S1' S2').
          + intros Hn s0 Hs0'. rewrite KEEPA; [apply Hshull; [exact Hn | exact Hs0'] | |];
            destruct (SHLOW (ea_scr a) (ea_len a + 1) ltac:(clear - Hscr0; lia)
              ltac:(clear - Hshi CR1; lia) Hn s0 Hs0') as [T1 T2]; [exact T1 | exact T2]. }
      split.
      { (* the tree *)
        destruct Htree0 as [Hv0 | (_ & _ & Hfoot)]; [left; exact Hv0|].
        destruct HT as [HT | (Hnode & Hhome & Hra56 & Hhull56)]; [left; exact HT | right].
        assert (HVB : 0 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47).
        { destruct Hhome as [(b & m0 & Hin & Hb & Hm) | [(cid & pos & Hin & Hb & Hm) | (Hsp & Hhi')]].
          - pose proof HLED as (_ & _ & HF & _).
            pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
            destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
            pose proof (@cf_head_nonneg cp) as Hch.
            assert (Hrq : m0 + cf_head <= req_size (m0 + cf_head)).
            { unfold req_size. destruct (Z.eqb_spec (m0 + cf_head) 0) as [He|He]; clear - Hm0 Hch He; lia. }
            clear - Hb Hm Hm0 H4096 Hc Hrq Hch CR1. lia.
          - destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [_ HFr].
            pose proof (proj1 (Forall_forall _ _) HFr _ Hin) as (H4096 & Hc). cbn [fst snd] in H4096, Hc.
            clear - Hb Hm H4096 Hc CR1. lia.
          - rewrite Hhi_eq in Hhi'. clear - Hsp Hhi' HSPLO Hhi47 CR1. unfold ea_sp0 in *. lia. }
        split; [|split; [exact Hhome|split]].
        - apply (PRH_Reader.pj_nodeR_frame SEGS (ea_t a) _ _ (prh_lin (ea_Lam a)) _ _ Hnode).
          intros x Hx.
          pose proof (evo_foot_rng ly S Hp W mem md _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hnode (proj1 HVB) (proj2 HVB) x Hx) as Hxr.
          split; [|intros Hw; exact (writable_at_grows SEGS _ _ _ HGR Hw)].
          apply (evo_keep_mbyte a W mem mem' x HK); [clear - Hxr; lia|].
          destruct (Hfoot x Hx) as (F1 & F2 & F3 & F4). unfold evo_W4.
          intros [H|[H|[H|H]]]; [apply F2; clear - H; lia | apply F2; clear - H; lia | apply F2; clear - H; lia |].
          apply F3. unfold ea_sp0 in *. clear - H HS287 HSsp HSTKa. lia.
        - apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem') SHADOW_OFF (ea_v a) 56); [|exact Hra56].
          intros y Hy.
          destruct (SHA (ea_v a) 56 ltac:(clear - HVB; lia) ltac:(clear - HVB; lia) y Hy) as [S1' S2'].
          exact (KEEPA _ S1' S2').
        - intros s0 Hs0. rewrite KEEPA; [apply Hhull56; exact Hs0 | |];
          destruct (SHLOW (ea_v a) 56 ltac:(clear - HVB; lia) ltac:(clear - HVB; lia) ltac:(lia) s0 Hs0) as [T1 T2];
          [exact T1 | exact T2]. }
      split.
      { (* the prologue's save area *)
        unfold ev_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *.
        intros [off r] Hin. cbn [fst snd] in *.
        assert (Hoff : 152 <= off <= 248).
        { clear - Hin. unfold EV_SAVED in Hin. cbn [In] in Hin.
          repeat (destruct Hin as [E|Hin]; [injection E as E1 E2; subst off; lia|]). destruct Hin. }
        apply (KEEPS _ 8%nat);
          [unfold ea_SA, ea_sp0 in *; clear - Hoff; lia
          | unfold ea_SA, ea_sp0 in *; cbn [Z.of_nat]; clear - Hoff; lia
          | exact (HSAV (off, r) Hin)]. }
      split; [|split; [exact HRL | split; [exact HRP | exact HMN']]].
      { (* the frame's flag word: the fake frame is in the allocator's frame area, below the ceiling *)
        assert (HFR : In (1, ea_pos a) (frames S)).
        { pose proof HJ' as (_ & _ & _ & _ & _ & Hfrm & _). rewrite Hfrm. left. reflexivity. }
        destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem' md' (proj1 HJ')) as [_ HFrames].
        pose proof (proj1 (Forall_forall _ _) HFrames _ HFR) as (H4096 & Hc). cbn [fst snd] in H4096, Hc.
        pose proof HPRE as (HPRE0' & _). pose proof (proj1 (proj1 HPRE0')) as HAR0.
        pose proof HJ0 as (_ & HLE1 & _).
        destruct (alx_layout SEGS B ARx LAWS (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) ly HAR0 HLE1)
          as (_ & Hfr_eq & _).
        assert (HFRB : 4096 <= ea_fr a /\ ea_fr a + fs_frame_bytes 1 <= alloc_ceiling).
        { unfold ea_fr. rewrite <- (Hfr_eq 1 (ea_pos a)). split; [exact H4096 | exact Hc]. }
        unfold rdword in HFLAG |- *.
        rewrite !KEEPA by (clear - HFRB CR1; pose proof (fs_frame_bytes_pos 1) as Hfb; lia). exact HFLAG. }
Qed.

(* ======== the tail of the piece: from 0x83768 to P_STEP (item 0) or P_END (the empty container) ======== *)

(* reading a cell back out of a symbolic state: the CVal chunk at offset off of region i *)
Definition evo_ck (rs : smem) (i : nat) (off : Z) : option (option nat * N * sv) :=
  match nth_error rs i with
  | Some r =>
      match find (fun c => Z.eqb (YP09.c_off c) off) (YP09.r_chunks r) with
      | Some (YP09.mkChunk _ (CVal w e)) => Some (YP09.r_base r, w, e)
      | _ => None
      end
  | None => None
  end.
Lemma evo_val_ck : forall fxc E ss (ms : machine_state) i off b (w : N) e,
  st_ok_pi (fx := fxc) SEGS VAL E ss ms -> evo_ck (ss_mem ss) i off = Some (b, w, e) ->
  forall v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (ms_mem ms) (base_val E b + off) (N.to_nat w) v.
Proof.
intros fxc E ss ms i off b w e HS Hck v He Hv Hw. unfold evo_ck in Hck.
destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate Hck].
destruct (find (fun c => Z.eqb (YP09.c_off c) off) (YP09.r_chunks r)) as [[off' cv]|] eqn:Hf; [|discriminate Hck].
destruct cv as [w' e'| | |]; try discriminate Hck. injection Hck as <- <- <-.
apply find_some in Hf as (Hin & Hoff). cbn [YP09.c_off] in Hoff. apply Z.eqb_eq in Hoff. subst off'.
exact (evo_region_val E (ms_mem ms) (ss_mem (abs_ss VAL ss)) r off w' e' v (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS)
  (nth_error_In _ _ Hi) Hin He Hv Hw).
Qed.
(* the chunk at offset off of region i of the state HS describes, as a val_mem with the value still to be given *)
Ltac evo_cv HS i off H :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss ?ms =>
    let ck := eval vm_compute in (evo_ck (ss_mem ss) i off) in
    lazymatch ck with
    | Some (?b, ?w, ?e) => pose proof (evo_val_ck _ E ss ms i off b w e HS ltac:(vm_compute; reflexivity)) as H
    end
  end.
(* an atom plus a constant, through the fresh atoms of a run (each ew E n = w64 v in the context is used) *)
Ltac evo_den :=
  cbn [sv_denot ew ewset Nat.eqb];
  repeat match goal with H : ew ?E0 ?n = w64 _ |- context [ew ?E0 ?n] => rewrite H end;
  unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia.
(* the value range of a w-byte cell, with the bound computed *)
Ltac evo_rng :=
  lazymatch goal with |- 0 <= _ < 2 ^ (8 * Z.of_N ?w) =>
    let n := eval vm_compute in (2 ^ (8 * Z.of_N w)) in change (2 ^ (8 * Z.of_N w)) with n; lia end.
(* a cell of the state after a run: region i, offset off; U rewrites the region's base *)
Ltac evo_chunk HS i off U :=
  let Hc := fresh "Hc" in evo_cv HS i off Hc;
  cbn [base_val ms_mem restrict ew ewset Nat.eqb] in Hc; rewrite U in Hc;
  apply Hc; clear Hc; [evo_den | evo_rng | cbv [Z.of_N]; lia].

(* the write windows of a stretch's regions are inside the four windows evo_W4 *)
Lemma evo_wr_W4 : forall a (E : env) (rs : smem) z,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/
    (forall y, base_val E (YP09.r_base r) + YP09.r_wlo r <= y < base_val E (YP09.r_base r) + YP09.r_whi r ->
       evo_W4 a y)) rs ->
  in_wrange E rs z -> evo_W4 a z.
Proof.
intros a E rs z HF (r & Hin & Hz). destruct (proj1 (Forall_forall _ _) HF r Hin) as [Hro|Hw]; [lia | exact (Hw z Hz)].
Qed.
(* ... and the four windows are inside the journal's stack window [sp0 + d - (STK + d), sp0 + d) *)
Lemma evo_W4_stk : forall a ly S Hp W mem md k p dep dl z,
  EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl -> evo_W4 a z ->
  (ea_sp0 a + ea_d a) - (ea_STK (PI := prh_img_A) a + ea_d a) <= z < ea_sp0 a + ea_d a.
Proof.
intros a ly S Hp W mem md k p dep dl z HPRE HMID HW.
pose proof (evo_bnd a ly S Hp W mem md k p dep dl HPRE HMID) as
  (_ & _ & Hsq & Hqd & _ & _ & _ & _ & HSsp & _ & HS287 & _).
pose proof (evo_stk (ea_n a)) as HSTK.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; exact HSTK).
unfold evo_W4 in HW. destruct HW as [H|[H|[H|H]]]; lia.
Qed.
(* the fake frame is in the allocator's frame area *)
Lemma evo_fr_bnd : forall a ly S Hp W mem md k p dep dl,
  EV_PRE a -> EV_MID a ly S Hp W mem md k p dep dl -> 4096 <= ea_fr a /\ ea_fr a + fs_frame_bytes 1 <= alloc_ceiling.
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID.
pose proof HMID as (HJ & _).
assert (HFR : In (1, ea_pos a) (frames S)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrm & _). rewrite Hfrm. left. reflexivity. }
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md (proj1 HJ)) as [_ HFrames].
pose proof (proj1 (Forall_forall _ _) HFrames _ HFR) as (H4096 & Hc). cbn [fst snd] in H4096, Hc.
pose proof HPRE as (HPRE0' & _). pose proof (proj1 (proj1 HPRE0')) as HAR0.
pose proof HJ as (_ & HLE1 & _).
destruct (alx_layout SEGS B ARx LAWS (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) ly HAR0 HLE1)
  as (_ & Hfr_eq & _).
unfold ea_fr. rewrite <- (Hfr_eq 1 (ea_pos a)). split; [exact H4096 | exact Hc].
Qed.

(* the tail cut's write windows *)
Lemma evo_T_W4 : forall a (E : env) z,
  bv_unsigned (ew E 19) = ea_q a -> bv_unsigned (ew E 9) = ea_S1 a ->
  in_wrange E (evo_Tin ++ [evo_Tf; evo_Ttext]) z \/ in_wrange E (evo_Tin ++ [evo_Tf]) z -> evo_W4 a z.
Proof.
intros a E z U19 U9 [Hw|Hw];
  [apply (evo_wr_W4 a E (evo_Tin ++ [evo_Tf; evo_Ttext]) z); [|exact Hw]
  |apply (evo_wr_W4 a E (evo_Tin ++ [evo_Tf]) z); [|exact Hw]];
  unfold evo_Tin, evo_Tp, evo_Re, evo_Td, evo_Rs, evo_Tl, evo_Tf, evo_Ttext; cbn [app];
  repeat apply Forall_cons; try apply Forall_nil;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U19, ?U9;
  first [left; lia | right; intros y Hy; unfold evo_W4; lia].
Qed.

(* a byte remains at the tail cut: the closer test, its outcome c a condition of the state *)
Definition evo_ssTc (c : branch_cond) : sstate :=
  mkSS (EVO_PC EVO_AFT) (sr_set sr_atoms 26%bv EVO_S10)
    (evo_Tin ++ [evo_Tf; evo_Ttext]) None
    (mkFacts evo_Tatoms [mkAC c (SOff 37 0) (SOff 40 0); mkAC BC_LTU (SOff 36 0) (SOff 12 0)] []).
(* the registers the tail does not write on its way to P_STEP / P_END (s10 is the state's EVO_S10, see evo_s10) *)
Definition EVO_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25]%bv.
(* s10 after a run whose state seats it as EVO_S10 and never writes it: still the shadow of q *)
Ltac evo_s10 HS q E19 E24 H :=
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 26%bv HS) as H;
  change (sr_get _ 26%bv) with EVO_S10 in H; cbn [ms_regs restrict] in H;
  rewrite (evo_S10_den _ q) in H; [| cbn [ew ewset Nat.eqb]; exact E19 | lia | cbn [ew ewset Nat.eqb]; exact E24].

(* what every cut of the piece between 0x836d4 and 0x83768 carries: the invariant at in->p = x0 + i, in->depth =
   dep + 1, in->differs = dln; the ev_regs set; a2 = in->end, s4, s5 the opener, s6 the frame, s7 = v'; the three
   spills piece 6 has written (q + 16, its shadow, the closer); the bounds; the differs bookkeeping *)
Definition evo_core (a : ev_act) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (St : astate) (Hp : list Z) (k : Z) (o : bool) (i : nat) (dln : Z) : Prop :=
  EV_MID a ly St Hp W mem md k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dln /\
  ev_regs (PA := PI_prog_A) a regs /\
  getr regs 12 = w64 (ea_x0 a + ea_len a) /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\
  getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 (ea_fr a) /\
  getr regs 23 = w64 (ev_v' (ea_v a) o (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 48) 8 (ea_q a + 16) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 56) 8 (shadow_addr (ea_q a + 16)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 64) 8 (PjGrammar.closer o) /\
  (dln = 0 \/ dln = 1) /\ (i <= length (ea_x a))%nat /\ 0 <= ea_dep a <= 31 /\
  0 <= ev_v' (ea_v a) o (ea_t a) <= EVO_TOP /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) [] dln.

Lemma evo_tail : forall a fxc W regs mem md ly St Hp k (o : bool) (iw : nat) dln,
EV_PRE a -> @ev_fx fx fxc -> evo_core a W regs mem md ly St Hp k o iw dln ->
prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
  match skipn iw (ea_x a) with
  | [] => None
  | c :: r => if c =? PjGrammar.closer o then Some (PjGrammar.mk o [], r)
              else ev_L (S (Z.to_nat (ea_dep a))) o 0 0 [] (c :: r)
  end ->
SRr SEGS W (ev_cfg (PA := PI_prog_A) fxc regs EVO_AFT mem md) (evo_post a fxc o).
Proof.
intros a fxc W regs mem md ly St Hp k o iw dln HPRE HFX HC HMODEL.
destruct HC as (HMID & HREG & H12 & H20 & H21 & H22 & H23v & H48 & H56 & H64 & Hdln & Hiw & Hdep & Hv' & Hdl).
pose proof (evo_bnd a ly St Hp W mem md k _ _ _ HPRE HMID) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & HQA).
pose proof (evo_Tstate a ly St Hp W mem md k iw dln o regs HPRE HMID HREG H12 H23v H48 H56 H64 Hdln Hiw Hv')
  as (HRG & HTX & HAT & HRO).
pose proof HMID as (HJ & _ & _ & _ & _ & Hcur & Hsrc & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof Hsrc as (Hga & Hx0lo & Hx0hi & _ & Hra & _).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
pose proof HREG as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs3 & Rs8 & Rs9 & Rs10).
assert (Hiwlen : Z.of_nat iw <= Z.of_nat (length (ea_x a))) by (apply inj_le; exact Hiw).
unfold ea_len in Hx0hi, H12.
unfold EVO_CEIL in Hqlo, HSlo. unfold EVO_TOP in Hqhi, HShi, Hv'.
set (byte := nth iw (ea_x a) 0) in *.
set (E := evo_ET a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, evo_ET; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (evo_ETx a (Z.of_nat iw) byte (PjGrammar.closer o) dln)) E)
  by (unfold E, evo_ET; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EQ19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 19 19%bv ltac:(lia) eq_refl); exact Rs3).
assert (EQ9 : ew E 9 = w64 (ea_S1 a))
  by (unfold E; rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 9 9%bv ltac:(lia) eq_refl); exact Rs1).
assert (EQ12 : ew E 12 = w64 (ea_x0 a + Z.of_nat (length (ea_x a))))
  by (unfold E; rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 12 12%bv ltac:(lia) eq_refl); exact H12).
assert (EQ36 : ew E 36 = w64 (ea_x0 a + Z.of_nat iw))
  by (unfold E; exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 4%nat ltac:(lia))).
(* the regions do not overlap: `in` field by field, the spill area below sp0, the text below the ceiling *)
pose proof (evo_sp_lo a ly St Hp W mem md k _ _ _ HPRE HMID) as (HSPLO & HSPHI).
assert (HPD : pairwise_disjoint E (evo_Tin ++ [evo_Tf; evo_Ttext])).
{ unfold evo_Tin, evo_Tp, evo_Re, evo_Td, evo_Rs, evo_Tl, evo_Tf, evo_Ttext. cbn [app pairwise_disjoint all_disjoint].
  unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EQ19, EQ9, EQ36. unfold w64. rewrite !unsigned_lit_small by lia.
  repeat split; try exact I; first [left; lia | right; lia]. }
assert (HPD2 : pairwise_disjoint E (evo_Tin ++ [evo_Tf])).
{ unfold evo_Tin, evo_Tp, evo_Re, evo_Td, evo_Rs, evo_Tl, evo_Tf. cbn [app pairwise_disjoint all_disjoint].
  unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EQ19, EQ9. unfold w64. rewrite !unsigned_lit_small by lia.
  repeat split; try exact I; first [left; lia | right; lia]. }
(* the rest of the environment, and the bounds the cells' values need *)
assert (EQ22 : ew E 22 = w64 (ea_fr a))
  by (unfold E; rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 22 22%bv ltac:(lia) eq_refl); exact H22).
assert (EQ23 : ew E 23 = w64 (ev_v' (ea_v a) o (ea_t a)))
  by (unfold E; rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 23 23%bv ltac:(lia) eq_refl); exact H23v).
assert (EQ24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (evo_ETreg a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 24 24%bv ltac:(lia) eq_refl); exact Rs8).
assert (EQ32 : ew E 32 = w64 (ea_dep a)) by (unfold E; exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 0%nat ltac:(lia))).
assert (EQ37 : ew E 37 = w64 byte) by (unfold E; exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 5%nat ltac:(lia))).
assert (EQ40 : ew E 40 = w64 (PjGrammar.closer o)) by (unfold E; exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 8%nat ltac:(lia))).
assert (EQ41 : ew E 41 = w64 dln) by (unfold E; exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 9%nat ltac:(lia))).
assert (EQ43 : ew E 43 = w64 (shadow_addr (ea_q a + 16)))
  by (unfold E; exact (evo_ETex a regs (Z.of_nat iw) byte (PjGrammar.closer o) dln 11%nat ltac:(lia))).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite EQ19; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite EQ9; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EVO_Bx = SHADOW_OFF) by (unfold EVO_Bx; apply (U_atom E 24 SHADOW_OFF EQ24); unfold SHADOW_OFF; lia).
pose proof (evo_fr_bnd a ly St Hp W mem md k _ _ _ HPRE HMID) as (HFR1 & HFR2).
pose proof (fs_frame_bytes_pos 1) as HFB.
assert (Hbyte : 0 <= byte < 256).
{ destruct (Nat.lt_ge_cases iw (length (ea_x a))) as [Hlt|Hge].
  - exact (proj2 (Hga iw Hlt)).
  - subst byte. rewrite nth_overflow by exact Hge. lia. }
assert (Hclo : 93 <= PjGrammar.closer o <= 125) by (unfold PjGrammar.closer; destruct o; lia).
assert (HSH : 0 <= shadow_addr (ea_q a + 16) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_pos (ea_q a + 16) 8 ltac:(lia) ltac:(lia)) as D1.
  assert (D2 : (ea_q a + 16) / 8 <= ea_q a + 16) by (apply Z.div_le_upper_bound; lia).
  lia. }
assert (HSOK : sh_ok SEGS EVO_Bx evo_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, evo_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, (U_atom E 19 (ea_q a) EQ19) by lia. split.
  - rewrite <- aview_rd_of, Z.add_0_r. exact HQA.
  - intros z Hz. rewrite Z.min_l, Z.max_r in Hz by lia.
    unfold SHADOW_OFF. lia. }
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B (prh_pst (PI := prh_img_A)) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (@ev_pc rc A_prog_listing PI_prog_A EVO_AFT) with (BASE + EVO_PC EVO_AFT) by (vm_compute; reflexivity).
(* the frame of every run of the tail: it writes only the four windows *)
assert (HKW : forall (m' : word -> option BvBase.byte),
  (frame_of E (evo_Tin ++ [evo_Tf]) (mrestrict (w_H W) mem) (mrestrict (w_H W) m') \/
   frame_of E (evo_Tin ++ [evo_Tf; evo_Ttext]) (mrestrict (w_H W) mem) (mrestrict (w_H W) m')) ->
  forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) mem x).
{ intros m' [HF'|HF'] x Hx; apply HF'; intros Hw; apply Hx; apply (evo_T_W4 a E _ U19 U9); [right|left]; exact Hw. }
destruct (Nat.eq_dec iw (length (ea_x a))) as [Hend|Hlt].
- (* (1) the end of the text: 0x83768 -> P_STEP 0x837ec with no item read (n = 0, cap = 0) *)
  assert (HS : st_ok_pi (fx := fxc) SEGS VAL E evo_ssTe
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVO_PC EVO_AFT)) mem (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold evo_ssTe. apply pa_entry_st_ok_full;
      [exact HRO | vm_compute; reflexivity | exact HRG | exact HPD2 |].
    split; [exact HAT|]. split; [|exact I]. split; [|exact I].
    unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_geu_U, (U_atom E 36 _ EQ36), (U_atom E 12 _ EQ12) by lia.
    apply negb_true_iff, Z.ltb_ge. rewrite Hend. lia. }
  paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EV_STEP).
  + intros z Hz. left. apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID).
    apply (evo_T_W4 a E z U19 U9). right. exact Hz.
  + pmkst HS.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs (evo_ETx a (Z.of_nat iw) byte (PjGrammar.closer o) dln) EVO_KEPT HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (11%bv : bv 5) Q11. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
    assert (Hp' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat iw)).
    { replace (ea_q a) with (ea_q a + 0) by lia. evo_chunk HS 0%nat 0 U19. }
    assert (Hd' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 16) 4 (ea_dep a + 1)).
    { evo_chunk HS 2%nat 16 U19. }
    assert (Hl' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 32) 4 dln).
    { evo_chunk HS 4%nat 32 U19. }
    pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ
      (HKW (ms_mem ms) (or_introl HFr)) HG Hp' Hd' Hl' HMN) as HMID'.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
      replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_STEP) by (vm_compute; reflexivity);
      apply SRr_ret; unfold evo_post; right; exists fxc, r, m, d, ly, St, Hp, k, iw, dln end.
    split; [exact HFX|]. left. split; [reflexivity|].
    unfold ev_at_step. cbv zeta.
    split; [exact HMID'|].
    evo_s10 HS (ea_q a) EQ19 EQ24 Q26.
    split; [unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]|].
    split; [rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20|].
    split; [rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21|].
    split; [rewrite Q22; reflexivity|].
    split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23v|].
    split; [rewrite Q27; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split.
    { unfold ev_spills. cbv zeta. rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
      repeat split; lazymatch goal with |- val_mem _ _ (ea_S1 a + ?off) _ _ => evo_chunk HS 5%nat off U9 end. }
    split; [evo_chunk HS 5%nat 104 U9|].
    split; [exact Hdep|]. split; [exact Hiw|]. split; [reflexivity|].
    split; [|split; [exact Hdl | apply Nat.le_0_l]].
    rewrite HMODEL. assert (Hnil : skipn iw (ea_x a) = []) by (apply skipn_all2; lia). rewrite Hnil.
    unfold ev_L. symmetry. exact (ev_jrl_nil _ _ _ _ _ _).
- (* a byte remains at x0 + iw: its shadow, then the closer test *)
  assert (Hlt' : (iw < length (ea_x a))%nat) by lia.
  assert (Hsk : skipn iw (ea_x a) = byte :: skipn (S iw) (ea_x a)) by (exact (skipn_nth (ea_x a) iw 0 Hlt')).
  rewrite Hsk in HMODEL.
  assert (HSc : forall c, branch_taken c (w64 byte) (w64 (PjGrammar.closer o)) = true ->
    st_ok_pi (fx := fxc) SEGS VAL E (evo_ssTc c)
      (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVO_PC EVO_AFT)) mem (YK11.seg_rom SEGS)))).
  { intros c Hc. rewrite restrict_mkst_fx. unfold evo_ssTc. apply pa_entry_st_ok_full;
      [exact HRO | vm_compute; reflexivity | | exact HPD |].
    - apply Forall_app. apply Forall_app in HRG. destruct HRG as [HRG1 HRG2]. split; [exact HRG1|].
      apply Forall_cons; [exact (Forall_inv HRG2)|]. apply Forall_cons; [exact (HTX Hlt')|apply Forall_nil].
    - split; [exact HAT|]. split; [|exact I]. split; [|split; [|exact I]].
      + unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot]. rewrite EQ37, EQ40, !Z.add_0_r. unfold w64 in *.
        rewrite !Z_to_bv_bv_unsigned. exact Hc.
      + unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite branch_ltu_U, (U_atom E 36 _ EQ36), (U_atom E 12 _ EQ12) by lia.
        apply Z.ltb_lt. lia. }
  destruct (Z.eq_dec byte (PjGrammar.closer o)) as [Heq|Hne].
  + (* (2) the closer: in->p := x0 + iw + 1, then P_END 0x83cec with the empty container *)
    pose proof (HSc BC_EQ ltac:(cbn [branch_taken]; rewrite Heq; unfold bv_eqb; apply Z.eqb_refl)) as HS.
    paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EV_END).
    * cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom E 36 (ea_x0 a + Z.of_nat iw) EQ36) by lia.
      apply (range_addressable_sub _ _ (ea_x0 a) (Z.of_nat (length (ea_x a)))); [exact Hra | lia | lia].
    * intros z Hz. left. apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID).
      apply (evo_T_W4 a E z U19 U9). left. exact Hz.
    * pmkst HS.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs (evo_ETx a (Z.of_nat iw) byte (PjGrammar.closer o) dln)
        (22%bv :: EVO_KEPT) HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (11%bv : bv 5) Q11.
      assert (Hp' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat (S iw))).
      { replace (ea_q a) with (ea_q a + 0) by lia. rewrite Nat2Z.inj_succ. evo_chunk HS 0%nat 0 U19. }
      assert (Hd' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 16) 4 (ea_dep a + 1)).
      { evo_chunk HS 2%nat 16 U19. }
      assert (Hl' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 32) 4 dln).
      { evo_chunk HS 4%nat 32 U19. }
      pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ
        (HKW (ms_mem ms) (or_intror HFr)) HG Hp' Hd' Hl' HMN) as HMID'.
      lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
        replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_END) by (vm_compute; reflexivity);
        apply SRr_ret; unfold evo_post; right; exists fxc, r, m, d, ly, St, Hp, k, (S iw), dln end.
      split; [exact HFX|]. right. split; [reflexivity|].
      unfold ev_at_end. cbv zeta.
      split; [exact HMID'|].
      evo_s10 HS (ea_q a) EQ19 EQ24 Q26.
      split; [unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]|].
      split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact H22|].
      split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23v|].
      split; [rewrite Q11; reflexivity|].
      split; [evo_chunk HS 5%nat 48 U9|].
      split; [evo_chunk HS 5%nat 56 U9|].
      split; [exact Hdep|]. split; [lia|].
      split; [|exact Hdl].
      rewrite HMODEL. cbv beta iota. rewrite Heq, Z.eqb_refl. reflexivity.
  + (* (3) another byte: the first item starts here; P_STEP 0x837ec with n = 0, cap = 0 *)
    pose proof (HSc BC_NE ltac:(cbn [branch_taken]; unfold bv_eqb, w64; rewrite !unsigned_lit_small by lia;
      apply negb_true_iff, Z.eqb_neq; exact Hne)) as HS.
    paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EV_STEP).
    * cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom E 36 (ea_x0 a + Z.of_nat iw) EQ36) by lia.
      apply (range_addressable_sub _ _ (ea_x0 a) (Z.of_nat (length (ea_x a)))); [exact Hra | lia | lia].
    * intros z Hz. left. apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID).
      apply (evo_T_W4 a E z U19 U9). left. exact Hz.
    * pmkst HS.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs (evo_ETx a (Z.of_nat iw) byte (PjGrammar.closer o) dln) EVO_KEPT HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (11%bv : bv 5) Q11. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
      assert (Hp' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat iw)).
      { replace (ea_q a) with (ea_q a + 0) by lia. evo_chunk HS 0%nat 0 U19. }
      assert (Hd' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 16) 4 (ea_dep a + 1)).
      { evo_chunk HS 2%nat 16 U19. }
      assert (Hl' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 32) 4 dln).
      { evo_chunk HS 4%nat 32 U19. }
      pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ
        (HKW (ms_mem ms) (or_intror HFr)) HG Hp' Hd' Hl' HMN) as HMID'.
      lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
        replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_STEP) by (vm_compute; reflexivity);
        apply SRr_ret; unfold evo_post; right; exists fxc, r, m, d, ly, St, Hp, k, iw, dln end.
      split; [exact HFX|]. left. split; [reflexivity|].
      unfold ev_at_step. cbv zeta.
      split; [exact HMID'|].
      evo_s10 HS (ea_q a) EQ19 EQ24 Q26.
      split; [unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]|].
      split; [rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20|].
      split; [rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21|].
      split; [rewrite Q22; reflexivity|].
      split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23v|].
      split; [rewrite Q27; reflexivity|].
      split; [rewrite Q11; reflexivity|].
      split.
      { unfold ev_spills. cbv zeta. rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
        repeat split; lazymatch goal with |- val_mem _ _ (ea_S1 a + ?off) _ _ => evo_chunk HS 5%nat off U9 end. }
      split; [evo_chunk HS 5%nat 104 U9|].
      split; [exact Hdep|]. split; [exact Hiw|]. split; [reflexivity|].
      split; [|split; [exact Hdl | apply Nat.le_0_l]].
      rewrite HMODEL, Hsk. cbv beta iota. rewrite (proj2 (Z.eqb_neq _ _) Hne). reflexivity.
Qed.

(* ======== the blanks after the opener: the inlined ex_ws loop at 0x836fc (0x836fc-0x83738, exit 0x83768). Its own
   lemma (WalkS8a's shared loop of S8aWs.v has other registers): a0 = a3 = in->p = x0 + i, a2 = in->end, a1 = 32,
   a4 = the mask, s10 = the shadow of q; it writes in->p (8 bytes at q) and a0, a3, a5 (and a6, a fresh value of the
   text byte's shadow check) only ======== *)
Definition evo_ssW : sstate :=
  mkSS (EVO_PC EVO_WS)
    (sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 13 0)) 11%bv (SLit 32)) 14%bv (SLit evo_WSM)) 26%bv EVO_S10)
    [YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 13 0))];
     YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]]
    None
    (mkFacts [(12%nat, mkAF 4096 EVO_TOP 0); (13%nat, mkAF 4096 EVO_TOP 0); (19%nat, mkAF EVO_CEIL EVO_TOP 3);
              (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] []).

(* the mask test of the loop, as the engine computes it (COPIED from WalkS8a's S8aWs.v ws_mask_bit, same words) *)
Lemma evo_mask_bit : forall bi, 0 <= bi <= 32 ->
  (zcanon (Z.land (zcanon (Z.shiftr (zcanon 4294977024) (Z.land bi 63))) (zcanon 1)) =? zcanon 0) = negb (PjGrammar.ws bi).
Proof.
intros bi Hb.
assert (H : forallb (fun k => Bool.eqb ((zcanon (Z.land (zcanon (Z.shiftr (zcanon 4294977024) (Z.land (Z.of_nat k) 63)))
  (zcanon 1)) =? zcanon 0)) (negb (PjGrammar.ws (Z.of_nat k)))) (seq 0 33) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H.
specialize (H (Z.to_nat bi) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Bool.eqb_prop in H. exact H.
Qed.
Lemma evo_ws_big : forall b, 32 < b -> PjGrammar.ws b = false.
Proof. intros b Hb. unfold PjGrammar.ws. repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

(* the registers the loop's state keeps as atoms (a1, a4 are literals, s10 is EVO_S10; a0, a3, a5, a6 are written) *)
Definition EVO_WKEPT : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Lemma evo_wreg_cases : forall r : bv 5, r <> 10%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv ->
  r = 0%bv \/ r = 11%bv \/ r = 14%bv \/ r = 26%bv \/ In r EVO_WKEPT.
Proof.
intros r H10 H13 H15 H16. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [contradiction | left; reflexivity | right; left; reflexivity
  | right; right; left; reflexivity | right; right; right; left; reflexivity
  | right; right; right; right; cbv; tauto] |]).
destruct Hin.
Qed.

(* a write confined to in->p's 8 bytes keeps every other byte *)
Lemma evo_q_mbyte : forall (m m' : word -> option BvBase.byte) q z,
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> m' x = m x) -> 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 8) ->
  mbyte SEGS m' z = mbyte SEGS m z.
Proof.
intros m m' q z HK Hz Hn. unfold mbyte. rewrite (HK (Z_to_bv 64 z)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma evo_q_aview : forall (H : word -> bool) m m' q z,
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= z < 2 ^ 64 -> ~ (q <= z < q + 8) -> aview SEGS H m' z = aview SEGS H m z.
Proof. intros H m m' q z HK Hz Hn. unfold aview. f_equal. exact (evo_q_mbyte _ _ q z HK Hz Hn). Qed.
Lemma evo_q_val : forall (m m' : word -> option BvBase.byte) q p (n : nat) v,
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> m' x = m x) -> 0 <= p -> p + Z.of_nat n <= 2 ^ 64 ->
  (p + Z.of_nat n <= q \/ q + 8 <= p) -> val_mem SEGS m p n v -> val_mem SEGS m' p n v.
Proof.
intros m m' q p n v HK Hp Hn Hout H j Hj.
assert (Hjz : 0 <= Z.of_nat j < Z.of_nat n) by lia.
rewrite (evo_q_mbyte m m' q (p + Z.of_nat j) HK) by lia. exact (H j Hj).
Qed.
Lemma evo_q_garr8 : forall (m m' : word -> option BvBase.byte) q x0 x,
  (forall z : word, ~ (q <= bv_unsigned z < q + 8) -> m' z = m z) ->
  0 <= x0 -> x0 + Z.of_nat (length x) <= q -> q <= 2 ^ 64 -> garr8 SEGS m x0 x -> garr8 SEGS m' x0 x.
Proof.
intros m m' q x0 x HK H0 Hq Hq64 Hg j Hj. destruct (Hg j Hj) as [V R]. split; [|exact R].
apply (evo_q_val m m' q _ 1 _ HK); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact V].
Qed.
Lemma evo_q_ra : forall (H : word -> bool) m m' q a n,
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a -> a + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 44 <= q ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
intros H m m' q a n HK Ha Hn Hq. apply range_addressable_agree. intros y Hy.
unfold shadow_of_addr. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)) as D1.
assert (D2 : y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply (evo_q_aview H m m' q); [exact HK | unfold SHADOW_OFF; lia | unfold SHADOW_OFF in *; lia].
Qed.

(* a run's write set inside the loop is in->p's 8 bytes (the region at s3; the text byte is read-only) *)
Ltac evo_wnotin U19 Hz :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); apply Hz; vm_compute in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hr; rewrite ?U19 in Hr; lia|]);
  destruct Hin.
Ltac evo_wawr U19 :=
  let z := fresh "z" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros z (r & Hin & Hr); left; vm_compute in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hr; rewrite ?U19 in Hr; lia|]);
  destruct Hin.
(* chain a run's frame and growth onto those from the loop's entry memory m0 *)
Ltac evo_wkeep q U19 m0 KM K GRo GRn :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?mA) (mrestrict _ ?mB) |- _ =>
    assert (K : forall z : word, ~ (q <= bv_unsigned z < q + 8) -> mrestrict Hh mB z = mrestrict Hh m0 z) by
      (let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; rewrite (HFr z); [exact (KM z Hz) | evo_wnotin U19 Hz]);
    clear HFr KM end;
  lazymatch goal with HG : mem_grows (mrestrict ?Hh ?mA) (mrestrict _ ?mB) |- _ =>
    pose proof (mem_grows_trans _ _ _ GRo HG) as GRn; clear HG GRo end;
  try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msn) |- _ =>
    repeat match goal with old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end end;
    try rename msn into ms end.
Ltac evo_wregs_kept HK R11 R14 Q26 H11 H14 H26 :=
  let r := fresh "r" in let h1 := fresh in let h2 := fresh in let h3 := fresh in let h4 := fresh in
  intros r h1 h2 h3 h4; destruct (evo_wreg_cases r h1 h2 h3 h4) as [->|[->|[->|[->|Hin]]]];
  [ rewrite !getr_zero; reflexivity
  | rewrite R11, H11; reflexivity
  | rewrite R14, H14; reflexivity
  | rewrite Q26, H26; reflexivity
  | exact (HK _ Hin) ].

Lemma evo_wsl : forall fxc (k : nat) W (regs : bvmap 5 word) mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk
    (q x0 : Z) (x : list Z) (i : nat),
  k = (length x - i)%nat -> (i < length x)%nat ->
  ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_A)) ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  sp0 - STK <= q -> q + 8 <= sp0 -> EVO_CEIL <= q -> q <= EVO_TOP -> q mod 8 = 0 -> alloc_ceiling <= q ->
  4096 <= x0 -> x0 + Z.of_nat (length x) <= alloc_ceiling ->
  getr regs 10 = w64 (x0 + Z.of_nat i) -> getr regs 13 = w64 (x0 + Z.of_nat i) ->
  getr regs 11 = w64 32 -> getr regs 12 = w64 (x0 + Z.of_nat (length x)) -> getr regs 14 = w64 evo_WSM ->
  getr regs 19 = w64 q -> getr regs 24 = w64 SHADOW_OFF -> getr regs 26 = w64 (shadow_addr q) ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 (x0 + Z.of_nat i) ->
  garr8 SEGS (mrestrict (w_H W) mem) x0 x ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x0 (Z.of_nat (length x)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 40 ->
  (forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (q + o)) -> YAkMemnorm.memnorm SEGS mem ->
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVO_PC EVO_WS)) mem (YK11.seg_rom SEGS)) md)
    (fun W' c' => W' = W /\ exists regs' mem' md' (i' : nat),
       c' = mkCfg (@YK11.mkst fxc regs' (Z_to_bv 64 (BASE + EVO_PC EVO_AFT)) mem' (YK11.seg_rom SEGS)) md' /\
       ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_A)) ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp
         W mem' md' kk /\
       (forall z : word, ~ (q <= bv_unsigned z < q + 8) -> mrestrict (w_H W) mem' z = mrestrict (w_H W) mem z) /\
       mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\ YAkMemnorm.memnorm SEGS mem' /\
       val_mem SEGS (mrestrict (w_H W) mem') q 8 (x0 + Z.of_nat i') /\
       (i <= i' <= length x)%nat /\ skipn i' x = PjGrammar.skip (skipn i x) /\
       (forall r : bv 5, r <> 10%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> getr regs' r = getr regs r)).
Proof.
intros fxc k. induction k as [|k IH]; intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x i
  Hk Hi HJ Hq1 Hq2 Hq3 Hq4 Hq8 Hqc Hx1 Hx2 H10 H13 H11 H12 H14 H19 H24 H26 Hvq Hgx Hrax Hqra Hwq HMN; [lia|].
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
unfold EVO_CEIL, EVO_TOP in Hq3, Hq4.
set (len := Z.of_nat (length x)) in *. assert (Hlen0 : len = Z.of_nat (length x)) by reflexivity. clearbody len.
set (p := x0 + Z.of_nat i) in *. assert (Hp0' : p = x0 + Z.of_nat i) by reflexivity. clearbody p.
set (bi := nth i x 0) in *.
destruct (Hgx i Hi) as [Hvb Hbi].
assert (Hil : Z.of_nat i < len) by lia.
remember (@Eimg _ A_prog_listing PI_prog_A (Ereg regs [w64 bi])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 bi]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E12 : ew E 12 = w64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = w64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E19 : ew E 19 = w64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E24 : ew E 24 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = w64 bi) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [w64 bi]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; unfold w64; apply unsigned_lit_small; exact Hv).
assert (U19 : bv_unsigned (ew E 19) = q) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EVO_Bx = SHADOW_OFF) by (unfold EVO_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi (fx := fxc) SEGS VAL E evo_ssW
  (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVO_PC EVO_WS)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold evo_ssW. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [|intros X; discriminate X|rewrite H26; symmetry; apply evo_S10_den; [exact E19 | lia | exact E24]].
    apply regs_ok_pin; [|intros X; discriminate X|exact H14].
    apply regs_ok_pin; [|intros X; discriminate X|exact H11].
    apply regs_ok_pin; [|intros X; discriminate X|].
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + rewrite H10. cbn [sv_denot]. rewrite E13, Z.add_0_r, Hp0'. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 19%nat q E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Hwq o Ho)|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 13 0) p);
        [cbn [sv_denot]; rewrite E13, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvq.
    + rewrite (VB 13%nat p E13) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) bi);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, Hp0'. exact Hvb.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19.
    rewrite E13. unfold w64. rewrite unsigned_lit_small by lia.
    repeat split; try exact I; first [left; lia | right; lia].
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, E13, E19, E24, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold EVO_CEIL, EVO_TOP, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS EVO_Bx evo_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, evo_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, (U_atom E 19 q E19) by lia. split.
  - rewrite <- aview_rd_of, Z.add_0_r. exact Hqra.
  - intros z Hz. rewrite Z.min_l, Z.max_r in Hz by lia. unfold SHADOW_OFF. lia. }
pose proof (@paj_run_x fxc rc SK A_prog_listing PL_prog_A PI_prog_A B (prh_pst (PI := prh_img_A)) ARx _ LAWS) as RUNh.
pose proof (@paj_run_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B (prh_pst (PI := prh_img_A)) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) as RUNhI.
pose proof (@paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B (prh_pst (PI := prh_img_A)) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) as RUNTOhI.
pose proof (paj_branch (fx := fxc) (PI := PI_prog_A)) as BRh.
assert (KM0 : forall z : word, ~ (q <= bv_unsigned z < q + 8) -> mrestrict (w_H W) mem z = mrestrict (w_H W) mem z)
  by reflexivity.
pose proof (mem_grows_refl (mrestrict (w_H W) mem)) as GR0.
assert (HSQ : SHADOW_OFF + 2 ^ 44 <= q) by (unfold SHADOW_OFF; lia).
(* the text byte's shadow: the run's one obligation, from the premise *)
paj_run_tok_x_inv RUNhI HS HJ SHOK HMN EVO_Bspan.
{ cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx. rewrite (U_atom E 13 p E13) by lia.
  apply (range_addressable_sub _ _ x0 len); [exact Hrax | lia | lia]. }
{ evo_wawr U19. }
evo_wkeep q U19 mem KM0 KM1 GR0 GR1.
psrr_branch_tok RUNh BRh HS SHOK EVO_Bspan.
- (* 32 < byte: not a blank; the branch goes to the exit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb]; exact E32 | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTOhI HS HJ SHOK HMN EVO_Bspan (EVO_PC EVO_AFT).
  { evo_wawr U19. }
  evo_wkeep q U19 mem KM1 KM2 GR1 GR2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 bi] EVO_WKEPT HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (11%bv : bv 5) R11. prreg HS (14%bv : bv 5) R14. evo_s10 HS q E19 E24 Q26.
  assert (Hvq2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat i)).
  { replace q with (q + 0) by lia. evo_chunk HS 0%nat 0 U19. }
  pmkst HS. apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- exists _ _ _ _, mkCfg (YK11.mkst ?rg (Z_to_bv 64 ?pc) ?m _) ?d = _ /\ _ =>
    replace pc with (BASE + EVO_PC EVO_AFT) by (vm_compute; reflexivity); exists rg, m, d, i end.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact KM2|]. split; [exact GR2|]. split; [exact HMN|].
  split; [exact Hvq2|]. split; [lia|].
  split; [rewrite (skipn_nth x i 0 Hi); cbn [PjGrammar.skip]; fold bi; rewrite (evo_ws_big bi Hc); reflexivity|].
  evo_wregs_kept HK R11 R14 Q26 H11 H14 H26.
- (* byte <= 32: test the mask bit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb]; exact E32 | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_ge in Hc.
  paj_run_tok_x_inv RUNhI HS HJ SHOK HMN EVO_Bspan.
  { evo_wawr U19. }
  evo_wkeep q U19 mem KM1 KM2 GR1 GR2.
  psrr_branch_tok RUNh BRh HS SHOK EVO_Bspan.
  + (* not a blank: the exit *)
    rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb]; exact E32 | lia].
    cbn [zalu_raw] in Hc0. rewrite (evo_mask_bit bi ltac:(lia)) in Hc0. apply negb_true_iff in Hc0.
    paj_run_to_tok_x_inv RUNTOhI HS HJ SHOK HMN EVO_Bspan (EVO_PC EVO_AFT).
    { evo_wawr U19. }
    evo_wkeep q U19 mem KM2 KM3 GR2 GR3.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 bi] EVO_WKEPT HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (11%bv : bv 5) R11. prreg HS (14%bv : bv 5) R14. evo_s10 HS q E19 E24 Q26.
    assert (Hvq2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat i)).
    { replace q with (q + 0) by lia. evo_chunk HS 0%nat 0 U19. }
    pmkst HS. apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- exists _ _ _ _, mkCfg (YK11.mkst ?rg (Z_to_bv 64 ?pc) ?m _) ?d = _ /\ _ =>
      replace pc with (BASE + EVO_PC EVO_AFT) by (vm_compute; reflexivity); exists rg, m, d, i end.
    split; [reflexivity|]. split; [exact HJ|]. split; [exact KM3|]. split; [exact GR3|]. split; [exact HMN|].
    split; [exact Hvq2|]. split; [lia|].
    split; [rewrite (skipn_nth x i 0 Hi); cbn [PjGrammar.skip]; fold bi; rewrite Hc0; reflexivity|].
    evo_wregs_kept HK R11 R14 Q26 H11 H14 H26.
  + (* a blank: in->p := p + 1, then the back edge or the end *)
    rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb]; exact E32 | lia].
    cbn [zalu_raw] in Hc0. rewrite (evo_mask_bit bi ltac:(lia)) in Hc0. apply negb_false_iff in Hc0.
    paj_run_tok_x_inv RUNhI HS HJ SHOK HMN EVO_Bspan.
    { evo_wawr U19. }
    evo_wkeep q U19 mem KM2 KM3 GR2 GR3.
    psrr_branch_tok RUNh BRh HS SHOK EVO_Bspan.
    * (* p + 1 <> end: back to the loop's head, then the loop's remaining iterations (IH) *)
      rewrite branch_ne_U, (U_atom_off _ 13 p 1), (U_atom _ 12 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb]; exact E12 | lia | cbn [ew ewset Nat.eqb]; exact E13 | lia | lia].
      apply negb_true_iff, Z.eqb_neq in Hc1.
      paj_run_to_tok_x_inv RUNTOhI HS HJ SHOK HMN EVO_Bspan (EVO_PC EVO_WS).
      { evo_wawr U19. }
      evo_wkeep q U19 mem KM3 KM4 GR3 GR4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 bi] EVO_WKEPT HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (10%bv : bv 5) R10. prreg HS (13%bv : bv 5) R13.
      prreg HS (11%bv : bv 5) R11. prreg HS (14%bv : bv 5) R14. evo_s10 HS q E19 E24 Q26.
      assert (Hvq1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat (Datatypes.S i))).
      { replace q with (q + 0) by lia. evo_chunk HS 0%nat 0 U19. }
      assert (Hw1 : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms)) (q + o))
        by (intros o Ho; exact (writable_at_grows SEGS _ _ _ GR4 (Hwq o Ho))).
      assert (Hg1 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) x0 x)
        by (apply (evo_q_garr8 _ _ q x0 x KM4); [lia | lia | lia | exact Hgx]).
      assert (Hr1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF x0 (Z.of_nat (length x)))
        by (apply (evo_q_ra _ mem _ q); [exact KM4 | lia | lia | exact HSQ | rewrite <- Hlen0; exact Hrax]).
      assert (Hq1' : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF q 40)
        by (apply (evo_q_ra _ mem _ q); [exact KM4 | lia | lia | exact HSQ | exact Hqra]).
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rg (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
        replace pc with (BASE + EVO_PC EVO_WS) by (vm_compute; reflexivity) end.
      eapply SRr_mono.
      { apply (IH W (ms_regs ms) (ms_mem ms) _ STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x (Datatypes.S i));
          try eassumption; try lia.
        all: lazymatch goal with
          | |- getr _ 10 = _ => rewrite R10; evo_den
          | |- getr _ 13 = _ => rewrite R13; evo_den
          | |- getr _ 11 = _ => rewrite R11; reflexivity
          | |- getr _ 14 = _ => rewrite R14; reflexivity
          | |- getr _ 12 = _ => rewrite (HK 12%bv ltac:(cbv; tauto)), H12, Hlen0; reflexivity
          | |- getr _ 26 = _ => exact Q26
          | |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption
          | |- ?g => idtac "EVO_WSL_IH_LEFT" g; fail
          end. }
      cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & i2 & -> & HJ2 & KM5 & GR5 & HMN5 & Hvq2 & Hii & Hsk & HK2).
      split; [reflexivity|]. exists regs2, mem2, md2, i2.
      split; [reflexivity|]. split; [exact HJ2|].
      split; [intros z Hz; rewrite (KM5 z Hz); exact (KM4 z Hz)|].
      split; [exact (mem_grows_trans _ _ _ GR4 GR5)|]. split; [exact HMN5|].
      split; [exact Hvq2|]. split; [lia|].
      split; [rewrite Hsk, (skipn_nth x i 0 Hi); cbn [PjGrammar.skip]; fold bi; rewrite Hc0; reflexivity|].
      intros r h1 h2 h3 h4. rewrite (HK2 r h1 h2 h3 h4). revert r h1 h2 h3 h4.
      evo_wregs_kept HK R11 R14 Q26 H11 H14 H26.
    * (* p + 1 = end: `j 0x83768` *)
      rewrite branch_ne_U, (U_atom_off _ 13 p 1), (U_atom _ 12 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb]; exact E12 | lia | cbn [ew ewset Nat.eqb]; exact E13 | lia | lia].
      apply negb_false_iff, Z.eqb_eq in Hc1.
      assert (Hend : Datatypes.S i = length x) by lia.
      paj_run_to_tok_x_inv RUNTOhI HS HJ SHOK HMN EVO_Bspan (EVO_PC EVO_AFT).
      { evo_wawr U19. }
      evo_wkeep q U19 mem KM3 KM4 GR3 GR4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 bi] EVO_WKEPT HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (11%bv : bv 5) R11. prreg HS (14%bv : bv 5) R14. evo_s10 HS q E19 E24 Q26.
      assert (Hvq2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat (Datatypes.S i))).
      { replace q with (q + 0) by lia. evo_chunk HS 0%nat 0 U19. }
      pmkst HS. apply SRr_ret. split; [reflexivity|].
      lazymatch goal with |- exists _ _ _ _, mkCfg (YK11.mkst ?rg (Z_to_bv 64 ?pc) ?m _) ?d = _ /\ _ =>
        replace pc with (BASE + EVO_PC EVO_AFT) by (vm_compute; reflexivity); exists rg, m, d, (Datatypes.S i) end.
      split; [reflexivity|]. split; [exact HJ|]. split; [exact KM4|]. split; [exact GR4|]. split; [exact HMN|].
      split; [exact Hvq2|]. split; [lia|].
      split.
      { assert (Hz : skipn (Datatypes.S i) x = []) by (apply skipn_all2; lia).
        rewrite (skipn_nth x i 0 Hi), Hz. cbn [PjGrammar.skip]. fold bi. rewrite Hc0. reflexivity. }
      evo_wregs_kept HK R11 R14 Q26 H11 H14 H26.
Qed.

(* the four windows contain in->p's 8 bytes *)
Lemma evo_q_W4 : forall a (Wx : world SEGS) (m m' : word -> option BvBase.byte),
  (forall z : word, ~ (ea_q a <= bv_unsigned z < ea_q a + 8) -> mrestrict (w_H Wx) m' z = mrestrict (w_H Wx) m z) ->
  forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H Wx) m' x = mrestrict (w_H Wx) m x.
Proof. intros a Wx m m' KM x Hx. apply KM. intros Hq. apply Hx. unfold evo_W4. left. exact Hq. Qed.

(* ======== from the loop's head to the end of the piece: the blanks (evo_wsl), then the tail (evo_tail) ======== *)
Lemma evo_from_ws : forall a fxc W regs mem md ly St Hp k (o : bool) (i : nat) dln,
  EV_PRE a -> @ev_fx fx fxc -> evo_core a W regs mem md ly St Hp k o i dln -> (i < length (ea_x a))%nat ->
  getr regs 10 = w64 (ea_x0 a + Z.of_nat i) -> getr regs 13 = w64 (ea_x0 a + Z.of_nat i) ->
  getr regs 11 = w64 32 -> getr regs 14 = w64 evo_WSM ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    match PjGrammar.skip (skipn i (ea_x a)) with
    | [] => None
    | c :: r => if c =? PjGrammar.closer o then Some (PjGrammar.mk o [], r)
                else ev_L (Datatypes.S (Z.to_nat (ea_dep a))) o 0 0 [] (c :: r)
    end ->
  SRr SEGS W (ev_cfg (PA := PI_prog_A) fxc regs EVO_WS mem md) (evo_post a fxc o).
Proof.
intros a fxc W regs mem md ly St Hp k o i dln HPRE HFX HC Hi H10 H13 H11 H14 HMODEL.
pose proof HC as (HMID & HREG & H12 & H20 & H21 & H22 & H23v & H48 & H56 & H64 & Hdln & Hiw & Hdep & Hv' & Hdl).
pose proof (evo_bnd a ly St Hp W mem md k _ _ _ HPRE HMID) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & HQA).
pose proof (evo_sp_lo a ly St Hp W mem md k _ _ _ HPRE HMID) as (HSPLO & HSPHI).
pose proof HMID as (HJ & _ & _ & _ & _ & Hcur & Hsrc & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof Hsrc as (Hga & Hx0lo & Hx0hi & _ & Hra & _).
destruct Hcur as (C0 & C8 & C16 & C24 & C32).
pose proof HREG as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs3 & Rs8 & Rs9 & Rs10).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
unfold ea_len in H12.
unfold ev_cfg. replace (@ev_pc rc A_prog_listing PI_prog_A EVO_WS) with (BASE + EVO_PC EVO_WS) by (vm_compute; reflexivity).
eapply SRr_bind.
{ apply (evo_wsl fxc (length (ea_x a) - i) W regs mem md (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a)
    (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly St Hp k
    (ea_q a) (ea_x0 a) (ea_x a) i);
    [reflexivity | exact Hi | exact HJ | lia | lia | exact Hqlo | exact Hqhi | exact Hq8 | lia | exact Hx0lo | exact Hx0hi
    | exact H10 | exact H13 | exact H11 | exact H12 | exact H14 | exact Rs3 | exact Rs8 | exact Rs10 | exact C0
    | exact Hga | exact Hra | exact HQA | intros o0 Ho0; apply (apresent_writable SEGS); apply Hpres; lia | exact HMN]. }
cbv beta. intros W' c' Hle (-> & regs' & mem' & md' & i' & -> & HJ' & KMq & GR & HMN' & Hvq' & Hii & Hsk & HK).
unfold EVO_CEIL in Hqlo, HSlo. unfold EVO_TOP in Hqhi, HShi, Hv'.
assert (Hd' : val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 16) 4 (ea_dep a + 1))
  by (apply (evo_q_val _ _ (ea_q a) _ 4 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | right; lia | exact C16]).
assert (Hl' : val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 32) 4 dln)
  by (apply (evo_q_val _ _ (ea_q a) _ 4 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | right; lia | exact C32]).
pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ' (evo_q_W4 a W mem mem' KMq) GR Hvq' Hd' Hl'
  HMN') as HMID'.
assert (HC' : evo_core a W regs' mem' md' ly St Hp k o i' dln).
{ unfold evo_core.
  split; [exact HMID'|].
  split; [unfold ev_regs; repeat split; rewrite HK by (intros X; discriminate X); assumption|].
  split; [rewrite HK by (intros X; discriminate X); unfold ea_len; exact H12|].
  split; [rewrite HK by (intros X; discriminate X); exact H20|].
  split; [rewrite HK by (intros X; discriminate X); exact H21|].
  split; [rewrite HK by (intros X; discriminate X); exact H22|].
  split; [rewrite HK by (intros X; discriminate X); exact H23v|].
  split; [apply (evo_q_val _ _ (ea_q a) _ 8 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia
    | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact H48]|].
  split; [apply (evo_q_val _ _ (ea_q a) _ 8 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia
    | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact H56]|].
  split; [apply (evo_q_val _ _ (ea_q a) _ 8 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia
    | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact H64]|].
  split; [exact Hdln|]. split; [lia|]. split; [exact Hdep|]. split; [unfold EVO_TOP; lia|]. exact Hdl. }
pose proof (evo_tail a fxc W regs' mem' md' ly St Hp k o i' dln HPRE HFX HC') as HT.
unfold ev_cfg in HT.
replace (@ev_pc rc A_prog_listing PI_prog_A EVO_AFT) with (BASE + EVO_PC EVO_AFT) in HT by (vm_compute; reflexivity).
apply HT. rewrite HMODEL, Hsk. reflexivity.
Qed.

(* ======== the cut 0x836d4 (after the type test): in->p := x0 + i1 + 1, then the end of the text (straight to the
   tail cut 0x83768) or the blanks loop 0x836fc ======== *)
Definition EVO_J : Z := 0x430.     (* 0x836d4: the join of the three type-test arms (LENGTH, bff8519b) *)
Definition evo_ssJ (c : branch_cond) : sstate :=
  mkSS (EVO_PC EVO_J) (sr_set sr_atoms 26%bv EVO_S10)
    [YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 11 0))]] None
    (mkFacts [(11%nat, mkAF 4096 EVO_TOP 0); (12%nat, mkAF 4096 EVO_TOP 0); (19%nat, mkAF EVO_CEIL EVO_TOP 3);
              (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [mkAC c (SOff 11 1) (SOff 12 0)] []).
Definition EVO_JKEPT : list (bv 5) := [2; 3; 4; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25]%bv.

Lemma evo_join : forall a fxc W regs mem md ly St Hp k (o : bool) (i1 : nat) dln,
  EV_PRE a -> @ev_fx fx fxc -> evo_core a W regs mem md ly St Hp k o i1 dln -> (i1 < length (ea_x a))%nat ->
  getr regs 11 = w64 (ea_x0 a + Z.of_nat i1) ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    match PjGrammar.skip (skipn (Datatypes.S i1) (ea_x a)) with
    | [] => None
    | c :: r => if c =? PjGrammar.closer o then Some (PjGrammar.mk o [], r)
                else ev_L (Datatypes.S (Z.to_nat (ea_dep a))) o 0 0 [] (c :: r)
    end ->
  SRr SEGS W (ev_cfg (PA := PI_prog_A) fxc regs EVO_J mem md) (evo_post a fxc o).
Proof.
intros a fxc W regs mem md ly St Hp k o i1 dln HPRE HFX HC Hi1 H11 HMODEL.
pose proof HC as (HMID & HREG & H12 & H20 & H21 & H22 & H23v & H48 & H56 & H64 & Hdln & Hiw & Hdep & Hv' & Hdl).
pose proof (evo_bnd a ly St Hp W mem md k _ _ _ HPRE HMID) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & HQA).
pose proof (evo_sp_lo a ly St Hp W mem md k _ _ _ HPRE HMID) as (HSPLO & HSPHI).
pose proof HMID as (HJ & _ & _ & _ & _ & Hcur & Hsrc & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof Hsrc as (Hga & Hx0lo & Hx0hi & _ & Hra & _).
destruct Hcur as (C0 & C8 & C16 & C24 & C32).
pose proof HREG as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs3 & Rs8 & Rs9 & Rs10).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
unfold ea_len in H12, Hx0hi.
unfold EVO_CEIL in Hqlo, HSlo. unfold EVO_TOP in Hqhi, HShi, Hv'.
set (E := @Eimg _ A_prog_listing PI_prog_A (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n) by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | reflexivity]).
assert (EQ11 : ew E 11 = w64 (ea_x0 a + Z.of_nat i1))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EQ12 : ew E 12 = w64 (ea_x0 a + Z.of_nat (length (ea_x a))))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (EQ19 : ew E 19 = w64 (ea_q a)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact Rs3).
assert (EQ24 : ew E 24 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact Rs8).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite EQ19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EVO_Bx = SHADOW_OFF) by (unfold EVO_Bx; apply (U_atom E 24 SHADOW_OFF EQ24); unfold SHADOW_OFF; lia).
assert (Hi1l : Z.of_nat i1 < Z.of_nat (length (ea_x a))) by lia.
assert (HSc : forall c, branch_taken c (w64 (ea_x0 a + Z.of_nat i1 + 1)) (w64 (ea_x0 a + Z.of_nat (length (ea_x a)))) = true ->
  st_ok_pi (fx := fxc) SEGS VAL E (evo_ssJ c)
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVO_PC EVO_J)) mem (YK11.seg_rom SEGS)))).
{ intros c Hc. rewrite restrict_mkst_fx. unfold evo_ssJ. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [unfold E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    rewrite Rs10. symmetry. apply evo_S10_den; [exact EQ19 | lia | exact EQ24].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
    split; [lia|]. split; [lia|]. split; [intros z Hz; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val _ _ _ _ _ 8%N _ (ea_x0 a + Z.of_nat i1));
      [rewrite (evo_Uoff _ 11 0 _ EQ11) by lia; f_equal; lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact C0].
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - split; [|split; [|exact I]].
    + cbn [f_atoms atoms_ok].
      split; [apply (evo_atom_ok _ 11 (ea_x0 a + Z.of_nat i1)); [exact EQ11 | lia | unfold EVO_TOP; lia | apply Z.mod_1_r | lia]|].
      split; [apply (evo_atom_ok _ 12 (ea_x0 a + Z.of_nat (length (ea_x a))));
        [exact EQ12 | lia | unfold EVO_TOP; lia | apply Z.mod_1_r | lia]|].
      split; [apply (evo_atom_ok _ 19 (ea_q a)); [exact EQ19 | lia | unfold EVO_CEIL, EVO_TOP; lia | exact Hq8 | lia]|].
      split; [apply (evo_atom_ok _ 24 SHADOW_OFF); [exact EQ24 | unfold SHADOW_OFF; lia | lia | apply Z.mod_1_r | lia]|].
      exact I.
    + cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite (evo_Uoff E 11 1 _ EQ11), (evo_Uoff E 12 0 _ EQ12) by lia. rewrite Z.add_0_r. exact Hc. }
assert (HSOK : sh_ok SEGS EVO_Bx evo_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, evo_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, (U_atom E 19 (ea_q a) EQ19) by lia. split.
  - rewrite <- aview_rd_of, Z.add_0_r. exact HQA.
  - intros z Hz. rewrite Z.min_l, Z.max_r in Hz by lia. unfold SHADOW_OFF. lia. }
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B (prh_pst (PI := prh_img_A)) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (@ev_pc rc A_prog_listing PI_prog_A EVO_J) with (BASE + EVO_PC EVO_J) by (vm_compute; reflexivity).
(* the write set of both runs is in->p's 8 bytes *)
assert (HJW : forall c z, in_wrange E (ss_mem (evo_ssJ c)) z -> ea_q a <= z < ea_q a + 8).
{ intros c z (r & Hin & Hz). cbn [evo_ssJ ss_mem In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz. rewrite U19 in Hz. lia. }
(* what both runs leave: the invariant at x0 + i1 + 1 and the carriers *)
assert (HPOST : forall c (ms : machine_state) md' (E' : env),
  frame_of E (ss_mem (evo_ssJ c)) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
  ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_A)) ARx (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a)
    (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly St Hp W (ms_mem ms) md' k ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat (Datatypes.S i1)) ->
  (forall r, In r EVO_JKEPT -> getr (ms_regs ms) r = getr regs r) ->
  getr (ms_regs ms) 26 = w64 (shadow_addr (ea_q a)) ->
  (Datatypes.S i1 <= length (ea_x a))%nat -> YAkMemnorm.memnorm SEGS (ms_mem ms) ->
  evo_core a W (ms_regs ms) (ms_mem ms) md' ly St Hp k o (Datatypes.S i1) dln).
{ intros c ms md' E' HFr HG HJ' Hp' HK Q26 Hle HMN'.
  assert (KMq : forall z : word, ~ (ea_q a <= bv_unsigned z < ea_q a + 8) ->
    mrestrict (w_H W) (ms_mem ms) z = mrestrict (w_H W) mem z).
  { intros z Hz. apply HFr. intros Hw. apply Hz. exact (HJW c _ Hw). }
  assert (Hd' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 16) 4 (ea_dep a + 1))
    by (apply (evo_q_val _ _ (ea_q a) _ 4 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | right; lia | exact C16]).
  assert (Hl' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a + 32) 4 dln)
    by (apply (evo_q_val _ _ (ea_q a) _ 4 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | right; lia | exact C32]).
  pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ' (evo_q_W4 a W mem _ KMq) HG Hp' Hd' Hl'
    HMN') as HMID'.
  unfold evo_core.
  split; [exact HMID'|].
  split; [unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]|].
  split; [rewrite HK by (cbv; tauto); unfold ea_len; exact H12|].
  split; [rewrite HK by (cbv; tauto); exact H20|].
  split; [rewrite HK by (cbv; tauto); exact H21|].
  split; [rewrite HK by (cbv; tauto); exact H22|].
  split; [rewrite HK by (cbv; tauto); exact H23v|].
  split; [apply (evo_q_val _ _ (ea_q a) _ 8 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia
    | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact H48]|].
  split; [apply (evo_q_val _ _ (ea_q a) _ 8 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia
    | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact H56]|].
  split; [apply (evo_q_val _ _ (ea_q a) _ 8 _ KMq); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia
    | left; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact H64]|].
  split; [exact Hdln|]. split; [exact Hle|]. split; [exact Hdep|]. split; [unfold EVO_TOP; lia|]. exact Hdl. }
destruct (Nat.eq_dec (Datatypes.S i1) (length (ea_x a))) as [Hend|Hlt].
- (* the end of the text: in->p := x0 + len, straight to the tail cut 0x83768 *)
  pose proof (HSc BC_GEU ltac:(cbn [branch_taken]; unfold bv_ltu, w64; rewrite !unsigned_lit_small by lia;
    apply negb_true_iff, Z.ltb_ge; lia)) as HS.
  paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EVO_AFT).
  + intros z Hz. left. apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID). unfold evo_W4. left. exact (HJW _ z Hz).
  + pmkst HS.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] EVO_JKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    evo_s10 HS (ea_q a) EQ19 EQ24 Q26.
    assert (Hp' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat (Datatypes.S i1))).
    { replace (ea_q a) with (ea_q a + 0) by lia. evo_chunk HS 0%nat 0 U19. }
    pose proof (HPOST BC_GEU ms _ E HFr HG HJ Hp' HK Q26 ltac:(lia) HMN) as HC'.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
      replace pc with (BASE + EVO_PC EVO_AFT) by (vm_compute; reflexivity) end.
    pose proof (evo_tail a fxc W _ _ _ ly St Hp k o (Datatypes.S i1) dln HPRE HFX HC') as HT.
    unfold ev_cfg in HT.
    replace (@ev_pc rc A_prog_listing PI_prog_A EVO_AFT) with (BASE + EVO_PC EVO_AFT) in HT by (vm_compute; reflexivity).
    apply HT. rewrite HMODEL. assert (Hz : skipn (Datatypes.S i1) (ea_x a) = []) by (apply skipn_all2; lia).
    rewrite Hz. reflexivity.
- (* a byte remains: a0 = a3 = x0 + i1 + 1, a1 = 32, a4 = the mask, into the blanks loop *)
  pose proof (HSc BC_LTU ltac:(cbn [branch_taken]; unfold bv_ltu, w64; rewrite !unsigned_lit_small by lia;
    apply Z.ltb_lt; lia)) as HS.
  paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EVO_WS).
  + intros z Hz. left. apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID). unfold evo_W4. left. exact (HJW _ z Hz).
  + pmkst HS.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] EVO_JKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    evo_s10 HS (ea_q a) EQ19 EQ24 Q26.
    prreg HS (10%bv : bv 5) R10. prreg HS (13%bv : bv 5) R13.
    prreg HS (11%bv : bv 5) R11. prreg HS (14%bv : bv 5) R14.
    assert (Hp' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat (Datatypes.S i1))).
    { replace (ea_q a) with (ea_q a + 0) by lia. evo_chunk HS 0%nat 0 U19. }
    pose proof (HPOST BC_LTU ms _ E HFr HG HJ Hp' HK Q26 ltac:(lia) HMN) as HC'.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
      replace pc with (BASE + EVO_PC EVO_WS) by (vm_compute; reflexivity) end.
    pose proof (evo_from_ws a fxc W _ _ _ ly St Hp k o (Datatypes.S i1) dln HPRE HFX HC' ltac:(lia)) as HT.
    unfold ev_cfg in HT.
    replace (@ev_pc rc A_prog_listing PI_prog_A EVO_WS) with (BASE + EVO_PC EVO_WS) in HT by (vm_compute; reflexivity).
    apply HT; [rewrite R10; evo_den | rewrite R13; evo_den | rewrite R11; reflexivity | rewrite R14; reflexivity | exact HMODEL].
Qed.

(* ======== the head: 0x834bc -> 0x836d4 (the closer spilled, in->depth := dep + 1, the depth test, v's type test) or
   -> P_EXIT 0x83d48 (the depth refusal, PjGrammar.MAXD) ======== *)

(* a condition the state's facts carry, from its truth at the machine state *)
Lemma evo_add_cond : forall fxc E ss ms c x y, st_ok_pi (fx := fxc) SEGS VAL E ss ms ->
  branch_taken c (sv_denot E x) (sv_denot E y) = true -> st_ok_pi (fx := fxc) SEGS VAL E (add_cond ss (mkAC c x y)) ms.
Proof.
intros fxc E ss ms c x y HS Hb. pose proof (st_ok_add_cond SEGS E (abs_ss VAL ss) ms c x y HS Hb) as H.
destruct ss. exact H.
Qed.
(* the depth test `li a4,31; blt a4,a5` on in->depth's old value d in [0, MAXD] (the signed compare, by enumeration) *)
Lemma evo_dep_lt : forall d, 0 <= d <= Z.of_nat PjGrammar.MAXD ->
  branch_taken BC_LT (Z_to_bv 64 31) (Z_to_bv 64 d) = (31 <? d).
Proof.
intros d Hd.
assert (H : forallb (fun k => Bool.eqb (branch_taken BC_LT (Z_to_bv 64 31) (Z_to_bv 64 (Z.of_nat k))) (31 <? Z.of_nat k))
  (seq 0 (S PjGrammar.MAXD)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat d) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Bool.eqb_prop in H. exact H.
Qed.
Lemma evo_dep_ge : forall d, 0 <= d <= Z.of_nat PjGrammar.MAXD ->
  branch_taken BC_GE (Z_to_bv 64 31) (Z_to_bv 64 d) = (d <=? 31).
Proof.
intros d Hd.
assert (H : forallb (fun k => Bool.eqb (branch_taken BC_GE (Z_to_bv 64 31) (Z_to_bv 64 (Z.of_nat k))) (Z.of_nat k <=? 31))
  (seq 0 (S PjGrammar.MAXD)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat d) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Bool.eqb_prop in H. exact H.
Qed.
(* the shadow address of atom n + c as the code computes it, ((n + c) >> 3) + s8 (as S8aClose.v's s8c_U_shx) *)
Lemma evo_shx_den : forall E n c x, ew E n = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 47 ->
  ew E 24 = w64 SHADOW_OFF ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0)) = Z_to_bv 64 (shadow_addr (x + c)).
Proof.
intros E n c x Hn Hx Hxc H24. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0))).
rewrite !U_SAlu, (U_atom_off E n x c Hn), U_SLit, (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64, shadow_addr, SHADOW_OFF.
change (bv_modulus 64) with (2 ^ 64).
assert (0 <= (x + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma evo_tag_le : forall t, 0 <= PjTree.tag t <= 6.
Proof. intros t. destruct t; cbn [PjTree.tag]; lia. Qed.

(* the head's regions do not overlap: `in` field by field, the spill area below sp0, v's type word outside both *)
Lemma evo_Hpd : forall a ly S Hp W mem md k i1 c regs,
  EV_PRE a -> EV_KIND a W regs mem md ly S Hp k i1 c ->
  pairwise_disjoint (evo_E a regs) (evo_Rin ++ [evo_Rf]) /\
  (ea_v a <> 0 -> pairwise_disjoint (evo_E a regs) (evo_Rin ++ [evo_Rf; evo_Rv])).
Proof.
intros a ly S Hp W mem md k i1 c regs HPRE HKIND.
pose proof (evo_bnd a ly S Hp W mem md k _ _ _ HPRE (proj1 HKIND)) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & _).
pose proof HKIND as (HMID & HREG & _ & _ & _ & H23 & _).
pose proof HREG as (_ & _ & _ & _ & H9 & _ & H19 & _).
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
assert (EQ19 : ew (evo_E a regs) 19 = w64 (ea_q a)) by (rewrite (evo_Ereg a regs 19 19%bv ltac:(lia) eq_refl); exact H19).
assert (EQ9 : ew (evo_E a regs) 9 = w64 (ea_S1 a)) by (rewrite (evo_Ereg a regs 9 9%bv ltac:(lia) eq_refl); exact H9).
assert (EQ23 : ew (evo_E a regs) 23 = w64 (ea_v a)) by (rewrite (evo_Ereg a regs 23 23%bv ltac:(lia) eq_refl); exact H23).
unfold EVO_CEIL, EVO_TOP in *.
split.
- unfold evo_Rin, evo_Rp, evo_Re, evo_Rd, evo_Rs, evo_Rl, evo_Rf. cbn [app pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EQ19, EQ9. unfold w64. rewrite !unsigned_lit_small by lia.
  repeat split; try exact I; first [left; lia | right; lia].
- intros Hv0.
  destruct (evo_Rv_ok a ly S Hp W mem md k i1 c regs HPRE HKIND Hv0) as (_ & _ & Hvb).
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htree0 & _).
  destruct Htree0 as [Hz|(_ & _ & Hfoot)]; [contradiction|].
  destruct (Hfoot (ea_v a) ltac:(left; lia)) as (_ & F1 & F2 & _).
  destruct (Hfoot (ea_v a + 3) ltac:(left; lia)) as (_ & G1 & G2 & _).
  unfold EVO_TOP in Hvb. unfold ea_sp0 in *.
  unfold evo_Rin, evo_Rp, evo_Re, evo_Rd, evo_Rs, evo_Rl, evo_Rf, evo_Rv. cbn [app pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EQ19, EQ9, EQ23. unfold w64. rewrite !unsigned_lit_small by lia.
  repeat split; try exact I; first [left; lia | right; lia | lia].
Qed.
(* the head's write windows *)
Lemma evo_H_W4 : forall a (E : env) z,
  bv_unsigned (ew E 19) = ea_q a -> bv_unsigned (ew E 9) = ea_S1 a ->
  in_wrange E (evo_Rin ++ [evo_Rf]) z \/ in_wrange E (evo_Rin ++ [evo_Rf; evo_Rv]) z -> evo_W4 a z.
Proof.
intros a E z U19 U9 [Hw|Hw];
  [apply (evo_wr_W4 a E (evo_Rin ++ [evo_Rf]) z); [|exact Hw]
  |apply (evo_wr_W4 a E (evo_Rin ++ [evo_Rf; evo_Rv]) z); [|exact Hw]];
  unfold evo_Rin, evo_Rp, evo_Re, evo_Rd, evo_Rs, evo_Rl, evo_Rf, evo_Rv; cbn [app];
  repeat apply Forall_cons; try apply Forall_nil;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U19, ?U9;
  first [left; lia | right; intros y Hy; unfold evo_W4; lia].
Qed.

(* P_EXIT after the depth refusal: in->depth = dep + 1 (written before the test), in->p and in->differs as at entry,
   s11 = -1 (P_KIND's), the text's outcome a refusal (prhex_V = None, ev_V_open_at above PjGrammar.MAXD) *)
Lemma evo_refuse_post : forall a fxc W regs mem md ly St Hp k i1 (o : bool) regs' mem' md',
  EV_PRE a -> @ev_fx fx fxc -> EV_KIND a W regs mem md ly St Hp k i1 (if o then 123 else 91) -> 31 < ea_dep a ->
  ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_A)) ARx (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a)
    (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly St Hp W mem' md' k ->
  (forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 (ea_x0 a + Z.of_nat i1) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 16) 4 (ea_dep a + 1) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 32) 4 (ea_dl a) ->
  ev_regs (PA := PI_prog_A) a regs' -> getr regs' 22 = getr regs 22 -> getr regs' 27 = getr regs 27 ->
  YAkMemnorm.memnorm SEGS mem' ->
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs' (Z_to_bv 64 (BASE + EVO_PC EV_EXIT)) mem' (YK11.seg_rom SEGS)) md')
    (evo_post a fxc o).
Proof.
intros a fxc W regs mem md ly St Hp k i1 o regs' mem' md' HPRE HFX HKIND Href HJ' HKW HG Hp' Hd' Hl' HREG' H22' H27'
  HMN'.
pose proof HKIND as (HMID & HREG & H20 & H21 & H22 & H23 & H27 & H11 & H12 & Hi1 & Hnth & Hws & Hskip).
pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ' HKW HG Hp' Hd' Hl' HMN') as HMID'.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0 & Hdep & _ & Hdl0 & _).
apply SRr_ret. unfold evo_post. left.
replace (BASE + EVO_PC EV_EXIT) with (@ev_pc rc A_prog_listing PI_prog_A EV_EXIT) by (vm_compute; reflexivity).
exists fxc, regs', mem', md', ly, St, Hp, k, (-1), (Z.of_nat i1), (ea_dep a + 1), (ea_dl a).
split; [reflexivity|]. split; [exact HFX|].
unfold ev_at_exit. split; [exact HMID'|]. split; [exact HREG'|].
split; [rewrite H22'; exact H22|]. split; [rewrite H27'; exact H27|].
unfold ev_out. split; [exact Hdl0|].
assert (Hsk1 : PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
  (if o then 123 else 91) :: skipn (Datatypes.S i1) (ea_x a))
  by (rewrite Hskip, (skipn_nth (ea_x a) i1 0 Hi1), Hnth; reflexivity).
rewrite (ev_V_open_at (ea_dep a) _ _ (if o then 123 else 91) ltac:(lia) Hsk1 ltac:(destruct o; [left|right]; reflexivity)).
replace (Z.of_nat PjGrammar.MAXD <? ea_dep a + 1) with true
  by (symmetry; apply Z.ltb_lt; change (Z.of_nat PjGrammar.MAXD) with 32; lia).
cbv beta iota. unfold ea_len. lia.
Qed.

(* 0x836d4 after the head: the carriers of evo_core at in->p = x0 + i1, the model at the opener, then evo_join *)
Lemma evo_head_post : forall a fxc W regs mem md ly St Hp k i1 (o : bool) regs' mem' md' dln,
  EV_PRE a -> @ev_fx fx fxc -> EV_KIND a W regs mem md ly St Hp k i1 (if o then 123 else 91) -> ea_dep a <= 31 ->
  ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_A)) ARx (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a)
    (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly St Hp W mem' md' k ->
  (forall x : word, ~ evo_W4 a (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 (ea_x0 a + Z.of_nat i1) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 16) 4 (ea_dep a + 1) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a + 32) 4 dln ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 48) 8 (ea_q a + 16) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 56) 8 (shadow_addr (ea_q a + 16)) ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 64) 8 (PjGrammar.closer o) ->
  ev_regs (PA := PI_prog_A) a regs' ->
  (forall r : bv 5, In r [11; 12; 20; 21; 22]%bv -> getr regs' r = getr regs r) ->
  getr regs' 23 = w64 (ev_v' (ea_v a) o (ea_t a)) ->
  (dln = 0 \/ dln = 1) -> ev_dl (ea_dl a) (ea_v a) o (ea_t a) [] dln -> YAkMemnorm.memnorm SEGS mem' ->
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs' (Z_to_bv 64 (BASE + EVO_PC EVO_J)) mem' (YK11.seg_rom SEGS)) md')
    (evo_post a fxc o).
Proof.
intros a fxc W regs mem md ly St Hp k i1 o regs' mem' md' dln HPRE HFX HKIND Hdep31 HJ' HKW HG Hp' Hd' Hl' H48 H56 H64
  HREG' HK5 H23' Hdln Hdl HMN'.
pose proof HKIND as (HMID & HREG & H20 & H21 & H22 & H23 & H27 & H11 & H12 & Hi1 & Hnth & Hws & Hskip).
pose proof (evo_mid_keep a ly St Hp W mem md k _ _ _ _ _ _ _ _ _ HPRE HMID HJ' HKW HG Hp' Hd' Hl' HMN') as HMID'.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0 & Hdep & _).
assert (Hv'b : 0 <= ev_v' (ea_v a) o (ea_t a) <= EVO_TOP).
{ unfold ev_v'. destruct (ev_tv (ea_v a) o (ea_t a)); [|unfold EVO_TOP; lia].
  destruct (Z.eq_dec (ea_v a) 0) as [->|Hv0]; [unfold EVO_TOP; lia|].
  destruct (evo_Rv_ok a ly St Hp W mem md k i1 _ regs HPRE HKIND Hv0) as (_ & _ & Hvb). lia. }
assert (HC : evo_core a W regs' mem' md' ly St Hp k o i1 dln).
{ unfold evo_core. split; [exact HMID'|]. split; [exact HREG'|].
  split; [rewrite HK5 by (cbv; tauto); exact H12|].
  split; [rewrite HK5 by (cbv; tauto); exact H20|].
  split; [rewrite HK5 by (cbv; tauto); exact H21|].
  split; [rewrite HK5 by (cbv; tauto); exact H22|].
  split; [exact H23'|].
  split; [exact H48|]. split; [exact H56|]. split; [exact H64|].
  split; [exact Hdln|]. split; [lia|]. split; [lia|]. split; [exact Hv'b|]. exact Hdl. }
replace (BASE + EVO_PC EVO_J) with (@ev_pc rc A_prog_listing PI_prog_A EVO_J) by (vm_compute; reflexivity).
apply (evo_join a fxc W regs' mem' md' ly St Hp k o i1 dln HPRE HFX HC Hi1).
- rewrite HK5 by (cbv; tauto). exact H11.
- assert (Hsk1 : PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    (if o then 123 else 91) :: skipn (Datatypes.S i1) (ea_x a))
    by (rewrite Hskip, (skipn_nth (ea_x a) i1 0 Hi1), Hnth; reflexivity).
  rewrite (ev_V_open_at (ea_dep a) _ _ (if o then 123 else 91) ltac:(lia) Hsk1 ltac:(destruct o; [left|right]; reflexivity)).
  replace (Z.of_nat PjGrammar.MAXD <? ea_dep a + 1) with false
    by (symmetry; apply Z.ltb_ge; change (Z.of_nat PjGrammar.MAXD) with 32; lia).
  replace ((if o then 123 else 91) =? 123) with o by (destruct o; reflexivity).
  reflexivity.
Qed.

(* the registers the head does not write (s5 is seated as the opener's literal; s7 is written on a type mismatch, and
   v = 0 seats it as the literal 0) *)
Definition EVO_HKEPT : list (bv 5) := [2; 3; 4; 8; 9; 11; 12; 18; 19; 20; 22; 24; 25; 27]%bv.

Lemma evo_head : forall a fxc W regs mem md ly St Hp k i1 (o : bool),
  EV_PRE a -> @ev_fx fx fxc -> EV_KIND a W regs mem md ly St Hp k i1 (if o then 123 else 91) ->
  SRr SEGS W (ev_cfg (PA := PI_prog_A) fxc regs EV_ITEMS mem md) (evo_post a fxc o).
Proof.
intros a fxc W regs mem md ly St Hp k i1 o HPRE HFX HKIND.
pose proof HKIND as (HMID & HREG & H20 & H21 & H22 & H23 & H27 & H11 & H12 & Hi1 & Hnth & Hws & Hskip).
pose proof (evo_bnd a ly St Hp W mem md k _ _ _ HPRE HMID) as
  (HAR & Hq8 & Hsq & Hqd & Hqlo & Hqhi & HS32 & HSlo & HSsp & HShi & HS287 & Hpres & HQA).
pose proof (evo_sp_lo a ly St Hp W mem md k _ _ _ HPRE HMID) as (HSPLO & HSPHI).
pose proof HMID as (HJ & _ & _ & _ & _ & Hcur & Hsrc & _ & HT & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof Hsrc as (Hga & Hx0lo & Hx0hi & _ & Hra & _).
destruct Hcur as (C0 & C8 & C16 & C24 & C32).
pose proof HREG as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs3 & Rs8 & Rs9 & Rs10).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0 & Hdep & _ & Hdl0 & _).
pose proof (@ASAN_CEIL_range rc) as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
assert (HSTKa : 4096 <= ea_STK (PI := prh_img_A) a) by (unfold ea_STK; apply evo_stk).
pose proof (evo_fr_bnd a ly St Hp W mem md k _ _ _ HPRE HMID) as (HFR1 & HFR2).
pose proof (fs_frame_bytes_pos 1) as HFB.
pose proof (evo_tag_le (ea_t a)) as Htg.
destruct (evo_Hpd a ly St Hp W mem md k i1 _ regs HPRE HKIND) as (HPD0 & HPDv).
set (E := evo_E a regs).
assert (HEI : img_env VAL A_LIM E) by (unfold E, evo_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))]) E)
  by (unfold E, evo_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EQ9 : ew E 9 = w64 (ea_S1 a)) by (unfold E; rewrite (evo_Ereg a regs 9 9%bv ltac:(lia) eq_refl); exact Rs1).
assert (EQ11 : ew E 11 = w64 (ea_x0 a + Z.of_nat i1)) by (unfold E; rewrite (evo_Ereg a regs 11 11%bv ltac:(lia) eq_refl); exact H11).
assert (EQ19 : ew E 19 = w64 (ea_q a)) by (unfold E; rewrite (evo_Ereg a regs 19 19%bv ltac:(lia) eq_refl); exact Rs3).
assert (EQ23 : ew E 23 = w64 (ea_v a)) by (unfold E; rewrite (evo_Ereg a regs 23 23%bv ltac:(lia) eq_refl); exact H23).
assert (EQ24 : ew E 24 = w64 SHADOW_OFF) by (unfold E; rewrite (evo_Ereg a regs 24 24%bv ltac:(lia) eq_refl); exact Rs8).
assert (EQ32 : ew E 32 = w64 (ea_dep a)) by (exact (evo_Eex a regs 0%nat ltac:(lia))).
assert (EQ34 : ew E 34 = w64 (ea_dl a)) by (exact (evo_Eex a regs 2%nat ltac:(lia))).
assert (EQ35 : ew E 35 = w64 (PjTree.tag (ea_t a))) by (exact (evo_Eex a regs 3%nat ltac:(lia))).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite EQ19; unfold w64; apply unsigned_lit_small; unfold EVO_CEIL, EVO_TOP in *; lia).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite EQ9; unfold w64; apply unsigned_lit_small; unfold EVO_CEIL, EVO_TOP in *; lia).
assert (UBx : U E EVO_Bx = SHADOW_OFF) by (unfold EVO_Bx; apply (U_atom E 24 SHADOW_OFF EQ24); unfold SHADOW_OFF; lia).
unfold ea_len in Hx0hi.
unfold EVO_CEIL in Hqlo, HSlo. unfold EVO_TOP in Hqhi, HShi.
assert (Hi1l : Z.of_nat i1 < Z.of_nat (length (ea_x a))) by lia.
assert (HSH : 0 <= shadow_addr (ea_q a + 16) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_pos (ea_q a + 16) 8 ltac:(lia) ltac:(lia)) as D1.
  assert (D2 : (ea_q a + 16) / 8 <= ea_q a + 16) by (apply Z.div_le_upper_bound; lia).
  lia. }
assert (HSOK : sh_ok SEGS EVO_Bx evo_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, evo_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, (U_atom E 19 (ea_q a) EQ19) by lia. split.
  - rewrite <- aview_rd_of, Z.add_0_r. exact HQA.
  - intros z Hz. rewrite Z.min_l, Z.max_r in Hz by lia. unfold SHADOW_OFF. lia. }
assert (H23s : getr regs 23 = sv_denot E (SOff 23 0))
  by (cbn [sv_denot]; rewrite EQ23, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H23).
assert (HD32 : sv_denot E (SOff 32 0) = Z_to_bv 64 (ea_dep a))
  by (cbn [sv_denot]; rewrite EQ32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B (prh_pst (PI := prh_img_A)) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (@ev_pc rc A_prog_listing PI_prog_A EV_ITEMS) with (BASE + EVO_PC EV_ITEMS) by (vm_compute; reflexivity).
destruct (Z_lt_ge_dec 31 (ea_dep a)) as [Href|Hgo].
- (* (R) dep + 1 > PjGrammar.MAXD: the refusal, 0x834bc -> P_EXIT 0x83d48 (s7 is not read on this path) *)
  pose proof (evo_entry a fxc W regs mem md ly St Hp k i1 (if o then 123 else 91) (SOff 23 0) [] [] HPRE HKIND H23s
    eq_refl (Forall_nil _) HPD0 I) as HS0. fold E in HS0.
  pose proof (evo_add_cond _ _ _ _ BC_LT (SLit 31) (SOff 32 0) HS0
    ltac:(rewrite HD32; cbn [sv_denot]; rewrite evo_dep_lt by (change (Z.of_nat PjGrammar.MAXD) with 32; lia);
      apply Z.ltb_lt; exact Href)) as HS.
  clear HS0.
  destruct o; paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EV_EXIT).
  all: lazymatch goal with
    | |- awr_ok _ _ _ _ _ _ _ _ _ =>
        intros z Hz; left; apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID);
        apply (evo_H_W4 a E z U19 U9); left; exact Hz
    | |- SRr _ _ _ _ =>
        pmkst HS;
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))]
          EVO_HKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK;
        cbn [ms_regs restrict] in HK;
        evo_s10 HS (ea_q a) EQ19 EQ24 Q26;
        lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
          replace pc with (BASE + EVO_PC EV_EXIT) by (vm_compute; reflexivity) end;
        eapply (evo_refuse_post a fxc W regs mem md ly St Hp k i1);
        [ exact HPRE | exact HFX | exact HKIND | exact Href | exact HJ
        | exact (fun x Hx => HFr x (fun Hw => Hx (evo_H_W4 a E (bv_unsigned x) U19 U9 (or_introl Hw)))) | exact HG
        | replace (ea_q a) with (ea_q a + 0) by lia; evo_chunk HS 0%nat 0 U19
        | evo_chunk HS 2%nat 16 U19
        | evo_chunk HS 4%nat 32 U19
        | unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]
        | rewrite HK by (cbv; tauto); reflexivity
        | rewrite HK by (cbv; tauto); reflexivity
        | exact HMN ]
    end.
- destruct (Z.eq_dec (ea_v a) 0) as [Hv0|Hv0].
  + (* (J0) v = 0: no node, s7 seated as 0 (`beqz s7` taken); 0x834bc -> 0x836d4 *)
    pose proof (evo_entry a fxc W regs mem md ly St Hp k i1 (if o then 123 else 91) (SLit 0) [] [] HPRE HKIND
      ltac:(cbn [sv_denot]; rewrite H23, Hv0; reflexivity) eq_refl (Forall_nil _) HPD0 I) as HS0. fold E in HS0.
    pose proof (evo_add_cond _ _ _ _ BC_GE (SLit 31) (SOff 32 0) HS0
      ltac:(rewrite HD32; cbn [sv_denot]; rewrite evo_dep_ge by (change (Z.of_nat PjGrammar.MAXD) with 32; lia);
        apply Z.leb_le; lia)) as HS.
    clear HS0.
    destruct o; paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EVO_J).
    all: lazymatch goal with
      | |- awr_ok _ _ _ _ _ _ _ _ _ =>
          intros z Hz; left; apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID);
          apply (evo_H_W4 a E z U19 U9); left; exact Hz
      | |- SRr _ _ _ _ =>
          pmkst HS;
          pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))]
            EVO_HKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK;
          cbn [ms_regs restrict] in HK;
          evo_s10 HS (ea_q a) EQ19 EQ24 Q26; prreg HS (21%bv : bv 5) Q21;
          prreg HS (23%bv : bv 5) Q23;
          lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
            replace pc with (BASE + EVO_PC EVO_J) by (vm_compute; reflexivity) end;
          eapply (evo_head_post a fxc W regs mem md ly St Hp k i1 _ _ _ _ (ea_dl a));
          [ exact HPRE | exact HFX | exact HKIND | lia | exact HJ
          | exact (fun x Hx => HFr x (fun Hw => Hx (evo_H_W4 a E (bv_unsigned x) U19 U9 (or_introl Hw)))) | exact HG
          | replace (ea_q a) with (ea_q a + 0) by lia; evo_chunk HS 0%nat 0 U19
          | evo_chunk HS 2%nat 16 U19
          | evo_chunk HS 4%nat 32 U19
          | evo_chunk HS 5%nat 48 U9
          | let Hc := fresh "Hc" in evo_cv HS 5%nat 56 Hc;
            cbn [base_val ms_mem restrict ew ewset Nat.eqb] in Hc; rewrite U9 in Hc; apply Hc; clear Hc;
            [ apply (evo_shx_den _ 19 16 (ea_q a)); [cbn [ew ewset Nat.eqb]; exact EQ19 | lia | lia | cbn [ew ewset Nat.eqb]; exact EQ24]
            | evo_rng | cbv [Z.of_N]; lia ]
          | cbn [PjGrammar.closer]; evo_chunk HS 5%nat 64 U9
          | unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]
          | intros r Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; first [rewrite Q21, H21; reflexivity | apply HK; cbv; tauto]
          | rewrite Q23; unfold ev_v', ev_tv; rewrite Hv0; reflexivity
          | exact Hdl0
          | split; [exact Hdl0 | split; [intros H; left; exact H | intros [H|(Hv & _)]; [exact H | contradiction]]]
          | exact HMN ]
      end.
  + destruct (evo_Rv_ok a ly St Hp W mem md k i1 _ regs HPRE HKIND Hv0) as (HRv & _ & Hvb).
    destruct HT as [HT|(_ & _ & Hra56 & _)]; [contradiction|].
    unfold EVO_TOP in Hvb.
    pose proof (evo_entry a fxc W regs mem md ly St Hp k i1 (if o then 123 else 91) (SOff 23 0) [evo_Rv] evo_vf23 HPRE HKIND
      H23s eq_refl ltac:(apply Forall_cons; [exact HRv | apply Forall_nil]) (HPDv Hv0)
      ltac:(cbn [evo_vf23 atoms_ok];
        split; [apply (evo_atom_ok _ 23 (ea_v a)); [exact EQ23 | lia | unfold EVO_TOP; lia | apply Z.mod_1_r | lia]|];
        split; [apply (evo_atom_ok _ 35 (PjTree.tag (ea_t a))); [exact EQ35 | lia | lia | apply Z.mod_1_r | lia]|];
        exact I)) as HS0. fold E in HS0.
    pose proof (evo_add_cond _ _ _ _ BC_GE (SLit 31) (SOff 32 0) HS0
      ltac:(rewrite HD32; cbn [sv_denot]; rewrite evo_dep_ge by (change (Z.of_nat PjGrammar.MAXD) with 32; lia);
        apply Z.leb_le; lia)) as HS1.
    clear HS0.
    destruct (Z.eq_dec (PjTree.tag (ea_t a)) (if o then 6 else 5)) as [Htag|Htag].
    * (* (J1) v's tag is the container's: s7 = v, differs kept *)
      pose proof (evo_add_cond _ _ _ _ BC_EQ (SOff 35 0) (SLit (if o then 6 else 5)) HS1
        ltac:(rewrite (evo_Uoff E 35 0 _ EQ35) by lia; cbn [sv_denot]; rewrite Z.add_0_r; cbn [branch_taken];
          unfold bv_eqb; rewrite !unsigned_lit_small by (destruct o; lia); apply Z.eqb_eq; exact Htag)) as HS.
      clear HS1.
      destruct o; paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EVO_J).
      all: lazymatch goal with
        | |- range_addressable _ _ _ _ =>
            cbn [ms_mem YK11.mkst]; rewrite <- aview_rd_of, UBx, (U_atom E 23 (ea_v a) EQ23) by lia;
            apply (range_addressable_sub _ _ (ea_v a) 56); [exact Hra56 | lia | lia]
        | |- awr_ok _ _ _ _ _ _ _ _ _ =>
            intros z Hz; left; apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID);
            apply (evo_H_W4 a E z U19 U9); right; exact Hz
        | |- SRr _ _ _ _ =>
            pmkst HS;
            pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))]
              (23%bv :: EVO_HKEPT) HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK;
            cbn [ms_regs restrict] in HK;
            evo_s10 HS (ea_q a) EQ19 EQ24 Q26; prreg HS (21%bv : bv 5) Q21;
            lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
              replace pc with (BASE + EVO_PC EVO_J) by (vm_compute; reflexivity) end;
            eapply (evo_head_post a fxc W regs mem md ly St Hp k i1 _ _ _ _ (ea_dl a));
            [ exact HPRE | exact HFX | exact HKIND | lia | exact HJ
            | exact (fun x Hx => HFr x (fun Hw => Hx (evo_H_W4 a E (bv_unsigned x) U19 U9 (or_intror Hw)))) | exact HG
            | replace (ea_q a) with (ea_q a + 0) by lia; evo_chunk HS 0%nat 0 U19
            | evo_chunk HS 2%nat 16 U19
            | evo_chunk HS 4%nat 32 U19
            | evo_chunk HS 5%nat 48 U9
            | let Hc := fresh "Hc" in evo_cv HS 5%nat 56 Hc;
              cbn [base_val ms_mem restrict ew ewset Nat.eqb] in Hc; rewrite U9 in Hc; apply Hc; clear Hc;
              [ apply (evo_shx_den _ 19 16 (ea_q a)); [cbn [ew ewset Nat.eqb]; exact EQ19 | lia | lia | cbn [ew ewset Nat.eqb]; exact EQ24]
              | evo_rng | cbv [Z.of_N]; lia ]
            | cbn [PjGrammar.closer]; evo_chunk HS 5%nat 64 U9
            | unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]
            | intros r Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; first [rewrite Q21, H21; reflexivity | apply HK; cbv; tauto]
            | rewrite HK by (cbv; tauto); rewrite H23; unfold ev_v', ev_tv; rewrite Htag, Z.eqb_refl, orb_true_r; reflexivity
            | exact Hdl0
            | split; [exact Hdl0 | split; [intros H; left; exact H | intros [H|(_ & [Hf|(j & Hj & _)])]; [exact H | | cbn [length] in Hj; lia]]];
              unfold ev_tv in Hf; rewrite Htag, Z.eqb_refl, orb_true_r in Hf; discriminate Hf
            | exact HMN ]
        end.
    * (* (J2) another type: s7 := 0 and in->differs := 1 (C :247-251), the ASan check of q + 32 by SH *)
      pose proof (evo_add_cond _ _ _ _ BC_NE (SOff 35 0) (SLit (if o then 6 else 5)) HS1
        ltac:(rewrite (evo_Uoff E 35 0 _ EQ35) by lia; cbn [sv_denot]; rewrite Z.add_0_r; cbn [branch_taken];
          unfold bv_eqb; rewrite !unsigned_lit_small by (destruct o; lia); apply negb_true_iff, Z.eqb_neq; exact Htag)) as HS.
      clear HS1.
      destruct o; paj_run_to_tok_x_inv RUNTOI HS HJ HSOK HMN EVO_Bspan (EVO_PC EVO_J).
      all: lazymatch goal with
        | |- range_addressable _ _ _ _ =>
            cbn [ms_mem YK11.mkst]; rewrite <- aview_rd_of, UBx, (U_atom E 23 (ea_v a) EQ23) by lia;
            apply (range_addressable_sub _ _ (ea_v a) 56); [exact Hra56 | lia | lia]
        | |- awr_ok _ _ _ _ _ _ _ _ _ =>
            intros z Hz; left; apply (evo_W4_stk a ly St Hp W mem md k _ _ _ z HPRE HMID);
            apply (evo_H_W4 a E z U19 U9); right; exact Hz
        | |- SRr _ _ _ _ =>
            pmkst HS;
            pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 (ea_dep a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a))]
              EVO_HKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK;
            cbn [ms_regs restrict] in HK;
            evo_s10 HS (ea_q a) EQ19 EQ24 Q26; prreg HS (21%bv : bv 5) Q21;
            prreg HS (23%bv : bv 5) Q23;
            lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom) ?d) _ =>
              replace pc with (BASE + EVO_PC EVO_J) by (vm_compute; reflexivity) end;
            eapply (evo_head_post a fxc W regs mem md ly St Hp k i1 _ _ _ _ 1);
            [ exact HPRE | exact HFX | exact HKIND | lia | exact HJ
            | exact (fun x Hx => HFr x (fun Hw => Hx (evo_H_W4 a E (bv_unsigned x) U19 U9 (or_intror Hw)))) | exact HG
            | replace (ea_q a) with (ea_q a + 0) by lia; evo_chunk HS 0%nat 0 U19
            | evo_chunk HS 2%nat 16 U19
            | evo_chunk HS 4%nat 32 U19
            | evo_chunk HS 5%nat 48 U9
            | let Hc := fresh "Hc" in evo_cv HS 5%nat 56 Hc;
              cbn [base_val ms_mem restrict ew ewset Nat.eqb] in Hc; rewrite U9 in Hc; apply Hc; clear Hc;
              [ apply (evo_shx_den _ 19 16 (ea_q a)); [cbn [ew ewset Nat.eqb]; exact EQ19 | lia | lia | cbn [ew ewset Nat.eqb]; exact EQ24]
              | evo_rng | cbv [Z.of_N]; lia ]
            | cbn [PjGrammar.closer]; evo_chunk HS 5%nat 64 U9
            | unfold ev_regs; repeat split; first [exact Q26 | rewrite HK by (cbv; tauto); assumption]
            | intros r Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; first [rewrite Q21, H21; reflexivity | apply HK; cbv; tauto]
            | rewrite Q23; unfold ev_v', ev_tv; rewrite (proj2 (Z.eqb_neq _ _) Hv0), (proj2 (Z.eqb_neq _ _) Htag); reflexivity
            | right; reflexivity
            | split; [right; reflexivity | split; [intros _; right; split; [exact Hv0 | left] | intros _; reflexivity]];
              unfold ev_tv; rewrite (proj2 (Z.eqb_neq _ _) Hv0), (proj2 (Z.eqb_neq _ _) Htag); reflexivity
            | exact HMN ]
        end.
Qed.

(* PIECE 6 at the interface's statement, over this Section's instances (cp generic) *)
Lemma evo_items_open : forall a fxc W regs mem md ly S Hp k i1 c,
  EV_PRE a -> @ev_fx fx fxc -> EV_KIND a W regs mem md ly S Hp k i1 c -> (c = 123 \/ c = 91) ->
  SRr SEGS W (ev_cfg (PA := PI_prog_A) fxc regs EV_ITEMS mem md) (evo_post a fxc (c =? 123)).
Proof.
intros a fxc W regs mem md ly S Hp k i1 c HPRE HFX HKIND [->| ->].
- exact (evo_head a fxc W regs mem md ly S Hp k i1 true HPRE HFX HKIND).
- exact (evo_head a fxc W regs mem md ly S Hp k i1 false HPRE HFX HKIND).
Qed.

End f.
End d.

(* ======== PIECE 6, ev_items_open (S8aIface.v:345), at the instances of the finished pieces 9 / 10 (S8aClose.v) and
   of WalkS8a's composition: L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A, cp := CfParams_preset. The walk
   ev_items_open_holds_zb takes the per-byte stack zero-shadow law (Section f's EV_ZSH_BYTE, S8aClose.v's s8c_ZB),
   verbatim; ev_items_open_holds cites it as AR_laws_x's field alx_zshadow_byte ======== *)
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Lemma ev_items_open_holds_zb :
  (forall ly S Hp (W : world SEGS) mem md z, ARx ly S Hp W mem md -> ly_stk_lo ly <= z < ly_stk_hi ly ->
     aview SEGS (w_H W) mem (SHADOW_OFF + z / 8) = Some 0) ->
  ev_items_open_spec (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof.
intros ZB a fxc W regs mem md ly S Hp k i1 c HPRE HFX HKIND Hc.
exact (evo_items_open (cp := CfParams_preset) B ARx SK LAWS ZB a fxc W regs mem md ly S Hp k i1 c HPRE HFX HKIND Hc).
Qed.

(* PIECE 6 under LAWS only: the premise of ev_items_open_holds_zb is AR_laws_x's field alx_zshadow_byte. *)
Lemma ev_items_open_holds :
  ev_items_open_spec (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof. exact (ev_items_open_holds_zb (alx_zshadow_byte SEGS B ARx LAWS)). Qed.
End z.
