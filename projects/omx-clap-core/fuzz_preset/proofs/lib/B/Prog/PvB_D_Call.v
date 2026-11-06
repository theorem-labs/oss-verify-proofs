(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PvB_NA.v, with its module paths and module names changed; 69 of its 92 lines of code are new or changed and 936 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c (segment D): the CALL-STATE contract between
   the dispatch walk (PvB_D.v pvD_holds, which runs from the cut C1 to each call) and the three call arms (one file
   each), so the arms are proved apart. pvd_cs is the state at a callee's entry (after `jal`): parse_value's frame and
   journal as at the cut C1 (pv_body at the call memory), the C1 reader facts (pv_chain, pv_reader0 at the C1 memory
   memC) and what the stretch from C1 to the call changed (only the node's type word [v, v + 4), and presence only
   grows), and the memory normal form at the call memory (YAkMemnorm.memnorm, which every run from C1 carries; the
   callee's m-form post keeps it to the exit cut). The arm goals state, per callee, the registers the code sets and
   the conclusion with the exit cut as the continuation: plain SRr .. pv_FINK for the literal (it frees nothing), and
   the record's relation YA0nH.SRr' segs RZ_cf .. pv_FINAL for parse_string and parse_items, whose texts conclude so
   (they free); pvd_kxR_of lifts the dispatch's plain continuation to the latter (YGcfRhLift.ra_rh_of_SRr).
   Listing offsets (DERIVED: B pc - B_prog_base 0x816cc): 20348 = 0x86648 (literal's return), 20116 = 0x86560
   (parse_string's return), 20320 = 0x8662c (parse_items' return). The literal words (.rodata, in the read-only band
   A_OBJ 2 = 0x10000; DERIVED offsets): "true" .str.6 0x21460 -> 70752, "false" .str.7 0x21480 -> 70784, "null"
   .str.8 0x214a0 -> 70816; the types the code passes (a2): true 2, false 1, null 0 (PjTree.tag).
   Rule 24: proves no function (kind: segment interface). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfRhLift.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.

(* the return addresses (listing offsets) *)
Definition AF_pv_lit_ret : Z := 20348.   (* 0x86648 *)
Definition AF_pv_str_ret : Z := 20116.   (* 0x86560 *)
Definition AF_pv_items_ret : Z := 20320. (* 0x8662c *)
(* the literal word each literal byte selects, as its offset in the read-only band A_OBJ 2, and the type passed *)
Definition pvd_word_off (c : Z) : Z := if c =? 116 then 70752 else if c =? 102 then 70784 else 70816.
Definition pvd_lit_ty (c : Z) : Z := if c =? 116 then 2 else if c =? 102 then 1 else 0.
Definition pvd_lit_word (c : Z) : list Z :=
  if c =? 116 then PjGrammar.w_true else if c =? 102 then PjGrammar.w_false else PjGrammar.w_null.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* the state at a callee's entry: registers (s-registers as at C1, ra the return address), parse_value's frame and
   journal at the call memory mem, the C1 reader facts at the C1 memory memC, mem against memC, and the memory normal
   form at mem *)
Definition pvd_cs (en : PvEnt) (ret p1 Y fa fl pos : Z) (lyc : alayout) (Sc : astate) (k : Z) (W' : world SEGS)
    (memC : word -> option byte) (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model) : Prop :=
  pv_keep_regs en regs Y fa /\ getr regs 9 = w64 Y /\ getr regs 19 = w64 (pe_v en) /\
  getr regs 20 = w64 (pe_q en) /\ getr regs 24 = w64 (SHADOW_OFF + pe_q en / 8) /\
  getr regs 1 = Z_to_bv 64 (BASE + ret) /\
  pv_body (SK := SK) B ARx en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W' mem mdc k /\
  pv_chain en lyc W' memC Y /\
  pv_reader0 B en pos p1 lyc Sc W' memC /\
  (forall x : word, ~ (pe_v en <= bv_unsigned x < pe_v en + 4) ->
     mrestrict (w_H W') mem x = mrestrict (w_H W') memC x) /\
  (forall a, apresent (w_H W') memC a -> apresent (w_H W') mem a) /\
  YAkMemnorm.memnorm SEGS mem.

(* the exit continuation every arm closes with: plain (the literal arm, the dispatch) and in the record's relation (the
   string and container arms) *)
Definition pvd_kx (en : PvEnt) : Prop :=
  forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en).
Definition pvd_kxR (en : PvEnt) : Prop :=
  forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 ->
    YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg ms2 md2) (pv_FINAL B ARx en).
Lemma pvd_kxR_of : forall en, pvd_kx en -> pvd_kxR en.
Proof.
intros en KX W2 ms2 md2 HX. apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf). exact (KX W2 ms2 md2 HX).
Qed.

(* 't' / 'f' / 'n': literal(q, word, type, v) at B 0x86644, returning to 0x86648 (`mv s5, a0`, then the exit) *)
Definition pvd_lit_goal : Prop :=
  forall en c y Y fa fl pos lyc Sc k W' regs mem mdc,
  pv_pre B ARx en ->
  PjGrammar.skip (pe_rest en) = c :: y -> (c = 116 \/ c = 102 \/ c = 110) ->
  pvd_cs en AF_pv_lit_ret (pe_text en + pe_len en - Z.of_nat (length (c :: y))) Y fa fl pos lyc Sc k W' mem
    regs mem mdc ->
  getr regs 10 = w64 (pe_q en) -> getr regs 11 = w64 (VAL (A_OBJ 2) + pvd_word_off c) ->
  getr regs 12 = w64 (pvd_lit_ty c) -> getr regs 13 = w64 (pe_v en) ->
  pvd_kx en ->
  SRr SEGS W' (mkCfg (@YK11.mkst fx0 regs (Z_to_bv 64 (SIGMA AS_literal)) mem (YK11.seg_rom SEGS)) mdc)
    (pv_FINK B ARx en).

(* the double quote: v->type = 4 stored (B 0x86554), parse_string(q) at 0x8655c, returning to 0x86560 (v->str = the
   result at v + 16 with its ASan check, s5 = (res != 0) - 1, then the exit) *)
Definition pvd_str_goal : Prop :=
  forall en y Y fa fl pos lyc Sc k W' memC regs mem mdc,
  pv_pre B ARx en ->
  PjGrammar.skip (pe_rest en) = 34 :: y ->
  pvd_cs en AF_pv_str_ret (pe_text en + pe_len en - Z.of_nat (length (34 :: y))) Y fa fl pos lyc Sc k W' memC
    regs mem mdc ->
  val_mem SEGS (mrestrict (w_H W') mem) (pe_v en) 4 4 ->
  getr regs 10 = w64 (pe_q en) ->
  pvd_kxR en ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W'
    (mkCfg (@YK11.mkst fx0 regs (Z_to_bv 64 (SIGMA AS_parse_string)) mem (YK11.seg_rom SEGS)) mdc)
    (pv_FINAL B ARx en).

(* '{' / '[': parse_items(q, v, 1 / 0) at B 0x86628, returning to 0x8662c (`j 86648`, `mv s5, a0`, the exit); the
   float state after it is the callee's (YCbqGwild.aj_call_xWFbR). The callee's text is a premise AT THE ENTRY'S DEPTH only
   (pe_d en; parse_items is called at the same depth), so the pair closes by lib/A/VrdUnit.v's depth induction *)
Definition pvd_items_goal : Prop :=
  forall en c y Y fa fl pos lyc Sc k W' regs mem mdc,
  pv_pre B ARx en ->
  (forall CTX CTX0 CW, tparse_items_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK (pe_d en) CTX CTX0 CW) ->
  PjGrammar.skip (pe_rest en) = c :: y -> (c = 123 \/ c = 91) ->
  pvd_cs en AF_pv_items_ret (pe_text en + pe_len en - Z.of_nat (length (c :: y))) Y fa fl pos lyc Sc k W' mem
    regs mem mdc ->
  getr regs 10 = w64 (pe_q en) -> getr regs 11 = w64 (pe_v en) -> getr regs 12 = w64 (if c =? 123 then 1 else 0) ->
  pvd_kxR en ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W'
    (mkCfg (@YK11.mkst fx0 regs (Z_to_bv 64 (SIGMA AS_parse_items)) mem (YK11.seg_rom SEGS)) mdc)
    (pv_FINAL B ARx en).

End c.
