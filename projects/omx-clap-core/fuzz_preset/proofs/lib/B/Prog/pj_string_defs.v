(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the CUTS of pj_string's image-B walk (fuzz_preset asan-ubsan, B entry B_entry_pj_string,
   49 instructions; preset_file.c :406-411). STATEMENTS ONLY: the entry record, the kit's premises of tpj_string_specX
   (lib/A/PRH_FnPj.v: ENTRY-keyed,
   rp_* binders, position and run premise at entry; no DW (prh_univ_closure B CTX0); the run keyed on
   ReaderRes.jr_strtod (no rp_sm); the entry premise PRH_Base.prh_cons_from; the live premise guarded by the call's
   success flag, `cnt <> fail -> blocks_bytes S + LIVE_pj_string |cs| <= LIVE_MAX`; the post conjunct DEAD-PJSTRING
   `cnt <> fail -> a <> 0`), the walk's own post (the position from fuzz_strdup's post implication applied at the entry
   position, and the DEAD conjunct from fuzz_strdup's OUTCOME conjunct at the same position) and the post with its
   run and prh_cons_from premises, the two cut states, the segment statements (each proved by its own file) and the
   MARKED image facts the segments take. The walk keeps the run's strtod model a parameter (js_sm); the top
   instantiates it at ReaderRes.jr_strtod. lib/B/Prog/pj_string_top.v composes them into the text.
   proves no function (kind: statement text).
   The text carries the three premises this walk found missing at a3bdeca3920: the live-set bounds through the
   model-run position PresetRoomPos.iface_room_pos (the walk derives fuzz_strdup's sec_cnt / ccnt24 premises from it by
   PresetRoomCounts.v counts_of_room_pos_rl, in the top: pjs_cnt), `v < YM05.alloc_ceiling`, and prh_head_wide. The walk's goal
   is fpostWm: pjs_Q (the position at the return, from fuzz_strdup's post implication at pj_string's entry position
   js_i) and the memnorm keep (PRH_Base.v fQmn); the keep is carried through the walk in pjs_inv (the runners' memory
   invariant, YC80x.v). The run premise (prh_run_at .. (prhPj_string_evs ..), pjs_run) and prh_cons_from (pjs_cons)
   turn pjs_Q into the post pjs_Q_K0 (pj_string_top.v pjs_Q_K0_of_Q).
   The body (whole-program listing lib/B/Listing_prog.v, slots B_prog_slot AS_pj_string ..  + 48), pc offsets from
   pj_string's entry (DERIVED: slot differences times 4):
     +0x00 .. +0x10  sp -= 32; ra, s0, s1, s2 saved at sp+24 / +16 / +8 / +0
     +0x14 .. +0x20  s1 := s; s2 := the shadow offset (GOT slot of __asan_shadow_memory_dynamic_address, then the cell)
     +0x24 .. +0x30  s0 := v; memset (v, 0, 56)                               return site PJS_M1 (+0x34)
     +0x34 / +0x3c   UBSan NULL / alignment checks on v (`unimp` traps)        NOT TAKEN (4096 <= v, v mod 8 = 0)
     +0x40 .. +0x4c  ASan check of the 4-byte store at v                       NOT TAKEN (v's shadow)
     +0x50 / +0x54   v->type := 4
     +0x58 .. +0x64  s = NULL: s1 := the image's "" literal (PJS_LIT); a0 := s1   CUT pjs_C1 at the `jal fuzz_strdup` (+0x68)
     +0x6c           s0 := v + 16                                              CUT pjs_C2 at +0x6c (the return site)
     +0x70 .. +0x7c  ASan check of the 8-byte store at v + 16                  NOT TAKEN
     +0x80 .. +0x8c  a0 := (str != 0) - 1; v->str := str
     +0x90 .. +0xa4  restore ra, s0, s1, s2; sp += 32; ret
   Callee texts: __asan_memset = YGcallMxmn.v aintrin_realizes_xm OSet (the m-form: the plain text plus the memnorm
   keep); fuzz_strdup = the tfuzz_strdup_specX (lib/A/PRH_FnAlloc.v:517-558 at d607d12e4b0f: the POST-IMPLICATION
   form, no position and no run premise at entry, each arm's position transfer an implication over the model run, and
   THE OUTCOME conjunct; a Section hypothesis, never unfolded, its post read by name). Every name is stated at
   PA := PI_prog_B, the whole-range instance. Numerals: 32 / 56 / 24 / 16 / 8 / 4 (LENGTH: frame, struct, slots, field
   offsets); 52 / 104 / 108 (DERIVED pc offsets, slot differences times 4: memset's return site, the
   `jal fuzz_strdup`, its return site);
   24 (DERIVED: the slot of the literal's `addi`); register numbers (WORD). No ADDRESS: PJS_LIT is read from the
   listing's PAddHi row. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
(* the node bytes pjs_bytes: the one copy, for both images *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ---- image B's numbers: the one pin block of this walk (every other file reads these names) ---- *)
#[local] Existing Instance prh_img_B.
(* pc offsets from pj_string's entry (DERIVED from the listing: slot index differences times 4) *)
Definition PJS_PC : Z := B_prog_sigma AS_pj_string - B_prog_base.
Definition PJS_M1 : Z := PJS_PC + 52.    (* the return site of `jal __asan_memset` *)
Definition PJS_C1 : Z := PJS_PC + 104.   (* the `jal fuzz_strdup` *)
Definition PJS_C2 : Z := PJS_PC + 108.   (* its return site *)
Definition PJS_FR : Z := 32.             (* pj_string's own frame (prh_img_B's pi_frame F_pj_string) *)
(* the image's "" literal pj_string passes for s = NULL: the `addi` of its auipc pair, read from the listing *)
Definition PJS_LIT : Z :=
  match nth (B_prog_slot AS_pj_string + 24) B_prog_listing (PW 0) with
  | PAddHi _ _ _ j off => B_prog_val j + off
  | _ => 0
  end.
Definition pjs_sarg (s : Z) : Z := if s =? 0 then PJS_LIT else s.
(* the callee-saved registers pj_string never writes: gp, tp, s3 .. s11 (s0, s1, s2 are restored by the epilogue) *)
Definition PJS_KEPT : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).

(* the callee texts: __asan_memset's intrinsic text in its m-form and the fuzz_strdup text, at the entry float state
   (pj_string's text is fpostWm: no float change; fuzz_strdup's text is at fx) *)
Definition pjs_texts : Prop :=
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset) /\
  tfuzz_strdup_specX (PA := PA) B ARx SK.

(* ---- the entry ---- *)
Record PjsEnt : Type := MkPjsEnt {
  js_ly : alayout; js_S : astate; js_Hp : list Z; js_W : world SEGS; js_regs : bvmap 5 word;
  js_mem : word -> option byte; js_md : Model; js_ch : list (Z * Z * Z);
  js_d : Z; js_v : Z; js_s : Z; js_cs : list Z; js_Lam : list (Z * Z);
  js_peak : Z; js_cnt : Z; js_fail : Z; js_ran : Z; js_most : Z; js_own : Z;
  (* the model-run position of the text (PresetRoomPos.iface_room_pos's parameters) *)
  js_sm : list Z -> Z * Z; js_x : list Z; js_os : list (option nat * option nat * option nat); js_i : nat;
  js_H0 : list Z; js_hist : list YG00.chunk }.
Definition js_sp0 (en : PjsEnt) : Z := spZ (js_regs en).
Definition js_sp1 (en : PjsEnt) : Z := js_sp0 en - PJS_FR.
Definition js_len (en : PjsEnt) : Z := Z.of_nat (length (js_cs en)).

(* The premises of tpj_string_specX (lib/A/PRH_FnPj.v:1996-2037, with `(length rp_os <= 4)%nat` at :2004) but its prh_cons_from
   and run premises (pjs_cons / pjs_run, below), in its order, at the entry float state fx, over the record's strtod model js_sm (the kit's
   ReaderRes.jr_strtod at the top). The live premise is the tip's, guarded by the call's success flag (cnt <> fail),
   as fuzz_strdup's is (pj_string_seg_call.v hands it on under the same guard). *)
Definition pjs_pre (CTX0 : list (list Z)) (en : PjsEnt) : Prop :=
  let ly := js_ly en in let S := js_S en in let Hp := js_Hp en in let W := js_W en in let regs := js_regs en in
  let mem := js_mem en in let md := js_md en in let ch := js_ch en in let d := js_d en in let v := js_v en in
  let s := js_s en in let cs := js_cs en in let Lam := js_Lam en in
  fpre (PA := PA) B ARx STK_pj_string ly S Hp W regs mem md ch /\ prh_univ_closure B CTX0 /\ room_live_cf S /\
  PresetRoomPos.iface_room_pos (js_sm en) (js_x en) (js_os en) (js_i en) (js_H0 en) (js_hist en) S /\
  (length (js_os en) <= 4)%nat /\
  getr regs 10 = w64 v /\ getr regs 11 = w64 s /\
  fwin (PA := PA) ly W regs mem d /\ prhPj_slot (PA := PA) B STK_pj_string d ly S Lam W regs mem v /\
  v < YM05.alloc_ceiling /\
  prh_head_wide /\
  (s = 0 /\ cs = [] \/
   s <> 0 /\ cstr_ok (PA := PA) W mem s cs /\ kept_at (PA := PA) B Lam s (Z.of_nat (length cs) + 1) /\
   (s + Z.of_nat (length cs) + 1 <= v \/ v + 56 <= s)) /\
  Z.of_nat (length cs) + 1 + cf_head < cf_malloc_max /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) /\
  (js_cnt en <> js_fail en -> blocks_bytes S + LIVE_pj_string (Z.of_nat (length cs)) <= LIVE_MAX).

(* fuzz_strdup's live-set premises at the entry allocator state (the call's state: memset keeps the allocator); the
   top derives them from pjs_pre's iface_room_pos by counts_of_room_pos_rl (lib/Spec/PresetRoomCounts.v) *)
Definition pjs_cnt (en : PjsEnt) : Prop :=
  YGcfRoomLive.sec_cnt (js_S en) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (js_S en) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* The kit's run premise (PRH_FnPj.v:1261 at d607d12e4b0f) and its prh_cons_from premise (:1234), over the entry's values *)
Definition pjs_run (en : PjsEnt) : Prop :=
  prh_run_at (js_sm en) (js_x en) (js_os en) (js_i en)
    (prhPj_string_evs (Z.of_nat (length (js_cs en))) (js_cnt en) (js_fail en)).
Definition pjs_cons (en : PjsEnt) : Prop :=
  PRH_Base.prh_cons_from (js_sm en) (js_x en) (js_os en) (js_i en)
    (length (prhPj_string_evs (Z.of_nat (length (js_cs en))) (js_cnt en) (js_fail en))).

(* the walk's own post body: the text's, with the position as fuzz_strdup's post implication (PRH_FnAlloc.v
   tfuzz_strdup_specX at d607d12e4b0f) gives it when applied at pj_string's entry position (js_i, js_hist, pjs_pre):
   a = 0 gives some history at js_i (E = []); a <> 0 with the run's HMal at js_i gives some history at S js_i
   (E = [HMal ..], prh_run_at_one); and DEAD-PJSTRING as fuzz_strdup's OUTCOME conjunct gives it at the same
   position: with no chosen failure (cnt <> fail), the kit's run and prh_cons_from premises put the HMal at js_i as a
   consumer event, and the strdup granted; over the entry's values *)
Definition pjs_Q (en : PjsEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  let cs := js_cs en in let Lam := js_Lam en in let v := js_v en in
  room_live_cf S' /\
  exists a,
  (a = 0 -> exists hist', PresetRoomPos.iface_room_pos (js_sm en) (js_x en) (js_os en) (js_i en) (js_H0 en) hist' S') /\
  (a <> 0 -> nth_error (PresetRun.hruns (js_sm en) (js_x en) (js_os en)) (js_i en) =
               Some (PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)) ->
     exists hist', PresetRoomPos.iface_room_pos (js_sm en) (js_x en) (js_os en) (Datatypes.S (js_i en)) (js_H0 en)
       hist' S') /\
  (js_cnt en <> js_fail en -> pjs_run en -> pjs_cons en -> a <> 0) /\
  prh_alloc_post (PA := PA) B (Z.of_nat (length cs) + 1) (js_ly en) (js_S en) (js_Hp en) (js_W en) Lam
      (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) a ly' S' Hp' W' mem' /\
  (a <> 0 -> getr regs' 10 = w64 0 /\
     pj_nodeR SEGS (rdW W' mem') (prh_lin ((a, Z.of_nat (length cs) + 1) :: Lam)) v (PjTree.JStr cs)
       [(a, Z.of_nat (length cs) + 1)]) /\
  (a = 0 -> getr regs' 10 = w64 (-1) /\ pj_rwR SEGS (rdW W' mem') v /\
     bytes_at (PA := PA) W' mem' v ([4; 0; 0; 0] ++ repeat 0 52) /\
     pj_fdR SEGS (rdW W' mem') (prh_lin Lam) 0 v []).

(* The post body of tpj_string_specX (PRH_FnPj.v:1263-1286 at d607d12e4b0f), verbatim, over the entry's values:
   the walk's post gives the text's under the run and prh_cons_from premises (pj_string_top.v pjs_Q_K0_of_Q). *)
Definition pjs_Q_K0 (en : PjsEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  let cs := js_cs en in let Lam := js_Lam en in let v := js_v en in
  room_live_cf S' /\
  exists a, prh_alloc_post (PA := PA) B (Z.of_nat (length cs) + 1) (js_ly en) (js_S en) (js_Hp en) (js_W en) Lam
      (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) a ly' S' Hp' W' mem' /\
  (js_cnt en <> js_fail en -> a <> 0) /\
  (a <> 0 \/ js_cnt en = js_fail en ->
     exists hist', PresetRoomPos.iface_room_pos (js_sm en) (js_x en) (js_os en)
       (js_i en + length (prhPj_string_evs (Z.of_nat (length cs)) (js_cnt en) (js_fail en)))%nat (js_H0 en) hist' S') /\
  (a <> 0 -> getr regs' 10 = w64 0 /\
     pj_nodeR SEGS (rdW W' mem') (prh_lin ((a, Z.of_nat (length cs) + 1) :: Lam)) v (PjTree.JStr cs)
       [(a, Z.of_nat (length cs) + 1)]) /\
  (a = 0 -> getr regs' 10 = w64 (-1) /\ pj_rwR SEGS (rdW W' mem') v /\
     bytes_at (PA := PA) W' mem' v ([4; 0; 0; 0] ++ repeat 0 52) /\
     pj_fdR SEGS (rdW W' mem') (prh_lin Lam) 0 v []).

(* the walk's goal: its own post (fpostWm: fpostW with the memnorm keep, PRH_Base.v fQmn) *)
Definition pjs_FIN (en : PjsEnt) : world SEGS -> config -> Prop :=
  fpostWm (PA := PA) B ARx SK STK_pj_string (js_d en) [(js_v en, js_v en + 56)] (js_regs en) (js_ly en) (js_S en)
    (js_Hp en) (js_W en) (js_mem en) (js_md en) (pjs_Q en).

(* the configuration at a cut (the entry float state: nothing in pj_string or its callees' texts moves it) *)
Definition pjs_cfg (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS)) md.

(* ---- what holds at both cuts: the journal from the entry (allocator state ly S Hp W), the caller window, pj_string's
   frame (sp1 = sp0 - 32, the four saved words), s0 = v, s2 = the shadow offset, the untouched callee-saved registers,
   the read-only view, v's bytes with str 0, writable, addressable, and the memnorm keep from the entry memory ---- *)
Definition pjs_inv (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  let v := js_v en in
  AJ (STK_pj_string + js_d en) (js_sp0 en + js_d en) [(v, v + 56)]
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp W mem md k /\
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (js_W en)) (js_mem en) a) /\
  spZ regs = js_sp1 en /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 24) 8 (raZ (js_regs en)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 16) 8 (s0Z (js_regs en)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 8) 8 (bv_unsigned (getr (js_regs en) 9)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en) 8 (bv_unsigned (getr (js_regs en) 18)) /\
  getr regs 8 = w64 v /\ getr regs 18 = w64 SHADOW_OFF /\
  (forall r, In r PJS_KEPT -> getr regs r = getr (js_regs en) r) /\
  (forall a, js_sp1 en <= a < js_sp0 en -> apresent (w_H W) mem a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  garr8 SEGS (rdW W mem) v (pjs_bytes 0) /\
  (forall a, v <= a < v + 56 -> writable_at SEGS (rdW W mem) a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 /\
  (YAkMemnorm.memnorm SEGS (js_mem en) -> YAkMemnorm.memnorm SEGS mem).

(* ---- the cuts ---- *)

(* C1, at the `jal fuzz_strdup`: entry allocator state; a0 is the string the call duplicates (the literal for s =
   NULL), which is a cstr_ok kept where fuzz_strdup's text wants it; the ledger read at the cut's memory *)
Definition pjs_C1 (en : PjsEnt) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_inv en (js_ly en) (js_S en) (js_Hp en) (js_W en) regs mem md k /\
  getr regs 10 = w64 (pjs_sarg (js_s en)) /\
  cstr_ok (PA := PA) (js_W en) mem (pjs_sarg (js_s en)) (js_cs en) /\
  kept_at (PA := PA) B (js_Lam en) (pjs_sarg (js_s en)) (js_len en + 1) /\
  prh_ledger (PA := PA) B (js_ly en) (js_S en) (js_Hp en) (js_W en) mem (js_Lam en)
    (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en).

(* C2, at the return site: fuzz_strdup's outcome res in a0 (prh_alloc_post over the entry's allocator state), the
   model-run position from fuzz_strdup's post implication at pj_string's entry position (as in pjs_Q), the grant from
   its OUTCOME conjunct at the same position (as in pjs_Q), its bytes on success, the new block's user bytes apart from
   v and its head word apart from the str field v + 16 .. v + 24 (the one field the rest of the walk writes) *)
Definition pjs_C2 (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_inv en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists res, getr regs 10 = w64 res /\
    (res = 0 -> exists hist', PresetRoomPos.iface_room_pos (js_sm en) (js_x en) (js_os en) (js_i en) (js_H0 en) hist' S) /\
    (res <> 0 -> nth_error (PresetRun.hruns (js_sm en) (js_x en) (js_os en)) (js_i en) =
                   Some (PresetReqAt.HMal (js_len en + 1 + cf_head)) ->
       exists hist', PresetRoomPos.iface_room_pos (js_sm en) (js_x en) (js_os en) (Datatypes.S (js_i en)) (js_H0 en)
         hist' S) /\
    (js_cnt en <> js_fail en -> pjs_run en -> pjs_cons en -> res <> 0) /\
    prh_alloc_post (PA := PA) B (js_len en + 1) (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_Lam en)
      (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) res ly S Hp W mem /\
    (res <> 0 -> bytes_at (PA := PA) W mem res (js_cs en ++ [0]) /\
       (forall x, res <= x < res + js_len en + 1 -> ~ (js_v en <= x < js_v en + 56)) /\
       (forall x, res - cf_head <= x < res - cf_head + 8 -> ~ (js_v en + 16 <= x < js_v en + 24))).

(* ---- the segment statements (one file each) ---- *)
Definition pjs_seg_C2 (CTX0 : list (list Z)) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 en -> pjs_C2 en ly S Hp W regs mem md k ->
  SRr SEGS W (pjs_cfg PJS_C2 regs mem md) (pjs_FIN en).
Definition pjs_seg_C1 (CTX0 : list (list Z)) : Prop :=
  forall en regs mem md k, pjs_pre CTX0 en -> pjs_cnt en -> pjs_C1 en regs mem md k ->
  SRr SEGS (js_W en) (pjs_cfg PJS_C1 regs mem md) (pjs_FIN en).
Definition pjs_seg_entry (CTX0 : list (list Z)) : Prop :=
  forall en, pjs_pre CTX0 en -> pjs_cnt en ->
  SRr SEGS (js_W en) (cfg_at SEGS (pa_sigma AS_pj_string) (js_regs en) (js_mem en) (js_md en)) (pjs_FIN en).

(* ---- MARKED image facts (the unit's binding of B at image B; owner a Theorem Labs lane), taken by the segments that need them ---- *)
(* G-Pj2 (the named gap, PRH_FnPj.v:54-57 at d607d12e4b0f): for s = NULL pj_string duplicates the image's ""
   literal PJS_LIT, a registered one-byte global (`.str.1`, 32 bytes with its redzone in the unstripped twin).
   RESTATED 2026-10-29 (kind-A vacuity; the image-A twin is S6PjString.v pal_lit, blob efdbe4e4b8f8): the old text asked for all 8 bytes PJS_LIT ..
   PJS_LIT + 7 `~ Exists (in_zr a) (as_owned_static B)`, which is FALSE at YD2l.TfibB (PJS_LIT + 1 .. + 7 lie in ASan's
   redzone after the 1-byte global, an owned-static range): pj_string_top.v pjs_g_lit_unsat_B. The walk reads ONE byte
   of the literal (strdup's string, cs = []): that byte is read through arodata_okP, so it asks not owned-static, not
   errno, and the granule's const shadow cell (route (a), kept_img); the other 7 bytes of its granule are only asked
   VISIBLE (cstr_ok's tail), which the image ROM gives (mbyte's ROM fallback, checked by computation in
   pj_string_seg_ent.v pjs0_lit_ok), so they carry no ownership claim. These are facts about B alone; the instance
   witness is pj_string_top.v pjs_g_lit_B (vm_compute at YD2l.TfibB). The kit's PRH_Base.cstr_ok_ro (the kit's note at
   PRH_FnPj.v:61-64) would give the literal's cstr_ok from an image premise YGcallRoStr.ro_str_img, but not its kept_at,
   which still needs these three facts, so the walk keeps pjs0_lit_ok and takes no second literal premise. *)
Definition pjs_g_lit : Prop :=
  ~ Exists (in_zr PJS_LIT) (as_owned_static B) /\ ~ (as_errno B <= PJS_LIT < as_errno B + 4) /\
  (forall ly, In (z1 (ANum (shadow_addr PJS_LIT)) 1) (as_const B ly)).
(* the old text's STATE conjunct, split off (a claim on every allocator state, not on the image): the image's shadow
   map is visible (pj_parse_defs.v pjp_g_vis's third conjunct, YGcfAmx2.v img_shadow_vis_cf); instance witness at
   ARcf rsegs YD2l.TfibB: pj_string_top.v pjs_g_lit_sh_B, from the cover check of image B's shadow lists *)
Definition pjs_g_lit_sh : Prop :=
  forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
    aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* THE HULL BUDGET AT A RUN POSITION (the premise the kit's text names for paying fuzz_strdup's hull budget:
   lib/A/PresetHullPay.v hull_budget_of_room_pos, stated there at preset's CfParams): at any position of a run of at
   most 4 calls a list within one call's counts has its budget, and every request is at most 2 ^ 30 (so the strdup's
   one malloc is within one call's counts, PresetHullPay.hull_nt_one_mal). A fact about the CfParams instance; at
   CfParams_preset it is pj_string_top.v pjs_hull_preset *)
Definition pjs_g_hull : Prop :=
  cf_malloc_max <= 2 ^ 30 /\
  forall sm x os i H0 hist S (Eg : list PresetReqAt.hev), (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL -> PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL ->
  PresetHullBudget.hull_budget S Eg.
End d.
