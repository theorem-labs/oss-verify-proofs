(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the CUTS of pj_set's image-B' walk (fuzz_preset asan-ubsan d663f82d, B 0x86e8c, 115
   instructions; preset_file.c :373-392). STATEMENTS ONLY: the kit's tpj_set_specX ITSELF (lib/A/PRH_FnPj.v:
   ENTRY-keyed, the run keyed on ReaderRes.jr_strtod, the entry premises prh_cons_from, a run of at most 4 calls,
   the tblk Permutation, the ORDERED free-order premise and cf_head = PresetReqAt.HEAD; the post's prh_oks over
   prh_ev_reqs (prhPj_set_trace ..) and most, DEAD-PJSET, the block Permutations and the FREEORD-COPY ordered
   free lists of the result, the failure arm's prh_refused_peak; its goal SRr' over preset's zone with the post
   fpostWmR at the re-hiding relation wle'), the entry record, the kit's premises (pjs_pre, in the kit's
   order), the kit's post (pjs_Q), the seven cut states, the segment statements (one file each) and the pure facts the
   segments share. lib/B/Prog/pj_set_top.v composes them.
   proves no function (kind: statement text).
   The body (whole-program listing lib/B/Listing_prog.v, int102's blob c97cc46b3e13, slots 5616..5730), pc offsets
   from pj_set's entry (DERIVED, by vm_compute below):
     +0x00..+0x18  prologue: sp -= 48; ra, s0, s1, s2, s3, s4 at sp+40, +32, +24, +16, +8, +0
     +0x1c..+0x34  s0 := val, s2 := key, s4 := the shadow base (the .got slot A_OBJ 0 -> the cell A_OBJ 12),
                   s1 := obj, a1 := key
     +0x38         jal pj_get (obj, key)                        CUT PJS_C1
     +0x3c         beqz a0                                      CUT PJS_RET (the fall-through is the PRESENT key)
     +0x40..+0x44  s3 := old; jal pj_free (old)                  [the present arm]
     +0x48..+0x4c  a2 := 56; a0 := s3
     +0x50..+0x54  a1 := s0; jal __asan_memcpy (dest, val, 56)   CUT PJS_TAIL (the JOIN of both arms)
     +0x58..+0x64  a2 := 56; a0 := s0; a1 := 0; jal __asan_memset (val, 0, 56)
     +0x68..+0x6c  a0 := 0; j +0x88
     +0x70..+0x74  a0 := s1; jal grow (obj)                     CUT PJS_MISS  [the absent arm]
     +0x78         beqz a0 -> +0xa8 (granted), else fall through
     +0x7c..+0x84  a0 := s0; jal pj_free (val); a0 := -1        CUT PJS_FAIL
     +0x88..+0xa4  the epilogue: the six loads, sp += 48, ret   CUT PJS_EPI
     +0xa8..+0xac  a0 := s2; jal fuzz_strdup (key)              CUT PJS_DUP
     +0xb0..+0x138 the UBSan guards and the two inline ASan checks of obj->keys / obj->n, then keys[n] := dup
     +0x13c        beqz a1 -> +0x7c (the strdup refusal)
     +0x140..+0x1a4 the checks of obj->kids, obj->n := n + 1, the 56 * n guards; a0 := kids + 56 n; j +0x50
   Callee texts (pjs_texts), every one CITED, never unfolded, all the kit's (lib/A/PRH_FnPj.v, PRH_FnReader.v,
   PRH_FnAlloc.v):
   pj_get = tpj_get_specX (the m-form); pj_free = tpj_free_specX CTX0 dd (the POST-IMPLICATION form: no entry
   position, the position transfer under a run-quantified implication in its post; keyed on the order list F,
   prhPj_free_evs F, PRH_PjOrder.v's pj_foR; it asks prh_head_wide) on the present arm and on the failure arms alike;
   grow = tgrow_specX CTX0 (post-implication; its position-free live-count premises along prhPg_evs .. [] are derived
   from the entry position by pj_set_miss_lem.v; its REFUSED arms carry their exclusion under prh_cons_from);
   fuzz_strdup = tfuzz_strdup_specX (post-implication, with THE OUTCOME conjunct); __asan_memcpy / __asan_memset =
   YGcallMxmn.v aintrin_realizes_xm OCpy / OSet (the m-forms). pj_free's, grow's and fuzz_strdup's posts are read BY NAME
   (their top-level conjunctions split and picked by type); pj_get's m-form post by a positional tuple (pj_set_seg_c1.v:178).
   THE DEAD REFUSAL ARM (DEAD-PJSET): under pjs_pre's prh_cons_from, grow's refused arms are excluded by their own
   exclusion clauses and a NULL strdup with cnt <> fail by fuzz_strdup's outcome clause, at the entry position (grow)
   or the position past grow's events (the strdup); so the failure cut pjs_FAILc is reached only at the CHOSEN
   failure, cnt + (c - 1) = fail, and its peak and outcome cells are the granted ones (PRH_Base.prh_refused_peak is 0
   there, prh_refused_peak_granted).
   THE MEMNORM KEEP (PRH_Base.v fQmn): the walk's goal is fpostWmR; the keep `memnorm mem0 -> memnorm mem` rides in
   pjs_inv (YSRrMemnorm.v: an SRr post is opaque, so the keep is in every cut).
   THE RE-HIDING MOVE: pj_free's and grow's restated posts end at wle' (YA0nH.v over preset's zone
   YGcfRehidePost.RZ_cf), so every segment statement is SRr' over that zone and the cuts after the walk's first
   free or realloc (TAIL, FAILc, DUP, EPI and pj_set_dup_mid.v's pjsd_Cp) hold the journal at wle': pjs_invR wle'.
   The cuts before (C1, RET, MISS) keep pjs_inv, which is pjs_invR at wle (pjs_inv_R_wle); a wle journal crosses into
   wle' by pjs_invR_mono / ajournal_xwR_mono with wle_wle'. The frame's keep is pjs_frame_kept_stmt (pj_get's call)
   and pjs_frame_kept_stmtR at wle' (the calls of pj_free, grow and fuzz_strdup).
   THE HULL BUDGET: pj_free, grow and fuzz_strdup each ask a hull budget for their events; the walk pays them from
   the run position (pjs_g_hull, a Section premise of the segments that call them) at a run of at most 4 calls
   (pjs_pre's length premise); pjs_FAILc carries what pj_free (val) asks.
   Every name is stated at PA := PI_prog_B (the whole-range instance), never at a per-function instance.
   Numerals: 48 / 56 / 40 / 32 / 24 / 16 / 8 (LENGTH: frame, struct size, slot offsets); 6 (the pj type tag of an
   object); pc offsets DERIVED. No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
(* the re-hiding relation wle' at preset's zone (the kit's restated posts) and the hull budget's names *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
Import ListNotations.
Local Open Scope Z_scope.
(* image B's generated PrhImg values (frames, statics, return sites) as the instance every kit name reads *)
#[local] Existing Instance prh_img_B.

(* pc offsets of the cuts from pj_set's entry (DERIVED from the listing: slot index differences times 4) *)
Definition PJS_PC : Z := B_prog_sigma AS_pj_set - B_prog_base.
Definition PJS_C1 : Z := PJS_PC + 56.    (* the `jal pj_get` *)
Definition PJS_RET : Z := PJS_PC + 60.   (* `beqz a0`: pj_get's result decides the arm *)
Definition PJS_TAIL : Z := PJS_PC + 80.  (* `mv a1, s0` before `jal __asan_memcpy`: the JOIN of both arms *)
Definition PJS_MISS : Z := PJS_PC + 112. (* `mv a0, s1` before `jal grow` *)
Definition PJS_FAIL : Z := PJS_PC + 124. (* `mv a0, s0` before `jal pj_free` on the refusal path *)
Definition PJS_EPI : Z := PJS_PC + 136.  (* the epilogue `ld ra, 40(sp)` *)
Definition PJS_DUP : Z := PJS_PC + 168.  (* `mv a0, s2` before `jal fuzz_strdup` *)
Definition PJS_FR : Z := 48.             (* pj_set's own frame (prh_img_B's pi_frame F_pj_set) *)

(* the callee-saved registers pj_set never writes: gp, tp, s5 .. s11 (s0 .. s4 and sp are restored by the epilogue) *)
Definition PJS_KEPT : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

(* THE PINS, checked against the listing of record lib/B/Listing_prog.v (image B' sha256 d663f82d7f48, slots
   5616 .. 5730): the whole-program listing of int102, blob c97cc46b3e13 (relocated from B f8f98a95bc52's listing v4
   f843fdf7fe2f, slots 5363 .. 5477; pj_set's 115 words are equal up to pc-relative fields, all 15 targets the same symbol + offset): the entry, this
   file's eight cut offsets and the three call targets this walk jumps to, as the words the listing holds. The seven
   clookup words are INSTRUCTION words, kept as they were (not addresses). 13 addresses, 0 mismatches (vm_compute). *)
Lemma pjs_pins :
  B_prog_sigma AS_pj_set = 0x86e8c /\ B_prog_slot AS_pj_set = 5616%nat /\
  PJS_PC + 460 = B_prog_sigma AS_grow - B_prog_base /\
  clookup B_prog_tbl (B_prog_base + PJS_C1) = Some 0xd81ff0ef /\
  clookup B_prog_tbl (B_prog_base + PJS_RET) = Some 0x02050a63 /\
  clookup B_prog_tbl (B_prog_base + PJS_TAIL) = Some 0x00040593 /\
  clookup B_prog_tbl (B_prog_base + PJS_MISS) = Some 0x00048513 /\
  clookup B_prog_tbl (B_prog_base + PJS_FAIL) = Some 0x00040513 /\
  clookup B_prog_tbl (B_prog_base + PJS_EPI) = Some 0x02813083 /\
  clookup B_prog_tbl (B_prog_base + PJS_DUP) = Some 0x00090513 /\
  B_prog_sigma AS_pj_get = 0x86c44 /\ B_prog_sigma AS_pj_free = 0x86a24 /\
  B_prog_sigma AS_fuzz_strdup = 0x860e0 /\ B_prog_sigma AS_grow = 0x87058.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* the head width at the model's value is at least a word *)
Lemma pjs_head_wide : forall {cp : CfParams}, cf_head = PresetReqAt.HEAD -> prh_head_wide.
Proof. intros cp H. unfold prh_head_wide. rewrite H. unfold PresetReqAt.HEAD. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx).
(* the world relation after a free or a realloc: the kit's restated posts end at wle' over preset's zone RZ_cf *)
#[local] Notation WLE' := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* the class-24 bound pj_free's text asks at entry when v <> 0 (the tpj_free_specX's position-free room premise,
   carried by the failure cut pjs_FAILc) *)
Definition pjs_PB (S : astate) : Prop := YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* the callee texts this walk composes (the kit's six), each CITED, never unfolded (the header) *)
Definition pjs_texts (CTX0 : list (list Z)) (dd : nat) : Prop :=
  tpj_get_specX (PA := PA) B ARx SK /\
  tpj_free_specX (PA := PA) B ARx SK CTX0 dd /\
  tgrow_specX (PA := PA) B ARx SK CTX0 /\
  tfuzz_strdup_specX (PA := PA) B ARx SK /\
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OCpy (pa_sigma AS___asan_memcpy) /\
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset).

(* ---- the entry ---- *)
Record PjsEnt : Type := MkPjsEnt {
  js_ly : alayout; js_S : astate; js_Hp : list Z; js_W : world SEGS; js_regs : bvmap 5 word;
  js_mem : word -> option byte; js_md : Model; js_ch : list (Z * Z * Z);
  js_d : Z; js_o : Z; js_k : Z; js_w : Z;
  js_ms : list (list Z * PjTree.jv); js_tv : PjTree.jv;
  js_D : list (Z * Z); js_Dw : list (Z * Z);
  js_num : Z; js_str : Z; js_kids : Z; js_keys : Z; js_n : Z; js_cap : Z;
  js_kname : list Z; js_Lam : list (Z * Z);
  js_peak : Z; js_cnt : Z; js_fail : Z; js_ran : Z; js_most : Z; js_own : Z;
  (* the model-run position of the text (PresetRoomPos.iface_room_pos's parameters; the strtod model is
     ReaderRes.jr_strtod, the kit's keyed run) *)
  js_x : list Z; js_os : list (option nat * option nat * option nat); js_i : nat;
  js_H0 : list Z; js_hist : list YG00.chunk }.
Definition js_sp0 (en : PjsEnt) : Z := spZ (js_regs en).
Definition js_sp1 (en : PjsEnt) : Z := js_sp0 en - PJS_FR.
Definition js_klen (en : PjsEnt) : Z := Z.of_nat (length (js_kname en)).
(* The footprint: both headers and every block of the two trees *)
Definition pjs_FP (en : PjsEnt) : list (Z * Z) :=
  (js_o en, js_o en + 56) :: (js_w en, js_w en + 56) :: ablocks_fp (prhPj_hbl (js_D en ++ js_Dw en)).

(* the kit's premises of tpj_set_specX (lib/A/PRH_FnPj.v), verbatim, in its order *)
Definition pjs_pre (CTX0 : list (list Z)) (dd : nat) (en : PjsEnt) : Prop :=
  let ly := js_ly en in let S := js_S en in let Hp := js_Hp en in let W := js_W en in let regs := js_regs en in
  let mem := js_mem en in let md := js_md en in let ch := js_ch en in let d := js_d en in
  let o := js_o en in let k := js_k en in let w := js_w en in let ms := js_ms en in let tv := js_tv en in
  let D := js_D en in let Dw := js_Dw en in let kname := js_kname en in let Lam := js_Lam en in
  let n := js_n en in let cap := js_cap en in
  fpre (PA := PA) B ARx (STK_pj_set dd) ly S Hp W regs mem md ch /\
  prh_univ_closure B CTX0 /\
  room_live_cf S /\
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (js_H0 en) (js_hist en) S /\
  (length (js_os en) <= 4)%nat /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (length (prhPj_set_evs ms kname n cap)) /\
  getr regs 10 = w64 o /\ getr regs 11 = w64 k /\ getr regs 12 = w64 w /\
  fwin (PA := PA) ly W regs mem d /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) o (PjTree.JObj ms) D /\
  pj_hdrR SEGS (rdW W mem) o 6 (js_num en) (js_str en) (js_kids en) (js_keys en) n cap /\ cap <= 2 ^ 54 /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) d ly S Lam W regs mem o /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) w tv Dw /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) d ly S Lam W regs mem w /\ w < YM05.alloc_ceiling /\
  (forall bk, In bk Dw -> ~ In bk D) /\
  (forall x, w <= x < w + 56 -> ~ pj_footR o D x) /\
  pj_apartR Dw o /\
  (PjTree.depth (PjTree.JObj ms) <= Datatypes.S dd)%nat /\ (PjTree.depth tv <= dd)%nat /\
  cstr_ok (PA := PA) W mem k kname /\ kept_at (PA := PA) B Lam k (js_klen en + 1) /\
  (forall x, k <= x < k + js_klen en + 1 -> ~ pj_footR o D x /\ ~ pj_footR w Dw x) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) /\
  js_cnt en + 3 < 2 ^ 64 - 1 /\
  js_klen en + 1 + cf_head < cf_malloc_max /\
  (n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max) /\
  blocks_bytes S + LIVE_pj_set n cap (js_klen en) <= LIVE_MAX /\
  Permutation (map (fun b => snd b + cf_head) D) (PresetReqAtNoMiss.tblk (PjTree.JObj ms)) /\
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam) nn o D F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms)) /\
  cf_head = PresetReqAt.HEAD /\
  prh_run_at ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (prhPj_set_evs ms kname n cap).

(* the model's own events of this call (the length the post's position advances by) *)
Definition pjs_evs (en : PjsEnt) : list PresetReqAt.hev :=
  prhPj_set_evs (js_ms en) (js_kname en) (js_n en) (js_cap en).

(* the walk's post: the kit's own named post of tpj_set_specX (lib/A/PRH_FnPj.v tpsP_Q, which tpsP_Q_check ties to the
   text's post body) over the entry's values *)
Definition pjs_Q (en : PjsEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  tpsP_Q (PA := PA) B (js_x en) (js_os en) (js_i en) (js_H0 en) (js_most en) (js_own en) (js_ly en) (js_S en)
    (js_W en) (js_mem en) (js_o en) (js_w en) (js_ms en) (js_tv en) (js_D en) (js_Dw en) (js_kids en) (js_keys en)
    (js_n en) (js_cap en) (js_kname en) (js_Lam en) (js_peak en) (js_cnt en) (js_fail en) (js_ran en).

(* the walk's goal: the kit's restated post, the memnorm-keep form at the re-hiding relation (fpostWmR at wle'), at the
   entry float state *)
Definition pjs_FIN (dd : nat) (en : PjsEnt) : world SEGS -> config -> Prop :=
  fpostWmR (PA := PA) B ARx SK WLE' (STK_pj_set dd) (js_d en) (pjs_FP en)
    (js_regs en) (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) (pjs_Q en).

(* the configuration at a cut (pj_set never changes the float state: every callee's post is at fx) *)
Definition pjs_cfg (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS)) md.

(* ---- what holds at every cut after the prologue ---- *)
Definition pjs_inv (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  (* the journal from the entry, at the caller-window widened window, footprint = the text's *)
  AJ (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp W mem md k /\
  (* the caller's window outside the footprint, untouched (fpostW's window clause) *)
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (js_W en)) (js_mem en) a) /\
  (* pj_set's frame: sp, the six saved registers, s0 = val, s4 = the shadow base, the untouched callee-saved
     registers, and the frame present *)
  spZ regs = js_sp1 en /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 40) 8 (raZ (js_regs en)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 32) 8 (s0Z (js_regs en)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 24) 8 (bv_unsigned (getr (js_regs en) 9)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 16) 8 (bv_unsigned (getr (js_regs en) 18)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 8) 8 (bv_unsigned (getr (js_regs en) 19)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en) 8 (bv_unsigned (getr (js_regs en) 20)) /\
  getr regs 8 = w64 (js_w en) /\ getr regs 18 = w64 (js_k en) /\ getr regs 20 = w64 SHADOW_OFF /\
  (forall r, In r PJS_KEPT -> getr regs r = getr (js_regs en) r) /\
  (forall a, js_sp1 en <= a < js_sp0 en -> apresent (w_H W) mem a) /\
  (* the read-only view *)
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (* the memnorm keep from the entry memory (PRH_Base.v fQmn; YSRrMemnorm.v srr_inv_laws_imp's P) *)
  (YAkMemnorm.memnorm SEGS (js_mem en) -> YAkMemnorm.memnorm SEGS mem).
(* pjs_inv over a world relation R: a copy of its body with the journal at R (ajournal_xR R). The cuts before pj_set's
   first free or realloc keep pjs_inv (R = wle, pjs_inv_R_wle); the cuts after one take R = wle' over preset's zone *)
Definition pjs_invR (R : world SEGS -> world SEGS -> Prop) (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  AJR R (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp W mem md k /\
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (js_W en)) (js_mem en) a) /\
  spZ regs = js_sp1 en /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 40) 8 (raZ (js_regs en)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 32) 8 (s0Z (js_regs en)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 24) 8 (bv_unsigned (getr (js_regs en) 9)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 16) 8 (bv_unsigned (getr (js_regs en) 18)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en + 8) 8 (bv_unsigned (getr (js_regs en) 19)) /\
  val_mem SEGS (rdW W mem) (js_sp1 en) 8 (bv_unsigned (getr (js_regs en) 20)) /\
  getr regs 8 = w64 (js_w en) /\ getr regs 18 = w64 (js_k en) /\ getr regs 20 = w64 SHADOW_OFF /\
  (forall r, In r PJS_KEPT -> getr regs r = getr (js_regs en) r) /\
  (forall a, js_sp1 en <= a < js_sp0 en -> apresent (w_H W) mem a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (YAkMemnorm.memnorm SEGS (js_mem en) -> YAkMemnorm.memnorm SEGS mem).
Lemma pjs_inv_R_wle : forall dd en ly S Hp W regs mem md k,
  pjs_inv dd en ly S Hp W regs mem md k = pjs_invR (@wle SEGS) dd en ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* a cut at R1 is one at any wider R2 (the journal's world conjunct, ajournal_xwR_mono) *)
Lemma pjs_invR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall dd en ly S Hp W regs mem md k,
  pjs_invR R1 dd en ly S Hp W regs mem md k -> pjs_invR R2 dd en ly S Hp W regs mem md k.
Proof.
  intros R1 R2 HR dd en ly S Hp W regs mem md k (HJ & HI).
  split; [exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx R1 R2 HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) | exact HI].
Qed.


(* the memory-side premises of the text, at the state a cut names (the entry's, transported): the object, the
   value, the key, and the ledger *)
Definition pjs_data (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (Lam : list (Z * Z))
  (W : world SEGS) (mem : word -> option byte) : Prop :=
  room_live_cf S /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam W (js_regs en) mem (js_o en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam W (js_regs en) mem (js_w en) /\
  cstr_ok (PA := PA) W mem (js_k en) (js_kname en) /\ kept_at (PA := PA) B Lam (js_k en) (js_klen en + 1) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en).

(* a struct's placement minus its shadow HULL (the first six conjuncts of prhPj_slot). What a program call keeps:
   the hull of a struct in the caller's window [sp0, sp0 + d) reads shadow bytes past the stack's top when that
   top is not 64-aligned, and no law at a generic ARx says it is, so the cuts after a call carry the object's
   placement in this form; nothing after the first call reads the object's hull (grow asks range_addressable only,
   the inline checks read one shadow byte each) *)
Definition pjs_place (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world SEGS)
  (mem : word -> option byte) (p : Z) : Prop :=
  4096 <= p /\ prhReader_at B ly S Lam (js_regs en) (js_d en) p 56 /\ pj_rwR SEGS (rdW W mem) p /\
  amem_range p 56 /\
  (forall a, p <= a < p + 56 -> ~ aowned B ly S a /\ ~ (spZ (js_regs en) - STK_pj_set dd <= a < spZ (js_regs en))) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 56.

(* pjs_data at a cut after a call: the object by pjs_place, the ledger stated by the cut itself (its counters move
   with the arm's allocations) *)
Definition pjs_data_c (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Lam : list (Z * Z))
  (W : world SEGS) (mem : word -> option byte) : Prop :=
  room_live_cf S /\
  pjs_place dd en ly S Lam W mem (js_o en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam W (js_regs en) mem (js_w en) /\
  cstr_ok (PA := PA) W mem (js_k en) (js_kname en) /\ kept_at (PA := PA) B Lam (js_k en) (js_klen en + 1).

(* ---- the cuts ---- *)

(* C1, at the `jal pj_get`: the entry allocator state, the memory after the prologue; the object's footprint still
   reads as at the entry (the first post arm names the replaced member at the ENTRY memory) *)
Definition pjs_C1 (dd : nat) (en : PjsEnt) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
  : Prop :=
  pjs_inv dd en (js_ly en) (js_S en) (js_Hp en) (js_W en) regs mem md k /\
  pjs_data dd en (js_ly en) (js_S en) (js_Hp en) (js_Lam en) (js_W en) mem /\
  getr regs 10 = w64 (js_o en) /\ getr regs 11 = w64 (js_k en) /\ getr regs 9 = w64 (js_o en) /\
  pj_nodeR SEGS (rdW (js_W en) mem) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en) /\
  pj_hdrR SEGS (rdW (js_W en) mem) (js_o en) 6 (js_num en) (js_str en) (js_kids en) (js_keys en)
    (js_n en) (js_cap en) /\
  pj_nodeR SEGS (rdW (js_W en) mem) (prh_lin (js_Lam en)) (js_w en) (js_tv en) (js_Dw en) /\
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW (js_W en) mem) (pj_footR (js_o en) (js_D en)) /\
  (* val's footprint reads as at the entry (the FREEORD-COPY conjuncts take val's order list there) *)
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW (js_W en) mem) (pj_footR (js_w en) (js_Dw en)).

(* RET, after pj_get returned z: the allocator state is the entry's (pj_get's m-form post: S' = S, so the model-run
   position is the entry's); the object's footprint still reads as at the entry *)
Definition pjs_RET (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_inv dd en ly S Hp W regs mem md k /\
  pjs_data_c dd en ly S (js_Lam en) W mem /\
  prh_ledger (PA := PA) B ly S Hp W mem (js_Lam en) (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) /\
  ablocks B ly S = ablocks B (js_ly en) (js_S en) /\ Hp = js_Hp en /\ S = js_S en /\
  getr regs 9 = w64 (js_o en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en) /\
  pj_hdrR SEGS (rdW W mem) (js_o en) 6 (js_num en) (js_str en) (js_kids en) (js_keys en) (js_n en) (js_cap en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (js_Lam en)) (js_w en) (js_tv en) (js_Dw en) /\
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW W mem) (pj_footR (js_o en) (js_D en)) /\
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW W mem) (pj_footR (js_w en) (js_Dw en)) /\
  exists z, getr regs 10 = w64 z /\
  prhPj_get_res (PA := PA) (rdW W mem) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en)
    (js_kname en) z.

(* TAIL, the join at `mv a1, s0`: a0 = the 56-byte destination, a2 = 56; everything but the copy is done. The
   destination is the member slot (both arms); Do is the final block list, Lam2 the ledger after the arm's work. *)
Definition pjs_TAIL (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_invR WLE' dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists dest Lam2 peak2 cnt2 fail2 ran2 (c : nat) (ok : list bool),
  getr regs 10 = w64 dest /\ getr regs 12 = w64 56 /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 cnt2 fail2 ran2 (js_most en) (js_own en) /\
  cnt2 = js_cnt en + Z.of_nat c /\
  prh_oks ok (js_cnt en) (js_fail en) c (prh_ev_reqs (prhPj_set_trace (js_n en) (js_cap en) (js_kname en)))
    (js_most en) (js_ran en) ran2 /\
  ReaderRes.fail_after (js_cnt en) (js_fail en) c fail2 /\
  (* the value's own facts, still at the entry's blocks Dw, and the destination's placement *)
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (js_w en) (js_tv en) (js_Dw en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam2 W (js_regs en) mem (js_w en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam2 W (js_regs en) mem dest /\
  (forall x, js_w en <= x < js_w en + 56 -> ~ (dest <= x < dest + 56)) /\
  dest + 56 <= YM05.alloc_ceiling /\ js_w en + 56 <= YM05.alloc_ceiling /\
  (* the two 56-byte writes are permitted: each byte is pj_set's own footprint in a live block, a block made
     since the entry, or a caller frame the footprint names (YCbq.v awr_byte / YCbqG.v wr_fp_frame) *)
  (forall a, (dest <= a < dest + 56) \/ (js_w en <= a < js_w en + 56) ->
     awr_byte (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
       (ablocks B (js_ly en) (js_S en)) (ablocks B ly S) ly [] a \/
     wr_fp_frame (pjs_FP en) (js_S en) ly a) /\
  (* the copy's source is readable; neither range holds an image byte *)
  (forall a, js_w en <= a < js_w en + 56 -> aview SEGS (w_H W) mem a <> None) /\
  (forall a, (dest <= a < dest + 56) \/ (js_w en <= a < js_w en + 56) -> ~ in_img SEGS a) /\
  (* The post holds of the state the copy and the zeroing make: the arm's own obligation, discharged where the
     arm is proved. The two intrinsics keep W, write only [dest, dest + 56), [w, w + 56) and their own ESTACK
     window below sp1, and leave a0 = 0. *)
  (forall mem' regs' md',
     (forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem' (dest + i) = aview SEGS (w_H W) mem (js_w en + i)) ->
     (forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem' (js_w en + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (dest <= a < dest + 56) -> ~ (js_w en <= a < js_w en + 56) ->
        ~ (js_sp1 en - ESTACK <= a < js_sp1 en) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
     getr regs' 10 = w64 0 ->
     pjs_Q en ly S Hp W regs' mem' md').

(* MISS, at `mv a0, s1` before the grow call: the key is absent; the allocator state is the entry's; the object's
   footprint still reads as at the entry (so the entry's ORDERED free list of the object holds here,
   PRH_PjOrder.pj_foR_frame) *)
Definition pjs_MISS (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_inv dd en ly S Hp W regs mem md k /\
  pjs_data_c dd en ly S (js_Lam en) W mem /\
  prh_ledger (PA := PA) B ly S Hp W mem (js_Lam en) (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) /\
  ablocks B ly S = ablocks B (js_ly en) (js_S en) /\ Hp = js_Hp en /\ S = js_S en /\
  getr regs 9 = w64 (js_o en) /\
  ~ In (js_kname en) (map fst (js_ms en)) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en) /\
  pj_hdrR SEGS (rdW W mem) (js_o en) 6 (js_num en) (js_str en) (js_kids en) (js_keys en) (js_n en) (js_cap en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (js_Lam en)) (js_w en) (js_tv en) (js_Dw en) /\
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW W mem) (pj_footR (js_o en) (js_D en)) /\
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW W mem) (pj_footR (js_w en) (js_Dw en)).

(* FAIL, at `mv a0, s0` before pj_free (val): the arm failed at its c-th allocation, which is the CHOSEN failure
   (cnt + (c - 1) = fail: a refusal there is excluded by the callees' outcome clauses under pjs_pre's prh_cons_from,
   the header's DEAD-PJSET), so the peak and the outcome cells are the granted ones; what the object holds now is
   Do over the ledger Lam2, val is still the entry's tree, and the class-24 count is within its bound (pj_free's
   position-free text's PB: a failed call keeps the model-run position, which bounds it by counts_of_room_pos_rl) *)
Definition pjs_FAILc (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_invR WLE' dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists Lam2 peak2 fail2 ran2 (c : nat) (ok : list bool) Do Lr,
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 (js_cnt en + Z.of_nat c) fail2 ran2 (js_most en) (js_own en) /\
  prh_oks ok (js_cnt en) (js_fail en) c (prh_ev_reqs (prhPj_set_trace (js_n en) (js_cap en) (js_kname en)))
    (js_most en) (js_ran en) ran2 /\
  ReaderRes.fail_after (js_cnt en) (js_fail en) c fail2 /\
  Permutation (js_Lam en) (js_D en ++ js_Dw en ++ Lr) /\ Permutation Lam2 (Do ++ js_Dw en ++ Lr) /\
  prhPj_blocks B (js_ly en) (js_S en) (js_Lam en) ly S Lam2 /\
  ~ In (js_kname en) (map fst (js_ms en)) /\
  (1 <= c <= length (prhPj_set_trace (js_n en) (js_cap en) (js_kname en)))%nat /\
  nth (c - 1) ok true = false /\ (forall i, (i < c - 1)%nat -> nth i ok true = true) /\
  js_cnt en + Z.of_nat (c - 1) = js_fail en /\
  peak2 = Z.max (js_peak en) (Ledger.lsum Lam2) /\
  pjs_PB S /\
  (exists Dold Dnew Dr, Permutation (js_D en) (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
     prhPj_new B (js_ly en) (js_S en) Dnew /\
     (c = 1%nat /\ Dold = [] /\ Dnew = [] \/
      js_n en = js_cap en /\ c = 2%nat /\ Dold = kids_blkR (js_kids en) (js_cap en) /\
        (exists k', Dnew = [(k', 56 * cap2R (js_cap en))]) \/
      js_n en = js_cap en /\ c = 3%nat /\
        Dold = kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en) /\
        exists k' y', Dnew = [(k', 56 * cap2R (js_cap en)); (y', 8 * cap2R (js_cap en))])) /\
  (* what the object reads once val's blocks are freed: the ARM owes it, because only the arm knows how the
     object was grown. The journal below is exactly pj_free (val)'s - it writes val's header and val's blocks and
     nothing else - with the call rule's extension clause (an object in the caller's window lies inside that
     journal's window, so only this clause keeps it), and Lam3 is the ledger list it leaves *)
  (forall md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3,
     AJR WLE' (STK_pj_free dd + (48 + js_d en)) (js_sp0 en + js_d en)
       ((js_w en, js_w en + 56) :: ablocks_fp (prhPj_hbl (js_Dw en)))
       ly S Hp W mem md0 [] ly3 S3 Hp3 W3 mem3 md3 k3 ->
     (forall a, js_sp1 en <= a < js_sp0 en + js_d en ->
        ~ inFP ((js_w en, js_w en + 56) :: ablocks_fp (prhPj_hbl (js_Dw en))) a ->
        aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a) ->
     Permutation Lam3 (Do ++ Lr) ->
     pj_fdR SEGS (rdW W3 mem3) (prh_lin Lam3) (PjTree.depth (PjTree.JObj (js_ms en))) (js_o en) Do /\
     (c = length (prhPj_set_trace (js_n en) (js_cap en) (js_kname en)) ->
        pj_nodeR SEGS (rdW W3 mem3) (prh_lin Lam3) (js_o en) (PjTree.JObj (js_ms en)) Do)) /\
  (* val is still whole, and it is pj_free's argument *)
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (js_w en) (js_tv en) (js_Dw en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam2 W (js_regs en) mem (js_w en) /\
  (* THE HULL BUDGET pj_free (val) asks (the kit's tpj_free_specX, v <> 0): the empty list's, what the failed allocation's
     budget leaves after its use (PresetHullBudget.hull_budget_used) *)
  PresetHullBudget.hull_budget S [].

(* DUP, at `mv a0, s2` before the fuzz_strdup call: grow has run (or had nothing to do). Dold / Dnew / Dr: the
   object's blocks grow replaced, the fresh ones, the rest (the second and third post arms name them); the model-run
   position is past grow's c granted reallocs (fuzz_strdup's live-set premises follow from it by PresetRoomCounts.v
   counts_of_room_pos_rl), and the room fuzz_strdup asks is left (from LIVE_pj_set). The object's ORDERED free list
   at this state (the conjunct before the last, :518-522: the members' slots as the entry's ordered premise gives them, the arrays at the
   capacity cap2v, which is the model's PresetReqAt.ncap (S |ms|) of the object AFTER the append) is what the
   appended arm's FREEORD-COPY conjunct is built from *)
Definition pjs_DUP (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_invR WLE' dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists Lam2 peak2 (c : nat) (ok : list bool) Do Lr kids2 keys2 cap2v Dold Dnew Dr,
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 (js_cnt en + Z.of_nat c) (js_fail en) (js_ran en) (js_most en) (js_own en) /\
  prh_oks ok (js_cnt en) (js_fail en) c (prh_ev_reqs (prhPj_set_trace (js_n en) (js_cap en) (js_kname en)))
    (js_most en) (js_ran en) (js_ran en) /\
  (forall i, (i < c)%nat -> nth i ok true = true) /\
  ~ (js_cnt en <= js_fail en < js_cnt en + Z.of_nat c) /\
  Permutation (js_Lam en) (js_D en ++ js_Dw en ++ Lr) /\ Permutation Lam2 (Do ++ js_Dw en ++ Lr) /\
  prhPj_blocks B (js_ly en) (js_S en) (js_Lam en) ly S Lam2 /\
  ~ In (js_kname en) (map fst (js_ms en)) /\
  Permutation (js_D en) (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
  prhPj_new B (js_ly en) (js_S en) Dnew /\
  (js_n en < js_cap en /\ c = 0%nat /\ kids2 = js_kids en /\ keys2 = js_keys en /\ cap2v = js_cap en /\
     Dold = [] /\ Dnew = []
   \/ js_n en = js_cap en /\ c = 2%nat /\ cap2v = cap2R (js_cap en) /\
     Dold = kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en) /\
     Dnew = [(kids2, 56 * cap2R (js_cap en)); (keys2, 8 * cap2R (js_cap en))]) /\
  peak2 = Z.max (js_peak en) (Ledger.lsum Lam2) /\
  js_n en < cap2v /\
  (exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en + c)%nat (js_H0 en)
     hist S) /\
  blocks_bytes S + (js_klen en + 1 + cf_head) <= LIVE_MAX /\
  (* the object now has room for one more member: it is still its own tree, over the blocks Do, and its slot
     arrays are the (possibly new) blocks of Lam2 *)
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (js_o en) (PjTree.JObj (js_ms en)) Do /\
  pj_hdrR SEGS (rdW W mem) (js_o en) 6 (js_num en) (js_str en) kids2 keys2 (js_n en) cap2v /\
  pj_slots_atR (prh_lin Lam2) 6 kids2 keys2 (js_n en) cap2v /\
  getr regs 9 = w64 (js_o en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (js_w en) (js_tv en) (js_Dw en) /\
  pjs_data_c dd en ly S Lam2 W mem /\
  (* the block lists IN ORDER: grow replaced the arrays at the front of the object's list and kept the members'
     blocks Dr where they were *)
  js_D en = Dold ++ Dr /\ Do = Dnew ++ Dr /\
  (* the capacities are the model's (the entry's ordered premise forces cap = ncap |ms|; cap2v is then the model's
     capacity AFTER the append, ncap (S |ms|) = gcap |ms| (ncap |ms|)) *)
  js_cap en = Z.of_nat (PresetReqAt.ncap (length (js_ms en))) /\
  cap2v = Z.of_nat (PresetReqAt.ncap (Datatypes.S (length (js_ms en)))) /\
  (* the object's ORDERED free list here (PjFoMember.pfm_slots: fo's member slots, value then key) *)
  (forall nn, (PjTree.depth (PjTree.JObj (js_ms en)) <= nn)%nat ->
     exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam2) nn (js_o en) Do F /\
       map (fun b => snd b + PresetReqAt.HEAD) F =
         PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (js_ms en) ++
         PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (js_ms en))))) /\
  (* val's footprint reads as at the entry (the appended arm's FREEORD-COPY takes val's order list there) *)
  pj_agreeR SEGS (rdW (js_W en) (js_mem en)) (rdW W mem) (pj_footR (js_w en) (js_Dw en)).

(* EPI, at the epilogue: the walk's post holds at this state, a0 included *)
Definition pjs_EPI (dd : nat) (en : PjsEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjs_invR WLE' dd en ly S Hp W regs mem md k /\ pjs_Q en ly S Hp W regs mem md.

(* ---- the segment statements (one file each); each takes the kit's premises (pjs_pre) ---- *)
Definition pjs_seg_epi (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 dd en -> pjs_EPI dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjs_cfg PJS_EPI regs mem md) (pjs_FIN dd en).
Definition pjs_seg_fail (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 dd en -> pjs_FAILc dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjs_cfg PJS_FAIL regs mem md) (pjs_FIN dd en).
Definition pjs_seg_tail (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 dd en -> pjs_TAIL dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjs_cfg PJS_TAIL regs mem md) (pjs_FIN dd en).
Definition pjs_seg_dup (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 dd en -> pjs_DUP dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjs_cfg PJS_DUP regs mem md) (pjs_FIN dd en).
Definition pjs_seg_miss (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 dd en -> pjs_MISS dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjs_cfg PJS_MISS regs mem md) (pjs_FIN dd en).
Definition pjs_seg_ret (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjs_pre CTX0 dd en -> pjs_RET dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjs_cfg PJS_RET regs mem md) (pjs_FIN dd en).
Definition pjs_seg_c1 (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en regs mem md k, pjs_pre CTX0 dd en -> pjs_C1 dd en regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (js_W en) (pjs_cfg PJS_C1 regs mem md) (pjs_FIN dd en).
Definition pjs_seg_entry (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en, pjs_pre CTX0 dd en ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (js_W en)
    (cfg_at SEGS (pa_sigma AS_pj_set) (js_regs en) (js_mem en) (js_md en)) (pjs_FIN dd en).

(* ---- the shared keep statement (proved in lib/B/Prog/pj_set_seg_epi.v): what a program call keeps of pj_set's
   state. EVERY program call of this walk is made at the widest callee window the call rule allows, e1 = 48 + d
   (YCbqGcallW.v aj_call_xW asks o + e1 <= 0 at o = - 48 - d), so the callee's own journal runs at
   (STK1 + 48 + d) (sp0 + d) and its extension clause (HX below, the third premise) keeps every byte of
   [sp1, sp0 + d) outside the callee's footprint - pj_set's six saved registers among them. The journal gives the
   frame's presence and the read-only view. ---- *)
Definition pjs_frame_kept_stmt (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1,
  pjs_inv dd en ly S Hp W regs mem md k ->
  AJ (STK1 + (48 + js_d en)) (js_sp0 en + js_d en) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, js_sp1 en <= a < js_sp0 en + js_d en -> ~ inFP FP1 a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, js_sp1 en <= a < js_sp0 en -> ~ inFP FP1 a) ->
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a -> ~ inFP FP1 a) ->
  0 <= STK1 -> 0 <= js_d en -> ~ YI16.sink_open_fp FP1 ->
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (js_W en)) (js_mem en) a) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 40) 8 (raZ (js_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 32) 8 (s0Z (js_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 24) 8 (bv_unsigned (getr (js_regs en) 9)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 16) 8 (bv_unsigned (getr (js_regs en) 18)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 8) 8 (bv_unsigned (getr (js_regs en) 19)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en) 8 (bv_unsigned (getr (js_regs en) 20)) /\
  (forall a, js_sp1 en <= a < js_sp0 en -> apresent (w_H W2) mem2 a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
(* pjs_frame_kept_stmt over a world relation R: a copy of its body with the cut (pjs_invR R) and the callee's journal
   (ajournal_xR R) at R. A call made at a cut after a free or a realloc takes R = wle' (both journals lifted there by
   ajournal_xwR_mono / pjs_invR_mono); the cuts before keep pjs_frame_kept_stmt (pjs_frame_kept_stmt_R_wle) *)
Definition pjs_frame_kept_stmtR (R : world SEGS -> world SEGS -> Prop) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1,
  pjs_invR R dd en ly S Hp W regs mem md k ->
  AJR R (STK1 + (48 + js_d en)) (js_sp0 en + js_d en) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, js_sp1 en <= a < js_sp0 en + js_d en -> ~ inFP FP1 a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, js_sp1 en <= a < js_sp0 en -> ~ inFP FP1 a) ->
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a -> ~ inFP FP1 a) ->
  0 <= STK1 -> 0 <= js_d en -> ~ YI16.sink_open_fp FP1 ->
  (forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (js_W en)) (js_mem en) a) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 40) 8 (raZ (js_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 32) 8 (s0Z (js_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 24) 8 (bv_unsigned (getr (js_regs en) 9)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 16) 8 (bv_unsigned (getr (js_regs en) 18)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en + 8) 8 (bv_unsigned (getr (js_regs en) 19)) /\
  val_mem SEGS (rdW W2 mem2) (js_sp1 en) 8 (bv_unsigned (getr (js_regs en) 20)) /\
  (forall a, js_sp1 en <= a < js_sp0 en -> apresent (w_H W2) mem2 a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
Lemma pjs_frame_kept_stmt_R_wle : forall dd, pjs_frame_kept_stmt dd = pjs_frame_kept_stmtR (@wle SEGS) dd.
Proof. reflexivity. Qed.

(* the shadow-visibility facts the cuts after a call need, which no journal clause keeps (MARKED kit facts,
   discharged at the instance ARx := ARcf, as pj_parse_defs.v's pjp_g_vis) *)
Definition pjs_g_vis : Prop :=
  ARx_frame_hull_vis SEGS B ARx /\
  (forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> in_zs B a n -> 0 < n ->
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n) /\
  (forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
     aview SEGS (w_H W) mem (shadow_addr a) <> None).

(* THE HULL BUDGET AT A RUN POSITION (the premise the kit's text names for paying a post-form callee: lib/A/PresetHullPay.v
   hull_budget_of_room_pos, stated there at preset's CfParams): at any position of a run of at most 4 calls a list
   within one call's counts has its budget, and every request of the walk is at most 2 ^ 30 (so one event, or grow's
   two, are within one call's counts). A fact about the CfParams instance; at CfParams_preset it is
   pj_set_vis_inst.v pjs_hull_preset *)
Definition pjs_g_hull : Prop :=
  cf_malloc_max <= 2 ^ 30 /\
  forall sm x os i H0 hist S (Eg : list PresetReqAt.hev), (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL -> PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL ->
  PresetHullBudget.hull_budget S Eg.
End d.

(* ---- the pure facts (lib/B/Prog/pj_set_glue.v proves each) ---- *)
Definition pjs_g_node_fd : Prop :=
  forall (segs : list Segment) m lblk t p D n,
  pj_nodeR segs m lblk p t D -> (PjTree.depth t <= n)%nat -> pj_fdR segs m lblk n p D.
Definition pjs_g_depth_mem : Prop :=
  forall ms i nm (v : PjTree.jv) (dd : nat), nth_error ms i = Some (nm, v) ->
  (PjTree.depth (PjTree.JObj ms) <= Datatypes.S dd)%nat -> (PjTree.depth v <= dd)%nat.
Definition pjs_g_model_hit : Prop :=
  forall (ms : list (list Z * PjTree.jv)) i (kname : list Z) vi tv,
  nth_error ms i = Some (kname, vi) ->
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) ->
  PjTree.pj_set_model ms kname tv = firstn i ms ++ (kname, tv) :: skipn (Datatypes.S i) ms.
Definition pjs_g_model_miss : Prop :=
  forall (ms : list (list Z * PjTree.jv)) (kname : list Z) tv, ~ In kname (map fst ms) ->
  PjTree.pj_set_model ms kname tv = ms ++ [(kname, tv)].
Definition pjs_g_trace_len : Prop :=
  forall (n cap : Z) (kname : list Z),
  length (prhPj_set_trace n cap kname) = if n =? cap then 3%nat else 1%nat.
(* the two live counts read only the block sizes, so they follow the allocator's block list *)
Definition pjs_g_counts_swap : Prop :=
  forall (S1 S2 : astate) (a b c : list Z),
  Permutation (map snd (blocks S1)) (a ++ c) -> Permutation (map snd (blocks S2)) (b ++ c) ->
  YGcfRoomLive.sec_cnt S2 <= YGcfRoomLive.sec_cnt S1 + Z.of_nat (length b) /\
  YGcfRoomLive.ccnt24 S2 <= YGcfRoomLive.ccnt24 S1 + Z.of_nat (length b).
Definition pjs_g_counts_eq : Prop :=
  forall (S1 S2 : astate), Permutation (map snd (blocks S1)) (map snd (blocks S2)) ->
  YGcfRoomLive.sec_cnt S1 = YGcfRoomLive.sec_cnt S2 /\ YGcfRoomLive.ccnt24 S1 = YGcfRoomLive.ccnt24 S2.
Definition pjs_g_ab_snd : Prop :=
  forall (B : asyms) ly S, map snd (ablocks B ly S) = map snd (blocks S).
Definition pjs_glue {ci : CfImg} {cp : CfParams} : Prop :=
  pjs_g_node_fd /\ pjs_g_depth_mem /\ pjs_g_model_hit /\ pjs_g_model_miss /\ pjs_g_trace_len /\
  pjs_g_counts_swap /\ pjs_g_counts_eq /\ pjs_g_ab_snd.
