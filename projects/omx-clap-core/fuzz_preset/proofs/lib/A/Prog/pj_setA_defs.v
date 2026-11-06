(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the CUTS of pj_set's image-A' walk (fuzz_preset asan, pin 1be0f53d96cb, unstripped twin
   bff8519bbe3e; A 0x8685c, 88 instructions; preset_file.c :373-392). STATEMENTS ONLY: tpj_set_specX ITSELF
   (lib/A/PRH_FnPj.v: ENTRY-keyed, the run keyed on ReaderRes.jr_strtod, the entry premises prh_cons_from, the tblk
   Permutation, the ORDERED free-order premise and cf_head = PresetReqAt.HEAD; the post's prh_oks over prh_ev_reqs
   (prhPj_set_trace ..) and most, DEAD-PJSET, the block Permutations and the FREEORD-COPY ordered free lists of the
   result, the failure arm's prh_refused_peak), the entry record, the contract's premises (pjsA_pre, in the
   contract's order), the contract's post (pjsA_Q), the seven cut states, the segment statements (one file each) and
   the pure facts the segments share. lib/A/Prog/pj_setA_top.v composes them.
   proves no function (kind: statement text).
   The body (whole-program listing lib/A/Listing_prog.v, slots 5279 .. 5366), pc offsets from pj_set's entry
   (DERIVED, by vm_compute below):
     +0x00..+0x18  prologue: sp -= 48; ra, s0, s1, s2, s3, s4 at sp+40, +32, +24, +16, +8, +0
     +0x1c..+0x34  s0 := val, s2 := key, s4 := the shadow base (the .got slot A_OBJ 0 -> the cell A_OBJ 12),
                   s1 := obj, a1 := key
     +0x38         jal pj_get (obj, key)                        CUT PJSA_C1
     +0x3c         beqz a0                                      CUT PJSA_RET (the fall-through is the PRESENT key)
     +0x40..+0x44  s3 := old; jal pj_free (old)                  [the present arm]
     +0x48..+0x4c  a2 := 56; a0 := s3
     +0x50..+0x54  a1 := s0; jal __asan_memcpy (dest, val, 56)   CUT PJSA_TAIL (the JOIN of both arms)
     +0x58..+0x64  a2 := 56; a0 := s0; a1 := 0; jal __asan_memset (val, 0, 56)
     +0x68..+0x6c  a0 := 0; j +0x88
     +0x70..+0x74  a0 := s1; jal grow (obj)                     CUT PJSA_MISS  [the absent arm]
     +0x78         beqz a0 -> +0xa8 (granted), else fall through
     +0x7c..+0x84  a0 := s0; jal pj_free (val); a0 := -1        CUT PJSA_FAIL
     +0x88..+0xa4  the epilogue: the six loads, sp += 48, ret   CUT PJSA_EPI
     +0xa8..+0xac  a0 := s2; jal fuzz_strdup (key)              CUT PJSA_DUP
     +0xb0..+0xfc  the inline ASan checks of &obj->keys, &obj->n and &keys[n] (shadow bytes), then keys[n] := dup
     +0x100        beqz a1 -> +0x7c (the strdup refusal)
     +0x104..+0x13c the inline ASan checks of &obj->kids and &obj->n, obj->n := n + 1; a0 := kids + 56 n;
                   a2 := 56; j +0x50
     +0x140..+0x15c the five __asan_report_* calls (never reached)
   Callee texts (pjsA_texts), every one CITED, never unfolded:
   pj_get = tpj_get_specX (the m-form); pj_free = tpj_free_specX CTX0 dd (the POST-IMPLICATION form: no entry
   position, the position transfer under a run-quantified implication in its post; keyed on the order list F,
   prhPj_free_evs F, PRH_PjOrder.v's pj_foR; it asks prh_head_wide) on the present arm and on the failure arms alike;
   grow = tgrow_specX CTX0 (post-implication; its position-free live-count premises along prhPg_evs .. [] are derived
   from the entry position by pj_setA_miss_lem.v; its REFUSED arms carry their exclusion under prh_cons_from);
   fuzz_strdup = tfuzz_strdup_specX (post-implication, with THE OUTCOME conjunct); __asan_memcpy / __asan_memset =
   YGcallMxmn.v aintrin_realizes_xm OCpy / OSet (the m-forms). Callee posts are read BY NAME (their top-level
   conjunctions split and picked by type), never by a positional tuple.
   THE DEAD REFUSAL ARM (DEAD-PJSET): under pjsA_pre's prh_cons_from, grow's refused arms are excluded by their own
   exclusion clauses and a NULL strdup with cnt <> fail by fuzz_strdup's outcome clause, at the entry position (grow)
   or the position past grow's events (the strdup); so the failure cut pjsA_FAILc is reached only at the CHOSEN
   failure, cnt + (c - 1) = fail, and its peak and outcome cells are the granted ones (PRH_Base.prh_refused_peak is 0
   there, prh_refused_peak_granted).
   THE MEMNORM KEEP (PRH_Base.v fQmn): the walk's goal is fpostWmR at wle'; the keep `memnorm mem0 -> memnorm mem`
   rides in pjsA_inv / pjsA_invR (YSRrMemnorm.v: an SRr post is opaque, so the keep is in every cut).
   THE RE-HIDING RELATION. pj_free and grow free or reallocate a live block, which can hide shadow again, so their
   texts conclude YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf at the R form of their posts at wle' SEGS RZ_cf, and so does
   tpj_set_specX: every segment statement below is an SRr' at RZ_cf and the walk's goal pjsA_FIN is fpostWmR at wle'.
   The cuts before the first free or realloc (C1, RET, MISS) keep pjsA_inv, the journal at wle; the cuts after one
   (TAIL, FAILc, DUP, EPI) carry pjsA_invR at wle', a copy of pjsA_inv's body over a world relation R
   (pjsA_inv_R_wle ties the two at wle; a wle journal crosses into wle' by YCbqG.v ajournal_xwR_mono with
   YA0nH.wle_wle'). The keep statement has the same two forms (pjsA_frame_kept_stmt, pjsA_frame_kept_stmtR).
   THE HULL BUDGET (lib/Spec/PresetHullBudget.v): pj_free, grow and fuzz_strdup ask hull_budget S Eg of their
   all-granted events at entry. pjsA_g_hull (a Section premise, an instance fact at CfParams_preset) gives it from a
   run position of a run of at most 4 calls (pjsA_pre's length premise) for a list of at most one call's counts;
   the failure cut pjsA_FAILc carries hull_budget S [] for its pj_free.
   Every name is stated at PA := PI_prog_A (the whole-range instance), never at a per-function instance.
   Numerals: 48 / 56 / 40 / 32 / 24 / 16 / 8 (LENGTH: frame, struct size, slot offsets); 6 (the pj type tag of an
   object); pc offsets DERIVED; the pins below are ADDRESS / WORD literals checked by vm_compute. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
Import ListNotations.
Local Open Scope Z_scope.
(* image A's generated PrhImg values (frames, statics, return sites) as the instance every kit name reads *)
#[local] Existing Instance prh_img_A.

(* pc offsets of the cuts from pj_set's entry (DERIVED from the listing: slot index differences times 4) *)
Definition PJSA_PC : Z := A_prog_sigma AS_pj_set - A_prog_base.
Definition PJSA_C1 : Z := PJSA_PC + 56.    (* the `jal pj_get` *)
Definition PJSA_RET : Z := PJSA_PC + 60.   (* `beqz a0`: pj_get's result decides the arm *)
Definition PJSA_TAIL : Z := PJSA_PC + 80.  (* `mv a1, s0` before `jal __asan_memcpy`: the JOIN of both arms *)
Definition PJSA_MISS : Z := PJSA_PC + 112. (* `mv a0, s1` before `jal grow` *)
Definition PJSA_FAIL : Z := PJSA_PC + 124. (* `mv a0, s0` before `jal pj_free` on the refusal path *)
Definition PJSA_EPI : Z := PJSA_PC + 136.  (* the epilogue `ld ra, 40(sp)` *)
Definition PJSA_DUP : Z := PJSA_PC + 168.  (* `mv a0, s2` before `jal fuzz_strdup` *)
Definition PJSA_FR : Z := 48.             (* pj_set's own frame (prh_img_A's pi_frame F_pj_set) *)

(* the callee-saved registers pj_set never writes: gp, tp, s5 .. s11 (s0 .. s4 and sp are restored by the epilogue) *)
Definition PJSA_KEPT : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

(* THE PINS, checked against the listing lib/A/Listing_prog.v (image A' sha256 1be0f53d96cb, slots
   5279 .. 5366, pj_set's 88 words): the entry, this file's seven cut offsets as the instruction words the listing
   holds there, the end of the body (the entry of grow, the next symbol) and the four call targets this walk jumps
   to. 14 facts, by vm_compute. *)
Lemma pjsA_pins :
  A_prog_sigma AS_pj_set = 0x8685c /\ A_prog_slot AS_pj_set = 5279%nat /\
  PJSA_PC + 352 = A_prog_sigma AS_grow - A_prog_base /\
  clookup A_prog_tbl (A_prog_base + PJSA_C1) = Some 0xe01ff0ef /\
  clookup A_prog_tbl (A_prog_base + PJSA_RET) = Some 0x02050a63 /\
  clookup A_prog_tbl (A_prog_base + PJSA_TAIL) = Some 0x00040593 /\
  clookup A_prog_tbl (A_prog_base + PJSA_MISS) = Some 0x00048513 /\
  clookup A_prog_tbl (A_prog_base + PJSA_FAIL) = Some 0x00040513 /\
  clookup A_prog_tbl (A_prog_base + PJSA_EPI) = Some 0x02813083 /\
  clookup A_prog_tbl (A_prog_base + PJSA_DUP) = Some 0x00090513 /\
  A_prog_sigma AS_pj_get = 0x86694 /\ A_prog_sigma AS_pj_free = 0x864e4 /\
  A_prog_sigma AS_fuzz_strdup = 0x85c28 /\ A_prog_sigma AS_grow = 0x869bc.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* the head width at the model's value is at least a word *)
Lemma pjsA_head_wide : forall {cp : CfParams}, cf_head = PresetReqAt.HEAD -> prh_head_wide.
Proof. intros cp H. unfold prh_head_wide. rewrite H. unfold PresetReqAt.HEAD. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Abbreviation AJR R := (ajournal_xR (SK := SK) SEGS B PST ARx R).
(* the world relation past a free or realloc (the re-hide's zone) *)
#[local] Abbreviation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* the class-24 bound pj_free's text asks at entry when v <> 0 (tpj_free_specX's position-free room premise,
   carried by the failure cut pjsA_FAILc) *)
Definition pjsA_PB (S : astate) : Prop := YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* the callee texts this walk composes (the six), each CITED, never unfolded (the header) *)
Definition pjsA_texts (CTX0 : list (list Z)) (dd : nat) : Prop :=
  tpj_get_specX (PA := PA) B ARx SK /\
  tpj_free_specX (PA := PA) B ARx SK CTX0 dd /\
  tgrow_specX (PA := PA) B ARx SK CTX0 /\
  tfuzz_strdup_specX (PA := PA) B ARx SK /\
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OCpy (pa_sigma AS___asan_memcpy) /\
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset).

(* ---- the entry ---- *)
Record PjsEntA : Type := MkPjsEntA {
  jsA_ly : alayout; jsA_S : astate; jsA_Hp : list Z; jsA_W : world SEGS; jsA_regs : bvmap 5 word;
  jsA_mem : word -> option byte; jsA_md : Model; jsA_ch : list (Z * Z * Z);
  jsA_d : Z; jsA_o : Z; jsA_k : Z; jsA_w : Z;
  jsA_ms : list (list Z * PjTree.jv); jsA_tv : PjTree.jv;
  jsA_D : list (Z * Z); jsA_Dw : list (Z * Z);
  jsA_num : Z; jsA_str : Z; jsA_kids : Z; jsA_keys : Z; jsA_n : Z; jsA_cap : Z;
  jsA_kname : list Z; jsA_Lam : list (Z * Z);
  jsA_peak : Z; jsA_cnt : Z; jsA_fail : Z; jsA_ran : Z; jsA_most : Z; jsA_own : Z;
  (* the model-run position of the contract text (PresetRoomPos.iface_room_pos's parameters; the strtod model is
     ReaderRes.jr_strtod, the contract's keyed run) *)
  jsA_x : list Z; jsA_os : list (option nat * option nat * option nat); jsA_i : nat;
  jsA_H0 : list Z; jsA_hist : list YG00.chunk }.
Definition jsA_sp0 (en : PjsEntA) : Z := spZ (jsA_regs en).
Definition jsA_sp1 (en : PjsEntA) : Z := jsA_sp0 en - PJSA_FR.
Definition jsA_klen (en : PjsEntA) : Z := Z.of_nat (length (jsA_kname en)).
(* the contract's footprint: both headers and every block of the two trees *)
Definition pjsA_FP (en : PjsEntA) : list (Z * Z) :=
  (jsA_o en, jsA_o en + 56) :: (jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_D en ++ jsA_Dw en)).

(* the contract's premises of tpj_set_specX (the kit , lib/A/PRH_FnPj.v), verbatim, in its order *)
Definition pjsA_pre (CTX0 : list (list Z)) (dd : nat) (en : PjsEntA) : Prop :=
  let ly := jsA_ly en in let S := jsA_S en in let Hp := jsA_Hp en in let W := jsA_W en in let regs := jsA_regs en in
  let mem := jsA_mem en in let md := jsA_md en in let ch := jsA_ch en in let d := jsA_d en in
  let o := jsA_o en in let k := jsA_k en in let w := jsA_w en in let ms := jsA_ms en in let tv := jsA_tv en in
  let D := jsA_D en in let Dw := jsA_Dw en in let kname := jsA_kname en in let Lam := jsA_Lam en in
  let n := jsA_n en in let cap := jsA_cap en in
  fpre (PA := PA) B ARx (STK_pj_set dd) ly S Hp W regs mem md ch /\
  prh_univ_closure B CTX0 /\
  room_live_cf S /\
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) (jsA_H0 en) (jsA_hist en) S /\
  (length (jsA_os en) <= 4)%nat /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) (length (prhPj_set_evs ms kname n cap)) /\
  getr regs 10 = w64 o /\ getr regs 11 = w64 k /\ getr regs 12 = w64 w /\
  fwin (PA := PA) ly W regs mem d /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) o (PjTree.JObj ms) D /\
  pj_hdrR SEGS (rdW W mem) o 6 (jsA_num en) (jsA_str en) (jsA_kids en) (jsA_keys en) n cap /\ cap <= 2 ^ 54 /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) d ly S Lam W regs mem o /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) w tv Dw /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) d ly S Lam W regs mem w /\ w < YM05.alloc_ceiling /\
  (forall bk, In bk Dw -> ~ In bk D) /\
  (forall x, w <= x < w + 56 -> ~ pj_footR o D x) /\
  pj_apartR Dw o /\
  (PjTree.depth (PjTree.JObj ms) <= Datatypes.S dd)%nat /\ (PjTree.depth tv <= dd)%nat /\
  cstr_ok (PA := PA) W mem k kname /\ kept_at (PA := PA) B Lam k (jsA_klen en + 1) /\
  (forall x, k <= x < k + jsA_klen en + 1 -> ~ pj_footR o D x /\ ~ pj_footR w Dw x) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) /\
  jsA_cnt en + 3 < 2 ^ 64 - 1 /\
  jsA_klen en + 1 + cf_head < cf_malloc_max /\
  (n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max) /\
  blocks_bytes S + LIVE_pj_set n cap (jsA_klen en) <= LIVE_MAX /\
  Permutation (map (fun b => snd b + cf_head) D) (PresetReqAtNoMiss.tblk (PjTree.JObj ms)) /\
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam) nn o D F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms)) /\
  cf_head = PresetReqAt.HEAD /\
  prh_run_at ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) (prhPj_set_evs ms kname n cap).

(* the model's own events of this call (the length the post's position advances by) *)
Definition pjsA_evs (en : PjsEntA) : list PresetReqAt.hev :=
  prhPj_set_evs (jsA_ms en) (jsA_kname en) (jsA_n en) (jsA_cap en).

(* the walk's post: the contract's post body of tpj_set_specX (lib/A/PRH_FnPj.v) under its kit name tpsP_Q (the
   text's post, checked by tpsP_Q_check), over the entry's values *)
Definition pjsA_Q (en : PjsEntA) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  tpsP_Q (PA := PA) B (jsA_x en) (jsA_os en) (jsA_i en) (jsA_H0 en) (jsA_most en) (jsA_own en) (jsA_ly en) (jsA_S en)
    (jsA_W en) (jsA_mem en) (jsA_o en) (jsA_w en) (jsA_ms en) (jsA_tv en) (jsA_D en) (jsA_Dw en) (jsA_kids en)
    (jsA_keys en) (jsA_n en) (jsA_cap en) (jsA_kname en) (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en)
    (jsA_ran en).

(* the walk's goal: the contract's post with the memnorm keep, the R form fpostWmR at the re-hiding relation wle'
   (the text's), at the entry float state *)
Definition pjsA_FIN (dd : nat) (en : PjsEntA) : world SEGS -> config -> Prop :=
  fpostWmR (PA := PA) B ARx SK WR (STK_pj_set dd) (jsA_d en) (pjsA_FP en)
    (jsA_regs en) (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) (pjsA_Q en).

(* the configuration at a cut (pj_set never changes the float state: every callee's post is at fx) *)
Definition pjsA_cfg (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS)) md.

(* ---- what holds at every cut after the prologue ---- *)
Definition pjsA_inv (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  (* the journal from the entry, at the caller-window widened window, footprint = the contract's *)
  AJ (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] ly S Hp W mem md k /\
  (* the caller's window outside the footprint, untouched (fpostW's window clause) *)
  (forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (jsA_W en)) (jsA_mem en) a) /\
  (* pj_set's frame: sp, the six saved registers, s0 = val, s4 = the shadow base, the untouched callee-saved
     registers, and the frame present *)
  spZ regs = jsA_sp1 en /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 40) 8 (raZ (jsA_regs en)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 32) 8 (s0Z (jsA_regs en)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 24) 8 (bv_unsigned (getr (jsA_regs en) 9)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 16) 8 (bv_unsigned (getr (jsA_regs en) 18)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 8) 8 (bv_unsigned (getr (jsA_regs en) 19)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en) 8 (bv_unsigned (getr (jsA_regs en) 20)) /\
  getr regs 8 = w64 (jsA_w en) /\ getr regs 18 = w64 (jsA_k en) /\ getr regs 20 = w64 SHADOW_OFF /\
  (forall r, In r PJSA_KEPT -> getr regs r = getr (jsA_regs en) r) /\
  (forall a, jsA_sp1 en <= a < jsA_sp0 en -> apresent (w_H W) mem a) /\
  (* the read-only view *)
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (* the memnorm keep from the entry memory (PRH_Base.v fQmn; YSRrMemnorm.v srr_inv_laws_imp's P) *)
  (YAkMemnorm.memnorm SEGS (jsA_mem en) -> YAkMemnorm.memnorm SEGS mem).
(* pjsA_inv over a world relation R: the same body with the journal at R (YCbqG.v ajournal_xR); the cuts after a free
   or realloc state it at WR. pjsA_inv_R_wle: pjsA_inv is its instance at wle *)
Definition pjsA_invR (R : world SEGS -> world SEGS -> Prop) (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  AJR R (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] ly S Hp W mem md k /\
  (forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (jsA_W en)) (jsA_mem en) a) /\
  spZ regs = jsA_sp1 en /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 40) 8 (raZ (jsA_regs en)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 32) 8 (s0Z (jsA_regs en)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 24) 8 (bv_unsigned (getr (jsA_regs en) 9)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 16) 8 (bv_unsigned (getr (jsA_regs en) 18)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en + 8) 8 (bv_unsigned (getr (jsA_regs en) 19)) /\
  val_mem SEGS (rdW W mem) (jsA_sp1 en) 8 (bv_unsigned (getr (jsA_regs en) 20)) /\
  getr regs 8 = w64 (jsA_w en) /\ getr regs 18 = w64 (jsA_k en) /\ getr regs 20 = w64 SHADOW_OFF /\
  (forall r, In r PJSA_KEPT -> getr regs r = getr (jsA_regs en) r) /\
  (forall a, jsA_sp1 en <= a < jsA_sp0 en -> apresent (w_H W) mem a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (YAkMemnorm.memnorm SEGS (jsA_mem en) -> YAkMemnorm.memnorm SEGS mem).
Lemma pjsA_inv_R_wle : forall dd en ly S Hp W regs mem md k,
  pjsA_inv dd en ly S Hp W regs mem md k = pjsA_invR (@wle SEGS) dd en ly S Hp W regs mem md k.
Proof. reflexivity. Qed.

(* the memory-side premises of the contract text, at the state a cut names (the entry's, transported): the object, the
   value, the key, and the ledger *)
Definition pjsA_data (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (Lam : list (Z * Z))
  (W : world SEGS) (mem : word -> option byte) : Prop :=
  room_live_cf S /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam W (jsA_regs en) mem (jsA_o en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam W (jsA_regs en) mem (jsA_w en) /\
  cstr_ok (PA := PA) W mem (jsA_k en) (jsA_kname en) /\ kept_at (PA := PA) B Lam (jsA_k en) (jsA_klen en + 1) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en).

(* a struct's placement minus its shadow HULL (the first six conjuncts of prhPj_slot). What a program call keeps:
   the hull of a struct in the caller's window [sp0, sp0 + d) reads shadow bytes past the stack's top when that
   top is not 64-aligned, and no law at a generic ARx says it is, so the cuts after a call carry the object's
   placement in this form; nothing after the first call reads the object's hull (grow asks range_addressable only,
   the inline checks read one shadow byte each) *)
Definition pjsA_place (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world SEGS)
  (mem : word -> option byte) (p : Z) : Prop :=
  4096 <= p /\ prhReader_at B ly S Lam (jsA_regs en) (jsA_d en) p 56 /\ pj_rwR SEGS (rdW W mem) p /\
  amem_range p 56 /\
  (forall a, p <= a < p + 56 -> ~ aowned B ly S a /\ ~ (spZ (jsA_regs en) - STK_pj_set dd <= a < spZ (jsA_regs en))) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 56.

(* pjsA_data at a cut after a call: the object by pjsA_place, the ledger stated by the cut itself (its counters move
   with the arm's allocations) *)
Definition pjsA_data_c (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Lam : list (Z * Z))
  (W : world SEGS) (mem : word -> option byte) : Prop :=
  room_live_cf S /\
  pjsA_place dd en ly S Lam W mem (jsA_o en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam W (jsA_regs en) mem (jsA_w en) /\
  cstr_ok (PA := PA) W mem (jsA_k en) (jsA_kname en) /\ kept_at (PA := PA) B Lam (jsA_k en) (jsA_klen en + 1).

(* ---- the cuts ---- *)

(* C1, at the `jal pj_get`: the entry allocator state, the memory after the prologue; the object's footprint still
   reads as at the entry (the contract's first post arm names the replaced member at the ENTRY memory) *)
Definition pjsA_C1 (dd : nat) (en : PjsEntA) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
  : Prop :=
  pjsA_inv dd en (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) regs mem md k /\
  pjsA_data dd en (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_Lam en) (jsA_W en) mem /\
  getr regs 10 = w64 (jsA_o en) /\ getr regs 11 = w64 (jsA_k en) /\ getr regs 9 = w64 (jsA_o en) /\
  pj_nodeR SEGS (rdW (jsA_W en) mem) (prh_lin (jsA_Lam en)) (jsA_o en) (PjTree.JObj (jsA_ms en)) (jsA_D en) /\
  pj_hdrR SEGS (rdW (jsA_W en) mem) (jsA_o en) 6 (jsA_num en) (jsA_str en) (jsA_kids en) (jsA_keys en)
    (jsA_n en) (jsA_cap en) /\
  pj_nodeR SEGS (rdW (jsA_W en) mem) (prh_lin (jsA_Lam en)) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW (jsA_W en) mem) (pj_footR (jsA_o en) (jsA_D en)) /\
  (* val's footprint reads as at the entry (the FREEORD-COPY conjuncts take val's order list there) *)
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW (jsA_W en) mem) (pj_footR (jsA_w en) (jsA_Dw en)).

(* RET, after pj_get returned z: the allocator state is the entry's (pj_get's m-form post: S' = S, so the model-run
   position is the entry's); the object's footprint still reads as at the entry *)
Definition pjsA_RET (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjsA_inv dd en ly S Hp W regs mem md k /\
  pjsA_data_c dd en ly S (jsA_Lam en) W mem /\
  prh_ledger (PA := PA) B ly S Hp W mem (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) /\
  ablocks B ly S = ablocks B (jsA_ly en) (jsA_S en) /\ Hp = jsA_Hp en /\ S = jsA_S en /\
  getr regs 9 = w64 (jsA_o en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_o en) (PjTree.JObj (jsA_ms en)) (jsA_D en) /\
  pj_hdrR SEGS (rdW W mem) (jsA_o en) 6 (jsA_num en) (jsA_str en) (jsA_kids en) (jsA_keys en) (jsA_n en) (jsA_cap en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W mem) (pj_footR (jsA_o en) (jsA_D en)) /\
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W mem) (pj_footR (jsA_w en) (jsA_Dw en)) /\
  exists z, getr regs 10 = w64 z /\
  prhPj_get_res (PA := PA) (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_o en) (PjTree.JObj (jsA_ms en)) (jsA_D en)
    (jsA_kname en) z.

(* TAIL, the join at `mv a1, s0`: a0 = the 56-byte destination, a2 = 56; everything but the copy is done. The
   destination is the member slot (both arms); Do is the final block list, Lam2 the ledger after the arm's work. *)
Definition pjsA_TAIL (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjsA_invR WR dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists dest Lam2 peak2 cnt2 fail2 ran2 (c : nat) (ok : list bool),
  getr regs 10 = w64 dest /\ getr regs 12 = w64 56 /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 cnt2 fail2 ran2 (jsA_most en) (jsA_own en) /\
  cnt2 = jsA_cnt en + Z.of_nat c /\
  prh_oks ok (jsA_cnt en) (jsA_fail en) c (prh_ev_reqs (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en)))
    (jsA_most en) (jsA_ran en) ran2 /\
  ReaderRes.fail_after (jsA_cnt en) (jsA_fail en) c fail2 /\
  (* the value's own facts, still at the entry's blocks Dw, and the destination's placement *)
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam2 W (jsA_regs en) mem (jsA_w en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam2 W (jsA_regs en) mem dest /\
  (forall x, jsA_w en <= x < jsA_w en + 56 -> ~ (dest <= x < dest + 56)) /\
  dest + 56 <= YM05.alloc_ceiling /\ jsA_w en + 56 <= YM05.alloc_ceiling /\
  (* the two 56-byte writes are permitted: each byte is pj_set's own footprint in a live block, a block made
     since the entry, or a caller frame the footprint names (YCbq.v awr_byte / YCbqG.v wr_fp_frame) *)
  (forall a, (dest <= a < dest + 56) \/ (jsA_w en <= a < jsA_w en + 56) ->
     awr_byte (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
       (ablocks B (jsA_ly en) (jsA_S en)) (ablocks B ly S) ly [] a \/
     wr_fp_frame (pjsA_FP en) (jsA_S en) ly a) /\
  (* the copy's source is readable; neither range holds an image byte *)
  (forall a, jsA_w en <= a < jsA_w en + 56 -> aview SEGS (w_H W) mem a <> None) /\
  (forall a, (dest <= a < dest + 56) \/ (jsA_w en <= a < jsA_w en + 56) -> ~ in_img SEGS a) /\
  (* the contract's post holds of the state the copy and the zeroing make: the arm's own obligation, discharged where the
     arm is proved. The two intrinsics keep W, write only [dest, dest + 56), [w, w + 56) and their own ESTACK
     window below sp1, and leave a0 = 0. *)
  (forall mem' regs' md',
     (forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem' (dest + i) = aview SEGS (w_H W) mem (jsA_w en + i)) ->
     (forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem' (jsA_w en + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (dest <= a < dest + 56) -> ~ (jsA_w en <= a < jsA_w en + 56) ->
        ~ (jsA_sp1 en - ESTACK <= a < jsA_sp1 en) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
     getr regs' 10 = w64 0 ->
     pjsA_Q en ly S Hp W regs' mem' md').

(* MISS, at `mv a0, s1` before the grow call: the key is absent; the allocator state is the entry's; the object's
   footprint still reads as at the entry (so the entry's ORDERED free list of the object holds here,
   PRH_PjOrder.pj_foR_frame) *)
Definition pjsA_MISS (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjsA_inv dd en ly S Hp W regs mem md k /\
  pjsA_data_c dd en ly S (jsA_Lam en) W mem /\
  prh_ledger (PA := PA) B ly S Hp W mem (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) /\
  ablocks B ly S = ablocks B (jsA_ly en) (jsA_S en) /\ Hp = jsA_Hp en /\ S = jsA_S en /\
  getr regs 9 = w64 (jsA_o en) /\
  ~ In (jsA_kname en) (map fst (jsA_ms en)) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_o en) (PjTree.JObj (jsA_ms en)) (jsA_D en) /\
  pj_hdrR SEGS (rdW W mem) (jsA_o en) 6 (jsA_num en) (jsA_str en) (jsA_kids en) (jsA_keys en) (jsA_n en) (jsA_cap en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W mem) (pj_footR (jsA_o en) (jsA_D en)) /\
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W mem) (pj_footR (jsA_w en) (jsA_Dw en)).

(* FAIL, at `mv a0, s0` before pj_free (val): the arm failed at its c-th allocation, which is the CHOSEN failure
   (cnt + (c - 1) = fail: a refusal there is excluded by the callees' outcome clauses under pjsA_pre's prh_cons_from,
   the header's DEAD-PJSET), so the peak and the outcome cells are the granted ones; what the object holds now is
   Do over the ledger Lam2, val is still the entry's tree, and the class-24 count is within its bound (pj_free's
   position-free text's PB: a failed call keeps the model-run position, which bounds it by counts_of_room_pos_rl);
   the journal is at WR (grow ran), and the last conjunct is pj_free's hull budget (hull_budget S [], what the
   failed callee's budget leaves after its use) *)
Definition pjsA_FAILc (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjsA_invR WR dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists Lam2 peak2 fail2 ran2 (c : nat) (ok : list bool) Do Lr,
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 (jsA_cnt en + Z.of_nat c) fail2 ran2 (jsA_most en) (jsA_own en) /\
  prh_oks ok (jsA_cnt en) (jsA_fail en) c (prh_ev_reqs (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en)))
    (jsA_most en) (jsA_ran en) ran2 /\
  ReaderRes.fail_after (jsA_cnt en) (jsA_fail en) c fail2 /\
  Permutation (jsA_Lam en) (jsA_D en ++ jsA_Dw en ++ Lr) /\ Permutation Lam2 (Do ++ jsA_Dw en ++ Lr) /\
  prhPj_blocks B (jsA_ly en) (jsA_S en) (jsA_Lam en) ly S Lam2 /\
  ~ In (jsA_kname en) (map fst (jsA_ms en)) /\
  (1 <= c <= length (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en)))%nat /\
  nth (c - 1) ok true = false /\ (forall i, (i < c - 1)%nat -> nth i ok true = true) /\
  jsA_cnt en + Z.of_nat (c - 1) = jsA_fail en /\
  peak2 = Z.max (jsA_peak en) (Ledger.lsum Lam2) /\
  pjsA_PB S /\
  (exists Dold Dnew Dr, Permutation (jsA_D en) (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
     prhPj_new B (jsA_ly en) (jsA_S en) Dnew /\
     (c = 1%nat /\ Dold = [] /\ Dnew = [] \/
      jsA_n en = jsA_cap en /\ c = 2%nat /\ Dold = kids_blkR (jsA_kids en) (jsA_cap en) /\
        (exists k', Dnew = [(k', 56 * cap2R (jsA_cap en))]) \/
      jsA_n en = jsA_cap en /\ c = 3%nat /\
        Dold = kids_blkR (jsA_kids en) (jsA_cap en) ++ keys_blkR 6 (jsA_keys en) (jsA_cap en) /\
        exists k' y', Dnew = [(k', 56 * cap2R (jsA_cap en)); (y', 8 * cap2R (jsA_cap en))])) /\
  (* what the object reads once val's blocks are freed: the ARM owes it, because only the arm knows how the
     object was grown. The journal below is exactly pj_free (val)'s - it writes val's header and val's blocks and
     nothing else - with the call rule's extension clause (an object in the caller's window lies inside that
     journal's window, so only this clause keeps it), and Lam3 is the ledger list it leaves *)
  (forall md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3,
     AJR WR (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en)
       ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en)))
       ly S Hp W mem md0 [] ly3 S3 Hp3 W3 mem3 md3 k3 ->
     (forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en ->
        ~ inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a ->
        aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a) ->
     Permutation Lam3 (Do ++ Lr) ->
     pj_fdR SEGS (rdW W3 mem3) (prh_lin Lam3) (PjTree.depth (PjTree.JObj (jsA_ms en))) (jsA_o en) Do /\
     (c = length (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en)) ->
        pj_nodeR SEGS (rdW W3 mem3) (prh_lin Lam3) (jsA_o en) (PjTree.JObj (jsA_ms en)) Do)) /\
  (* val is still whole, and it is pj_free's argument *)
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam2 W (jsA_regs en) mem (jsA_w en) /\
  PresetHullBudget.hull_budget S [].

(* DUP, at `mv a0, s2` before the fuzz_strdup call: grow has run (or had nothing to do). Dold / Dnew / Dr: the
   object's blocks grow replaced, the fresh ones, the rest (the contract's second and third post arms name them); the model-run
   position is past grow's c granted reallocs (fuzz_strdup's live-set premises follow from it by counts_of_room_pos_rl), and the room fuzz_strdup asks is left (from LIVE_pj_set). The object's ORDERED free list
   at this state (the last conjunct: the members' slots as the entry's ordered premise gives them, the arrays at the
   capacity cap2v, which is the model's PresetReqAt.ncap (S |ms|) of the object AFTER the append) is what the
   appended arm's FREEORD-COPY conjunct is built from *)
Definition pjsA_DUP (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjsA_invR WR dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  exists Lam2 peak2 (c : nat) (ok : list bool) Do Lr kids2 keys2 cap2v Dold Dnew Dr,
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) /\
  prh_oks ok (jsA_cnt en) (jsA_fail en) c (prh_ev_reqs (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en)))
    (jsA_most en) (jsA_ran en) (jsA_ran en) /\
  (forall i, (i < c)%nat -> nth i ok true = true) /\
  ~ (jsA_cnt en <= jsA_fail en < jsA_cnt en + Z.of_nat c) /\
  Permutation (jsA_Lam en) (jsA_D en ++ jsA_Dw en ++ Lr) /\ Permutation Lam2 (Do ++ jsA_Dw en ++ Lr) /\
  prhPj_blocks B (jsA_ly en) (jsA_S en) (jsA_Lam en) ly S Lam2 /\
  ~ In (jsA_kname en) (map fst (jsA_ms en)) /\
  Permutation (jsA_D en) (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
  prhPj_new B (jsA_ly en) (jsA_S en) Dnew /\
  (jsA_n en < jsA_cap en /\ c = 0%nat /\ kids2 = jsA_kids en /\ keys2 = jsA_keys en /\ cap2v = jsA_cap en /\
     Dold = [] /\ Dnew = []
   \/ jsA_n en = jsA_cap en /\ c = 2%nat /\ cap2v = cap2R (jsA_cap en) /\
     Dold = kids_blkR (jsA_kids en) (jsA_cap en) ++ keys_blkR 6 (jsA_keys en) (jsA_cap en) /\
     Dnew = [(kids2, 56 * cap2R (jsA_cap en)); (keys2, 8 * cap2R (jsA_cap en))]) /\
  peak2 = Z.max (jsA_peak en) (Ledger.lsum Lam2) /\
  jsA_n en < cap2v /\
  (exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en + c)%nat (jsA_H0 en)
     hist S) /\
  blocks_bytes S + (jsA_klen en + 1 + cf_head) <= LIVE_MAX /\
  (* the object now has room for one more member: it is still its own tree, over the blocks Do, and its slot
     arrays are the (possibly new) blocks of Lam2 *)
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (jsA_o en) (PjTree.JObj (jsA_ms en)) Do /\
  pj_hdrR SEGS (rdW W mem) (jsA_o en) 6 (jsA_num en) (jsA_str en) kids2 keys2 (jsA_n en) cap2v /\
  pj_slots_atR (prh_lin Lam2) 6 kids2 keys2 (jsA_n en) cap2v /\
  getr regs 9 = w64 (jsA_o en) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam2) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
  pjsA_data_c dd en ly S Lam2 W mem /\
  (* the block lists IN ORDER: grow replaced the arrays at the front of the object's list and kept the members'
     blocks Dr where they were *)
  jsA_D en = Dold ++ Dr /\ Do = Dnew ++ Dr /\
  (* the capacities are the model's (the entry's ordered premise forces cap = ncap |ms|; cap2v is then the model's
     capacity AFTER the append, ncap (S |ms|) = gcap |ms| (ncap |ms|)) *)
  jsA_cap en = Z.of_nat (PresetReqAt.ncap (length (jsA_ms en))) /\
  cap2v = Z.of_nat (PresetReqAt.ncap (Datatypes.S (length (jsA_ms en)))) /\
  (* the object's ORDERED free list here (PjFoMember.pfm_slots: fo's member slots, value then key) *)
  (forall nn, (PjTree.depth (PjTree.JObj (jsA_ms en)) <= nn)%nat ->
     exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam2) nn (jsA_o en) Do F /\
       map (fun b => snd b + PresetReqAt.HEAD) F =
         PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (jsA_ms en) ++
         PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (jsA_ms en))))) /\
  (* val's footprint reads as at the entry (the appended arm's FREEORD-COPY takes val's order list there) *)
  pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W mem) (pj_footR (jsA_w en) (jsA_Dw en)).

(* EPI, at the epilogue: the walk's post holds at this state, a0 included *)
Definition pjsA_EPI (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjsA_invR WR dd en ly S Hp W regs mem md k /\ pjsA_Q en ly S Hp W regs mem md.

(* ---- the segment statements (one file each); each takes the contract's premises (pjsA_pre) and concludes at the
   re-hiding relation (YA0nH.SRr' at RZ_cf), as the contract does ---- *)
Definition pjsA_seg_epi (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjsA_pre CTX0 dd en -> pjsA_EPI dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_EPI regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_fail (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjsA_pre CTX0 dd en -> pjsA_FAILc dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_FAIL regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_tail (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjsA_pre CTX0 dd en -> pjsA_TAIL dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_TAIL regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_dup (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjsA_pre CTX0 dd en -> pjsA_DUP dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_DUP regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_miss (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjsA_pre CTX0 dd en -> pjsA_MISS dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_MISS regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_ret (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k, pjsA_pre CTX0 dd en -> pjsA_RET dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_RET regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_c1 (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en regs mem md k, pjsA_pre CTX0 dd en -> pjsA_C1 dd en regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (jsA_W en) (pjsA_cfg PJSA_C1 regs mem md) (pjsA_FIN dd en).
Definition pjsA_seg_entry (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall en, pjsA_pre CTX0 dd en ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (jsA_W en) (cfg_at SEGS (pa_sigma AS_pj_set) (jsA_regs en) (jsA_mem en)
    (jsA_md en)) (pjsA_FIN dd en).

(* ---- the shared keep statement (proved in lib/A/Prog/pj_setA_seg_epi.v): what a program call keeps of pj_set's
   state. EVERY program call of this walk is made at the widest callee window the call rule allows, e1 = 48 + d
   (YCbqGcallW.v aj_call_xW asks o + e1 <= 0 at o = - 48 - d), so the callee's own journal runs at
   (STK1 + 48 + d) (sp0 + d) and its extension clause (HX below, the third premise) keeps every byte of
   [sp1, sp0 + d) outside the callee's footprint - pj_set's six saved registers among them. The journal gives the
   frame's presence and the read-only view. ---- *)
Definition pjsA_frame_kept_stmt (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1,
  pjsA_inv dd en ly S Hp W regs mem md k ->
  AJ (STK1 + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP FP1 a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en -> ~ inFP FP1 a) ->
  (forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a -> ~ inFP FP1 a) ->
  0 <= STK1 -> 0 <= jsA_d en -> ~ YI16.sink_open_fp FP1 ->
  (forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (jsA_W en)) (jsA_mem en) a) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 40) 8 (raZ (jsA_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 32) 8 (s0Z (jsA_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 24) 8 (bv_unsigned (getr (jsA_regs en) 9)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 16) 8 (bv_unsigned (getr (jsA_regs en) 18)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 8) 8 (bv_unsigned (getr (jsA_regs en) 19)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en) 8 (bv_unsigned (getr (jsA_regs en) 20)) /\
  (forall a, jsA_sp1 en <= a < jsA_sp0 en -> apresent (w_H W2) mem2 a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
(* the keep statement over a world relation R: the cut's invariant and the callee's journal at R (a call after a
   free or realloc is made at WR); pjsA_frame_kept_stmt is its instance at wle *)
Definition pjsA_frame_kept_stmtR (R : world SEGS -> world SEGS -> Prop) (dd : nat) : Prop :=
  forall en ly S Hp W regs mem md k STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1,
  pjsA_invR R dd en ly S Hp W regs mem md k ->
  AJR R (STK1 + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP FP1 a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en -> ~ inFP FP1 a) ->
  (forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a -> ~ inFP FP1 a) ->
  0 <= STK1 -> 0 <= jsA_d en -> ~ YI16.sink_open_fp FP1 ->
  (forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (jsA_W en)) (jsA_mem en) a) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 40) 8 (raZ (jsA_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 32) 8 (s0Z (jsA_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 24) 8 (bv_unsigned (getr (jsA_regs en) 9)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 16) 8 (bv_unsigned (getr (jsA_regs en) 18)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en + 8) 8 (bv_unsigned (getr (jsA_regs en) 19)) /\
  val_mem SEGS (rdW W2 mem2) (jsA_sp1 en) 8 (bv_unsigned (getr (jsA_regs en) 20)) /\
  (forall a, jsA_sp1 en <= a < jsA_sp0 en -> apresent (w_H W2) mem2 a) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
Lemma pjsA_frame_kept_stmt_R_wle : forall dd, pjsA_frame_kept_stmt dd = pjsA_frame_kept_stmtR (@wle SEGS) dd.
Proof. reflexivity. Qed.

(* the shadow-visibility facts the cuts after a call need, which no journal clause keeps (MARKED kit facts,
   discharged at the instance ARx := ARcf, pj_setA_vis_inst.v) *)
Definition pjsA_g_vis : Prop :=
  ARx_frame_hull_vis SEGS B ARx /\
  (forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> in_zs B a n -> 0 < n ->
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n) /\
  (forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
     aview SEGS (w_H W) mem (shadow_addr a) <> None).

(* the hull budget's instance fact (a Section premise of the composition, like pjsA_g_vis): the requests are at most
   2 ^ 30 bytes, and at a position of a run of at most 4 calls the meters leave room for one call's counts (at
   CfParams_preset: lib/A/PresetHullPay.v hull_budget_of_room_pos, pj_setA_top.v pjsA_g_hull_preset) *)
Definition pjsA_g_hull : Prop :=
  cf_malloc_max <= 2 ^ 30 /\
  forall sm x os i H0 hist S Eg, (length os <= 4)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL -> PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL ->
  PresetHullBudget.hull_budget S Eg.
End d.

(* ---- the pure facts (lib/A/Prog/pj_setA_glue.v proves each) ---- *)
Definition pjsA_g_node_fd : Prop :=
  forall (segs : list Segment) m lblk t p D n,
  pj_nodeR segs m lblk p t D -> (PjTree.depth t <= n)%nat -> pj_fdR segs m lblk n p D.
Definition pjsA_g_depth_mem : Prop :=
  forall ms i nm (v : PjTree.jv) (dd : nat), nth_error ms i = Some (nm, v) ->
  (PjTree.depth (PjTree.JObj ms) <= Datatypes.S dd)%nat -> (PjTree.depth v <= dd)%nat.
Definition pjsA_g_model_hit : Prop :=
  forall (ms : list (list Z * PjTree.jv)) i (kname : list Z) vi tv,
  nth_error ms i = Some (kname, vi) ->
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) ->
  PjTree.pj_set_model ms kname tv = firstn i ms ++ (kname, tv) :: skipn (Datatypes.S i) ms.
Definition pjsA_g_model_miss : Prop :=
  forall (ms : list (list Z * PjTree.jv)) (kname : list Z) tv, ~ In kname (map fst ms) ->
  PjTree.pj_set_model ms kname tv = ms ++ [(kname, tv)].
Definition pjsA_g_trace_len : Prop :=
  forall (n cap : Z) (kname : list Z),
  length (prhPj_set_trace n cap kname) = if n =? cap then 3%nat else 1%nat.
(* the two live counts read only the block sizes, so they follow the allocator's block list *)
Definition pjsA_g_counts_swap : Prop :=
  forall (S1 S2 : astate) (a b c : list Z),
  Permutation (map snd (blocks S1)) (a ++ c) -> Permutation (map snd (blocks S2)) (b ++ c) ->
  YGcfRoomLive.sec_cnt S2 <= YGcfRoomLive.sec_cnt S1 + Z.of_nat (length b) /\
  YGcfRoomLive.ccnt24 S2 <= YGcfRoomLive.ccnt24 S1 + Z.of_nat (length b).
Definition pjsA_g_counts_eq : Prop :=
  forall (S1 S2 : astate), Permutation (map snd (blocks S1)) (map snd (blocks S2)) ->
  YGcfRoomLive.sec_cnt S1 = YGcfRoomLive.sec_cnt S2 /\ YGcfRoomLive.ccnt24 S1 = YGcfRoomLive.ccnt24 S2.
Definition pjsA_g_ab_snd : Prop :=
  forall (B : asyms) ly S, map snd (ablocks B ly S) = map snd (blocks S).
Definition pjsA_glue {ci : CfImg} {cp : CfParams} : Prop :=
  pjsA_g_node_fd /\ pjsA_g_depth_mem /\ pjsA_g_model_hit /\ pjsA_g_model_miss /\ pjsA_g_trace_len /\
  pjsA_g_counts_swap /\ pjsA_g_counts_eq /\ pjsA_g_ab_snd.
