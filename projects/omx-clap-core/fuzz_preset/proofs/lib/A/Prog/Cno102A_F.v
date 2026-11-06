(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the LAST TWO
   SEGMENTS of the re-walk of check_no_overread (cno) against the kit's text tcheck_no_overread_specX: CA10 Free (three
   pj_free, three __wrap_free) and CA11 End (the frame's shadow poisoned, its magic, __asan_set_shadow_f5, the inline
   release of the class-3 fake frame, the epilogue, `ret` with a0 = s5 = r). Lane CnoA102f (a Theorem Labs lane, #102 plan
   the internal file PLAN-cno-caw-102.md sections 5.0 / 5.1 rows CA10 / CA11).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   CONTRACT: lib/A/Prog/Cno102A_Base.v (on the kit cut 7cdbb61b5fa0): the start cut
   cn_at_free / CN_FREE (1060, A' 0x81d28), the exit cn_ex_ret (the function's exit, the text's full post cn_Q at the
   wild budget wbudget [] 6, under the kit's fpostFb, which is at the walk's relation wle' SEGS RZ_cf), the image facts
   cn_img. THIS FILE adds the one cut between its two segments, CN_END (1108, A' 0x81d58, after the third free), as
   cn_at_end / cn_ex_end, and CA10's inner cut CN_FRCUT.
   THE RE-HIDING MOVE: a free can hide shadow again, so every cut here (the base's cn_at_free, used as its R form
   cn_at_freeR at wle' SEGS RZ_cf, and this file's cn_pjm, cn_at_fr, cn_at_end) lies AFTER a free (its journal from
   entry spans parse_noting, pj_free, __wrap_free): this file's cuts are stated in place over the base's cn_baseR at
   R := wle' SEGS RZ_cf (lib/Reusable/YA0nH.v wle', lib/Reusable/YGcfRehidePost.v RZ_cf), and the four segment
   statements conclude SRr' SEGS RZ_cf (YA0nH.v: SRrG at wle'). CA11 crosses no free itself, but its journal from
   entry does, and the engine's runners and call rules over R tie the journal's R to SRrG's, so it concludes SRr'
   too. The halves compose by YSRrG.v SRr'_bind.
   THE HULL (the threaded allocator hull premise, lib/Spec/PresetHullBudget.v): every cut here carries ONE conjunct
   `PresetHullBudget.hull_budget S <list>`, LAST, over the base's literal suffixes of the all-granted list still to
   pay: cn_pjm by the structs still to free (cn_hrest_rd0 / pf1 / pf2 / pf0, cn_hrest_pjm, stepped by
   cn_hrest_pjm_step across a pj_free whose post uses `hull_used S S' []`), cn_at_fr cn_hrest_pf0, cn_at_end the
   three frees' cn_hF3 (= cn_hrest_pf0: a free keeps both meters, so its admission is the same budget).
   INPUTS: every path at the kit cut's blob (lib/A/PRH_FnPj.v 5aca5cbe2cfb: tpj_free_specX; PRH_FnCheck.v c40cf3fdcd2a;
   PRH_Base.v ef7c8ca98529; PRH_PjOrder.v e5917626b82b; the engine of the cut, YCbqG.v / YCbqGwild.v: the journal at a
   wild budget); the kit of this lane lib/A/Prog/Cno102_FKit.v (pjf_fd_of_node, aj_flag_store_x_inv,
   aj_set_shadow_at_xm, aj_free_null_at_x) and lib/Prog/PvFdZeroR.v (pv_fd_zeroR).
   PIN: asan 1be0f53d96cb9d6c (facts 8f3e7e1a07f1). PARAMETRIC over {PA : PAImg A_prog_listing}.
   THE CODE (the A' disassembly of check_no_overread; DERIVED offsets inside cno; slot kinds re-checked on
   lib/A/Listing_prog.v, the cut's blob 7ed1529926bd, CN_SLOT = 201):
     1060 mv a0, s9 ; 1064 jal pj_free ; 1068 ld a0, 48(s1) ; 1072 jal pj_free ; 1076 mv a0, s3 ; 1080 jal pj_free ;
     1084 mv a0, s10 ; 1088 jal __wrap_free ; 1092 ld a0, 40(s1) ; 1096 jal __wrap_free ; 1100 mv a0, s6 ;
     1104 jal __wrap_free ;                                                                       [CA10]
     1108 li a0, -8 ; 1112-1192 21 x `sb a0, off(s2)` (the struct slots' shadow re-poisoned) ; 1196 / 1200 a0 =
     0x45e0360e ; 1204 sd a0, 0(s11) (the frame's magic) ; 1208 ld s3, 32(s1) (the fake-frame pointer, = F) ;
     1212 beqz s3 (NOT taken: F <> 0; the real-stack arm 1240-1396 is unreachable, the base's refutation of the
     fallback) ; 1216 li a1, 64 ; 1220 mv a0, s2 ; 1224 jal __asan_set_shadow_f5 ; 1228 ld a0, 504(s3) (the flag
     pointer, at F + fs_frame_bytes 3 - 8) ; 1232 sb zero, 0(a0) (the release) ; 1236 j 1400 ; 1400 mv a0, s5 ;
     1404 addi sp, s0, -192 ; 1408-1456 13 x ld (the saved registers) ; 1460 addi sp, sp, 192 ; 1464 ret.  [CA11]
   g_own_ran_out / g_most: every cut of this file carries them in its LEDGER, `prh_ledger .. ran (ci_most D) ownl`
   (ownl: the byte the code holds), from cn_at_free through CN_FRCUT and CN_END to the exit's ledger.
   THE ROOM POSITION (the cut texts' post-implication form): under ownl = 0 (no copy refused, the only arm the text's position
   clause covers) every cut carries cn_prog D E S over the events made since entry, E = C3 ++ revs3 ++ (the pj_free part
   cn_fpj at CN_FRCUT | the whole cn_fevs at CN_END), as the B' twin's cuts do; at CN_END that is ck_cno_evs by
   cn_ck_cno_evs. The runtime frees' advance is PROVED (PresetRoomPosKeep room_pos_keep_free).
   NAMED ARGUMENTS (Section hypotheses, owners): HPJFREE (the kit's text tpj_free_specX, owned by the kit); AFREE (the free
   wrapper row in the re-hiding form afree_realizes_cf_rh, lib/Reusable/YG0dcfR.v); SS5M
   (aset_shadow_realizes_xm at the walk's relation for __asan_set_shadow_f5: the frozen contract FCiface.v:1426 with
   the memnorm keep, owner a Theorem Labs lane, YGcallMxmn's family 1 has no set_shadow row); IMG (the base's cn_img). No
   other.
   NO STATE PREMISE: the former PJF-TIE (a filled struct's pj_free order list F has the model's pj_frees (okof o) x
   as its sizes) is CLOSED at the cut: tparse_noting_specX's Some arm states it (PRH_FnCheck.v c40cf3fdcd2a :718-720,
   under CFHEAD-16), the readings make it and cn_at_free carries it (the base's cn_fo). CNO-COPY: cn_at_fr /
   cn_at_end carry `ownl <> 0 -> cn_cdead D` from cn_at_free, so CA11 states own' = 0 at every consumer run.
   Numerals: offsets above (DERIVED); 192 / 32 / 40 / 48 / 504 / 64 (LENGTH: frame, slot and shadow-range offsets);
   3 (the frame class); 245 (WORD: the shadow byte 0xf5); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YG0lawscf.
(* the re-hiding move: SRr' / wle' (YA0nH), SRr'_bind (YSRrG), the zone RZ_cf (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger PvFdZeroR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetLiveBounds
  PresetReqAt PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_StepKit Cno102_FKit
  Cno102A_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- this file's cut and the sites of its calls: DERIVED byte offsets inside check_no_overread ---- *)
Definition CN_PJF1 : Z := 1064.
Definition CN_PJF2 : Z := 1072.
Definition CN_PJF3 : Z := 1080.
Definition CN_FR1 : Z := 1088.
Definition CN_FR2 : Z := 1096.
Definition CN_FR3 : Z := 1104.
Definition CN_END : Z := 1108.
Definition CN_SS5 : Z := 1224.
Definition CN_SS5R : Z := 1228.
Definition CN_RET : Z := 1464.

Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Instance CF_PL : PAListing A_prog_listing := PL_cno_A.
#[local] Instance CF_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* the walk's allocator relation, the cf instance (S1KitAlloc's ARxs, YGcallcf.v; FuzzFree.v:379, Caw102A_Base.v) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
Variable CTX0 : list (list Z).

(* ---- CN_FR (1084, A' 0x81d40, after the third pj_free; CA10's inner cut between its pj_free half and its free
   half): the three trees are gone (Lam back to the entry's, their blocks out of ablocks), the three copies still
   live; s3 / s9 are no longer read ---- *)
Definition CN_FRCUT : Z := 1084.
(* a copy at the frees: NULL, or a live runtime block of size + 16 whose base is no harness head (the free wrapper's
   premises; its bytes are no longer read) *)
Definition cn_cpy (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (r : Z) : Prop :=
  r = 0 \/ (In (r, cn_size D + 16) (ablocks B ly S) /\ ~ In r Hp).
(* THE pj_free PART of the frees' events (cn_fevs without its three HFr; the base's cn_fevs is this ++ the HFr x3 by
   its definition): the accepted trees' pj_free by the ranout cases, the model of record's p1_tfree *)
Definition cn_fpj (D : cn_in) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  if cn_ro D o1 then []
  else if cn_ro D o2 then PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o1
  else PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o1 ++ PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o2 ++
       PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o0.
(* AFTER a free (the journal from entry spans parse_noting and the three pj_free): stated in place at the walk's
   relation, cn_baseR at wle' SEGS RZ_cf; the hull budget at stage pf0 (after the three pj_free) *)
Definition cn_at_fr (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z))
  (peak cnt ran r1 r2 r3 r ownl : Z) : Prop :=
  cn_baseR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [(21%bv, r); (22%bv, r3); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\
  cn_cpy D ly S Hp r1 /\ cn_cpy D ly S Hp r2 /\ cn_cpy D ly S Hp r3 /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl /\
  ci_peak D <= peak /\ ci_cnt D <= cnt <= ci_cnt D + 3 * ck_ncalls (ci_x D) /\
  room_live_cf S /\
  Permutation Lam (ci_Lam D) /\
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 r3 ++ ablocks B (ci_ly D) (ci_S D)) /\
  0 <= ownl < 256 /\ ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) /\
  (* the events made since entry, through the three pj_free (no copy refused) *)
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\ exists o1 o2 o0,
     cn_prog D (cn_C3 D ++ cn_revs3 D o1 o2 o0 ++ cn_fpj D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0) /\
  (* a refused copy: dead at a consumer run (the base's cn_cdead, for the exit's CNO-COPY conjunct) *)
  (ownl <> 0 -> cn_cdead D) /\
  PresetHullBudget.hull_budget S (cn_hrest_pf0 (ci_x D)).
Definition cn_ex_fr (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 r ownl,
  c = @cn_cfg SEGS fxk (cn_pc CN_FRCUT) regs mem md /\
  cn_at_fr D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl.

(* ---- CN_END (CA11's start): the three structs and the three copies freed; the registers the epilogue reads
   (sp = s1, s0 = the entry sp, s2 = F's shadow, s11 = F, s5 = r), the fake-frame pointer at s1 + 32, and the
   state facts cn_Q asks, at the current state; under ownl = 0 the events made are the text's whole list (by
   cn_ck_cno_evs), as the B' twin's cnb_at_end states it. AFTER the frees: cn_baseR at wle' SEGS RZ_cf; the hull
   budget over the three frees' cn_hF3 (they keep both meters; CA11 makes no allocator call) ---- *)
Definition cn_at_end (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z))
  (peak cnt ran r ownl : Z) : Prop :=
  cn_baseR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [(21%bv, r)]) /\
  rdword (aview SEGS (w_H W) mem) (cn_S1 D + 32) = Some (cn_F D) /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl /\
  Permutation Lam (ci_Lam D) /\ Permutation (ablocks B ly S) (ablocks B (ci_ly D) (ci_S D)) /\
  ci_peak D <= peak /\ ci_cnt D <= cnt <= ci_cnt D + 3 * ck_ncalls (ci_x D) /\
  room_live_cf S /\
  ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) /\
  (ownl = 0 -> exists o1 o2 o0,
     cn_prog D (cn_C3 D ++ cn_revs3 D o1 o2 o0 ++ cn_fevs D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0) /\
  (ownl <> 0 -> cn_cdead D) /\
  PresetHullBudget.hull_budget S (cn_hF3 (ci_x D)).
Definition cn_ex_end (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r ownl,
  c = @cn_cfg SEGS fxk (cn_pc CN_END) regs mem md /\ cn_at_end D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl.

(* ---- THE TWO SEGMENT STATEMENTS (the base's FORWARD form, the internal file lane-102.md :29-30): generic P with its runner laws and
   the call law (both segments cross calls whose posts give the memnorm keep: pj_free's fpostWm, __wrap_free's leaf,
   set_shadow's SS5M). Each concludes SRr' SEGS RZ_cf (the walk's relation wle' SEGS RZ_cf: the run, or the
   journal from entry, crosses a free). CA10 takes no premise beyond the base's: the free-order ties of the three
   structs (the former PJF-TIE) come from the readings, carried by cn_at_free's cn_fo; the start cut is the base's
   cn_at_freeR at wle' SEGS RZ_cf (AFTER the readings' frees) ---- *)
Definition cn_seg_freeP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_at_freeR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl
    st1 st2 st3 o1 o2 o0 ->
  P mem ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc CN_FREE) regs mem md)
    (fun W' c' => cn_ex_end D W' c' /\ P (ms_mem (cfg_ms c'))).
(* CA10's two halves: the three pj_free (CN_FREE -> CN_FRCUT) and the three __wrap_free (CN_FRCUT -> CN_END) *)
Definition cn_seg_pjfP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_at_freeR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl
    st1 st2 st3 o1 o2 o0 ->
  P mem ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc CN_FREE) regs mem md)
    (fun W' c' => cn_ex_fr D W' c' /\ P (ms_mem (cfg_ms c'))).
Definition cn_seg_frP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_at_fr D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl -> P mem ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc CN_FRCUT) regs mem md)
    (fun W' c' => cn_ex_end D W' c' /\ P (ms_mem (cfg_ms c'))).
(* CA10 from its halves (SRr'_bind at the inner cut) *)
Lemma cn_seg_free_of_halves : cn_seg_pjfP -> cn_seg_frP -> cn_seg_freeP.
Proof.
intros H1 H2 P PL PC D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0
  HPRE HAT HP.
eapply SRr'_bind;
  [exact (H1 P PL PC D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HPRE HAT HP)|].
intros W2 c2 _ ((fxk2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Lam2 & peak2 & cnt2 & ran2 & q1 & q2 & q3 & r' & ownl2 &
  -> & HAT2) & HP2).
exact (H2 P PL PC D fxk2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak2 cnt2 ran2 q1 q2 q3 r' ownl2 HPRE HAT2 HP2).
Qed.
Definition cn_seg_endP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl,
  cn_pre (fx := fx) B ARcfx CTX0 D -> cn_at_end D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl -> P mem ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc CN_END) regs mem md)
    (fun W' c' => cn_ex_ret (fx := fx) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c'))).


(* ==== CA10a: the three pj_free (1060 -> 1084) ==== *)
(* the hull budget between the pj_free calls, by the structs still to free: three (stage rd0, none freed yet), two
   (pf1), one (pf2), none (pf0); a longer list (never reached) keeps rd0, so every step below drops a prefix *)
Definition cn_hrest_pjm (D : cn_in) (rest : list (Z * cn_st)) : list PresetReqAt.hev :=
  match length rest with
  | 0%nat => cn_hrest_pf0 (ci_x D)
  | 1%nat => cn_hrest_pf2 (ci_x D)
  | 2%nat => cn_hrest_pf1 (ci_x D)
  | _ => cn_hrest_rd0 (ci_x D)
  end.
(* a call that used nothing ([], pj_free's hull_used) leaves a budget for any suffix of the budget's list *)
Lemma cn_hull_skip : forall S S' E R, PresetHullBudget.hull_budget S (E ++ R) -> PresetHullBudget.hull_used S S' [] ->
  PresetHullBudget.hull_budget S' R.
Proof.
intros S S' E R H U.
exact (PresetHullBudget.hull_budget_app S S' E R H (PresetHullBudget.hull_used_infix S S' [] [] E U)).
Qed.
(* one pj_free: the budget for the structs left (the base's splits cn_hrest_<prev> x = _ ++ cn_hrest_<stage> x) *)
Lemma cn_hrest_pjm_step : forall D p rest S S2,
  PresetHullBudget.hull_budget S (cn_hrest_pjm D (p :: rest)) -> PresetHullBudget.hull_used S S2 [] ->
  PresetHullBudget.hull_budget S2 (cn_hrest_pjm D rest).
Proof.
intros D p rest S S2 H U.
destruct rest as [|p1 [|p2 [|p3 rest]]]; cbv beta iota delta [cn_hrest_pjm length] in H |- *.
- rewrite (cn_hrest_pf0_split (ci_x D)) in H. exact (cn_hull_skip S S2 _ _ H U).
- rewrite (cn_hrest_pf2_split (ci_x D)) in H. exact (cn_hull_skip S S2 _ _ H U).
- rewrite (cn_hrest_pf1_split (ci_x D)) in H. exact (cn_hull_skip S S2 _ _ H U).
- exact (cn_hull_skip S S2 [] (cn_hrest_rd0 (ci_x D)) H U).
Qed.
(* the state between the pj_free calls: the structs still to free (rest), each open and holding its tree or the zero
   struct over the CURRENT ledger list; the blocks of the freed ones gone from Lam and ablocks; AFTER a free (cn_baseR
   at wle' SEGS RZ_cf); the hull budget by rest *)
Definition cn_Dofs (rest : list (Z * cn_st)) : list (Z * Z) := concat (map (fun p => cn_Dof (snd p)) rest).
Definition cn_pjm (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran ownl r1 r2 r3 : Z)
  (rest : list (Z * cn_st)) : Prop :=
  cn_baseR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k 6 /\
  cn_slots D W mem r1 r2 /\
  cn_cpy D ly S Hp r1 /\ cn_cpy D ly S Hp r2 /\ cn_cpy D ly S Hp r3 /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl /\
  ci_peak D <= peak /\ ci_cnt D <= cnt <= ci_cnt D + 3 * ck_ncalls (ci_x D) /\
  room_live_cf S /\
  Forall (fun p => In (fst p) [cn_d1 D; cn_d2 D; cn_d3 D] /\ cn_open W mem (fst p) /\ cn_doc W mem Lam (fst p) (snd p))
    rest /\
  List.NoDup (map fst rest) /\
  Permutation Lam (cn_Dofs rest ++ ci_Lam D) /\
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 r3 ++ ck_hblks (cn_Dofs rest) ++ ablocks B (ci_ly D) (ci_S D)) /\
  (forall a k, In (a, k) (cn_Dofs rest) -> ~ In (a - cf_head, k + cf_head) (ablocks B (ci_ly D) (ci_S D))) /\
  PresetHullBudget.hull_budget S (cn_hrest_pjm D rest).

Lemma cn_cpy_of_copy : forall D ly S Hp W mem r, cn_copy B D ly S Hp W mem r -> cn_cpy D ly S Hp r.
Proof. intros D ly S Hp W mem r [H | (H1 & H2 & _)]; [left; exact H | right; exact (conj H1 H2)]. Qed.

(* at CN_FREE: the three structs to free, in the code's order d1, d2, d3 *)
Lemma cn_pjm_of_free : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cn_at_freeR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl
    st1 st2 st3 o1 o2 o0 ->
  cn_pjm D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 [(cn_d1 D, st1); (cn_d2 D, st2); (cn_d3 D, st3)] /\
  cn_regsat regs (cn_core D ++ [(19%bv, cn_d3 D); (21%bv, r); (22%bv, r3); (25%bv, cn_d1 D); (26%bv, r1)]) /\
  0 <= ownl < 256 /\ ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HAT.
destruct HAT as (HB & HR & HSL & HMID & HOWN & HRF & _ & _ & HHB).
destruct HMID as (C1 & C2 & C3 & HLG & Hpk & Hcn & HRL & _ & O1 & O2 & O3 & D1 & D2 & D3 & HLam & HAB & HNEW).
split; [|split; [exact HR | exact (conj HOWN HRF)]].
assert (EDofs : cn_Dofs [(cn_d1 D, st1); (cn_d2 D, st2); (cn_d3 D, st3)] = cn_Dof st1 ++ cn_Dof st2 ++ cn_Dof st3).
{ unfold cn_Dofs. cbn [map concat snd]. rewrite app_nil_r. reflexivity. }
split; [exact HB|]. split; [exact HSL|].
split; [exact (cn_cpy_of_copy _ _ _ _ _ _ _ C1)|]. split; [exact (cn_cpy_of_copy _ _ _ _ _ _ _ C2)|].
split; [exact (cn_cpy_of_copy _ _ _ _ _ _ _ C3)|].
split; [exact HLG|]. split; [exact Hpk|]. split; [lia|]. split; [exact HRL|].
split.
{ repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  - split; [left; reflexivity | exact (conj O1 D1)].
  - split; [right; left; reflexivity | exact (conj O2 D2)].
  - split; [right; right; left; reflexivity | exact (conj O3 D3)]. }
split.
{ cbn [map fst]. unfold cn_d1, cn_d2, cn_d3.
  apply NoDup_cons; [cbn [In]; intros [Hx | [Hx | []]]; lia|].
  apply NoDup_cons; [cbn [In]; intros [Hx | []]; lia|].
  apply NoDup_cons; [intros []|]. apply NoDup_nil. }
rewrite EDofs, <- !app_assoc. split; [exact HLam|]. split; [exact HAB|]. split; [exact HNEW | exact HHB].
Qed.

(* at CN_FRCUT: none left *)
Lemma cn_fr_of_pjm : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl,
  cn_pjm D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 [] ->
  cn_regsat regs (cn_core D ++ [(21%bv, r); (22%bv, r3); (26%bv, r1)]) ->
  0 <= ownl < 256 -> ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) ->
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\ exists o1 o2 o0,
     cn_prog D (cn_C3 D ++ cn_revs3 D o1 o2 o0 ++ cn_fpj D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0) ->
  (ownl <> 0 -> cn_cdead D) ->
  cn_at_fr D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl.
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl HM HR Ho Hr HEV HCD.
destruct HM as (HB & HSL & C1 & C2 & C3 & HLG & Hpk & Hcn & HRL & _ & _ & HLam & HAB & _ & HHB).
cbn [cn_Dofs map concat app] in HLam, HAB. unfold cn_Dofs in HLam, HAB. cbn [map concat app ck_hblks] in HLam, HAB.
split; [exact HB|]. split; [exact HR|]. split; [exact HSL|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
split; [exact HLG|]. split; [exact Hpk|]. split; [exact Hcn|]. split; [exact HRL|].
split; [exact HLam|]. split; [|exact (conj Ho (conj Hr (conj HEV (conj HCD HHB))))].
unfold ck_hblks in HAB. cbn [map app] in HAB. exact HAB.
Qed.

End cf.
