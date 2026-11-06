(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1213 of its 1267 lines of code are new or changed and 724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/BTxString.v, with its module paths and module names changed; 485 of its 540 lines of code are new or changed and 1212 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c (a Theorem Labs walk): segment X, the EXIT, B 0x8664c .. 0x866ec,
   over the ONE image-B program listing (lib/B/Listing_prog.v) with the PA-listing engine on YCbqG's
   ajournal_x. The segment's cuts are PvB_Defs.v's: from pv_at_exit (the result code in s5, the fake
   frame still on top, the post's memory part at the fake-frame state) to pv_FINK (the kit's caller-window float post
   fpostWF_xbR of lib/A/PRH_FnParse.v's tparse_value_specX, in the record's relation YA0nH.SRr' segs RZ_cf). The exit
   journal is at the re-hiding relation wle' segs RZ_cf (the string and container calls before it free), so the run
   is YGcallSx.v's aj_flag_store_xR at that relation and the ret is lifted into it (YA0nH.SRr_SRrG).
   Rule 24: proves no function (kind: segment lemma). No released or live-head ajournal_x-form walk of preset's
   parse_value exists; the old-vocabulary measurements (lib/B/Prog/PvHolds.v,
   lib/B/Prog/PvClosed.v, both on other branches) are not sources.
   WHAT THE CODE DOES (the listing, 0x8664c ..): it stores the retired magic 0x45e0360e in the fake frame's word 0;
   s2 (the frame) is non-zero, so it takes the f5 arm and writes 0xf5 into the frame's 8 shadow bytes; it loads the
   runtime's flag cell at frame + 56 and stores a zero byte there (THE INLINE RELEASE: no __asan_stack_free_N symbol
   is linked, so the release is inline in every epilogue); then it moves s5 to a0, restores ra and s0 .. s11 from the
   real frame and returns.
   HOW IT IS PROVED: one run of the listing engine over the whole segment (no shadow check and no UBSan check lies in
   it: its stores are the runtime's own frame bookkeeping) under YGcallSx.v's aj_flag_store_xR, whose write premise is
   `the fake frame is the journal's own frame` (its word 0 and its shadow bytes) plus the flag byte, and whose flag
   premise is read off the run's final symbolic memory; then YC1fP.v's paj_ret_at at the `ret`. The journal the rule
   returns has own = [] at the allocator state stack_free_state 0 pos Sc: fpostWF_xbR's journal, frames the entry's.
   THE POST moves from the fake-frame memory to the released memory (pvx_Qm_move) because the release writes only 17
   bytes - the frame's word 0, its 8 shadow bytes and the runtime-owned flag byte - and every byte the post reads is
   (a) in the image (the ledger's five statics: PSTOK; a read-only text: pa_relro_img), (b) in an allocator block of
   the exit state (the ledger's heads, the subtree's blocks D, a node or text in a block), (c) at or above
   alloc_ceiling (the caller's window: the cursor q, a node on the caller's stack), or (d) in a fake frame of the
   ENTRY state (a node in an outer frame); each is apart from the three written ranges by the allocator's own laws
   (alx_sep / alx_blocks / alx_frames / alx_client_img, the flag law's aowned flag cell, in_app vs the shadow band).
   room_live_cf across the release is the class PrhRoomLive's field RL_stack_free (PRH_Base.v; YGcfRoomLive.v's
   room_live_stack_free at the instance); ablocks and blocks_bytes across it are unchanged (YG01.v's
   blocks_stack_free_state: stack_free_state is a set_fs).
   THE ROOM (pv_Qm's rp_post after room_live_cf: the live list and the run position moved by the trace's events)
   across the release is the exit's: the release is a set_fs of the frames, so the live list (map snd (blocks S)) is
   equal and iface_room_pos never reads st_fs (PvB_Room.v rp_keep_stack_free, rp_post_keep).
   THE MEMORY NORMAL FORM at the ret memory comes from the exit's by YGcallMxmn.v's memnorm_frame_of: the rule's
   continuation gives the run's unrestricted frame_of over its start symbolic memory, and the run's start st_ok makes
   every byte of its write windows writable in the start view (so off the read-only segments, in a segment or below
   TASK_SIZE); the ret (paj_ret_at) leaves the memory as it is.
   Numerals: listing offsets (DERIVED: B pc - B_prog_base 0x816cc): AF_pv_exit = 20352 (PvB_Defs), the ret's 20512;
   64 / 8 / 56 / 160 / 176 are LENGTH (the class-0 fake frame, its shadow, the flag slot's offset, the real frame,
   parse_value's pi_frame); 2 ^ 45 / 2 ^ 46 / 2 ^ 47 and 4096 are LENGTH (atom ranges); 320 / 16560 are DERIVED
   (pi_frame F_parse_value + F_parse_items, LEAF_pv_pi of prh_img_B). The word the code stores (0x45e0360e) comes from
   the listing, never written here. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx YG0p FCiface YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_PjExt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_X_Tree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the segment's symbolic state (atoms: 8 = the entry sp (s0), 18 = the fake frame (s2 = s10),
   27 = its shadow address (s11), 33 = the runtime's flag cell, 34 .. 46 = the entry ra and s0 .. s11 in the real
   frame, in pv_saved's order) ---- *)
Definition PVX_Bx : sv := SLit SHADOW_OFF.
(* no shadow entry (SH = []) and no shadow check in the segment: the shadow span the entries may name is the point
   (0, 0), so every write window - the frame's word 0, its shadow bytes, the flag cell - is apart from it
   (sh_static_ok's cells_safe_b) *)
Definition PVX_Bspan : Z * Z := (0, 0).
Definition PVX_RET : Z := 20512.        (* DERIVED: B 0x866ec - B_prog_base *)
Definition pvx_regs : list sv := sr_set sr_atoms 26%bv (SOff 18 0).
Definition pvx_sav : smem :=
  [ YP09.mkRegion (Some 8%nat) (-160) 0 0 0
      [YP09.mkChunk (-8) (CVal 8 (SOff 34 0)); YP09.mkChunk (-16) (CVal 8 (SOff 35 0));
       YP09.mkChunk (-24) (CVal 8 (SOff 36 0)); YP09.mkChunk (-32) (CVal 8 (SOff 37 0));
       YP09.mkChunk (-40) (CVal 8 (SOff 38 0)); YP09.mkChunk (-48) (CVal 8 (SOff 39 0));
       YP09.mkChunk (-56) (CVal 8 (SOff 40 0)); YP09.mkChunk (-64) (CVal 8 (SOff 41 0));
       YP09.mkChunk (-72) (CVal 8 (SOff 42 0)); YP09.mkChunk (-80) (CVal 8 (SOff 43 0));
       YP09.mkChunk (-88) (CVal 8 (SOff 44 0)); YP09.mkChunk (-96) (CVal 8 (SOff 45 0));
       YP09.mkChunk (-104) (CVal 8 (SOff 46 0))];
    YP09.mkRegion (Some 18%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 27%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 33%nat) 0 1 0 1 [] ].
Definition pvx_facts : facts :=
  mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF 4096 (2 ^ 47) 5);
            (27%nat, mkAF SHADOW_OFF (2 ^ 45) 0); (33%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition pvx_ss : sstate := mkSS AF_pv_exit pvx_regs pvx_sav None pvx_facts.
Definition pvx_K : nat := Eval vm_compute in (run_K A_LIM PVX_Bx [] pvx_ss).
Definition pvx_out : shst * ptrun_status asym :=
  Eval vm_compute in (sym_runN_pi_tok B_prog_tpi B_prog_tw pvx_K PVX_Bx PVX_Bspan [] 3000%N pvx_ss).
Definition pvx_st : shst := fst pvx_out.
Definition pvx_r : ptrun_status asym := snd pvx_out.

Lemma pvx_out_eq : sym_runN_pi_tok B_prog_tpi B_prog_tw pvx_K PVX_Bx PVX_Bspan [] 3000%N pvx_ss = pvx_out.
Proof. vm_cast_no_check (eq_refl pvx_out). Qed.
Lemma pvx_run_eq : sym_runN_pi_tok B_prog_tpi B_prog_tw pvx_K PVX_Bx PVX_Bspan [] 3000%N pvx_ss = (pvx_st, pvx_r).
Proof. rewrite pvx_out_eq. unfold pvx_st, pvx_r. apply surjective_pairing. Qed.
Lemma pvx_r_ok : match pvx_r with PTS_call _ => False | PTS_ecall => False | _ => True end.
Proof. vm_compute. exact I. Qed.
Lemma pvx_j0 : sh_j pvx_st = 0%nat. Proof. vm_compute. reflexivity. Qed.
Lemma pvx_obls : sh_obls pvx_st = []. Proof. vm_compute. reflexivity. Qed.
Lemma pvx_resv : ss_resv (sh_ss pvx_st) = None. Proof. vm_compute. reflexivity. Qed.
Lemma pvx_ret_word : plookup B_prog_tpi (ss_pc (sh_ss pvx_st)) = Some (PW RET_WORD_r).
Proof. vm_compute. reflexivity. Qed.
Lemma pvx_static : sh_static_ok pvx_K PVX_Bx PVX_Bspan [] (ss_facts pvx_ss) (ss_mem pvx_ss) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pvx_KA : (A_LIM <= pvx_K)%nat. Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
(* the flag byte at the end of the run: the fourth region's only chunk *)
Lemma pvx_flag_region :
  nth_error (ss_mem (sh_ss pvx_st)) 3 =
  Some (YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]).
Proof. vm_compute. reflexivity. Qed.

(* a register at the end of the run: its symbolic value read off the final state, then its denotation *)
Ltac pvx_reg HS n :=
  etransitivity; [exact (st_ok_pi_restrict_reg _ _ _ _ _ HS)|];
  lazymatch goal with |- sv_denot _ (sr_get _ ?r) = _ =>
    replace (sr_get (ss_regs (sh_ss pvx_st)) r) with (SOff n 0) by (vm_compute; reflexivity) end;
  cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
(* the run's write windows, region by region *)
Ltac pvx_wr Hin :=
  vm_compute in Hin; destruct Hin as [<- | [<- | [<- | [<- | []]]]].

Section c.
Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PSTX := (@prh_pst prh_img_B).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- Section hypotheses: kit-rule hypotheses and marked instance facts ---- *)
(* the kit rule: YCbqG's 16-field record at the harness head length, as the instance AR_laws_x_xs gives it (the
   sibling segments PvB_D / PvB_D_Lit state it the same way) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* YGcallSx.v:280-292, the three ARx-form hypotheses of aj_flag_store_xR, verbatim (ASFX = YG0dcf astack_free_law_cf,
   FFLX = the two conjuncts of cgif's frame_flag_lawP the rule reads, SFX = YG05cf stack_free_ok_cf) *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* MARKED: YG0dcf.v AR_flag_law_cf with ARcf segs B -> ARx (the cf instance discharges it by its flag law): the
   walk's store to the flag cell needs the cell present, which aj_flag_store_xR's FFLX no longer carries *)
Hypothesis FLAGP : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
  in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < YM05.alloc_ceiling.
(* MARKED image fact, discharged at PI_prog_B: alloc.c's five statics are image bytes the program owns
   (YC80x.v:53's PST_ok, the listing engine's own hypothesis for a program-written static) *)
Hypothesis PSTOK : forall a, Exists (in_zr a) PSTX ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* MARKED instance fact, discharged at lib/A/CfParamsPreset.v (cf_head = 16, preset source/alloc.c:31): a harness
   block's hidden head holds its 8-byte size word *)
Hypothesis HHEAD : 8 <= cf_head.
(* ---- small helpers over the engine's state ---- *)
Lemma pvx_region_nth : forall (fx : YK11.FPState) E ss ms i r,
  st_ok_pi (fx := fx) SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros fx E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma pvx_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.

(* ---- THE POST ACROSS THE RELEASE: pv_Qm at the fake-frame memory gives pv_Qm at the released memory, given that
   the release keeps the bytes of the four places the post reads ---- *)
Lemma pvx_Qm_move : forall en (fr fr' : astate -> Prop) code lyc Sc S2 Hpc (W' : world SEGS) mem mem',
  pv_pre B ARx en ->
  (forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p) ->
  pv_Qm B en fr code lyc Sc Hpc W' mem ->
  ablocks B lyc S2 = ablocks B lyc Sc -> blocks_bytes S2 = blocks_bytes Sc ->
  (room_live_cf Sc -> room_live_cf S2) ->
  rp_keep Sc S2 -> YGcfSecsStep.secs_same Sc S2 ->
  fr' S2 ->
  (forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
     mbyte SEGS (rdW W' mem') (b + i) = mbyte SEGS (rdW W' mem) (b + i)) ->
  (forall x, in_img SEGS x -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x) ->
  (forall x, YM05.alloc_ceiling <= x < 2 ^ 64 -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x) ->
  (forall cid p x, In (cid, p) (frames (pe_S en)) ->
     frame_addr lyc cid p <= x < frame_addr lyc cid p + fs_frame_bytes cid ->
     mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x) ->
  (forall x, writable_at SEGS (rdW W' mem) x -> writable_at SEGS (rdW W' mem') x) ->
  pv_Qm B en fr' code lyc S2 Hpc W' mem'.
Proof.
intros en fr fr' code lyc Sc S2 Hpc W' mem mem' HPRE Efr HQM Eab Ebb HRK HRP HSEC2 Hfr2 KB KI KS KF KW.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
pose proof HFPRE as (HAFN & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HRDP as (_ & _ & _ & _ & Hcur & Hwin & Hqlo & Hqhi & _ & Hsrc & Hhome & _ & Hnode & _ & _ & _ & _ & _).
pose proof Hwin as (He0 & _ & Hetop & _).
pose proof Hcur as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
pose proof (@cf_head_nonneg cp) as Hch.
unfold pv_Qm in HQM |- *.
destruct HQM as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & Hjr & HLED & HROOM & HHULL & HPOS &
  HOUT & HINJ & HMOVE & HFRESH & HPERM & _ & HPEAK & HBYT & HLS & HM).
pose proof HMOVE as (_ & _ & _ & HLP & _).
assert (HinL : forall x, In x D \/ In x (pe_Lam en) -> In x Lam').
{ intros x Hx. apply (Permutation_in _ (Permutation_sym HLP)). apply in_or_app. exact Hx. }
assert (HEB : forall b m, In (b, m) (ablocks B (pe_ly en) (pe_S en)) -> In (b, m) (ablocks B lyc Sc)).
{ intros b m Hb. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. exact Hb. }
pose proof HLED as HLEDu. unfold prh_ledger in HLEDu. destruct HLEDu as (HG & HND & HFA & HPP).
unfold prh_hblock in HFA. rewrite Forall_forall in HFA.
(* the bytes of a ledger block (a harness block of the exit state) *)
assert (HLB : forall a kk x, In (a, kk) Lam' -> a <= x < a + kk ->
  mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
{ intros a kk x Hin Hx. destruct (HFA (a, kk) Hin) as (Hk0 & Hb & _ & _ & _). cbn [fst snd] in Hk0, Hb.
  replace x with ((a - cf_head) + (cf_head + (x - a))) by lia.
  apply (KB _ _ _ Hb). unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia. }
(* the bytes of an entry allocator block *)
assert (HBB : forall b m x, In (b, m) (ablocks B (pe_ly en) (pe_S en)) -> b <= x < b + m ->
  mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
{ intros b m x Hb Hx. replace x with (b + (x - b)) by lia.
  apply (KB _ _ _ (HEB b m Hb)). unfold req_size. destruct (Z.eqb_spec m 0); lia. }
(* the cursor, in the caller's window *)
assert (KQ : forall x, pe_q en <= x < pe_q en + 24 -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x)
  by (intros x Hx; apply KS; lia).
(* the text: a ledger block, a read-only global, or an entry block *)
assert (KT : forall x, pe_text en <= x < pe_text en + Z.of_nat (length (pe_tb en)) ->
  mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
{ intros x Hx. rewrite Hlen in Hx.
  destruct Hhome as [[(b & m & Hb & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hb & _ & H1 & H2)].
  - apply (HLB b m x (HinL _ (or_intror Hb))). lia.
  - apply KI. destruct (Hro x Hx) as ([(s & Hs & _ & Hr) | Hr] & _ & _).
    + exists s. split; [exact Hs | exact Hr].
    + apply pa_relro_img. exact Hr.
  - apply KI. destruct (Hro x Hx) as ([(s & Hs & _ & Hr) | Hr] & _ & _ & _).
    + exists s. split; [exact Hs | exact Hr].
    + apply pa_relro_img. exact Hr.
  - apply (HBB b m x Hb). lia. }
(* the node: a ledger block, an entry block, an entry fake frame, or the caller's window *)
assert (KV : forall x, pe_v en <= x < pe_v en + 56 -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
{ intros x Hx.
  destruct Hvat as [(a & kk & Ha & H1 & H2) | [(b & m & Hb & _ & H1 & H2) | [(cid & p & Hcp & H1 & H2) | (H1 & H2)]]].
  - apply (HLB a kk x (HinL _ (or_intror Ha))). lia.
  - apply (HBB b m x Hb). lia.
  - apply (KF cid p x Hcp). rewrite !Efr. lia.
  - apply KS. lia. }
assert (KD : forall x, pjx_foot (pe_v en) D x -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
{ intros x Hx. unfold pjx_foot in Hx. destruct Hx as [Hx | ([a kk] & Hb & Hx)]; [exact (KV x Hx)|].
  unfold pj_holdsR in Hx. cbn [fst snd] in Hx. exact (HLB a kk x (HinL _ (or_introl Hb)) Hx). }
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
split; [exact Hjr|].
split.
{ (* the ledger: the statics are image bytes, the heads lie in their blocks *)
  unfold prh_ledger. split; [|split; [exact HND | split; [|exact HPP]]].
  - unfold prh_glob in HG |- *. destruct HG as (G1 & G2 & G3 & G4 & G5 & (Gm & Gmr) & (Go & Gor) & Hb).
    assert (KP : forall x, Exists (in_zr x) PSTX -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x)
      by (intros x Hx; apply KI; exact (proj1 (PSTOK x Hx))).
    split; [apply (pjx_val SEGS _ _ _ _ _ G1); intros x Hx; apply KP; unfold prh_pst;
            apply Exists_cons_hd; exact Hx|].
    split; [apply (pjx_val SEGS _ _ _ _ _ G2); intros x Hx; apply KP; unfold prh_pst;
            apply Exists_cons_tl, Exists_cons_hd; exact Hx|].
    split; [apply (pjx_val SEGS _ _ _ _ _ G3); intros x Hx; apply KP; unfold prh_pst;
            apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; exact Hx|].
    split; [apply (pjx_val SEGS _ _ _ _ _ G4); intros x Hx; apply KP; unfold prh_pst;
            apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; exact Hx|].
    split; [apply (pjx_val SEGS _ _ _ _ _ G5); intros x Hx; apply KP; unfold prh_pst;
            apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; exact Hx|].
    (* the two #102 statics g_most / g_own_ran_out (prh_pst's sixth and seventh rows) *)
    split; [split; [apply (pjx_val SEGS _ _ _ _ _ Gm); intros x Hx; apply KP; unfold prh_pst;
            do 5 apply Exists_cons_tl; apply Exists_cons_hd; exact Hx | exact Gmr]|].
    split; [split; [apply (pjx_val SEGS _ _ _ _ _ Go); intros x Hx; apply KP; unfold prh_pst;
            do 6 apply Exists_cons_tl; apply Exists_cons_hd; exact Hx | exact Gor]|].
    exact Hb.
  - rewrite Forall_forall. intros [a kk] Hin. unfold prh_hblock. cbn [fst snd].
    destruct (HFA (a, kk) Hin) as (Hk0 & Hb & Hhp & Hal & Hv). cbn [fst snd] in Hk0, Hb, Hhp, Hal, Hv.
    split; [exact Hk0|]. split; [rewrite Eab; exact Hb|]. split; [exact Hhp|]. split; [exact Hal|].
    apply (pjx_val SEGS _ _ _ _ _ Hv). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
    apply (KB _ _ _ Hb). unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia. }
split; [exact (HRK HROOM)|].
(* the hull use across the release: it keeps both meters (a set_fs) *)
split.
{ destruct HHULL as [HN HT]. destruct HSEC2 as [EN ET]. unfold PresetHullBudget.hull_used. rewrite EN, ET.
  split; assumption. }
split; [exact (rp_post_keep _ _ _ _ HPOS HRP)|].
split; [exact (pv_outc_keep _ _ _ _ _ _ HOUT HRP)|].
split; [exact HINJ|].
split; [exact HMOVE|].
split; [exact HFRESH|].
split; [rewrite Eab; exact HPERM|].
split; [exact Hfr2|].
split; [exact HPEAK|].
split; [rewrite Ebb; exact HBYT|].
split; [exact HLS|].
(* the free order across the release: the same order F of the same blocks D, the footprint's bytes kept *)
assert (FT : forall nlo, pv_ftie en nlo Lam' W' mem D ok -> pv_ftie en nlo Lam' W' mem' D ok).
{ intros nlo Hft Hhd n Hn. destruct (Hft Hhd n Hn) as (F & HF & HFm). exists F. split; [|exact HFm].
  apply (PRH_PjOrder.pj_foR_frame SEGS n _ _ _ _ _ _ _ HF);
    [exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF)
    |apply (pjx_agree_of_bytes SEGS); [exact KD | exact KW]]. }
destruct res as [[t r]|].
- destruct HM as (Hc & Hft & Hin & Hnd & Hnc & Hsum). split; [exact Hc|].
  split; [exact (FT _ Hft)|].
  split; [apply (pjx_in_ok_frame SEGS _ _ _ _ _ _ _ _ Hin);
          [exact KQ | intros x _ Hw; exact (KW x Hw) | exact KT]|].
  split; [|split; [|exact Hsum]].
  + apply (pj_nodeR_frame SEGS t _ _ _ _ _ Hnd). apply (pjx_agree_of_bytes SEGS); [exact KD | exact KW].
  + apply (PvB_Frees.pvf_ncap_frame SEGS t (w_H W') mem (rdW W' mem') _ (pe_v en) D Hnd); [|exact Hnc].
    apply (pjx_agree_of_bytes SEGS); [exact KD | exact KW].
- destruct HM as (Hc & Hft & Haf & Hfd). split; [exact Hc|].
  split; [exact (FT _ Hft)|].
  split; [apply (pjx_in_after_frame SEGS _ _ _ _ _ _ _ Haf); [exact KQ | intros x _ Hw; exact (KW x Hw)]|].
  apply (pjx_fd_frame SEGS _ _ _ _ _ _ Hfd). apply (pjx_agree_of_bytes SEGS); [exact KD | exact KW].
Qed.

(* ---- the segment: a plain run to the continuation post (the run itself is in the record's relation) ---- *)
Lemma pvX_holds : forall en W' ms mdc,
  pv_pre B ARx en -> pv_at_exit B ARx en W' ms mdc ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK B ARx en).
Proof.
intros en W' ms mdc HPRE HEX.
destruct HEX as (fx' & regs & mem & Y & fa & fl & pos & lyc & Sc & Hpc & k & code &
  Ems & HFZ & HFK & HKR & Hcode & HBODY & HQM & HMN).
subst ms.
apply SRr_ret. unfold pv_FINK, YA0nH.SRr'.
(* the exit cut's journal is budgeted (pv_body_x: ajournal_xwR .. WS at wle' segs RZ_cf, WS within CW); the release
   is run on the journal REBASED at the exit depot (YCbqGwild.ajournal_xw_rebaseR) and unbased back at the end
   (ajournal_xw_unbase0R with ajxR_wild, the wild part of the exit depot within the entry's and WS) *)
destruct HBODY as (WS & HBODYw & HWB).
pose proof HBODYw as (HFRM & HinF & Efa & Efl & HJw & HWIN).
pose proof (ajxR_wild HJw) as HWILD.
assert (HJ : ajournal_xR (SK := SK) SEGS B PSTX ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (pe_STK en + pe_e en)
    (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (set_depot (st_depot Sc) (pe_S en)) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)]
    lyc Sc Hpc W' mem mdc k)
  by (eapply YCbqGwild.ajournal_xw_rebaseR; exact HJw).
clear HBODYw.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs.
pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk0. pose proof (ajxR_hi HJ) as J1.
pose proof (ajxR_blk HJ) as J2. pose proof (ajxR_img HJ) as J3. pose proof (ajxR_frm HJ) as J4.
pose proof (ajxR_gone HJ) as Jgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstk.
pose proof (ajxR_extra HJ) as J5. pose proof (ajxR_qt HJ) as HQT.
change (frames (set_depot (st_depot Sc) (pe_S en))) with (frames (pe_S en)) in Hfrs.
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
pose proof HFPRE as (HAFN & _).
pose proof HAFN as (HAR0 & Hra_ok & _).
pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & _).
pose proof Hwin as (He0 & He16 & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (CSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (CLB : kLowShadowBeg = 2147446784) by reflexivity.
assert (CAC : ASAN_CEIL = YM05.alloc_ceiling) by reflexivity.
assert (Esp : pe_sp en = spZ (pe_regs en)) by reflexivity.
set (sh := SHADOW_OFF + fa / 8) in *.
assert (Esh' : sh = SHADOW_OFF + fa / 8) by reflexivity.

(* ---- 1. the frame's places and bounds ---- *)
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfa0 & Hfac & Hfapp).
rewrite <- Efa in Hfa0, Hfac, Hfapp. rewrite Efb in Hfac, Hfapp.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfal32 & _ & Hfbytes & Hfsh).
rewrite <- Efa in Hfal32, Hfbytes, Hfsh. rewrite Efb in Hfbytes, Hfsh.
assert (Esh : shadow_addr fa = sh) by reflexivity.
rewrite Esh in Hfsh.
destruct (FLAGP lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hflpres & Hflown & Hflapp & Hflceil).
destruct (FFLX lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (_ & _ & Hflimg).
rewrite <- Efl in Hflpres, Hflown, Hflapp, Hflceil, Hflimg.
assert (Hfl4096 : 4096 <= fl) by (destruct Hflapp as (H & _); exact H).
assert (Hshpres : forall i, 0 <= i < 8 -> apresent (w_H W') mem (sh + i))
  by (intros i Hi; exact (proj1 (Hfsh i ltac:(cbn; lia)))).
assert (Hshown : forall i, 0 <= i < 8 -> ~ aowned B lyc Sc (sh + i))
  by (intros i Hi; exact (proj2 (Hfsh i ltac:(cbn; lia)))).
(* the shadow band is not application memory; the frame is *)
assert (Hsh_napp : forall x, sh <= x < sh + 8 -> ~ app_addr x).
{ intros x Hx (Hx0 & Hxr).
  destruct Hfapp as (_ & [HA | (HB1 & HB2)]); destruct Hxr as [Hlow | (Hh1 & Hh2)]; lia. }
assert (Hsh_hi : sh + 8 <= kHighShadowEnd).
{ destruct Hfapp as (_ & [HA | (HB1 & HB2)]); lia. }
assert (Hsh_lo : SHADOW_OFF <= sh) by lia.
assert (Hfa_sh : fa + 64 <= sh \/ sh + 8 <= fa).
{ destruct Hfapp as (_ & [HA | (HB1 & HB2)]); lia. }
assert (Hfl_nfa : ~ (fa <= fl < fa + 64)) by (intros Hc; exact (proj2 (Hfbytes fl Hc) Hflown)).
assert (Hfl_nsh : ~ (sh <= fl < sh + 8)).
{ intros Hc. apply (Hshown (fl - sh) ltac:(lia)). replace (sh + (fl - sh)) with fl by lia. exact Hflown. }
(* the real frame lies above alloc_ceiling, every written byte below it *)
assert (HSTK : 176 <= pe_STK en).
{ pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - pe_d en)).
  change (pe_STK en) with (Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560). lia. }
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (Hsp_lo : YM05.alloc_ceiling + 176 <= pe_sp en) by lia.
assert (Hsp_hi : pe_sp en + pe_e en <= 2 ^ 47) by lia.
assert (Hsp_mod : pe_sp en mod 16 = 0) by lia.
assert (Hceil_hi : kHighShadowEnd < YM05.alloc_ceiling) by (unfold kHighShadowEnd; lia).
destruct (alx_layout SEGS B ARx LAWS (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) lyc HAR0 Hly)
  as (_ & Efr & _).

(* ---- 2. the environment and the entry symbolic state ---- *)
set (xtra := Z_to_bv 64 SHADOW_OFF :: Z_to_bv 64 fl ::
  map (fun oc : Z * Z => getr (pe_regs en) (Z_to_bv 5 (snd oc))) pv_saved).
set (E := Eimg (Ereg regs xtra)).
assert (HEI : img_env VAL A_LIM E) by exact (Eimg_env _).
assert (E8 : ew E 8 = w64 (pe_sp en)) by exact R8.
assert (E18 : ew E 18 = w64 fa) by exact R18.
assert (E27 : ew E 27 = w64 sh) by exact R27.
assert (E33 : ew E 33 = w64 fl) by reflexivity.
assert (U8 : bv_unsigned (ew E 8) = pe_sp en) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = fa) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = sh) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = fl) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HSAV : forall j oc, nth_error pv_saved j = Some oc ->
  YP09.chunk_ok SEGS E (rdW W' mem) (pe_sp en) (YP09.mkChunk (fst oc) (CVal 8 (SOff (34 + j) 0)))).
{ intros j oc Hj.
  assert (Hv : val_mem SEGS (rdW W' mem) (pe_sp en + fst oc) 8
    (bv_unsigned (getr (pe_regs en) (Z_to_bv 5 (snd oc)))))
    by exact (proj1 (Forall_forall _ _) Vsav oc (nth_error_In _ _ Hj)).
  assert (He : ew E (34 + j) = getr (pe_regs en) (Z_to_bv 5 (snd oc))).
  { unfold pv_saved in Hj.
    do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]).
    destruct j; cbn in Hj; discriminate Hj. }
  apply (chunk_ok_val SEGS E _ (pe_sp en) (fst oc) 8 (SOff (34 + j) 0)
    (bv_unsigned (getr (pe_regs en) (Z_to_bv 5 (snd oc))))).
  - cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr (pe_regs en) (Z_to_bv 5 (snd oc)))) as R.
    unfold bv_modulus in R. cbn in R |- *. lia.
  - cbn. lia.
  - exact Hv. }
assert (HS : st_ok_pi (fx := fx') SEGS VAL E pvx_ss
  (restrict (w_H W') (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + AF_pv_exit)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pvx_ss. apply (pa_entry_st_ok_full (fx := fx')).
  - unfold pvx_regs. apply regs_ok_pin; [exact (regs_ok_Eimg_Ereg regs xtra) | intros X; discriminate X |].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. etransitivity; [exact R26|]. symmetry. exact R18.
  - vm_compute. reflexivity.
  - unfold pvx_sav. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal 8 (SOff ?n 0))) =>
             exact (HSAV (n - 34)%nat _ eq_refl) end.
    + rewrite U18. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRfa; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ fa 56 8 (SOff 33 0) fl);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact Vfl].
    + rewrite U27. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (Hshpres o ltac:(lia)) | apply Forall_nil].
    + rewrite U33. split; [lia|]. split; [lia|].
      split; [intros o Ho; replace (fl + o) with fl by lia; apply (apresent_writable SEGS); exact Hflpres
             | apply Forall_nil].
  - apply pairwise_disjoint_of_extents. unfold pvx_sav. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U18, U27, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pvx_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U18, U27, U33. change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
assert (SHOK : sh_ok SEGS PVX_Bx [] E
  (rdW W' (ms_mem (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + AF_pv_exit)) mem (YK11.seg_rom SEGS)))))
  by exact (Forall_nil _).

(* ---- 3. the run, under the inline release, in the record's relation ---- *)
eapply (aj_flag_store_xR (fx := fx') (rc := rc) (SK := SK) SEGS B PSTX ARx LAWS pa_segs_low ASFX FFLX SFX
  asym pa_wx (clookup pa_tbl) VAL pa_sigma B_prog_listing B_prog_tpi B_prog_tw
  pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text (@pl_lim _ PL_prog_B) (@pl_len _ PL_prog_B)
  (@pl_tpi_eq _ PL_prog_B) (@pl_tw_eq _ PL_prog_B)
  (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
  W' 3000%N E pvx_K PVX_Bx PVX_Bspan [] pvx_ss pvx_st pvx_r _
  (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (pe_ly en) (set_depot (st_depot Sc) (pe_S en)) (pe_Hp en)
  (pe_W en) (pe_mem en)
  (pe_md en) [] lyc Sc Hpc mdc k 0 pos _ pvx_KA HEI ltac:(lia) HS SHOK pvx_static pvx_run_eq pvx_r_ok HJ).
- rewrite pvx_obls. apply Forall_nil.
- (* the write premise: the frame's word 0, its shadow bytes, the flag cell *)
  intros a (r & Hin & Hr). unfold pvx_ss in Hin. pvx_wr Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U18, ?U27, ?U33 in Hr.
  + lia.
  + left. right; right; right. unfold in_frames. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite <- Efa, Efb. lia.
  + left. right; right; right. unfold in_frames. exists 0, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite <- Efa, Esh, Efb. cbn. lia.
  + right. rewrite <- Efl. lia.
- (* the flag byte is zero at the end of the run *)
  intros ws msr Hlen HSr. rewrite pvx_j0 in Hlen. destruct ws as [|w ws]; [|discriminate Hlen].
  cbn [extK] in HSr.
  pose proof (pvx_region_nth fx' _ _ _ 3%nat _ HSr pvx_flag_region) as RF.
  pose proof (pvx_field E (ms_mem msr) 33%nat fl _ 0 1 0 1 0 1%N (SLit 0) 0 RF U33 ltac:(left; reflexivity)
    ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VF.
  pose proof (VF 0%nat ltac:(cbn; lia)) as VF0.
  rewrite <- Efl. replace (fl + 0 + Z.of_nat 0) with fl in VF0 by lia. exact VF0.
- (* ---- 4. after the release: the epilogue's ret, and the post ---- *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HF HFr HG.
  rewrite pvx_j0 in Hlen. destruct ws as [|w ws]; [|discriminate Hlen]. clear Hlen.
  cbn [extK] in HS', SHOK', HEI'.
  cbn [ms_mem YK11.mkst] in HFr, HG.
  set (mem' := ms_mem ms') in *.
  (* every byte outside the three written ranges is kept *)
  assert (KEPT : forall x, 0 <= x < 2 ^ 64 -> ~ (fa <= x < fa + 8) -> ~ (sh <= x < sh + 8) -> x <> fl ->
    mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
  { intros x Hx H1 H2 H3. unfold YP09.mbyte. rewrite (HFr (Z_to_bv 64 x)); [reflexivity|].
    rewrite unsigned_lit_small by lia.
    intros (r & Hin & Hr). unfold pvx_ss in Hin. pvx_wr Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U18, ?U27, ?U33 in Hr; lia. }
  assert (GROWS : forall x, writable_at SEGS (rdW W' mem) x -> writable_at SEGS (rdW W' mem') x)
    by (intros x Hw; exact (writable_at_grows SEGS _ _ x HG Hw)).
  (* the four places the post reads *)
  assert (KEPTB : forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
    mbyte SEGS (rdW W' mem') (b + i) = mbyte SEGS (rdW W' mem) (b + i)).
  { intros b n i Hb Hi.
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b n HAR Hb) as (_ & Hb0 & Hbc & Hbapp & Hbyt & _).
    pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b n 0 pos HAR Hb HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efa, Efb in Hd.
    apply KEPT; [lia | lia | |].
    - intros Hc. apply (Hsh_napp (b + i) Hc). exact (in_app_addr b (req_size n) (b + i) Hbapp ltac:(lia)).
    - intros Hc. apply (proj2 (Hbyt (b + i) ltac:(lia))). rewrite Hc. exact Hflown. }
  assert (KEPTI : forall x, in_img SEGS x -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
  { intros x Hx. pose proof (pa_segs_low x Hx) as Hxl.
    apply KEPT; [lia | | lia |].
    - intros Hc. apply (frm_img_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos x HAR HinF); [|exact Hx].
      rewrite <- Efa, Efb. lia.
    - intros Hc. apply Hflimg. rewrite <- Hc. exact Hx. }
  assert (KEPTS : forall x, YM05.alloc_ceiling <= x < 2 ^ 64 ->
    mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x)
    by (intros x Hx; apply KEPT; lia).
  assert (KEPTF : forall cid p x, In (cid, p) (frames (pe_S en)) ->
    frame_addr lyc cid p <= x < frame_addr lyc cid p + fs_frame_bytes cid ->
    mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x).
  { intros cid p x Hin Hx.
    assert (HinC : In (cid, p) (frames Sc)) by (rewrite Hfrs; cbn [app]; right; exact Hin).
    destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc cid p HAR HinC) as (Hg0 & Hgc & Hgapp).
    destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W' mem mdc cid p HAR HinC) as (_ & _ & Hgbyt & _).
    destruct (in_split _ _ Hin) as (l2 & l3 & El).
    pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc (0, pos) (cid, p) [] l2 l3 HAR
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite <- Efa, Efb in Hd.
    apply KEPT; [lia | lia | |].
    - intros Hc. apply (Hsh_napp x Hc).
      exact (in_app_addr (frame_addr lyc cid p) (fs_frame_bytes cid) x Hgapp Hx).
    - intros Hc. apply (proj2 (Hgbyt x Hx)). rewrite Hc. exact Hflown. }
  (* the ret: a plain step, lifted into the record's relation *)
  apply (YA0nH.SRr_SRrG SEGS _ (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
  eapply (@paj_ret_at fx' rc B_prog_listing PL_prog_B PA W' E (sh_ss pvx_st) ms' _ _ HS' pvx_resv pvx_ret_word).
  intros mat2. cbv beta.
  assert (Eabl : ablocks B lyc (stack_free_state 0 pos Sc) = ablocks B lyc Sc)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  pose proof HJ' as (_ & _ & _ & _ & _ & Hfrs2 & _).
  assert (Epc : v_jalr (getr (ms_regs ms') 1) 0 = getr (pe_regs en) 1).
  { etransitivity; [|exact Hra_ok]. f_equal. pvx_reg HS' 34%nat. reflexivity. }
  unfold pv_FINAL, YCbqGwild.fpostWF_xbR. cbv beta.
  exists fx', lyc, (stack_free_state 0 pos Sc), Hpc, (ms_regs ms'), mem',
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy mdc) mat' mdc)) mat2
      (with_vm_backing (m_vm_lazy mdc) mat' mdc)), k, WS.
  split.
  { f_equal. f_equal. exact Epc. }
  split; [exact HFZ|]. split; [exact HFK|]. split; [exact HWB|].
  split; [eapply YCbqGwild.ajournal_xw_unbase0R;
    [apply (ajournal_x_materializeR (SK := SK) SEGS B PSTX ARx LAWS pa_segs_low); exact HJ' | exact HWILD]|].
  split.
  { (* the caller's window: above alloc_ceiling, the release writes below it *)
    intros a Ha Hnf. rewrite <- (HWIN a ltac:(rewrite Esp; exact Ha) Hnf).
    unfold aview. rewrite (KEPTS a ltac:(lia)). reflexivity. }
  split.
  { (* the callee-saved registers: sp is the entry sp, gp / tp untouched, s0 .. s11 the real frame's words *)
    intros r Hr. unfold acallee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - pvx_reg HS' 8%nat. etransitivity; [exact E8|]. unfold w64. rewrite Esp. unfold spZ.
      apply Z_to_bv_bv_unsigned.
    - pvx_reg HS' 3%nat. etransitivity; [exact R3|]. reflexivity.
    - pvx_reg HS' 4%nat. etransitivity; [exact R4|]. reflexivity.
    - pvx_reg HS' 35%nat. reflexivity.
    - pvx_reg HS' 36%nat. reflexivity.
    - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
      + pvx_reg HS' 37%nat. reflexivity.
      + pvx_reg HS' 38%nat. reflexivity.
      + pvx_reg HS' 39%nat. reflexivity.
      + pvx_reg HS' 40%nat. reflexivity.
      + pvx_reg HS' 41%nat. reflexivity.
      + pvx_reg HS' 42%nat. reflexivity.
      + pvx_reg HS' 43%nat. reflexivity.
      + pvx_reg HS' 44%nat. reflexivity.
      + pvx_reg HS' 45%nat. reflexivity.
      + pvx_reg HS' 46%nat. reflexivity. }
  (* the post's memory part *)
  unfold pv_Q. split; [exists code; split|].
  { pvx_reg HS' 21%nat. etransitivity; [exact Hcode|]. reflexivity. }
  { apply (pvx_Qm_move en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en)))
      (fun S2 => Permutation (frames S2) (frames (pe_S en))) code lyc Sc (stack_free_state 0 pos Sc) Hpc W' mem mem'
      HPRE Efr HQM Eabl eq_refl (RL_stack_free Sc 0 pos)
      (rp_keep_stack_free Sc 0 pos) (YGcfSecsStep.secs_same_of_secs _ _ eq_refl)).
    + cbv beta. rewrite Hfrs2. apply Permutation_refl.
    + exact KEPTB.
    + exact KEPTI.
    + exact KEPTS.
    + exact KEPTF.
    + exact GROWS. }
  (* the memory normal form at the ret memory: the run's start st_ok and its unrestricted frame_of *)
  exact (YGcallMxmn.memnorm_frame_of (fx := fx') SEGS (w_H W') E _
    (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + AF_pv_exit)) mem (YK11.seg_rom SEGS)) mem' HMN HS HF).
Qed.

End c.
