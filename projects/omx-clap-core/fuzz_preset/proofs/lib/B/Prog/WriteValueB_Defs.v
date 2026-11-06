(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d), lane of write_value: THE
   CONTRACT of write_value's container walk (an array or an object): the container's entry data (wvx), the text's
   premises at that entry (wv_pre), what every join carries (wv_common), the two measured join states - the ITEM LOOP
   HEAD (write_value + 4 * 90, old B 0x86fc0 `beqz s5`) and the CLOSE (write_value + 4 * 173, old B 0x8710c, the
   closing bracket's path, shared by the empty and the non-empty container) - and the container's final post
   (wv_Qfin: the float-form post's R form fpostWFR at wle' SEGS RZ_cf, at the CONTAINER'S ENTRY float state, with the
   runner's memory invariant Pm).
   Over the draft's texts of record (lib/A/PRH_FnWriter.v,
   lib/A/PRH_Base.v, whose fpre carries FRM0-ENTRY `frm_zero (fp_csr fx)`).
   THE FLOAT STATE. The text posts fpostWFR at wle' SEGS RZ_cf, put_string posts fpostWFmR and write_value itself
   fpostWFR: after such a call the machine runs at the callee's exit float state fx2 (frm_zero, fregs_kept_x). So a
   join state is stated at the CURRENT float state, an argument fxc of wv_commonR / wv_headR / wv_clR, and wvx carries the
   container's ENTRY float state y_fx; every join keeps `frm_zero (fp_csr fxc) /\ fregs_kept_x (y_fx X) fxc`
   (wv_common's last two conjuncts), and its config is `@mkst fxc ..`.
   THE JOIN STATES are MEASURED with the engine on B's listing (WriteValueB's probe; the instruction compare old B /
   B' is EQUAL-mod-pcrel, so the slots are the same): at the loop head, from `wv_ssH` the run reaches `put` (slot 94)
   for i <> 0 and `indent` (slot 99) for i = 0 with no obligation left.
   The frame word R + k (R = the entry sp - 192, write_value's own frame): 8 = (v & 7) + 3 = 3, 16 = v & 7 = 0,
   24 = dep, 32 = the separator's length (1 + (pretty <> 0)), 40 = shadow (v + 32), 48 = v + 32, 56 = the separator
   literal (": " pretty, ":" not), 64 = the comma literal, 72 = the shadow offset (the GOT word), 80 = shadow (v),
   88 .. 176 = the entry s11 .. s0, 184 = the entry ra. The registers at the head: s0 = o, s1 = v, s2 = v + 40,
   s3 = pretty, s4 = shadow (v + 24), s5 = i, s6 = dep + 1 (addiw), s7 = 56 i, s8 = v + 24, s9 = 8 i, s10 = 0
   (slt (dep + 1) dep), s11 = shadow (v + 40).
   Numerals: 192 (LENGTH: the frame), 8 .. 184 (LENGTH: frame offsets), 24 / 32 / 40 (LENGTH: the node's kids /
   keys / n fields, PRH_Reader pj_hdrR), 56 (LENGTH: a node), 8 (LENGTH: a key slot), 90 / 173 (DERIVED: slots). No
   ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* the two join pcs (offsets from the image base) *)
Definition WVH_PC : Z := AF_write_value + 4 * 90.
Definition WVC_PC : Z := AF_write_value + 4 * 173.

(* the container's entry data: the arguments, named; y_fx is the ENTRY float state *)
Record wvx := mkWVX {
  y_fx : YK11.FPState;
  y_d : Z; y_STK : Z; y_ly : alayout; y_S : astate; y_Hp : list Z; y_W : world SEGS; y_regs : bvmap 5 word;
  y_mem : word -> option byte; y_md : Model; y_o : Z; y_v : Z; y_pretty : Z; y_dep : Z; y_buf : Z;
  y_st : WriterApp.wst; y_t : PjTree.jv; y_D : list (Z * Z); y_Lam : list (Z * Z); y_peak : Z; y_ran : Z;
  y_most : Z; y_own : Z;
  y_rpsm : list Z -> Z * Z; y_rpx : list Z; y_rpos : list (option nat * option nat * option nat); y_rpi : nat;
  y_rpH0 : list Z; y_rphist : list YG00.chunk }.
Definition y_sp (X : wvx) : Z := spZ (y_regs X).
Definition y_p (X : wvx) : bool := negb (y_pretty X =? 0).
Definition y_FP (X : wvx) : list (Z * Z) := prhWriter_cfp (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)).
(* the number of items, the tag, the pieces of the opening bracket and the first i items *)
Definition wv_nitems (t : PjTree.jv) : nat :=
  match t with PjTree.JArr l => length l | PjTree.JObj l => length l | _ => 0 end.
Definition wv_tagc (t : PjTree.jv) : Z := match t with PjTree.JObj _ => 6 | _ => 5 end.
Definition wv_done (X : wvx) (i : nat) : list (list Z) :=
  match y_t X with
  | PjTree.JArr l => [91] :: wv_arr_go (y_p X) (y_dep X) 0 (firstn i l)
  | PjTree.JObj l => [123] :: wv_obj_go (y_p X) (y_dep X) 0 (firstn i l)
  | _ => []
  end.
(* the pieces written when the close starts (slot 173): every piece but the closing bracket - the opening bracket,
   all the items, and indent (dep) for a non-empty container (wv_arr_pieces / wv_obj_pieces) *)
Definition wv_clP (X : wvx) : list (list Z) :=
  wv_done X (wv_nitems (y_t X)) ++
  (match wv_nitems (y_t X) with O => [] | S _ => WriterValue.wind (y_p X) (y_dep X) end).
(* the separator literal's slot (": " when pretty, ":" otherwise) and the closing bracket's *)
Definition wv_sep_slot (X : wvx) : nat := if y_pretty X =? 0 then 57%nat else 54%nat.
Definition wv_close_slot (X : wvx) : nat := match y_t X with PjTree.JObj _ => 251%nat | _ => 180%nat end.

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* NOTE: a binder of type YK11.FPState in scope is a typeclass candidate, so every text / post / pre that must be
   at the Section's fx is written `(fx := fx)` wherever another FPState is bound. *)
(* ---- THE FLOAT POST, ONE LEMMA EACH WAY (FRM0-ENTRY, kit f97c8b2f046b) ----
   (1) a post at the CURRENT float state fx (put's / indent's non-float fpostW, with the machine at fx) is the
       float-form post at an earlier float state fx0, when fx has rounding mode 0 and keeps fx0's callee-saved f
       registers (the join's float invariant, wv_common);
   (2) the precondition at one float state is the precondition at another of rounding mode 0 (fpre reads the float
       state only in its last conjunct, FRM0-ENTRY). *)
Lemma wv_fpostW_F : forall (fx0 : YK11.FPState) STK d FP (regs : bvmap 5 word) ly S Hp (W : world SEGS) mem md Q W' c',
  frm_zero (@YK11.fp_csr fx) -> fregs_kept_x fx0 fx ->
  fpostW (fx := fx) B ARx SK STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWF (fx := fx0) B ARx SK STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros fx0 STK d FP regs ly S Hp W mem md Q W' c' Hz Hk (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HW & Hpr & HQ).
exists fx, ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact Hz|]. split; [exact Hk|]. split; [exact HJ|]. split; [exact HW|].
split; [exact Hpr | exact HQ].
Qed.
(* (1) over a world relation Rw: the R-forms of the two posts (the free / realloc move's crossing texts) *)
Lemma wv_fpostW_FR : forall (Rw : world SEGS -> world SEGS -> Prop) (fx0 : YK11.FPState) STK d FP
  (regs : bvmap 5 word) ly S Hp (W : world SEGS) mem md Q W' c',
  frm_zero (@YK11.fp_csr fx) -> fregs_kept_x fx0 fx ->
  fpostWR (fx := fx) B ARx SK Rw STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWFR (fx := fx0) B ARx SK Rw STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros Rw fx0 STK d FP regs ly S Hp W mem md Q W' c' Hz Hk (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HW & Hpr & HQ).
exists fx, ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact Hz|]. split; [exact Hk|]. split; [exact HJ|]. split; [exact HW|].
split; [exact Hpr | exact HQ].
Qed.


Lemma wv_fpre_at : forall (fx0 : YK11.FPState) STK ly S Hp (W : world SEGS) regs mem md ch,
  fpre (fx := fx0) B ARx STK ly S Hp W regs mem md ch -> frm_zero (@YK11.fp_csr fx) ->
  fpre (fx := fx) B ARx STK ly S Hp W regs mem md ch.
Proof.
intros fx0 STK ly S Hp W regs mem md ch (H1 & H2 & H3 & H4 & _) Hz.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact Hz].
Qed.

Lemma wv_fregs_kept_refl : forall f : YK11.FPState, fregs_kept_x f f.
Proof. intros f r _. reflexivity. Qed.

Lemma wv_fregs_kept_trans : forall f1 f2 f3 : YK11.FPState,
  fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

Section cl.
Variable CTX0 : list (list Z).
Section cont.
(* the runner's memory invariant, ABSTRACT in every segment; the top instantiates it once (the memnorm keep) *)
Variable Pm : (word -> option byte) -> Prop.

(* the text's inner post at the container's entry data (twrite_value_specX, lib/A/PRH_FnWriter.v) *)
Definition wv_Qin (X : wvx) :=
  fun ly' S' Hp' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
    room_live_cf S' /\
    pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X) /\
    exists ok, prhWriter_ret_ok B ok (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_ran X) (y_most X) (y_own X)
      (y_o X) (y_buf X) (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X)) ly' S' Hp' W' regs' mem' md' /\
    prh_granted ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X))
      (prhWriter_k ok (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))) /\
    exists hist', PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X)
      (y_rpi X + length (prhWriter_evs ok (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))))%nat
      (y_rpH0 X) hist' S'.
(* the container's final post: the float-form post AT THE ENTRY FLOAT STATE y_fx, at the inner post, with Pm at the
   final memory (the top turns Pm into fQmn's memnorm keep). The container's run crosses its puts' grows, so the post
   is the float-form family's R-form at wle' SEGS RZ_cf (its journal's world conjunct; nothing else changes) *)
Definition wv_Qfin (X : wvx) : world SEGS -> config -> Prop :=
  fun W' c' =>
    fpostWFR (fx := y_fx X) B ARx SK (wle' SEGS RZ_cf) (y_STK X) (y_d X) (y_FP X) (y_regs X) (y_ly X) (y_S X)
      (y_Hp X) (y_W X) (y_mem X) (y_md X) (wv_Qin X) W' c' /\ Pm (ms_mem (cfg_ms c')).

(* the text's premises at the container's entry (twrite_value_specX, in its order but for its window premise
   prh_cons_from and the run-length bound the callees' texts take, which are the LAST two conjuncts here so that the
   walk's prefix destructs keep their positions), at the entry float state, with Pm at entry *)
Definition wv_pre (X : wvx) (ch : list (Z * Z * Z)) : Prop :=
  fpre (fx := y_fx X) B ARx (y_STK X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X) ch /\
  room_live_cf (y_S X) /\
  PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X) (y_rpH0 X) (y_rphist X) (y_S X) /\
  prh_univ_closure B CTX0 /\
  getr (y_regs X) 10 = w64 (y_o X) /\ getr (y_regs X) 11 = w64 (y_v X) /\
  getr (y_regs X) 12 = w64 (y_pretty X) /\ getr (y_regs X) 13 = w64 (y_dep X) /\
  0 <= y_pretty X < 2 ^ 64 /\ 0 <= y_dep X < 2 ^ 31 /\ y_dep X + Z.of_nat (PjTree.depth (y_t X)) <= 2 ^ 31 - 1 /\
  (y_sp X + 16 <= y_o X \/ y_o X = y_sp X + 8) /\
  (y_sp X + 16 <= y_o X ->
     exists ra, rdword (aview SEGS (w_H (y_W X)) (y_mem X)) (y_o X - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H (y_W X)) (y_mem X)) (y_o X - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) /\
  (s0Z (y_regs X) = y_o X \/ s0Z (y_regs X) < YM05.alloc_ceiling) /\
  fwin (y_ly X) (y_W X) (y_regs X) (y_mem X) (y_d X) /\ y_sp X <= y_o X /\ y_o X + 32 <= y_sp X + y_d X /\
  prhWriter_out (y_W X) (y_mem X) (y_Lam X) (y_o X) (y_buf X) (y_st X) /\
  prh_ledger B (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_Lam X) (y_peak X)
    (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (y_ran X) (y_most X) (y_own X) /\
  prh_run_at (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))) /\
  pj_nodeR SEGS (mrestrict (w_H (y_W X)) (y_mem X)) (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X) /\
  ((y_sp X <= y_v X /\ y_v X + 56 <= ly_stk_hi (y_ly X)) \/
   (exists x z, In (x, z) (y_Lam X) /\ x <> y_buf X /\ x <= y_v X /\ y_v X + 56 <= x + z) \/
   prhWriter_in_frame (y_ly X) (y_S X) (y_v X)) /\
  range_addressable (aview SEGS (w_H (y_W X)) (y_mem X)) SHADOW_OFF (y_v X) 56 /\
  prhWriter_tree_vis (y_W X) (y_mem X) (y_D X) /\
  (forall a k, In (a, k) (y_D X) -> In (a, k) (y_Lam X) /\ a <> y_buf X) /\
  (forall x, y_o X <= x < y_o X + 32 -> ~ pj_footR (y_v X) (y_D X) x) /\
  Z.of_nat (length (frames (y_S X))) < fs_frames 0 /\
  Z.of_nat (length (WriterApp.w_text (y_st X))) +
    Z.of_nat (length (concat (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X)))) + 1 <= prhWriter_WMAX /\
  prhWriter_WMAX + cf_head < cf_malloc_max /\
  prh_live_evs (y_S X) (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))) /\
  Pm (y_mem X) /\
  PRH_Base.prh_cons_from (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (length (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X)))) /\
  (length (y_rpos X) <= 4)%nat.

(* what every join of the container carries about the current state (lyc Sc Hpc Wc memc mdc kc) after the pieces
   P, at the CURRENT float state fxc: the journal from the entry (own list empty), the caller window kept off FP, Pm,
   the writer after P (opened with no refusal, prhW_oksg; the model-run position at the EXACT advance
   y_rpi X + length (prhWriter_evs ok (y_st X) P)), the room, the read-only view, and the float invariant *)
Definition wv_common (X : wvx) (fxc : YK11.FPState) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (memc : word -> option byte) mdc kc : Prop :=
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (y_STK X + y_d X) (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc /\
  (forall a, y_sp X <= a < y_sp X + y_d X -> ~ inFP (y_FP X) a ->
     aview SEGS (w_H Wc) memc a = aview SEGS (w_H (y_W X)) (y_mem X) a) /\
  Pm memc /\
  (exists ok ranc bufc Lamc peakc,
     prhW_oksg ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) (y_ran X) ranc /\
     prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) /\
     prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
       (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) /\
     prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
       (prhWriter_putN ok (y_st X) P) /\
     exists rp_hist', PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X)
       (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat (y_rpH0 X) rp_hist' Sc) /\
  room_live_cf Sc /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
  frm_zero (@YK11.fp_csr fxc) /\ fregs_kept_x (y_fx X) fxc.

(* THE LOOP HEAD (write_value + 4 * 90): item i is next (i < n), P = the opening bracket and the first i items'
   pieces; the registers and the own frame's words (R = the entry sp - 192) as the engine measured them *)
Definition wv_head (X : wvx) (fxc : YK11.FPState) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  let R := y_sp X - 192 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  wv_common X fxc P lyc Sc Hpc Wc memc mdc kc /\
  (i < wv_nitems (y_t X))%nat /\ P = wv_done X i /\
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\ getr regsc 18 = w64 (v + 40) /\
  getr regsc 19 = w64 (y_pretty X) /\ getr regsc 20 = w64 (SHADOW_OFF + (v + 24) / 8) /\
  getr regsc 21 = w64 (Z.of_nat i) /\ getr regsc 22 = w64 (y_dep X + 1) /\
  getr regsc 23 = w64 (56 * Z.of_nat i) /\ getr regsc 24 = w64 (v + 24) /\
  getr regsc 25 = w64 (8 * Z.of_nat i) /\ getr regsc 26 = w64 0 /\
  getr regsc 27 = w64 (SHADOW_OFF + (v + 40) / 8) /\
  rdword rd (R + 8) = Some 3 /\ rdword rd (R + 16) = Some 0 /\ rdword rd (R + 24) = Some (y_dep X) /\
  rdword rd (R + 32) = Some (if y_pretty X =? 0 then 1 else 2) /\
  rdword rd (R + 40) = Some (SHADOW_OFF + (v + 32) / 8) /\ rdword rd (R + 48) = Some (v + 32) /\
  rdword rd (R + 56) = Some (WV_STR (wv_sep_slot X)) /\ rdword rd (R + 64) = Some (WV_STR 88) /\
  rdword rd (R + 72) = Some SHADOW_OFF /\ rdword rd (R + 80) = Some (SHADOW_OFF + v / 8) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 176) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 184) = Some (bv_unsigned (getr (y_regs X) 1)).

(* THE CLOSE (write_value + 4 * 173): every piece but the closing bracket is written (wv_clP); what the path to the
   closing bracket's tail `j put` (slot 268) reads: sp, s0 = o, s1 = v, gp / tp, the frame words 72 / 80 (the shadow
   offset, v's shadow) and the saved registers it restores *)
Definition wv_cl (X : wvx) (fxc : YK11.FPState) lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word)
  (memc : word -> option byte) mdc kc : Prop :=
  let R := y_sp X - 192 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  wv_common X fxc (wv_clP X) lyc Sc Hpc Wc memc mdc kc /\
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\
  rdword rd (R + 16) = Some 0 /\
  rdword rd (R + 72) = Some SHADOW_OFF /\ rdword rd (R + 80) = Some (SHADOW_OFF + v / 8) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 176) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 184) = Some (bv_unsigned (getr (y_regs X) 1)).

(* the two continuations, at ANY float state: from a loop head, and from the close, to the container's final post *)
Definition wv_HEADK (X : wvx) : Prop :=
  forall (fx' : YK11.FPState) i P lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc kc,
    wv_head X fx' i P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr SEGS Wc (mkCfg (@mkst fx' regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc) (wv_Qfin X).
Definition wv_CLOSEK (X : wvx) : Prop :=
  forall (fx' : YK11.FPState) lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc kc,
    wv_cl X fx' lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr SEGS Wc (mkCfg (@mkst fx' regsc (Z_to_bv 64 (BASE + WVC_PC)) memc (seg_rom SEGS)) mdc) (wv_Qfin X).

(* ---- THE R-FORMS, BESIDE (the free / realloc move): the join states and the two continuations over a world relation
   Rw. A join after one of the container's puts carries a journal whose world conjunct is wle' SEGS RZ_cf, so the walk
   names wv_commonR / wv_headR / wv_clR / wv_HEADKR / wv_CLOSEKR at Rw := wle' SEGS RZ_cf. Each is a COPY of the old
   body with the journal at Rw and SRr read as SRrG at Rw (proofs unfold the old names and read their bodies, so the
   old names stay as they are); X_R_wle checks by reflexivity that the old name is the R-form at wle. ---- *)
Definition wv_commonR (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) (fxc : YK11.FPState) (P : list (list Z))
  lyc Sc Hpc (Wc : world SEGS) (memc : word -> option byte) mdc kc : Prop :=
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx Rw (y_STK X + y_d X) (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc /\
  (forall a, y_sp X <= a < y_sp X + y_d X -> ~ inFP (y_FP X) a ->
     aview SEGS (w_H Wc) memc a = aview SEGS (w_H (y_W X)) (y_mem X) a) /\
  Pm memc /\
  (exists ok ranc bufc Lamc peakc,
     prhW_oksg ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) (y_ran X) ranc /\
     prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) /\
     prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
       (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) /\
     prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
       (prhWriter_putN ok (y_st X) P) /\
     exists rp_hist', PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X)
       (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat (y_rpH0 X) rp_hist' Sc) /\
  room_live_cf Sc /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
  frm_zero (@YK11.fp_csr fxc) /\ fregs_kept_x (y_fx X) fxc.
Lemma wv_common_R_wle : forall X fxc P lyc Sc Hpc Wc memc mdc kc,
  wv_common X fxc P lyc Sc Hpc Wc memc mdc kc = wv_commonR (@wle SEGS) X fxc P lyc Sc Hpc Wc memc mdc kc.
Proof. reflexivity. Qed.

Definition wv_headR (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) (fxc : YK11.FPState) (i : nat)
  (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  let R := y_sp X - 192 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  wv_commonR Rw X fxc P lyc Sc Hpc Wc memc mdc kc /\
  (i < wv_nitems (y_t X))%nat /\ P = wv_done X i /\
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\ getr regsc 18 = w64 (v + 40) /\
  getr regsc 19 = w64 (y_pretty X) /\ getr regsc 20 = w64 (SHADOW_OFF + (v + 24) / 8) /\
  getr regsc 21 = w64 (Z.of_nat i) /\ getr regsc 22 = w64 (y_dep X + 1) /\
  getr regsc 23 = w64 (56 * Z.of_nat i) /\ getr regsc 24 = w64 (v + 24) /\
  getr regsc 25 = w64 (8 * Z.of_nat i) /\ getr regsc 26 = w64 0 /\
  getr regsc 27 = w64 (SHADOW_OFF + (v + 40) / 8) /\
  rdword rd (R + 8) = Some 3 /\ rdword rd (R + 16) = Some 0 /\ rdword rd (R + 24) = Some (y_dep X) /\
  rdword rd (R + 32) = Some (if y_pretty X =? 0 then 1 else 2) /\
  rdword rd (R + 40) = Some (SHADOW_OFF + (v + 32) / 8) /\ rdword rd (R + 48) = Some (v + 32) /\
  rdword rd (R + 56) = Some (WV_STR (wv_sep_slot X)) /\ rdword rd (R + 64) = Some (WV_STR 88) /\
  rdword rd (R + 72) = Some SHADOW_OFF /\ rdword rd (R + 80) = Some (SHADOW_OFF + v / 8) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 176) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 184) = Some (bv_unsigned (getr (y_regs X) 1)).
Lemma wv_head_R_wle : forall X fxc i P lyc Sc Hpc Wc regsc memc mdc kc,
  wv_head X fxc i P lyc Sc Hpc Wc regsc memc mdc kc = wv_headR (@wle SEGS) X fxc i P lyc Sc Hpc Wc regsc memc mdc kc.
Proof. reflexivity. Qed.

Definition wv_clR (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) (fxc : YK11.FPState) lyc Sc Hpc
  (Wc : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  let R := y_sp X - 192 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  wv_commonR Rw X fxc (wv_clP X) lyc Sc Hpc Wc memc mdc kc /\
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\
  rdword rd (R + 16) = Some 0 /\
  rdword rd (R + 72) = Some SHADOW_OFF /\ rdword rd (R + 80) = Some (SHADOW_OFF + v / 8) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 176) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 184) = Some (bv_unsigned (getr (y_regs X) 1)).
Lemma wv_cl_R_wle : forall X fxc lyc Sc Hpc Wc regsc memc mdc kc,
  wv_cl X fxc lyc Sc Hpc Wc regsc memc mdc kc = wv_clR (@wle SEGS) X fxc lyc Sc Hpc Wc regsc memc mdc kc.
Proof. reflexivity. Qed.

Definition wv_HEADKR (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) : Prop :=
  forall (fx' : YK11.FPState) i P lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc kc,
    wv_headR Rw X fx' i P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRrG SEGS Rw Wc (mkCfg (@mkst fx' regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc) (wv_Qfin X).
Lemma wv_HEADK_R_wle : forall X, wv_HEADK X = wv_HEADKR (@wle SEGS) X.
Proof. reflexivity. Qed.
Definition wv_CLOSEKR (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) : Prop :=
  forall (fx' : YK11.FPState) lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc kc,
    wv_clR Rw X fx' lyc Sc Hpc Wc regsc memc mdc kc ->
    SRrG SEGS Rw Wc (mkCfg (@mkst fx' regsc (Z_to_bv 64 (BASE + WVC_PC)) memc (seg_rom SEGS)) mdc) (wv_Qfin X).
Lemma wv_CLOSEK_R_wle : forall X, wv_CLOSEK X = wv_CLOSEKR (@wle SEGS) X.
Proof. reflexivity. Qed.

End cont.
End cl.
End h.
End f.
End d.
