(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value (B 0x8352c, 850 instructions, 31 UBSan checks, recursive, class-1 fake frame): the STATEMENTS of its
   walk. Text of record: the draft's tex_value_specX (lib/A/PRH_FnEx.v),
   instantiated at image B (PI := prh_img_B, the listing PI_prog_B of lib/B/PAImg_prog.v, the B' pin d663f82d).
   This file states, and proves nothing about the program:
   - exv_e, the entry record, EXV_PRE (tex_value_specX's premises at the record), EXV_Q / EXV_POST (its post);
   - the SEVEN CUTS of the walk (one segment lemma per cut, each proved in its own file over B's listing, each taking
     the downstream cuts as hypotheses):
       C0 ENTRY   B 0x8352c (entry)       prologue, frame_alloc_1 (class 1), redzone poison, first ex_ws call
       C1 DISP    entry + 0x11c (0x83648)  after ex_ws: dispatch on the first byte; string arm (ex_string, strcmp),
                                           word arms (ex_word); exits to CN, CI, CX
       CN NUM     entry + 0x278 (0x837a4)  number arm (inline ex_number): scan, __asan_memcpy, strtod, strcmp, bcmp
       CI OPEN    entry + 0x374 (0x838a0)  container open (inline ex_items): depth + 1, type check, ex_ws; to CL, CC, CX
       CL LOOP    entry + 0x534 (0x83a60)  loop head: one member / item per pass (ex_ws, ex_string, strcmp, the
                                           recursive ex_value), back to CL or to CC / CX
       CC CLOSE   entry + 0x9f8 (0x83f24)  count compare, depth - 1; to CX
       CX EXIT    entry + 0xa7c (0x83fa8)  frame retired (magic, f5 shadow, inline flag release), epilogue, ret
     The offsets are DERIVED (B address minus B's ex_value entry, both from the internal file neutral_dis.py on the rebuilt image).
   - EXV_HYP, every callee text and law the segments take: the tex_ws_specX / tex_string_specX / tex_word_specX
     (B twins, each owned by a Theorem Labs lane), YGcallMx's strcmp / bcmp / __asan_memcpy texts, FCiface's
     astack_malloc_realizes_x 1 (owner: a Theorem Labs lane), a Theorem Labs lane's strtod row astrtod_realizes_x
     (YStrtodRowX.v, its B instance strtod_row_aj_B cited as exv_strtod; its aj_memnorm is a premise at the call), YGcallSx.v's frame laws (SMX, ASFX, FFLX, SFX), and the image facts
     the code reads through the GOT (as_got_uar B = VAL (A_OBJ 1) is a Theorem Labs lane's marked hypothesis text).
   Each callee text is quantified over the floating-point state: after strtod or the recursive call the walk runs
   at the callee's fx' (YCbqGcall.v st_ok_restrict_xfx moves its symbolic state there).
   Numerals: register numbers 1-4, 8, 9, 10-12, 18-27 (WORD); 288, 304, 176, 120, 144, 152, 184-280 (LENGTH: frame,
   slot offsets of B's code); 0x11c, 0x278, 0x374, 0x534, 0x9f8, 0xa7c (DERIVED: cut offsets); 32, 34, 44, 58, 91,
   93, 102, 110, 116, 123, 125 (WORD: ASCII bytes the code compares); 40 (LENGTH: struct ex); 2 ^ 60 (WORD: the
   code's overflow mask constant). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YGcallx YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ex_ws_x strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- pure: the reading of the items list from a point, the plain ex_L shape (lib/Prog/ex_value_m.v, restated at
   ReaderRes.jr_strtod, the prhex_V model; no plain lemma cited) ---- *)
Definition exv_run0 {A : Type} (c : PjGrammar.M A) : option A := fst (fst (c [])).
Definition exv_L (dn : nat) (o : bool) (n cap : nat) (acc : list (list Z * PjTree.jv)) (y : list Z)
  : option (PjTree.jv * list Z) :=
  exv_run0 (PjGrammar.jrl ReaderRes.jr_strtod (2 * length y + 2) dn o n cap acc y).
(* the members / items read so far are the tree's first ones (names too for an object), and no more than it has *)
Definition exv_pref (o : bool) (acc : list (list Z * PjTree.jv)) (t : PjTree.jv) : Prop :=
  match o, t with
  | true, PjTree.JObj ms => (length acc <= length ms)%nat /\ firstn (length acc) ms = rev acc
  | false, PjTree.JArr its => (length acc <= length its)%nat /\ firstn (length acc) its = map snd (rev acc)
  | _, _ => False
  end.
(* the tree's node count, as the reader's struct stores it at +40 (plain PjStruct: kids of an array, members of an
   object) *)
Definition exv_count (t : PjTree.jv) : nat :=
  match t with PjTree.JArr its => length its | PjTree.JObj ms => length ms | _ => 0%nat end.

(* the one ASCII class test the dispatch makes *)
Definition exv_disp (c : Z) : bool :=
  (c =? 34) || (c =? 91) || (c =? 123) || (c =? 116) || (c =? 102) || (c =? 110).

(* the callee-saved registers ex_value saves (B 0x83534-0x83564), slot offset from the entry sp minus 288 *)
Definition exv_saved : list (Z * Z) :=
  [(280, 1); (272, 8); (264, 9); (256, 18); (248, 19); (240, 20); (232, 21); (224, 22); (216, 23); (208, 24);
   (200, 25); (192, 26); (184, 27)].


(* ---- the entry record: every quantified name of tex_value_specX, plus the entry float state ---- *)
Record exv_e : Type := MkExv {
  e_fx : YK11.FPState; e_n : nat; e_ly : alayout; e_S : astate; e_Hp : list Z; e_W : world rsegs;
  e_regs : bvmap 5 word; e_mem : word -> option byte; e_md : Model; e_ch : list (Z * Z * Z);
  e_q : Z; e_v : Z; e_x0 : Z; e_i0 : Z; e_dep : Z; e_dl : Z; e_scr : Z; e_d : Z;
  e_x : list Z; e_t : PjTree.jv; e_D : list (Z * Z);
  e_Lam : list (Z * Z); e_peak : Z; e_cnt : Z; e_fail : Z; e_ran : Z; e_most : Z; e_own : Z }.

Definition exv_len (E : exv_e) : Z := Z.of_nat (length (e_x E)).
Definition exv_X (E : exv_e) : list Z := skipn (Z.to_nat (e_i0 E)) (e_x E).
Definition exv_V (E : exv_e) : option (PjTree.jv * list Z) := prhex_V (e_dep E) (exv_X E).
Definition exv_STK (E : exv_e) : Z := STK_ex_value (e_n E).
Definition exv_FP (E : exv_e) : list (Z * Z) :=
  [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8); (e_q E + 16, e_q E + 20); (e_q E + 32, e_q E + 36)].
(* the entry sp, the realigned frame base s1 (B 0x8356c `andi sp, sp, -32`), the first byte position after ex_ws *)
Definition exv_sp (E : exv_e) : Z := spZ (e_regs E).
Definition exv_s1 (E : exv_e) : Z := Z.land (exv_sp E - 288) (-32).
Definition exv_i1 (E : exv_e) : Z := exv_len E - Z.of_nat (length (PjGrammar.skip (exv_X E))).
(* the cut pcs *)
Definition exv_pc (off : Z) : Z := B_prog_sigma AS_ex_value + off.

(* ---- the allocator-state and memory relation ex_value keeps from its entry to a cut (the kit 4f18c75d4900's post:
   the non-primary room, the run position iface_room_pos and the m-form's memnorm keep; the draft's tex_value_specX
   adds, at PRH_FnEx.v:335, the hull use with no events, both secondary-map meters kept), as ONE conjunct of EXB, so no positional destruct of EXB moves. ex_value
   makes no allocator call: S changes only by the fake frame's take (set_fs) and release (stack_free_state), which
   keep st_secs, and by the recursive call, which posts the relation itself; every other callee keeps S (S' = S).
   memnorm is carried as the keep from the ENTRY memory (YSRrMemnorm.v's design: P m := memnorm mem0 -> memnorm m,
   srr_inv_laws_imp), by the _inv runners and the callees' m-form keeps. ---- *)
Section rm. Context {cp : CfParams} {RL : PrhRoomLive}.
Definition exv_room (S0 S : astate) : Prop :=
  (room_live_cf S0 -> room_live_cf S) /\
  (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S0 ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S) /\
  PresetHullBudget.hull_used S0 S [].
Lemma exv_room_refl : forall S, exv_room S S.
Proof. intros S. split; [|split]; [intros; assumption | intros; assumption | apply PresetHullBudget.hull_used_refl]. Qed.
Lemma exv_room_trans : forall S0 S1 S2, exv_room S0 S1 -> exv_room S1 S2 -> exv_room S0 S2.
Proof.
intros S0 S1 S2 (A1 & B1 & C1) (A2 & B2 & C2). split; [intros H; exact (A2 (A1 H)) |].
split; [intros; apply B2, B1; assumption | exact (PresetHullBudget.hull_used_app S0 S1 S2 [] [] C1 C2)].
Qed.
Lemma exv_room_eq : forall S0 S1 S2, exv_room S0 S1 -> S2 = S1 -> exv_room S0 S2.
Proof. intros S0 S1 S2 H ->. exact H. Qed.
Lemma exv_room_set_fs : forall S0 S f, exv_room S0 S -> exv_room S0 (set_fs f S).
Proof.
intros S0 S f (A & B & C). split; [intros H; exact (RL_set_fs S f (A H)) |].
split; [intros; apply PresetRoomPosKeep.room_pos_set_fs, B; assumption |].
exact (PresetHullBudget.hull_used_app S0 S (set_fs f S) [] [] C
  (PresetHullBudget.hull_used_secs S (set_fs f S) [] eq_refl)).
Qed.
Lemma exv_room_free : forall S0 S c p, exv_room S0 S -> exv_room S0 (stack_free_state c p S).
Proof.
intros S0 S c p (A & B & C). split; [intros H; exact (RL_stack_free S c p (A H)) |].
split; [intros; apply PresetRoomPosKeep.room_pos_stack_free, B; assumption |].
exact (PresetHullBudget.hull_used_app S0 S (stack_free_state c p S) [] [] C
  (PresetHullBudget.hull_used_secs S (stack_free_state c p S) [] eq_refl)).
Qed.
Lemma exv_room_post : forall S0 S1 S2, exv_room S0 S1 -> (room_live_cf S1 -> room_live_cf S2) ->
  (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S1 ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S2) ->
  PresetHullBudget.hull_used S1 S2 [] -> exv_room S0 S2.
Proof. intros S0 S1 S2 H A B C. exact (exv_room_trans S0 S1 S2 H (conj A (conj B C))). Qed.
(* the EXB conjunct: room / position from the entry state, memnorm keep from the entry memory *)
Definition exv_rm (S0 : astate) (mem0 : word -> option byte) (S : astate) (mem : word -> option byte) : Prop :=
  exv_room S0 S /\ (YAkMemnorm.memnorm rsegs mem0 -> YAkMemnorm.memnorm rsegs mem).
End rm.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* tex_value_specX's premises at the record, read at the record's own float state *)
Definition EXV_PRE (E : exv_e) : Prop :=
  let len := exv_len E in
  let ly := e_ly E in let S := e_S E in let Hp := e_Hp E in let W := e_W E in let regs := e_regs E in
  let mem := e_mem E in let md := e_md E in
  let q := e_q E in let v := e_v E in let x0 := e_x0 E in let i0 := e_i0 E in let scr := e_scr E in
  fpre (fx := e_fx E) B ARx (exv_STK E) ly S Hp W regs mem md (e_ch E) /\
  frm_zero (@YK11.fp_csr (e_fx E)) /\
  count_cid 1 (frames S) + Z.of_nat (Nat.succ (e_n E)) <= fs_frames 1 /\
  getr regs 10 = w64 q /\ getr regs 11 = w64 v /\
  prhex_cur W mem q (x0 + i0) (x0 + len) (e_dep E) scr (e_dl E) /\ q mod 8 = 0 /\
  prhex_ch_apart ly W mem regs (e_ch E) q 40 /\
  spZ regs <= q /\ q + 40 <= spZ regs + e_d E /\ fwin ly W regs mem (e_d E) /\
  src_rd W mem x0 (e_x E) /\ (0 < len -> prhex_inblk B ly S Hp x0 len) /\ len <= 3 * 2 ^ 20 /\ 0 <= i0 <= len /\
  0 <= e_dep E <= 32 /\ 32 <= e_dep E + Z.of_nat (e_n E) /\ (e_dl E = 0 \/ e_dl E = 1) /\
  wdest_ok B (exv_STK E) ly S W regs mem scr (len + 1) /\ prhex_inblk B ly S Hp scr (len + 1) /\
  (scr + len + 1 <= x0 \/ x0 + len <= scr) /\ (scr + len + 1 <= q \/ q + 40 <= scr) /\
  (v = 0 \/
   prhex_tree ly S (e_Lam E) W regs mem v (e_t E) (e_D E) /\ Forall (fun ak => 0 < fst ak) (e_D E) /\
   (forall z, PRH_Reader.pj_footR v (e_D E) z ->
      ~ (scr <= z < scr + len + 1) /\ ~ (q <= z < q + 40) /\ ~ (spZ regs - exv_STK E <= z < spZ regs) /\
      ~ (as_errno B <= z < as_errno B + 4))) /\
  prh_ledger B ly S Hp W mem (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) /\
  (* kit 4f18c75d4900: the memory is normal at entry (YAkMemnorm.memnorm over the full overlay) *)
  YAkMemnorm.memnorm rsegs mem.

(* the functional part of the post, at a state (W', mem') with result r *)
Definition EXV_RES (E : exv_e) (W' : world rsegs) (mem' : word -> option byte) (r : Z) : Prop :=
  exists p' dep' dl',
    prhex_cur W' mem' (e_q E) (e_x0 E + p') (e_x0 E + exv_len E) dep' (e_scr E) dl' /\ (dl' = 0 \/ dl' = 1) /\
    match exv_V E with
    | None => r = -1 /\ 0 <= p' <= exv_len E /\ e_dep E <= dep' <= 33
    | Some (u, rest) => r = 0 /\ p' = exv_len E - Z.of_nat (length rest) /\ dep' = e_dep E /\
        (dl' = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> u))
    end.
Definition EXV_Q (E : exv_e) : alayout -> astate -> list Z -> world rsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' => exv_room (e_S E) S' /\ exists r,
    getr regs' 10 = w64 r /\ EXV_RES E W' mem' r /\
    Hp' = e_Hp E /\ ablocks B ly' S' = ablocks B (e_ly E) (e_S E) /\
    prh_ledger B ly' S' Hp' W' mem' (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E).
Definition EXV_POST (E : exv_e) : world rsegs -> config -> Prop :=
  fpostWFm (fx := e_fx E) B ARx SK (exv_STK E) (e_d E) (exv_FP E) (e_regs E) (e_ly E) (e_S E) (e_Hp E) (e_W E)
    (e_mem E) (e_md E) (EXV_Q E).

(* ---- the base invariant at every cut after the prologue, at the current float state fx and the current state
   (lyc, Sc, Hpc, Wc, regs, memc, mdc), the frame being the class-1 fake frame (1, pos) at f ---- *)
Definition EXB (E : exv_e) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world rsegs) (regs : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (k pos : Z) : Prop :=
  let f := frame_addr lyc 1 pos in
  let len := exv_len E in
  (* the journal from the entry, at the caller-window width, with the frame live *)
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc mdc k /\
  (* the caller's window outside the cursor cells and the scratch, unchanged *)
  (forall a, exv_sp E <= a < exv_sp E + e_d E -> ~ inFP (exv_FP E) a ->
     aview rsegs (w_H Wc) memc a = aview rsegs (w_H (e_W E)) (e_mem E) a) /\
  (* the float state: rounding mode 0, the callee-saved f registers those of the entry *)
  fregs_kept_x (e_fx E) fx /\ frm_zero (@YK11.fp_csr fx) /\
  Hpc = e_Hp E /\ ablocks B lyc Sc = ablocks B (e_ly E) (e_S E) /\ exv_rm (e_S E) (e_mem E) Sc memc /\
  prh_ledger B lyc Sc Hpc Wc memc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) /\
  count_cid 1 (frames Sc) + Z.of_nat (e_n E) <= fs_frames 1 /\
  (* the registers every cut has: sp = s1, s0 = the entry sp, s2 = s8 = the frame, s9 = the shadow base, s10 = the
     frame's shadow, s3 = in, gp, tp *)
  getr regs 2 = w64 (exv_s1 E) /\ getr regs 8 = w64 (exv_sp E) /\ getr regs 9 = w64 (exv_s1 E) /\
  getr regs 18 = w64 f /\ getr regs 24 = w64 f /\ getr regs 25 = w64 SHADOW_OFF /\
  getr regs 26 = w64 (shadow_addr f) /\ getr regs 19 = w64 (e_q E) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  (* the saved registers (restored by the epilogue), the frame's slot 176(s1), the frame's flag pointer *)
  (forall o r, In (o, r) exv_saved ->
     val_mem rsegs (rdW Wc memc) (exv_sp E - 288 + o) 8 (bv_unsigned (getr (e_regs E) (Z_to_bv 5 r)))) /\
  val_mem rsegs (rdW Wc memc) (exv_s1 E + 176) 8 f /\
  rdword (aview rsegs (w_H Wc) memc) (f + 120) = Some (flag_addr lyc 1 pos) /\
  (* the text, the scratch, the cursor's shadow, the tree, at the current state *)
  src_rd Wc memc (e_x0 E) (e_x E) /\ (0 < len -> prhex_inblk B lyc Sc Hpc (e_x0 E) len) /\
  wdest_ok B 0 lyc Sc Wc regs memc (e_scr E) (len + 1) /\ prhex_inblk B lyc Sc Hpc (e_scr E) (len + 1) /\
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_q E) 40 /\
  (e_v E = 0 \/ prhex_tree lyc Sc (e_Lam E) Wc regs memc (e_v E) (e_t E) (e_D E)).

Definition exv_spill (E : exv_e) (Wc : world rsegs) (memc : word -> option byte) (o v : Z) : Prop :=
  val_mem rsegs (rdW Wc memc) (exv_s1 E + o) 8 v.

(* ---- the cut statements: from the cut's state, the run ends in the function's post ---- *)
Definition CUT_C1 (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos,
  e_n E = n -> EXV_PRE E -> EXB E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  getr regs 27 = w64 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x11c) regs memc mdc) (EXV_POST E).

Definition CUT_CN (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z),
  e_n E = n -> EXV_PRE E -> EXB E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> exv_disp c = false ->
  getr regs 11 = w64 (e_x0 E + exv_i1 E) -> getr regs 12 = w64 (e_x0 E + exv_len E) -> getr regs 27 = w64 c ->
  getr regs 20 = w64 (shadow_addr (e_q E)) ->
  exv_spill E Wc memc 144 (shadow_addr (e_q E)) -> exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x278) regs memc mdc) (EXV_POST E).

Definition CUT_CI (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z),
  e_n E = n -> EXV_PRE E -> EXB E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  getr regs 10 = w64 (if c =? 123 then 125 else 93) -> getr regs 11 = w64 (e_x0 E + exv_i1 E) ->
  getr regs 27 = w64 c -> getr regs 21 = w64 (-1) ->
  getr regs 20 = w64 (shadow_addr (e_q E)) -> getr regs 22 = w64 (shadow_addr (e_q E + 8)) ->
  getr regs 23 = w64 (e_q E + 8) ->
  exv_spill E Wc memc 144 (shadow_addr (e_q E)) -> exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x374) regs memc mdc) (EXV_POST E).

(* the differs bookkeeping of the items loop: vv is the node still compared (0: none, the C NULL), dlc the current
   in->differs; acc the members / items read so far (reversed) *)
Definition exv_dif (E : exv_e) (o : bool) (vv dlc : Z) (acc : list (list Z * PjTree.jv)) : Prop :=
  (vv = 0 /\ (e_v E = 0 -> dlc = e_dl E) /\
   (e_v E <> 0 -> dlc = 1 /\ PjTree.tag (e_t E) <> (if o then 6 else 5))) \/
  (vv = e_v E /\ vv <> 0 /\ PjTree.tag (e_t E) = (if o then 6 else 5) /\
   (dlc = 1 <-> e_dl E = 1 \/ ~ exv_pref o acc (e_t E))).

(* the loop head (B 0x83a60): i items read, in->p at x0 + ip, in->depth dep + 1, the spills of B 0x839ec-0x83a5c *)
Definition CUT_CL (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z) (i cap : nat) (acc : list (list Z * PjTree.jv)) (ip vv dlc : Z),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE E -> EXB E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur Wc memc q (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= exv_len E -> (dlc = 0 \/ dlc = 1) -> Z.of_nat i <= ip ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) o i cap acc (skipn (Z.to_nat ip) (e_x E)) ->
  exv_dif E o vv dlc acc ->
  getr regs 27 = w64 c -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spill E Wc memc 152 vv -> exv_spill E Wc memc 88 (vv + 40) -> exv_spill E Wc memc 56 (vv + 24) ->
  exv_spill E Wc memc 48 (vv + 32) -> exv_spill E Wc memc 40 (shadow_addr (vv + 32)) ->
  exv_spill E Wc memc 80 (q + 32) -> exv_spill E Wc memc 24 (q + 24) ->
  exv_spill E Wc memc 16 (shadow_addr (q + 24)) -> exv_spill E Wc memc 72 (shadow_addr (q + 32)) ->
  exv_spill E Wc memc 8 3 -> exv_spill E Wc memc 32 (2 ^ 60) ->
  exv_spill E Wc memc 136 (Z.of_nat i) -> exv_spill E Wc memc 112 (56 * Z.of_nat i) ->
  exv_spill E Wc memc 128 (8 * Z.of_nat i) -> exv_spill E Wc memc 64 (if o then 125 else 93) ->
  exv_spill E Wc memc 104 (shadow_addr (q + 16)) -> exv_spill E Wc memc 96 (q + 16) ->
  exv_spill E Wc memc 120 (frame_addr lyc 1 pos) -> exv_spill E Wc memc 144 (shadow_addr q) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x534) regs memc mdc) (EXV_POST E).

(* the close (B 0x83f24): the list read whole, a1 its count *)
Definition CUT_CC (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z) (acc : list (list Z * PjTree.jv)) (ip vv dlc : Z),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE E -> EXB E lyc Sc Hpc Wc regs memc mdc k pos ->
  (c = 91 \/ c = 123) -> e_dep E + 1 <= 32 ->
  prhex_cur Wc memc q (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= exv_len E -> (dlc = 0 \/ dlc = 1) ->
  exv_V E = Some (PjGrammar.mk o (rev acc), skipn (Z.to_nat ip) (e_x E)) ->
  exv_dif E o vv dlc acc ->
  getr regs 11 = w64 (Z.of_nat (length acc)) ->
  exv_spill E Wc memc 152 vv -> exv_spill E Wc memc 96 (q + 16) -> exv_spill E Wc memc 104 (shadow_addr (q + 16)) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x9f8) regs memc mdc) (EXV_POST E).

(* the exit (B 0x83fa8): s5 the result, the functional post already holds *)
Definition CUT_CX (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (r : Z),
  e_n E = n -> EXV_PRE E -> EXB E lyc Sc Hpc Wc regs memc mdc k pos ->
  getr regs 21 = w64 r -> EXV_RES E Wc memc r ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0xa7c) regs memc mdc) (EXV_POST E).

(* the entry (B 0x8352c): the text itself *)
Definition CUT_C0 (n : nat) : Prop :=
  forall E, e_n E = n -> e_fx E = fx -> EXV_PRE E ->
  SRr rsegs (e_W E) (cfg_at rsegs (B_prog_sigma AS_ex_value) (e_regs E) (e_mem E) (e_md E)) (EXV_POST E).
End c.

(* the three word literals ex_value passes ex_word (ExvDisp: listing slots exv_pc 0x420 / 0x19c / 0x268, PAddHi
   (A_OBJ 2) + off; image B' (pin d663f82d): .str / .str.1 / .str.2 at 0x20f60 / 0x20f80 / 0x20fa0 in the read-only band,
   each 0x20 above old B's - the target pass, the internal file exv_targets.out); offsets DERIVED from the B' listing *)
Definition exvd_lit (c w ty : Z) (wl : list Z) (u : PjTree.jv) : Prop :=
  (c = 116 /\ w = B_prog_val (A_OBJ 2) + 0x10f60 /\ ty = 2 /\ wl = PjGrammar.w_true /\ u = PjTree.JTrue) \/
  (c = 102 /\ w = B_prog_val (A_OBJ 2) + 0x10f80 /\ ty = 1 /\ wl = PjGrammar.w_false /\ u = PjTree.JFalse) \/
  (c = 110 /\ w = B_prog_val (A_OBJ 2) + 0x10fa0 /\ ty = 0 /\ wl = PjGrammar.w_null /\ u = PjTree.JNull).

(* ---- every callee text and law the segments take, each callee text at any float state ---- *)
(* strtod's model (= the strtod row owner's strtod_c.strtod_model by conversion): the double and the parsed length of a text *)
Definition exv_strtod_model (txt : list Z) : option (Z * Z) := FloatScan.scan_strtod (txt ++ [0]).
Definition exv_txt_ok (txt : list Z) : Prop :=
  Forall (fun c => FmtFp_facts3.is_numch c = true) txt /\ Z.of_nat (length txt) < 2 ^ 30.

Section h. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Record EXV_HYP : Prop := {
  (* The B text of ex_string (a Theorem Labs lane). ex_word's text is NOT a field: the tex_word_specX at a3bdeca3920 is
     false on both images (owner ruling 09:19Z, a Theorem Labs lane's counterexamples); only the word arm takes it, as its own
     premise EHW (ExvB_Disp_word.v / ExvB_Disp.v), WITHDRAWN, PENDING the kit *)
  eh_string : forall fx : YK11.FPState, tex_string_specX (fx := fx) (PA := PI_prog_B) B ARx SK;
  (* the runtime texts over ARx (YGcallMx.v; the rows are c-libc-stdio's / c-asan's) *)
  (* the strcmp / strlen rows in the read-only-premise m-form, engine home YGcallMxmn.v (s1b 459129c18903, blob
     2b01e06e3fc4; c-libc-stdio 11:46Z): MARKED TEXTS, owner c-libc-stdio *)
  eh_strcmp : forall fx : YK11.FPState,
    YGcallMxmn.astrcmp_realizes_xrom (fx := fx) rsegs B ARx B_prog_relro_lo B_prog_relro_hi (B_prog_sigma AS___wrap_strcmp);
  eh_strlen : forall fx : YK11.FPState,
    YGcallMxmn.astrlen_realizes_xrom (fx := fx) rsegs B ARx B_prog_relro_lo B_prog_relro_hi (B_prog_sigma AS___wrap_strlen);
  eh_bcmp : forall fx : YK11.FPState, YGcallMxmn.abcmp_realizes_xm (fx := fx) rsegs B ARx (B_prog_sigma AS___wrap_bcmp);
  eh_memcpy : forall fx : YK11.FPState, YGcallMxmn.aintrin_realizes_xm (fx := fx) rsegs B ARx OCpy (B_prog_sigma AS___asan_memcpy);
  (* musl strtod: the image facts the strtod row owner's B' row needs (lib/B/Prog/strtod_row.v strtod_row_aj_B, strtod_c.v's
     B' constants; cold/h-verbs-1-strtod102 84b0603ea373); errno at YF0m.TFIB_ERRNO (= STRTOD_ERRNO, the same number) *)
  eh_tp : as_tp B = STRTOD_TP;
  eh_errno_B : as_errno B = YF0m.TFIB_ERRNO;
  (* strtod's GOT guard cell is one of B's const cells, so alx_const_cells gives its view (strtod_site_x at exv_pc 0x8d0) *)
  eh_got_const : forall ly, In (z8 (ANum STRTOD_GOT_GUARD) STRTOD_GUARD) (as_const B ly);
  eh_errno_own : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B);
  (* (no memnorm field: `ARx -> aj_memnorm` is FALSE (the memnorm owner, 09:24Z: ARx sees memory through views only,
     aj_memnorm is whole-overlay). strtod_site_x's aj_memnorm is a PREMISE at the strtod state, threaded from the
     entry: see ExvB_Num*.v; every cut carries the memnorm keep from the entry memory, EXB's exv_rm) *)
  (* MARKED, owner: the allocator-model owner (ARcf's AR_blocks_law_cf gives n < cf_malloc_max): a live block's size fits strcmp's
     32-bit length premise (ExvNum; image A's CUTFIX_blk32) *)
  eh_blk32 : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 32;
  (* a live block's prefixes lie in the runtime's 8-byte-margin application range (ExvNum's strcmp premise); at the
     instance this is the allocator-model owner's PROVED block_amem_range8_cf (lib/Reusable/YGcfBlockRange.v:46, commit 6c9f248bed97), in
     its k-form; not marked *)
  eh_blk_amem8 : forall ly S Hp W mem md p n k, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= k <= n ->
    YGcallMx.amem_range8 p (k + 1);
  (* image facts of B's start-up tables (the kit's gap EX-LIT-SHADOW, closed, PRH_FnEx.v:48-50; the internal file B-STARTUP-FACTS.md rows 7.5-7.6;
     discharged at the instance by alx_const_cells / alx_zshadow, ExvB_ImgFacts.v:268 exvi_eh_litsh): the literals' shadow,
     for ex_word's cstr_ok (ExvDisp) *)
  eh_litsh : forall ly S Hp W mem md, ARx ly S Hp W mem md -> forall c w ty wl u, exvd_lit c w ty wl u ->
    range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF w (Z.of_nat (length wl) + 1) /\
    shadow_hull_vis (aview rsegs (w_H W) mem) w (Z.of_nat (length wl) + 1);
  (* MARKED, owner a Theorem Labs lane (stand-in pal_pst_ok of OwnB_p102.v / FuzzFreeB.v): the program statics are not runtime-owned, so
     the ledger cells survive frame_alloc_1's call (ExvB_Entry.v) *)
  eh_pst_own : forall a, Exists (in_zr a) prh_pst -> ~ Exists (in_zr a) (as_owned_static B);
  (* MARKED, owner: the allocator-model owner (preset's cf_head = 16): a harness head covers its 8-byte size word (ExvEntry; the kit's
     PRH_Keep.v Hhead) *)
  eh_head : 8 <= cf_head;  (* = the prh_head_wide (PRH_Base.v); the preset instance discharges it by a Theorem Labs lane's preset_head_wide *)
  (* MARKED, owner: the B start-up facts owner / image facts (H6_LA.v pal_uar_cell, S8aEntry.v UAR_CELL): the use-after-return flag cell
     lies in the low application range (ExvEntry reads it at entry + 0x5c) *)
  eh_uar_cell : 4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kLowMemEnd /\
    (as_uar_cell B + 4 <= B_prog_val (A_OBJ 0) \/ B_prog_val (A_OBJ 0) + 8 <= as_uar_cell B) /\
    (as_uar_cell B + 4 <= B_prog_val (A_OBJ 1) \/ B_prog_val (A_OBJ 1) + 8 <= as_uar_cell B) /\
    (as_uar_cell B + 4 <= B_prog_val (A_OBJ 12) \/ B_prog_val (A_OBJ 12) + 8 <= as_uar_cell B);
  (* MARKED, owner: the allocator-model owner (the hull twin of alx_zshadow_byte; ASan maps the whole low shadow): the shadow hull of a
     real-stack range is visible at every ARx state, so a stack-home tree root keeps prhex_tree's hull across calls
     (ExvEntry) *)
  eh_stk_hull : forall ly S Hp W mem md x n, ARx ly S Hp W mem md ->
    ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> shadow_hull_vis (aview rsegs (w_H W) mem) x n;
  (* MARKED, owner: the allocator-model owner (at ARcf by fs_iface's fi_area_Fsh: the fake-stack shadow area is visible): the shadow
     hull of a range inside a live fake frame is visible at every ARx state (a frame-home tree root; ExvEntry). Kept
     frame-only rather than for all in_app ranges, the narrower claim *)
  eh_frame_hull : forall ly S Hp W mem md cid pos x n, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    frame_addr ly cid pos <= x -> x + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
    shadow_hull_vis (aview rsegs (w_H W) mem) x n;
  (* MARKED, owner: the allocator-model owner (at ARcf the second conjunct of frame_facts_cf, lib/Reusable/YG0scf.v:322): a live fake
     frame's position is in range, so the frame lies above the image (strtod_site_x's si_globals_top <= e at B 0x83dfc;
     ExvNum) *)
  eh_fpos : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 0 <= pos < fs_frames cid;
  (* MARKED, owner: the allocator-model owner (at ARcf ARm's wf_fakestack; FCiface's fi_own_free_frame takes the same premise): a live
     fake frame's class is a real class, so its shadow range is whole granules (a frame-home tree root's
     range_addressable through the journal's frame clause; ExvEntry, ExvLoop's KIT_EXB_CALL; cgif YCbq.v:2661) *)
  eh_frames_cid : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 0 <= cid <= 10;
  (* MARKED image fact of B (closed, by computation at the B record; owner: the B start-up facts owner): the word literals' bytes and NUL
     are not runtime-owned (each literal's redzone starts after its NUL); the word arm reads them through the image
     view at non-owned read-only bytes (KIT_RODATA) *)
  eh_lit_own : forall c w ty wl u, exvd_lit c w ty wl u ->
    forall a, w <= a <= w + Z.of_nat (length wl) -> ~ Exists (in_zr a) (as_owned_static B);
  (* the class-1 frame area (FCiface.v; owner: the frame-class owner) and its address in image B *)
  eh_sm1 : forall fx : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fx) rsegs B ARx 1;
  eh_sm1_pc : B_prog_sigma AS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1;
  (* the allocator laws (YCbqG.v) and YGcallSx.v's frame laws *)
  eh_laws : AR_laws_x rsegs B ARx cf_head;
  eh_errno : api_env rsegs B;
  eh_ownlow : YGcallx.ARx_owned_low_law rsegs B ARx;
  eh_smx : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
    count_cid cid (frames S) < fs_frames cid ->
    exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
      frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S);
  eh_asfx : forall ly S Hp W mem md mem' md' cid pos,
    ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    aview rsegs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
       aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
    (forall a, aview rsegs (w_H W) mem a <> None -> aview rsegs (w_H W) mem' a <> None) ->
    m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
    (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
    ARx ly (stack_free_state cid pos S) Hp W mem' md';
  eh_fflx : forall ly S Hp (W : world rsegs) mem md cid pos,
    ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
    (app_addr (flag_addr ly cid pos) /\ ~ in_img rsegs (flag_addr ly cid pos)) /\
    (4096 <= flag_addr ly cid pos /\ zone2 (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling);
  eh_sfx : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2;
  (* the image facts the code reads through the GOT: YC1fP.v's PALib (shadow base cell) and the B' writer's marked
     hypothesis for the use-after-return flag's GOT word (B 0x8357c-0x83588) *)
  eh_palib : YC1fP.PALib (PI := PI_prog_B) B;
  eh_got_uar : as_got_uar B = B_prog_val (A_OBJ 1)
}.

(* ex_ws: the PROVED B' walk (int102 2dfa8b73a537, lib/B/Prog/ex_ws_x.v blob 1da1e4be3773, ex_ws_holds_x on the kit's
   tex_ws_specX), at any float state, from EXV_HYP's laws and PALib's GOT-shadow facts *)
Lemma exv_ws : forall (HYP : EXV_HYP) (fx : YK11.FPState),
  tex_ws_specX (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
intros HYP fx.
exact (ex_ws_x.ex_ws_holds_x SK B ARx (eh_laws HYP) (YC1fP.pal_got_shadow _ (eh_palib HYP)) (YC1fP.pal_cell _ (eh_palib HYP))).
Qed.

(* the frame room laws: no longer hypotheses, the class PrhRoomLive's own fields (kit a3bdeca3920; at the preset instance
   prh_room_live_a8 they are a Theorem Labs lane's PROVED room_live_set_fs / room_live_stack_free, YGcfRoomLive.v 9f8646ff07c0); kept
   under the old names with the EXV_HYP argument so the segment files' citations stand *)
Lemma room_live_set_fs : forall (HYP : EXV_HYP) S f, room_live_cf S -> room_live_cf (set_fs f S).
Proof. intros _. exact RL_set_fs. Qed.
Lemma room_live_free : forall (HYP : EXV_HYP) S c p, room_live_cf S -> room_live_cf (stack_free_state c p S).
Proof. intros _. exact RL_stack_free. Qed.

(* musl strtod at ex_value's one call site (exv_pc 0x8d0): the strtod row owner's PROVED B' row over ajournal_x, at B's strtod
   (STRTOD = B_prog_sigma AS_strtod), the stack need STK_RT_STRTOD (>= STRTOD_K), the model exv_strtod_model (=
   strtod_model by conversion) and the text class exv_txt_ok *)
Lemma exv_strtod_pc : B_prog_sigma AS_strtod = STRTOD.
Proof. vm_compute. reflexivity. Qed.
Lemma exv_strtod : forall (HYP : EXV_HYP) (fx : YK11.FPState) (PST : list (Z * Z)),
  YStrtodRowX.aj_strtod_row (fx := fx) (SK := SK) rsegs B ARx strtod_row.strtod_img_B PST (B_prog_sigma AS_strtod)
    STK_RT_STRTOD exv_strtod_model exv_txt_ok.
Proof.
intros HYP fx PST. rewrite exv_strtod_pc.
assert (Eerr : as_errno B = STRTOD_ERRNO) by (rewrite (eh_errno_B HYP); reflexivity).
apply (strtod_row.strtod_row_aj_B SK B PST ARx (eh_laws HYP) (eh_tp HYP) Eerr (eh_errno_own HYP)).
- unfold STK_RT_STRTOD, STRTOD_K. pose proof asan_consts. assert (ESTACK = 4096) by reflexivity. lia.
- intros txt H. exact H.
- intros txt bits c _ H. exact H.
Qed.
End h.
