(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 892 of its 1130 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from fuzz_grant's lib/A/Prog/GrantEntrySeat.v (a working branch
   b47e973d564) for libreac/fuzz_boxreg B (fuzz_boxreg.asan-ubsan) over BoxBLxDefs.v: the context is BoxBLxDefs.v's
   lxcx / lx_base / lx_body; the environment is built here from the registers at the seat (the grant context's c_E0
   has no boxreg counterpart); the machine frame's saved words, its spill area, the class-3 side-stack frame
   (512 bytes, flag word at F + 504) and its 64 shadow bytes take boxreg B's numbers; the GOT / shadow-cell regions
   of the prologue are not part of a cut (no phase after the prologue reads them) and were dropped; the landing reads
   the memory facts from the phase's own lemmas (lx_saved_of_ss, lx_shadow_of_ss, lx_word_of_ss) instead of from a
   fixed region shape, and the shent / atom-fact lemmas a token walk needs were added.

   The seat and the landing of a phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, stated once for all
   of its phases, at ANY pc of the body (a cut of BoxBLxDefs.v or a phase's own loop head).

   A phase carries its machine state as `lx_body` and its own facts; the walk engine wants a symbolic state
   (`st_ok_pi`). `lx_seat` turns the first into the second, and `lx_land` turns the symbolic state back into
   `lx_body`.

   The environment (`lx_env cx fp regs ex`): atoms 0 .. 31 are the registers at the seat (regs = ms_regs ms3);
   32 is SHADOW_OFF; 33 .. 45 the caller's saved words (33 ra, 34 s0, 35 s1, 36 .. 45 s2 .. s11); 46 the frame F
   on the side stack; 47 its flag word's address; 48 up the phase's own words `ex`; 240 .. 511 the image (Eimg).
   The registers (`lx_sr ov`): sr_atoms with the overrides ov; LX_OV makes s1 the atom of sp (2) and s2 the atom of
   SHADOW_OFF (32), LX_OVP also s5 = F + 64 (prev).
   The regions (`lx_regions`), by index: 0 the saved words (base s0 = sp0, read-only); 1 the spill slots
   sp1 + 0 .. sp1 + 0x97 (base sp, writable); 2 the frame (base 46, writable, flag word chunk at 504); 3 its shadow
   bytes (base s6, window [wlo, whi), which may be empty); then the phase's `extra`. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBLxDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the atoms of the walk ---- *)
Definition LA_SP : nat := 2%nat.     (* sp = s1 = sp1 at the seat          *)
Definition LA_SP0 : nat := 8%nat.    (* s0 = sp0                           *)
Definition LA_FSH : nat := 22%nat.   (* s6 = the frame's shadow base       *)
Definition LA_SB : nat := 32%nat.    (* SHADOW_OFF                         *)
Definition LA_SAV : nat := 33%nat.   (* 33 + j: the caller's saved word j  *)
Definition LA_F : nat := 46%nat.     (* the frame on the side stack        *)
Definition LA_FL : nat := 47%nat.    (* its flag word's address            *)
Definition LA_EX : nat := 48%nat.    (* the phase's own atoms start here   *)

(* The registers whose entry values the machine frame saves, in the order of lsaved: ra, s0, s1, s2 .. s11. *)
Definition lx_sregs : list (bv 5) :=
  map (Z_to_bv 5) [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* The saved words: ra at sp0 - 8, then s0, s1, s2 .. s11 at sp0 - 16 - 8j. *)
Definition lx_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 33%nat 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 34%nat 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 35%nat 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 36%nat 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 37%nat 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 38%nat 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 39%nat 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 40%nat 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 41%nat 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 42%nat 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 43%nat 0));
    YP09.mkChunk (-96) (CVal 8 (SOff 44%nat 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 45%nat 0)) ].

Definition lx_saved_region : YP09.region := YP09.mkRegion (Some LA_SP0) (-104) 0 0 0 lx_saved_chunks.
(* The spill slots sp1 + 0 .. sp1 + 0x97 (the saved words start at sp0 - 104 >= sp1 + 0x98). *)
Definition LX_SPILL : Z := 0x98.
Definition lx_spill_region (scs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some LA_SP) 0 LX_SPILL 0 LX_SPILL scs.
(* The frame, with a write window [fwlo, fwhi) a phase chooses: empty when the phase's own instructions store nothing
   into the frame (then a run's frame_of keeps every byte of it, prev and mac included). *)
Definition lx_frame_region (fwlo fwhi : Z) (fcs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some LA_F) 0 (fs_frame_bytes LX_CID) fwlo fwhi
    (fcs ++ [YP09.mkChunk (fs_frame_bytes LX_CID - 8) (CVal 8 (SOff LA_FL 0))]).
Definition lx_shadow_region (wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
  fshadow_region LA_FSH LX_CID wlo whi cs.

Fixpoint lx_sh_chunks_from (i : Z) (sh : list Z) : list YP09.chunk :=
  match sh with
  | [] => []
  | v :: t => YP09.mkChunk i (CVal 1 (SLit v)) :: lx_sh_chunks_from (i + 1) t
  end.
Definition lx_sh_chunks (sh : list Z) : list YP09.chunk := lx_sh_chunks_from 0 sh.

(* A phase's spill slots, as (offset, value) pairs. *)
Definition lx_slot_chunks (l : list (Z * sv)) : list YP09.chunk :=
  map (fun p => YP09.mkChunk (fst p) (CVal 8 (snd p))) l.

Definition lx_regions0 (sh : list Z) (scs fcs : list YP09.chunk) (fwlo fwhi wlo whi : Z) : YP09.smem :=
  [lx_saved_region; lx_spill_region scs; lx_frame_region fwlo fwhi fcs;
   lx_shadow_region wlo whi (lx_sh_chunks sh)].
Definition lx_regions (sh : list Z) (scs fcs : list YP09.chunk) (fwlo fwhi wlo whi : Z) (extra : YP09.smem)
  : YP09.smem := lx_regions0 sh scs fcs fwlo fwhi wlo whi ++ extra.
Definition lx_ss (pc : Z) (sr : list sv) (sh : list Z) (scs fcs : list YP09.chunk) (fwlo fwhi wlo whi : Z)
  (extra : YP09.smem) (G : facts) : sstate :=
  mkSS pc sr (lx_regions sh scs fcs fwlo fwhi wlo whi extra) None G.

(* The registers of the seat: sr_atoms with overrides. *)
Fixpoint lx_sr (ov : list (bv 5 * sv)) : list sv :=
  match ov with [] => sr_atoms | p :: t => sr_set (lx_sr t) (fst p) (snd p) end.
Definition LX_OV : list (bv 5 * sv) := [((9%bv : bv 5), SOff LA_SP 0); ((18%bv : bv 5), SOff LA_SB 0)].
Definition LX_OVP : list (bv 5 * sv) := LX_OV ++ [((21%bv : bv 5), SOff LA_F 64)].

(* The facts on the seat's atoms that every cut gives (lx_af_ok): the stack pointers above the shadow span, the
   frame 64-aligned in application memory, its shadow base 8-aligned, the shadow offset. *)
Definition LX_AF : list (nat * afact) :=
  [(LA_SP, mkAF 0x7fff7f800000 (2 ^ 47) 5); (LA_SP0, mkAF 0x7fff7f808000 (2 ^ 47) 4);
   (LA_F, mkAF 4096 0x7fffff800000 6); (LA_FSH, mkAF 0x7fff8200 0x10007ff78000 3);
   (LA_SB, mkAF 0x7fff8000 0x7fff8000 0)].

(* A byte the shadow region's chunks fix: a one-byte literal chunk at offset i. *)
Definition lx_byte_chunk (i v : Z) (c : YP09.chunk) : bool :=
  match c with
  | YP09.mkChunk co (CVal w (SLit z)) => (co =? i) && N.eqb w 1 && (z mod 256 =? v)
  | _ => false
  end.
Fixpoint lx_sh_check_from (cs : list YP09.chunk) (i : Z) (sh : list Z) : bool :=
  match sh with [] => true | v :: t => existsb (lx_byte_chunk i v) cs && lx_sh_check_from cs (i + 1) t end.
Definition lx_sh_check (cs : list YP09.chunk) (sh : list Z) : bool := lx_sh_check_from cs 0 sh.

Lemma lx_all_disj_app : forall (E : env) r l1 l2,
  YP09.all_disjoint E r l1 -> YP09.all_disjoint E r l2 -> YP09.all_disjoint E r (l1 ++ l2).
Proof.
  intros E r l1. induction l1 as [|x l1 IH]; intros l2 H1 H2; cbn [app YP09.all_disjoint] in *;
    [exact H2|]. destruct H1 as [Hx Hr]. split; [exact Hx | exact (IH l2 Hr H2)].
Qed.

Lemma lx_pwd_app : forall (E : env) l1 l2,
  YP09.pairwise_disjoint E l1 -> YP09.pairwise_disjoint E l2 ->
  Forall (fun r => YP09.all_disjoint E r l2) l1 ->
  YP09.pairwise_disjoint E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|r l1 IH]; intros l2 H1 H2 HF; cbn [app]; [exact H2|].
  cbn [YP09.pairwise_disjoint] in H1 |- *. destruct H1 as [Ha Hp].
  inversion HF as [|x y Hx Ht]; subst.
  split; [apply lx_all_disj_app; [exact Ha | exact Hx] | exact (IH l2 Hp H2 Ht)].
Qed.

Lemma lx_sh_chunks_from_In : forall sh i j, (i < length sh)%nat ->
  In (YP09.mkChunk (j + Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (lx_sh_chunks_from j sh).
Proof.
  intros sh. induction sh as [|v t IH]; intros i j Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [lx_sh_chunks_from nth].
  - left. rewrite Z.add_0_r. reflexivity.
  - right. replace (j + Z.of_nat (S i)) with (j + 1 + Z.of_nat i) by lia.
    apply IH. cbn [length] in Hi. lia.
Qed.

Lemma lx_sh_chunks_In : forall sh i, (i < length sh)%nat ->
  In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (lx_sh_chunks sh).
Proof.
  intros sh i Hi. unfold lx_sh_chunks.
  replace (Z.of_nat i) with (0 + Z.of_nat i) by lia. apply lx_sh_chunks_from_In. exact Hi.
Qed.

Lemma lx_sv_SOff0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma lx_sh_check_from_spec : forall cs sh i j, lx_sh_check_from cs i sh = true -> (j < length sh)%nat ->
  exists z, In (YP09.mkChunk (i + Z.of_nat j) (CVal 1 (SLit z))) cs /\ z mod 256 = nth j sh 0.
Proof.
  intros cs sh. induction sh as [|v t IH]; intros i j Hc Hj; cbn [length] in Hj; [lia|].
  cbn [lx_sh_check_from] in Hc. apply andb_true_iff in Hc as [Hx Hr].
  destruct j as [|j].
  - apply existsb_exists in Hx as (c & Hin & Hb). destruct c as [co cv].
    destruct cv as [w e | | |]; try discriminate. destruct e; try discriminate.
    cbn [lx_byte_chunk] in Hb. apply andb_true_iff in Hb as [Hb Hz]. apply andb_true_iff in Hb as [Hco Hw].
    apply Z.eqb_eq in Hco. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst co w.
    exists z. cbn [nth]. rewrite Z.add_0_r. split; [exact Hin | exact Hz].
  - destruct (IH (i + 1) j Hr ltac:(lia)) as (z & Hin & Hz). exists z. cbn [nth].
    replace (i + Z.of_nat (S j)) with (i + 1 + Z.of_nat j) by lia. split; [exact Hin | exact Hz].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

(* ---- the environment of a seat ---- *)
Definition lx_xatoms (cx : lxcx) (fp : Z) : list word :=
  [w64 SHADOW_OFF] ++ map (getr (lc_regs cx)) lx_sregs ++ [w64 (lF cx fp); w64 (lFL cx fp)].
Definition lx_env (cx : lxcx) (fp : Z) (regs : bvmap 5 word) (ex : list word) : env :=
  Eimg (Ereg regs (lx_xatoms cx fp ++ ex)).

(* The facts on the atoms below LA_EX that the landing needs; they survive any havoc at LA_EX or above. *)
Definition lx_E (cx : lxcx) (fp : Z) (E : env) : Prop :=
  ew E LA_SP = w64 (lsp1 cx) /\ ew E LA_SP0 = w64 (lsp0 cx) /\
  ew E 3 = getr (lc_regs cx) 3 /\ ew E 4 = getr (lc_regs cx) 4 /\
  ew E LA_FSH = w64 (lSH cx fp) /\ ew E LA_SB = w64 SHADOW_OFF /\
  (forall j, (j < 13)%nat -> ew E (LA_SAV + j) = nth j (map (getr (lc_regs cx)) lx_sregs) (w64 0)) /\
  ew E LA_F = w64 (lF cx fp) /\ ew E LA_FL = w64 (lFL cx fp).

Lemma lx_xatoms_length : forall cx fp, length (lx_xatoms cx fp) = 16%nat.
Proof. intros cx fp. reflexivity. Qed.

Lemma lx_env_reg : forall cx fp regs ex n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (lx_env cx fp regs ex) n = getr regs r.
Proof.
  intros cx fp regs ex n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold lx_env. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma lx_env_x : forall cx fp regs ex i, (i < 16)%nat ->
  ew (lx_env cx fp regs ex) (32 + i) = nth i (lx_xatoms cx fp) (w64 0).
Proof.
  intros cx fp regs ex i Hi. unfold lx_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. rewrite app_nth1 by (rewrite lx_xatoms_length; exact Hi). reflexivity.
Qed.

Lemma lx_env_ex : forall cx fp regs ex i, (48 + i < 240)%nat ->
  ew (lx_env cx fp regs ex) (LA_EX + i) = nth i ex (w64 0).
Proof.
  intros cx fp regs ex i Hi. unfold lx_env, LA_EX. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (48 + i)%nat with (32 + (16 + i))%nat by lia.
  rewrite ew_Ereg_extra. rewrite app_nth2 by (rewrite lx_xatoms_length; lia).
  rewrite lx_xatoms_length. replace (16 + i - 16)%nat with i by lia. reflexivity.
Qed.

Lemma lx_env_img : forall cx fp regs ex, img_env VAL A_LIM (lx_env cx fp regs ex).
Proof. intros cx fp regs ex. unfold lx_env. apply Eimg_env. Qed.

Lemma lx_env_E : forall cx fp (ms3 : machine_state) ex,
  lregs cx fp ms3 -> lx_E cx fp (lx_env cx fp (ms_regs ms3) ex).
Proof.
  intros cx fp ms3 ex (H2 & H8 & H9 & H3 & H4 & H18 & H22).
  split; [rewrite (lx_env_reg cx fp _ ex 2 (Z_to_bv 5 2)) by reflexivity; exact H2|].
  split; [rewrite (lx_env_reg cx fp _ ex 8 (Z_to_bv 5 8)) by reflexivity; exact H8|].
  split; [rewrite (lx_env_reg cx fp _ ex 3 (Z_to_bv 5 3)) by reflexivity; exact H3|].
  split; [rewrite (lx_env_reg cx fp _ ex 4 (Z_to_bv 5 4)) by reflexivity; exact H4|].
  split; [rewrite (lx_env_reg cx fp _ ex 22 (Z_to_bv 5 22)) by reflexivity; exact H22|].
  split; [exact (lx_env_x cx fp _ ex 0 ltac:(lia))|].
  split.
  - intros j Hj. unfold LA_SAV. replace (33 + j)%nat with (32 + S j)%nat by lia.
    rewrite (lx_env_x cx fp _ ex (S j)) by lia. unfold lx_xatoms. cbn [app nth].
    rewrite app_nth1 by (rewrite length_map; cbn [length lx_sregs map]; lia). reflexivity.
  - split; [exact (lx_env_x cx fp _ ex 14 ltac:(lia)) | exact (lx_env_x cx fp _ ex 15 ltac:(lia))].
Qed.

Lemma lx_E_agree : forall cx fp E E', lx_E cx fp E ->
  (forall n, (n < LA_EX)%nat -> ew E' n = ew E n) -> lx_E cx fp E'.
Proof.
  intros cx fp E E' (H2 & H8 & H3 & H4 & H22 & H32 & Hs & H46 & H47) Ha. unfold LA_EX in Ha.
  split; [rewrite Ha by (unfold LA_SP; lia); exact H2|].
  split; [rewrite Ha by (unfold LA_SP0; lia); exact H8|].
  split; [rewrite Ha by lia; exact H3|]. split; [rewrite Ha by lia; exact H4|].
  split; [rewrite Ha by (unfold LA_FSH; lia); exact H22|].
  split; [rewrite Ha by (unfold LA_SB; lia); exact H32|].
  split; [intros j Hj; rewrite Ha by (unfold LA_SAV; lia); exact (Hs j Hj)|].
  split; [rewrite Ha by (unfold LA_F; lia); exact H46 | rewrite Ha by (unfold LA_FL; lia); exact H47].
Qed.

(* The overrides of the seat's registers hold when each says the register's value. *)
Lemma lx_regs_ok : forall E regs ov,
  regs_ok E sr_atoms regs ->
  Forall (fun p => sv_denot E (snd p) = getr regs (fst p)) ov ->
  regs_ok E (lx_sr ov) regs.
Proof.
  intros E regs ov H0 Hov. induction ov as [|p t IH]; cbn [lx_sr]; [exact H0|].
  inversion Hov as [|x y Hp Ht]; subst.
  specialize (IH Ht). destruct (bv_eqb (fst p) 0) eqn:Hz.
  - unfold sr_set. rewrite Hz. exact IH.
  - intros r. destruct (decide (r = fst p)) as [-> | Hne].
    + rewrite sr_get_set_same by exact Hz. symmetry. exact Hp.
    + rewrite sr_get_set_other by exact Hne. apply IH.
Qed.

Lemma lx_regs_ok_atoms : forall cx fp regs ex, regs_ok (lx_env cx fp regs ex) sr_atoms regs.
Proof.
  intros cx fp regs ex. unfold lx_env. apply regs_ok_Eimg_Ereg.
Qed.

(* LX_OV / LX_OVP at a cut: s1 = sp, s2 = SHADOW_OFF, s5 = F + 64. *)
Lemma lx_ov_ok : forall cx fp (ms3 : machine_state) ex,
  lregs cx fp ms3 ->
  Forall (fun p => sv_denot (lx_env cx fp (ms_regs ms3) ex) (snd p) = getr (ms_regs ms3) (fst p)) LX_OV.
Proof.
  intros cx fp ms3 ex HR. pose proof HR as (H2 & H8 & H9 & H3 & H4 & H18 & H22).
  unfold LX_OV. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; rewrite lx_sv_SOff0.
  - rewrite (lx_env_reg cx fp _ ex LA_SP (2%bv : bv 5)) by reflexivity. rewrite H2. symmetry. exact H9.
  - rewrite (lx_env_x cx fp _ ex 0) by lia. rewrite H18. reflexivity.
Qed.

Lemma lx_ovp_ok : forall cx fp (ms3 : machine_state) ex,
  lregs cx fp ms3 -> getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) ->
  Forall (fun p => sv_denot (lx_env cx fp (ms_regs ms3) ex) (snd p) = getr (ms_regs ms3) (fst p)) LX_OVP.
Proof.
  intros cx fp ms3 ex HR H21. unfold LX_OVP. apply Forall_app. split; [exact (lx_ov_ok cx fp ms3 ex HR)|].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd sv_denot].
  rewrite (lx_env_x cx fp _ ex 14) by lia.
  change (nth 14 (lx_xatoms cx fp) (w64 0)) with (w64 (lF cx fp)). rewrite H21.
  unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Zplus_mod_idemp_l.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

Section d.
Variable cx : lxcx.
Variable fp : Z.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
#[local] Notation M3 := (mrestrict (w_H W3) (ms_mem ms3)).

(* A phase's spill slots: each holds the value its expression denotes. *)
Definition lx_slots (E : env) (l : list (Z * sv)) : Prop :=
  Forall (fun p => rdword (lview W3 ms3) (lsp1 cx + fst p) = Some (bv_unsigned (sv_denot E (snd p)))) l.

Lemma lx_slot_chunks_ok : forall (E : env) l,
  lx_slots E l -> Forall (YP09.chunk_ok SEGS E M3 (lsp1 cx)) (lx_slot_chunks l).
Proof.
  intros E l. induction l as [|p t IH]; intros H; cbn [lx_slot_chunks map]; [constructor|].
  inversion H as [|x y Hp Ht]; subst. constructor; [|exact (IH Ht)].
  apply (chunk_ok_val SEGS E M3 (lsp1 cx) (fst p) 8%N (snd p) (bv_unsigned (sv_denot E (snd p)))).
  - symmetry. apply Z_to_bv_bv_unsigned.
  - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hp.
Qed.

(* A slot whose value is a literal or an atom (plus an offset). *)
Lemma lx_slot_lit : forall (E : env) off v, lslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64 ->
  rdword (lview W3 ms3) (lsp1 cx + off) = Some (bv_unsigned (sv_denot E (SLit v))).
Proof.
  intros E off v Hv Hr. cbn [sv_denot]. rewrite unsigned_lit_small by exact Hr. exact Hv.
Qed.

Lemma lx_slot_atom : forall (E : env) off n b c, lslot cx W3 ms3 off (b + c) -> ew E n = w64 b ->
  0 <= b < 2 ^ 64 -> 0 <= b + c < 2 ^ 64 ->
  rdword (lview W3 ms3) (lsp1 cx + off) = Some (bv_unsigned (sv_denot E (SOff n c))).
Proof.
  intros E off n b c Hv Hn Hb Hbc. cbn [sv_denot]. rewrite Hn. unfold w64.
  rewrite (unsigned_lit_small b) by exact Hb. rewrite unsigned_lit_small by exact Hbc. exact Hv.
Qed.

Lemma lx_sh_chunks_from_ok : forall (E : env) sh i,
  (forall j, (j < length sh)%nat -> lview W3 ms3 (lSH cx fp + (i + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E M3 (lSH cx fp)) (lx_sh_chunks_from i sh).
Proof.
  intros E sh. induction sh as [|v t IH]; intros i H; cbn [lx_sh_chunks_from]; [constructor|].
  constructor.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0.
    rewrite Z.add_0_r in H0. unfold lview in H0.
    destruct (aview SEGS (w_H W3) (ms_mem ms3) (lSH cx fp + i)) as [b|] eqn:Hb0; [|discriminate].
    injection H0 as <-. unfold aview in Hb0.
    destruct (mbyte SEGS M3 (lSH cx fp + i)) as [bb|] eqn:Ebb; cbn [option_map] in Hb0; [|discriminate].
    injection Hb0 as <-.
    intros k Hk. cbn [YP09.c_len YP09.c_val cv_len Z.of_N] in Hk. assert (k = 0) by lia. subst k.
    exists bb. cbn [YP09.c_off YP09.c_val cbyte]. split.
    + f_equal. unfold byte_of_word. cbn [sv_denot]. apply bv_eq.
      rewrite Z_to_bv_unsigned, Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 bb) as Hr.
      change (bv_modulus 8) with 256 in Hr. rewrite Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
      rewrite (Z.mod_small (bv_unsigned bb) (2 ^ 64)) by lia. apply Z.mod_small. exact Hr.
    + rewrite Z.add_0_r. exact Ebb.
  - apply IH. intros j Hj. pose proof (H (S j) ltac:(cbn [length]; lia)) as Hs. cbn [nth] in Hs.
    replace (lSH cx fp + (i + 1 + Z.of_nat j)) with (lSH cx fp + (i + Z.of_nat (S j))) by lia.
    exact Hs.
Qed.

Lemma lx_sh_chunks_ok : forall (E : env) sh,
  lshadow cx fp W3 ms3 sh -> Forall (YP09.chunk_ok SEGS E M3 (lSH cx fp)) (lx_sh_chunks sh).
Proof.
  intros E sh H. apply lx_sh_chunks_from_ok. intros j Hj.
  replace (lSH cx fp + (0 + Z.of_nat j)) with (lSH cx fp + Z.of_nat j) by lia. exact (H j Hj).
Qed.

(* ---- the bytes a phase's facts speak about, and what keeps them ---- *)
(* A call that leaves this phase's own memory alone keeps every byte at or above the realigned stack pointer, the
   caller's input block, the frame and its shadow, and the blocks the phase holds (`rs`, (address, size) pairs). *)
Definition lx_keep_at (rs : list (Z * Z)) (a : Z) : Prop :=
  lsp1 cx <= a < 2 ^ 64 \/
  lc_p cx <= a < lc_p cx + lc_n cx \/
  lF cx fp <= a < lF cx fp + fs_frame_bytes LX_CID \/
  lSH cx fp <= a < lSH cx fp + fs_frame_bytes LX_CID / 8 \/
  Exists (fun r => fst r <= a < fst r + snd r) rs.
Definition lx_keep (rs : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, lx_keep_at rs a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma lx_keep_refl : forall rs m, lx_keep rs m m.
Proof. intros rs m a _. reflexivity. Qed.

Lemma lx_keep_trans : forall rs m1 m2 m3, lx_keep rs m1 m2 -> lx_keep rs m2 m3 -> lx_keep rs m1 m3.
Proof. intros rs m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma lx_keep_sub : forall rs rs' m m',
  (forall r, In r rs -> In r rs') -> lx_keep rs' m m' -> lx_keep rs m m'.
Proof.
  intros rs rs' m m' Hin Hk a Ha. apply Hk.
  unfold lx_keep_at in Ha |- *.
  destruct Ha as [H|[H|[H|[H|H]]]]; [left|right;left|right;right;left|right;right;right;left|].
  1-4: exact H.
  right; right; right; right. apply Exists_exists in H as (r & Hr & Hb).
  apply Exists_exists. exists r. split; [exact (Hin r Hr) | exact Hb].
Qed.

Lemma lx_rdword_keep : forall rs m m' a v,
  lx_keep rs m m' -> (forall i, 0 <= i < 8 -> lx_keep_at rs (a + i)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v ->
  rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros rs m m' a v Hk Hin Hr.
  assert (K : forall i, 0 <= i < 8 ->
    aview SEGS (w_H W3) m' (a + i) = aview SEGS (w_H W3) m (a + i))
    by (intros i Hi; apply Hk; apply Hin; lia).
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Lemma lx_garr8_keep : forall rs m m' a l,
  lx_keep rs m m' ->
  (forall i, 0 <= i < Z.of_nat (length l) -> lx_keep_at rs (a + i)) ->
  garr8 SEGS (mrestrict (w_H W3) m) a l ->
  garr8 SEGS (mrestrict (w_H W3) m') a l.
Proof.
  intros rs m m' a l Hk Hin Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) m m' (a + Z.of_nat j)
             (Hk (a + Z.of_nat j) (Hin (Z.of_nat j) ltac:(lia)))).
  exact Hv0.
Qed.

(* ---- the geometry a phase runs in ---- *)
Section e.
Variable ly3 : alayout.
Variable S3 : astate.
Variable md3 : Model.
Variable k : Z.
Hypothesis HB : lx_base B MT cx.
Hypothesis HJ : ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
  (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].

Lemma lx_fin : In (LX_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.

Lemma lx_frame_addr_eq : frame_addr ly3 LX_CID fp = lF cx fp.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  unfold lF. apply Efa.
Qed.

Lemma lx_flag_addr_eq : flag_addr ly3 LX_CID fp = lFL cx fp.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  pose proof (Efa 0 0) as E00. unfold frame_addr in E00.
  unfold lFL, flag_addr. lia.
Qed.

Lemma lx_sp_facts :
  lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx /\ lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  unfold lsp1, lsp0 in *. unfold LX_STK in *.
  pose proof (Z.div_mod (spZ (lc_regs cx) - 256) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (lc_regs cx) - 256) 32 ltac:(lia)) as Hmp.
  split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Lemma lx_F_facts :
  4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\
  in_app (lF cx fp) 512 /\
  (lF cx fp + 512 <= IMG_LO \/ IMG_TOP <= lF cx fp) /\
  lF cx fp mod 64 = 0 /\
  lSH cx fp = SHADOW_OFF + lF cx fp / 8.
Proof.
  pose proof HJ as (HAR3 & _).
  pose proof (frames_bounds _ _ LAWS _ _ _ _ _ LX_CID fp HAR3 lx_fin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 LX_CID fp HAR3 lx_fin) as HFo.
  pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 LX_CID fp HAR3 lx_fin) as (Hal & _).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  rewrite lx_frame_addr_eq in HF0, HFc, HFia, HFo, Hal. rewrite Hfb in HFc, HFia, HFo.
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|].
  split; [exact Hal|]. reflexivity.
Qed.

Lemma lx_base_sp : forall E, lx_E cx fp E -> YP09.base_val E (Some LA_SP) = lsp1 cx.
Proof.
  intros E (H2 & _). pose proof lx_sp_facts as (_ & Hlo & Hhi & Hsp1 & _).
  pose proof asan_consts as (Hac & _).
  cbn [YP09.base_val]. rewrite H2. apply unsigned_lit_small. lia.
Qed.

Lemma lx_base_sp0 : forall E, lx_E cx fp E -> YP09.base_val E (Some LA_SP0) = lsp0 cx.
Proof.
  intros E (_ & H8 & _). pose proof lx_sp_facts as (_ & Hlo & Hhi & _).
  pose proof asan_consts as (Hac & _).
  cbn [YP09.base_val]. rewrite H8. apply unsigned_lit_small. lia.
Qed.

Lemma lx_base_F : forall E, lx_E cx fp E -> YP09.base_val E (Some LA_F) = lF cx fp.
Proof.
  intros E (_ & _ & _ & _ & _ & _ & _ & H46 & _). pose proof lx_F_facts as (HF0 & HFc & _).
  pose proof asan_consts as (Hac & _).
  cbn [YP09.base_val]. rewrite H46. apply unsigned_lit_small. lia.
Qed.

Lemma lx_sh_range : 0 <= lSH cx fp /\ lSH cx fp + 64 <= 2 ^ 64.
Proof.
  pose proof lx_F_facts as (HF0 & HFc & _ & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  rewrite HSHeq. unfold SHADOW_OFF. lia.
Qed.

Lemma lx_base_FSH : forall E, lx_E cx fp E -> YP09.base_val E (Some LA_FSH) = lSH cx fp.
Proof.
  intros E (_ & _ & _ & _ & H22 & _). pose proof lx_sh_range as (Hs0 & Hs1).
  cbn [YP09.base_val]. rewrite H22. apply unsigned_lit_small. lia.
Qed.

Lemma lx_region_saved : forall E, lx_E cx fp E -> lsaved cx W3 ms3 ->
  YP09.region_ok SEGS E M3 lx_saved_region.
Proof.
  intros E HE Hsv. pose proof (lx_base_sp0 E HE) as Ub.
  pose proof HE as (_ & _ & _ & _ & _ & _ & HS & _).
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & _).
  pose proof asan_consts as (Hac & _).
  assert (HSV : forall (j : nat) off,
    (j < 13)%nat -> (LA_SAV + j)%nat = Z.to_nat (33 + Z.of_nat j) ->
    rdword (lview W3 ms3) (lsp0 cx + off) = Some (bv_unsigned (nth j (map (getr (lc_regs cx)) lx_sregs) (w64 0))) ->
    YP09.chunk_ok SEGS E M3 (lsp0 cx) (YP09.mkChunk off (CVal 8 (SOff (LA_SAV + j) 0)))).
  { intros j off Hj _ Hrd.
    apply (chunk_ok_val SEGS E M3 (lsp0 cx) off 8%N (SOff (LA_SAV + j) 0)
             (bv_unsigned (nth j (map (getr (lc_regs cx)) lx_sregs) (w64 0)))).
    - rewrite lx_sv_SOff0, (HS j Hj). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hrd. }
  destruct Hsv as (Hra & Hsj).
  unfold YP09.region_ok, lx_saved_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold lx_saved_chunks.
  apply Forall_cons;
    [apply (HSV 0%nat (-8)); [lia | reflexivity |
      replace (lsp0 cx + -8) with (lsp0 cx - 8) by lia; exact Hra] | ].
  assert (SJ : forall j : nat, (1 <= j < 13)%nat ->
    rdword (lview W3 ms3) (lsp0 cx + (-8 - 8 * Z.of_nat j)) =
      Some (bv_unsigned (nth j (map (getr (lc_regs cx)) lx_sregs) (w64 0)))).
  { intros j Hj. replace (lsp0 cx + (-8 - 8 * Z.of_nat j)) with (lsp0 cx - 16 - 8 * (Z.of_nat j - 1)) by lia.
    rewrite (Hsj (Z.of_nat j - 1) ltac:(lia)). do 2 f_equal.
    assert (Hc : j = 1%nat \/ j = 2%nat \/ j = 3%nat \/ j = 4%nat \/ j = 5%nat \/ j = 6%nat \/ j = 7%nat \/
                 j = 8%nat \/ j = 9%nat \/ j = 10%nat \/ j = 11%nat \/ j = 12%nat) by lia.
    repeat (destruct Hc as [-> | Hc]; [reflexivity|]). subst j. reflexivity. }
  apply Forall_cons; [apply (HSV 1%nat (-16)); [lia | reflexivity | exact (SJ 1%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 2%nat (-24)); [lia | reflexivity | exact (SJ 2%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 3%nat (-32)); [lia | reflexivity | exact (SJ 3%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 4%nat (-40)); [lia | reflexivity | exact (SJ 4%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 5%nat (-48)); [lia | reflexivity | exact (SJ 5%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 6%nat (-56)); [lia | reflexivity | exact (SJ 6%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 7%nat (-64)); [lia | reflexivity | exact (SJ 7%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 8%nat (-72)); [lia | reflexivity | exact (SJ 8%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 9%nat (-80)); [lia | reflexivity | exact (SJ 9%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 10%nat (-88)); [lia | reflexivity | exact (SJ 10%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 11%nat (-96)); [lia | reflexivity | exact (SJ 11%nat ltac:(lia))]|].
  apply Forall_cons; [apply (HSV 12%nat (-104)); [lia | reflexivity | exact (SJ 12%nat ltac:(lia))]|].
  apply Forall_nil.
Qed.

Lemma lx_region_spill : forall E scs, lx_E cx fp E ->
  Forall (YP09.chunk_ok SEGS E M3 (lsp1 cx)) scs ->
  YP09.region_ok SEGS E M3 (lx_spill_region scs).
Proof.
  intros E scs HE Hcs.
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & _).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  unfold YP09.region_ok, lx_spill_region, LX_SPILL.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (lx_base_sp E HE). split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
Qed.

Lemma lx_region_frame : forall E fwlo fwhi fcs, lx_E cx fp E -> 0 <= fwlo -> fwhi <= fs_frame_bytes LX_CID ->
  rdword (lview W3 ms3) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) ->
  Forall (YP09.chunk_ok SEGS E M3 (lF cx fp)) fcs ->
  YP09.region_ok SEGS E M3 (lx_frame_region fwlo fwhi fcs).
Proof.
  intros E fwlo fwhi fcs HE Hfwlo Hfwhi Hfl Hcs.
  pose proof lx_F_facts as (HF0 & HFc & HFia & HFo & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ LX_CID fp HAR3 lx_fin) as (_ & _ & HFpres & _).
  rewrite lx_frame_addr_eq, Hfb in HFpres.
  destruct (al_flag _ _ LAWS _ _ _ _ _ LX_CID fp HAR3 lx_fin) as (_ & _ & Hfia & Hflt).
  rewrite lx_flag_addr_eq in Hfia, Hflt.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & HFE & HFLE).
  assert (HflZ : 0 <= lFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  unfold YP09.region_ok, lx_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (lx_base_F E HE), Hfb. rewrite Hfb in Hfwhi. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (lF cx fp + o) ltac:(lia))).
  - apply Forall_app. split; [exact Hcs|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (lF cx fp) (512 - 8) 8%N (SOff LA_FL 0) (lFL cx fp)).
    + rewrite lx_sv_SOff0, HFLE. reflexivity.
    + cbn [Z.of_N]. change (8 * 8) with 64. exact HflZ.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. rewrite Hfb in Hfl.
      replace (lF cx fp + (512 - 8)) with (lF cx fp + 512 - 8) by lia.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hfl.
Qed.

Lemma lx_region_shadow : forall E sh wlo whi, lx_E cx fp E ->
  0 <= wlo -> whi <= 64 -> lshadow cx fp W3 ms3 sh ->
  YP09.region_ok SEGS E M3 (lx_shadow_region wlo whi (lx_sh_chunks sh)).
Proof.
  intros E sh wlo whi HE Hwlo Hwhi Hsh.
  pose proof lx_sh_range as (Hs0 & Hs1).
  pose proof HJ as (HAR3 & _).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ LX_CID fp HAR3 lx_fin) as (_ & _ & _ & HFSpres).
  rewrite lx_frame_addr_eq, Hfb8 in HFSpres.
  pose proof (lx_sh_chunks_ok E sh Hsh) as Hcs.
  unfold YP09.region_ok, lx_shadow_region, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (lx_base_FSH E HE), Hfb8. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
Qed.

(* The extents of the four regions of every seat. *)
Lemma lx_extents : forall E, lx_E cx fp E ->
  YP09.base_val E (Some LA_SP0) = lsp0 cx /\ YP09.base_val E (Some LA_SP) = lsp1 cx /\
  YP09.base_val E (Some LA_F) = lF cx fp /\ YP09.base_val E (Some LA_FSH) = lSH cx fp.
Proof.
  intros E HE. split; [exact (lx_base_sp0 E HE)|]. split; [exact (lx_base_sp E HE)|].
  split; [exact (lx_base_F E HE) | exact (lx_base_FSH E HE)].
Qed.

(* The write windows of the four regions of every seat are the journal's to write: the spill slots are in the
   function's stack window, the frame and its shadow bytes are the function's own frame (in_frames). A phase gives
   awr_ok for its own `extra` regions. The layout lyc is the current one (frame_addr is the same in every layout
   of the journal: lx_frame_addr_eq). *)
(* The four regions as a run leaves them (the chunk lists are whatever the run holds): usable at every run of a
   phase, not only the first one. *)
Lemma lx_awr_ok_cons : forall E (rs : YP09.smem) scs fcs shc fwlo fwhi wlo whi lyc bl0 blc,
  lx_E cx fp E -> frame_addr lyc LX_CID fp = lF cx fp ->
  0 <= wlo -> whi <= 64 -> 0 <= fwlo -> fwhi <= 512 ->
  awr_ok E rs LX_STK (lsp0 cx) [] bl0 blc lyc [(LX_CID, fp)] ->
  awr_ok E (lx_saved_region :: lx_spill_region scs :: lx_frame_region fwlo fwhi fcs
            :: lx_shadow_region wlo whi shc :: rs) LX_STK (lsp0 cx) [] bl0 blc lyc [(LX_CID, fp)].
Proof.
  intros E rs scs fcs shc fwlo fwhi wlo whi lyc bl0 blc HE Hfa Hwlo Hwhi Hfwlo Hfwhi Hex.
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & _).
  pose proof (lx_extents E HE) as (U8 & U2 & U46 & U22).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ LA_SP (lsp1 cx - lsp0 cx));
    [reflexivity | cbn [YP09.base_val] in U2; rewrite U2; lia | cbn; unfold LX_STK; lia
    | cbn; unfold LX_SPILL; lia |].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ LA_F (lF cx fp));
    [reflexivity | cbn [YP09.base_val] in U46; exact U46 | |].
  { intros a Ha. cbn [lx_frame_region YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right. exists LX_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hfb. lia. }
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ LA_FSH (lSH cx fp));
    [reflexivity | cbn [YP09.base_val] in U22; exact U22 | | exact Hex].
  intros a Ha. cbn [lx_shadow_region fshadow_region YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists LX_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hfb8. unfold lSH in Ha. lia.
Qed.

Lemma lx_awr_ok : forall E sh scs fcs fwlo fwhi wlo whi extra lyc bl0 blc,
  lx_E cx fp E -> frame_addr lyc LX_CID fp = lF cx fp ->
  0 <= wlo -> whi <= 64 -> 0 <= fwlo -> fwhi <= 512 ->
  awr_ok E extra LX_STK (lsp0 cx) [] bl0 blc lyc [(LX_CID, fp)] ->
  awr_ok E (lx_regions sh scs fcs fwlo fwhi wlo whi extra) LX_STK (lsp0 cx) [] bl0 blc lyc [(LX_CID, fp)].
Proof.
  intros E sh scs fcs fwlo fwhi wlo whi extra lyc bl0 blc HE Hfa Hwlo Hwhi Hfwlo Hfwhi Hex.
  unfold lx_regions, lx_regions0. cbn [app].
  exact (lx_awr_ok_cons E extra scs fcs (lx_sh_chunks sh) fwlo fwhi wlo whi lyc bl0 blc
           HE Hfa Hwlo Hwhi Hfwlo Hfwhi Hex).
Qed.

Lemma lx_disj : forall E sh scs fcs fwlo fwhi wlo whi, lx_E cx fp E ->
  YP09.pairwise_disjoint E (lx_regions0 sh scs fcs fwlo fwhi wlo whi).
Proof.
  intros E sh scs fcs fwlo fwhi wlo whi HE.
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & _).
  pose proof lx_F_facts as (HF0 & HFc & HFia & HFo & _ & HSHeq).
  pose proof lx_sh_range as (Hs0 & Hs1).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  pose proof (lx_extents E HE) as (U8 & U2 & U46 & U22).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  apply pairwise_disjoint_of_extents.
  unfold lx_regions0, lx_saved_region, lx_spill_region, LX_SPILL, lx_frame_region,
    lx_shadow_region, fshadow_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U8, U2, U46, U22, Hfb8, Hfb.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HSHeq.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  repeat split; lia.
Qed.

(* A region inside a heap block of the current state (the registry, the input, a name) is apart from the four
   regions of every seat: the block is below the allocator's ceiling (the stack is above it), apart from the frame
   (AR's separation of blocks and frames) and in application memory (the frame's shadow is not). *)
Lemma lx_block_disj : forall E (n : nat) q b sz lo hi wlo whi cs sh scs fcs fwlo fwhi wlo' whi',
  lx_E cx fp E -> In (b, sz) (ablocks B ly3 S3) -> bv_unsigned (ew E n) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  Forall (fun r0 => YP09.all_disjoint E r0 [YP09.mkRegion (Some n) lo hi wlo whi cs])
    (lx_regions0 sh scs fcs fwlo fwhi wlo' whi').
Proof.
  intros E n q b sz lo hi wlo whi cs sh scs fcs fwlo fwhi wlo' whi' HE Hin Hq Hlo Hlh Hhi.
  pose proof lx_sp_facts as (Hal & Hslo & Hshi & Hsp1 & _).
  pose proof lx_F_facts as (HF0 & HFc & HFia & HFo & _ & HSHeq).
  pose proof lx_sh_range as (Hs0 & Hs1).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof HJ as (HAR3 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR3 Hin) as (_ & Hb4096 & Hbceil & Hbia & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b sz LX_CID fp HAR3 Hin lx_fin) as Hsep.
  rewrite lx_frame_addr_eq in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  pose proof (lx_extents E HE) as (U8 & U2 & U46 & U22).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  rewrite Hfb in Hsep.
  unfold lx_regions0. repeat apply Forall_cons; try apply Forall_nil;
    apply all_disjoint_of_extents;
    unfold lx_saved_region, lx_spill_region, LX_SPILL, lx_frame_region,
      lx_shadow_region, fshadow_region, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint]; unfold zdisj; cbn [fst snd base_val];
    cbn [YP09.base_val] in U8, U2, U46, U22;
    rewrite ?U8, ?U2, ?U46, ?U22, ?Hfb8, ?Hfb, ?Hq;
    (split; [|exact I]); rewrite ?HSHeq;
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* ---- the seat: a phase's machine state as the engine's symbolic state ---- *)
Theorem lx_seat : forall E pc sr sh l fcs fwlo fwhi wlo whi extra G,
  lx_E cx fp E ->
  lx_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  lx_slots E l ->
  Forall (YP09.chunk_ok SEGS E M3 (lF cx fp)) fcs ->
  0 <= wlo -> whi <= 64 -> 0 <= fwlo -> fwhi <= 512 ->
  YP09.regions_wf (lx_regions sh (lx_slot_chunks l) fcs fwlo fwhi wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (lx_regions0 sh (lx_slot_chunks l) fcs fwlo fwhi wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (lx_ss pc sr sh (lx_slot_chunks l) fcs fwlo fwhi wlo whi extra G) (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh l fcs fwlo fwhi wlo whi extra G HE HBD HR HSL HFC Hwlo Hwhi Hfwlo Hfwhi Hwf Hex Hexp Hexd HG.
  assert (Hfb512 : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & Hgregs & Hsaved & Hshadow
                     & Hflag & _ & _ & _ & Hgarr).
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold lx_ss, lx_regions.
  apply pa_entry_st_ok_full; [exact HR | exact Hwf | | | exact HG].
  - apply Forall_app. split; [|exact Hex].
    unfold lx_regions0. apply Forall_cons; [exact (lx_region_saved E HE Hsaved)|].
    apply Forall_cons; [exact (lx_region_spill E (lx_slot_chunks l) HE (lx_slot_chunks_ok E l HSL))|].
    apply Forall_cons;
      [exact (lx_region_frame E fwlo fwhi fcs HE Hfwlo ltac:(rewrite Hfb512; exact Hfwhi) Hflag HFC)|].
    apply Forall_cons; [exact (lx_region_shadow E sh wlo whi HE Hwlo Hwhi Hshadow)|].
    apply Forall_nil.
  - apply lx_pwd_app;
      [exact (lx_disj E sh (lx_slot_chunks l) fcs fwlo fwhi wlo whi HE) | exact Hexp | exact Hexd].
Qed.

(* The facts of LX_AF at a seat. *)
Lemma lx_af_ok : forall E, lx_E cx fp E -> atoms_ok E LX_AF.
Proof.
  intros E HE. pose proof HE as (H2 & H8 & _ & _ & H22 & H32 & _ & H46 & _).
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hal32).
  pose proof lx_F_facts as (HF0 & HFc & _ & _ & Hal64 & HSHeq).
  pose proof lx_sh_range as (Hs0 & Hs1).
  pose proof asan_consts as (Hac & _).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  assert (HF8 : (lF cx fp / 8) mod 8 = 0).
  { pose proof (Z.div_mod (lF cx fp) 64 ltac:(lia)) as D. rewrite Hal64, Z.add_0_r in D.
    rewrite D. replace (64 * (lF cx fp / 64)) with ((8 * (lF cx fp / 64)) * 8) by lia.
    rewrite Z.div_mul by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
  assert (HSH8 : lSH cx fp mod 8 = 0).
  { rewrite HSHeq. unfold SHADOW_OFF. rewrite Z.add_mod, HF8 by lia. reflexivity. }
  assert (Hd2 : 512 <= lF cx fp / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HSHlo : 0x7fff8200 <= lSH cx fp <= 0x10007ff78000) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
  unfold LX_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H2, H8, H46, H22, H32. unfold w64.
  rewrite (unsigned_lit_small (lsp1 cx)) by lia.
  rewrite (unsigned_lit_small (lsp0 cx)) by lia.
  rewrite (unsigned_lit_small (lF cx fp)) by lia.
  rewrite (unsigned_lit_small (lSH cx fp)) by lia.
  rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
  rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SHADOW_OFF; lia].
Qed.

(* ---- the landing: the engine's symbolic state back as a phase's machine state ---- *)
(* A word a region's chunk fixes. *)
Lemma lx_word_of_region : forall E n b cs lo hi wlo whi off e v,
  YP09.region_ok SEGS E M3 (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (lview W3 ms3) (b + off) = Some v.
Proof.
  intros E n b cs lo hi wlo whi off e v HR Hb Hin He Hv.
  apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact Hv].
  apply (field_of_region E M3 n b cs lo hi wlo whi off 8%N e v HR Hb Hin He);
    [cbn [Z.of_N]; change (8 * 8) with 64; exact Hv | cbn [Z.of_N]; lia].
Qed.

Lemma lx_word_of_ss : forall E ss i n b lo hi wlo whi cs off e v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (lview W3 ms3) (b + off) = Some v.
Proof.
  intros E ss i n b lo hi wlo whi cs off e v HS Hi Hb Hin He Hv.
  pose proof (st_ok_pi_region_nth E ss (restrict (w_H W3) ms3) i _ HS Hi) as HR.
  cbn [restrict ms_mem] in HR.
  exact (lx_word_of_region E n b cs lo hi wlo whi off e v HR Hb Hin He Hv).
Qed.

(* A spill slot from the spill region's chunk. *)
Lemma lx_slot_of_ss : forall E ss lo hi wlo whi cs off e v,
  lx_E cx fp E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some LA_SP) lo hi wlo whi cs) ->
  In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  lslot cx W3 ms3 off v.
Proof.
  intros E ss lo hi wlo whi cs off e v HE HS Hi Hin He Hv.
  pose proof (lx_base_sp E HE) as Ub. cbn [YP09.base_val] in Ub.
  exact (lx_word_of_ss E ss 1 LA_SP (lsp1 cx) lo hi wlo whi cs off e v HS Hi Ub Hin He Hv).
Qed.

(* The flag word (or any word of the frame) from the frame region's chunk. *)
Lemma lx_fword_of_ss : forall E ss lo hi wlo whi cs off e v,
  lx_E cx fp E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  nth_error (ss_mem ss) 2 = Some (YP09.mkRegion (Some LA_F) lo hi wlo whi cs) ->
  In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (lview W3 ms3) (lF cx fp + off) = Some v.
Proof.
  intros E ss lo hi wlo whi cs off e v HE HS Hi Hin He Hv.
  pose proof (lx_base_F E HE) as Ub. cbn [YP09.base_val] in Ub.
  exact (lx_word_of_ss E ss 2 LA_F (lF cx fp) lo hi wlo whi cs off e v HS Hi Ub Hin He Hv).
Qed.

Lemma lx_flag_of_ss : forall E ss lo hi wlo whi cs,
  lx_E cx fp E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  nth_error (ss_mem ss) 2 = Some (YP09.mkRegion (Some LA_F) lo hi wlo whi cs) ->
  In (YP09.mkChunk 504 (CVal 8 (SOff LA_FL 0))) cs ->
  rdword (lview W3 ms3) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp).
Proof.
  intros E ss lo hi wlo whi cs HE HS Hi Hin.
  pose proof HJ as (HAR3 & _).
  destruct (al_flag _ _ LAWS _ _ _ _ _ LX_CID fp HAR3 lx_fin) as (_ & _ & Hfia & Hflt).
  rewrite lx_flag_addr_eq in Hfia, Hflt.
  pose proof asan_consts as (Hac & _).
  assert (HflZ : 0 <= lFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  rewrite Hfb. replace (lF cx fp + 512 - 8) with (lF cx fp + 504) by lia.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HFLE).
  apply (lx_fword_of_ss E ss lo hi wlo whi cs 504 (SOff LA_FL 0) (lFL cx fp) HE HS Hi Hin);
    [rewrite lx_sv_SOff0; exact HFLE | exact HflZ].
Qed.

(* The saved words, while region 0 is the seat's. *)
Lemma lx_saved_of_ss : forall E ss,
  lx_E cx fp E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  nth_error (ss_mem ss) 0 = Some lx_saved_region ->
  lsaved cx W3 ms3.
Proof.
  intros E ss HE HS Hi.
  pose proof (st_ok_pi_region_nth E ss (restrict (w_H W3) ms3) 0 _ HS Hi) as HR.
  cbn [restrict ms_mem] in HR.
  pose proof (lx_base_sp0 E HE) as Ub. cbn [YP09.base_val] in Ub.
  pose proof HE as (_ & _ & _ & _ & _ & _ & HSV & _).
  assert (SAV : forall (j : nat) od, (j < 13)%nat ->
    In (YP09.mkChunk od (CVal 8 (SOff (LA_SAV + j) 0))) lx_saved_chunks ->
    rdword (lview W3 ms3) (lsp0 cx + od) = Some (bv_unsigned (nth j (map (getr (lc_regs cx)) lx_sregs) (w64 0)))).
  { intros j od Hj Hin.
    apply (lx_word_of_region E LA_SP0 (lsp0 cx) lx_saved_chunks (-104) 0 0 0 od (SOff (LA_SAV + j) 0)
             _ HR Ub Hin); [|apply u64_range].
    rewrite lx_sv_SOff0, (HSV j Hj). symmetry. apply Z_to_bv_bv_unsigned. }
  split.
  - replace (lsp0 cx - 8) with (lsp0 cx + -8) by lia.
    rewrite (SAV 0%nat (-8) ltac:(lia) ltac:(unfold lx_saved_chunks; cbn [In]; tauto)). reflexivity.
  - intros j Hj.
    assert (SJ : forall (q : nat) (od : Z), (q < 13)%nat -> (1 <= q)%nat -> od = -8 - 8 * Z.of_nat q ->
      In (YP09.mkChunk od (CVal 8 (SOff (LA_SAV + q) 0))) lx_saved_chunks ->
      Z.of_nat q = j + 1 ->
      rdword (lview W3 ms3) (lsp0 cx - 16 - 8 * j) =
        Some (bv_unsigned (getr (lc_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
    { intros q od Hq Hq1 Hod Hin Hjq.
      replace (lsp0 cx - 16 - 8 * j) with (lsp0 cx + od) by lia.
      rewrite (SAV q od Hq Hin). do 2 f_equal.
      replace j with (Z.of_nat q - 1) by lia.
      assert (Hc : q = 1%nat \/ q = 2%nat \/ q = 3%nat \/ q = 4%nat \/ q = 5%nat \/ q = 6%nat \/ q = 7%nat \/
                   q = 8%nat \/ q = 9%nat \/ q = 10%nat \/ q = 11%nat \/ q = 12%nat) by lia.
      repeat (destruct Hc as [-> | Hc]; [reflexivity|]). subst q. reflexivity. }
    assert (Hcase : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/
                    j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 1%nat (-16));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 2%nat (-24));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 3%nat (-32));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 4%nat (-40));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 5%nat (-48));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 6%nat (-56));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 7%nat (-64));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 8%nat (-72));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 9%nat (-80));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 10%nat (-88));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 11%nat (-96));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity]|].
    subst j. apply (SJ 12%nat (-104));
      [lia | lia | reflexivity | unfold lx_saved_chunks; cbn [In]; tauto | reflexivity].
Qed.

(* The frame's shadow bytes from region 3's chunks (lx_sh_check is decided by vm_compute). *)
Lemma lx_shadow_of_ss : forall E ss lo hi wlo whi cs sh,
  lx_E cx fp E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  nth_error (ss_mem ss) 3 = Some (YP09.mkRegion (Some LA_FSH) lo hi wlo whi cs) ->
  lx_sh_check cs sh = true ->
  lshadow cx fp W3 ms3 sh.
Proof.
  intros E ss lo hi wlo whi cs sh HE HS Hi Hc j Hj.
  pose proof (st_ok_pi_region_nth E ss (restrict (w_H W3) ms3) 3 _ HS Hi) as HR.
  cbn [restrict ms_mem] in HR.
  pose proof (lx_base_FSH E HE) as Ub. cbn [YP09.base_val] in Ub.
  destruct (lx_sh_check_from_spec cs sh 0 j Hc Hj) as (z & Hin & Hz). rewrite Z.add_0_l in Hin.
  destruct HR as (_ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ Hin).
  cbn [YP09.r_base base_val] in HF. rewrite Ub in HF.
  destruct (HF 0 ltac:(cbn; lia)) as (bb & Hcb & Hm).
  cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hcb. injection Hcb as <-.
  cbn [YP09.c_off YP09.c_val] in Hm. rewrite Z.add_0_r in Hm.
  assert (Hbyte : bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) = z mod 256).
  { unfold byte_of_word. rewrite !Z_to_bv_unsigned. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (256 * 72057594037927936).
    rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256 _), Z.mod_add by lia. apply Z.mod_mod. lia. }
  unfold lview, aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Hbyte. exact Hz.
Qed.

(* The landing: the registers of lregs from the symbolic registers, the rest from the phase's memory facts. *)
Theorem lx_land : forall E pc ss sh,
  lx_E cx fp E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  ss_pc ss = pc -> ss_resv ss = None ->
  sr_get (ss_regs ss) 2 = SOff LA_SP 0 -> sr_get (ss_regs ss) 8 = SOff LA_SP0 0 ->
  sr_get (ss_regs ss) 9 = SOff LA_SP 0 ->
  sr_get (ss_regs ss) 3 = SOff 3%nat 0 -> sr_get (ss_regs ss) 4 = SOff 4%nat 0 ->
  sr_get (ss_regs ss) 18 = SOff LA_SB 0 -> sr_get (ss_regs ss) 22 = SOff LA_FSH 0 ->
  lsaved cx W3 ms3 -> lshadow cx fp W3 ms3 sh ->
  rdword (lview W3 ms3) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) ->
  lslot cx W3 ms3 0x10 (lF cx fp) -> lslot cx W3 ms3 0x18 (lF cx fp) -> lslot cx W3 ms3 0x80 (lF cx fp) ->
  garr8 SEGS M3 (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) ->
  lx_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc ss sh HE HS Hpc0 Hresv0 Hr2 Hr8 Hr9 Hr3 Hr4 Hr18 Hr22 Hsv Hsh Hfl H10 H18 H80 Hgarr.
  pose proof HE as (H2E & H8E & H3E & H4E & H22E & H32E & _).
  pose proof HS as (Hfr & Hpcv & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
  destruct ss as [pc1 sr1 fr1 sm1 rv1 fs1]. cbn [ss_pc ss_resv ss_regs] in Hpc0, Hresv0, Hr2, Hr8, Hr9, Hr3, Hr4, Hr18, Hr22.
  subst pc1 rv1.
  unfold abs_ss, setpc in Hpcv, Hresv, Hregs.
  cbn [ss_pc ss_regs ss_resv resv_denot restrict
       ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs]
    in Hfr, Hpcv, Hpend, Hresv, Hfcsr, Hrom, Hregs.
  unfold lx_body.
  split; [rewrite Hpcv; reflexivity|].
  split; [exact Hresv|]. split; [exact Hpend|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfcsr|].
  split.
  { unfold lregs.
    split; [rewrite (Hregs (2%bv : bv 5)), Hr2, lx_sv_SOff0, H2E; reflexivity|].
    split; [rewrite (Hregs (8%bv : bv 5)), Hr8, lx_sv_SOff0, H8E; reflexivity|].
    split; [rewrite (Hregs (9%bv : bv 5)), Hr9, lx_sv_SOff0, H2E; reflexivity|].
    split; [rewrite (Hregs (3%bv : bv 5)), Hr3, lx_sv_SOff0; exact H3E|].
    split; [rewrite (Hregs (4%bv : bv 5)), Hr4, lx_sv_SOff0; exact H4E|].
    split; [rewrite (Hregs (18%bv : bv 5)), Hr18, lx_sv_SOff0, H32E; reflexivity|].
    rewrite (Hregs (22%bv : bv 5)), Hr22, lx_sv_SOff0, H22E; reflexivity. }
  split; [exact Hsv|]. split; [exact Hsh|]. split; [exact Hfl|].
  split; [exact H10|]. split; [exact H18|]. split; [exact H80 | exact Hgarr].
Qed.

(* ---- a call that leaves this phase's own memory alone ---- *)
(* The journal of a call made from the realigned stack pointer that takes no frame of its own and leaves the blocks
   as it found them keeps every byte this phase's facts speak about outside the call's footprint FP1. *)
Lemma lx_keep_call_fp : forall rs FP1 STK1 memc mdc mem2 md2 k1,
  alloc_ceiling <= lsp1 cx ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun r => exists n, In (fst r, n) (ablocks B ly3 S3) /\ 0 <= snd r <= req_size n) rs ->
  (forall a, lx_keep_at rs a -> ~ inFP FP1 a) ->
  ajournal SEGS B STK1 (lsp1 cx) FP1 ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  lx_keep rs memc mem2.
Proof.
  intros rs FP1 STK1 memc mdc mem2 md2 k1 Hceil Hbl Hrs Hfp HJ1 a Ha.
  pose proof (Hfp a Ha) as Hna.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct HB as (_ & _ & _ & Hpn & _).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hsa : shadow_addr (lF cx fp) = lSH cx fp) by reflexivity.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
    pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq].
    replace a with (lc_p cx + (a - lc_p cx)) in Hna |- * by lia.
    apply (F2 (lc_p cx) (lc_n cx) (a - lc_p cx) (Hbl _ _ Hin) (Hbl _ _ Hin)); [lia | exact Hna].
  - apply (F4 LX_CID fp a lx_fin); [|exact Hna].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite lx_frame_addr_eq. rewrite Hfb in Ha. lia.
  - apply (F4 LX_CID fp a lx_fin); [|exact Hna].
    right. unfold in_zr. cbn [fst snd]. rewrite lx_frame_addr_eq, Hsa. exact Ha.
  - apply Exists_exists in Ha as (r & Hr & Hb).
    rewrite Forall_forall in Hrs. destruct (Hrs r Hr) as (n & Hin & Hn).
    replace a with (fst r + (a - fst r)) in Hna |- * by lia.
    apply (F2 (fst r) n (a - fst r) Hin Hin); [lia | exact Hna].
Qed.

Lemma lx_keep_call : forall rs STK1 memc mdc mem2 md2 k1,
  alloc_ceiling <= lsp1 cx ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun r => exists n, In (fst r, n) (ablocks B ly3 S3) /\ 0 <= snd r <= req_size n) rs ->
  ajournal SEGS B STK1 (lsp1 cx) [] ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  lx_keep rs memc mem2.
Proof.
  intros rs STK1 memc mdc mem2 md2 k1 Hceil Hbl Hrs HJ1.
  exact (lx_keep_call_fp rs [] STK1 memc mdc mem2 md2 k1 Hceil Hbl Hrs (fun a _ => inFP_nil a) HJ1).
Qed.

(* ---- a phase's facts across such a call ---- *)
Lemma lx_map_length : forall (f : byte -> Z) (xs : list byte), length (map f xs) = length xs.
Proof. intros f xs. apply length_map. Qed.

Lemma lx_saved_keep : forall rs (ms ms' : machine_state),
  lx_keep rs (ms_mem ms) (ms_mem ms') -> lsaved cx W3 ms -> lsaved cx W3 ms'.
Proof.
  intros rs ms ms' Hk (Hra & Hsj).
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & _).
  split.
  - apply (lx_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact Hra].
  - intros j Hj. apply (lx_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk);
      [intros i Hi; left; lia | exact (Hsj j Hj)].
Qed.

Lemma lx_shadow_keep : forall rs (ms ms' : machine_state) sh,
  lx_keep rs (ms_mem ms) (ms_mem ms') ->
  Z.of_nat (length sh) <= fs_frame_bytes LX_CID / 8 ->
  lshadow cx fp W3 ms sh -> lshadow cx fp W3 ms' sh.
Proof.
  intros rs ms ms' sh Hk Hlen Hs i Hi. unfold lshadow, lview in *.
  rewrite (Hk (lSH cx fp + Z.of_nat i)); [exact (Hs i Hi)|].
  right; right; right; left. lia.
Qed.

Lemma lx_slot_keep : forall rs (ms ms' : machine_state) off v,
  lx_keep rs (ms_mem ms) (ms_mem ms') -> 0 <= off -> off <= 0x90 ->
  lslot cx W3 ms off v -> lslot cx W3 ms' off v.
Proof.
  intros rs ms ms' off v Hk H0 H1 Hv.
  pose proof lx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & _).
  apply (lx_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact Hv].
Qed.

Lemma lx_flag_keep : forall rs (ms ms' : machine_state),
  lx_keep rs (ms_mem ms) (ms_mem ms') ->
  rdword (lview W3 ms) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) ->
  rdword (lview W3 ms') (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp).
Proof.
  intros rs ms ms' Hk Hv.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  apply (lx_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk);
    [intros i Hi; right; right; left; rewrite Hfb; lia | exact Hv].
Qed.

Lemma lx_input_keep : forall rs (ms ms' : machine_state),
  lx_keep rs (ms_mem ms) (ms_mem ms') ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)).
Proof.
  intros rs ms ms' Hk Hg.
  apply (lx_garr8_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [|exact Hg].
  intros i Hi. rewrite lx_map_length in Hi. right; left. unfold lc_n. lia.
Qed.

Lemma lx_reg_keep : forall rs (ms ms' : machine_state) r bs,
  lx_keep rs (ms_mem ms) (ms_mem ms') -> In (r, LX_REG) rs ->
  lreg W3 ms r bs -> lreg W3 ms' r bs.
Proof.
  intros rs ms ms' r bs Hk Hin Hr i Hi. unfold lreg, lview in *.
  rewrite (Hk (r + i)); [exact (Hr i Hi)|].
  right; right; right; right. apply Exists_exists. exists (r, LX_REG).
  split; [exact Hin | cbn [fst snd]; lia].
Qed.

Lemma lx_prev_keep : forall rs (ms ms' : machine_state) bs,
  lx_keep rs (ms_mem ms) (ms_mem ms') ->
  lprev cx fp W3 ms bs -> lprev cx fp W3 ms' bs.
Proof.
  intros rs ms ms' bs Hk Hp i Hi. unfold lprev, lview in *.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  rewrite (Hk (lF cx fp + 64 + i)); [exact (Hp i Hi)|].
  right; right; left. rewrite Hfb. unfold LX_REG in Hi. lia.
Qed.

Lemma lx_cur_keep : forall rs (ms ms' : machine_state) pos,
  lx_keep rs (ms_mem ms) (ms_mem ms') ->
  lcur cx W3 ms pos -> lcur cx W3 ms' pos.
Proof.
  intros rs ms ms' pos Hk (Hp & H88 & H90).
  split; [exact Hp|]. split; [apply (lx_slot_keep rs ms ms' 0x88 _ Hk); [lia | lia | exact H88]|].
  apply (lx_slot_keep rs ms ms' 0x90 _ Hk); [lia | lia | exact H90].
Qed.

Lemma lx_slots_loop_keep : forall rs (ms ms' : machine_state) r fab,
  lx_keep rs (ms_mem ms) (ms_mem ms') ->
  lslots_loop cx fp W3 ms r fab -> lslots_loop cx fp W3 ms' r fab.
Proof.
  intros rs ms ms' r fab Hk (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  split; [apply (lx_slot_keep rs ms ms' 0x08 _ Hk); [lia | lia | exact S08]|].
  split; [apply (lx_slot_keep rs ms ms' 0x28 _ Hk); [lia | lia | exact S28]|].
  split; [apply (lx_slot_keep rs ms ms' 0x30 _ Hk); [lia | lia | exact S30]|].
  split; [apply (lx_slot_keep rs ms ms' 0x38 _ Hk); [lia | lia | exact S38]|].
  split; [apply (lx_slot_keep rs ms ms' 0x40 _ Hk); [lia | lia | exact S40]|].
  split; [apply (lx_slot_keep rs ms ms' 0x68 _ Hk); [lia | lia | exact S68]|].
  split; [apply (lx_slot_keep rs ms ms' 0x70 _ Hk); [lia | lia | exact S70]|].
  apply (lx_slot_keep rs ms ms' 0x78 _ Hk); [lia | lia | exact S78].
Qed.

(* ---- the shadow entries a token walk needs ---- *)
(* A heap block: its bytes are addressable (rbi_shent of BoxBReacBoxregInit.v, for any atom). *)
Lemma lx_shent_block : forall lyb Sb (Wb : world SEGS) memb mdb Ex (q b sz lo hi : Z) (n : nat),
  AR SEGS B lyb Sb Wb memb mdb -> In (b, sz) (ablocks B lyb Sb) ->
  U Ex (SOff LA_SB 0) = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS (SOff LA_SB 0) Ex (mrestrict (w_H Wb) memb) (mkSHE n lo hi).
Proof.
  intros lyb Sb Wb memb mdb Ex q b sz lo hi n HAR Hin HBx Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyb Sb Wb memb mdb b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS lyb Sb Wb memb mdb b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

(* A write window in application memory: the reversed entry (lo > hi) has no bytes to check, and its window is
   apart from the shadow. *)
Lemma lx_shent_rev : forall Ex m (q len : Z) (n : nat),
  U Ex (SOff LA_SB 0) = SHADOW_OFF -> U Ex (SOff n 0) = q -> in_app q len -> 0 <= len ->
  shent_ok SEGS (SOff LA_SB 0) Ex m (mkSHE n len 0).
Proof.
  intros Ex m q len n HBx Hq Hia Hl.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, Hq. split.
  - intros x Hx. lia.
  - intros a Ha. rewrite Z.min_r in Ha by lia. rewrite Z.max_l in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hia Hl C1 C3 C5. clear. intros. lia.
Qed.

Lemma lx_LSH_iter_mac : nth 4 LSH_iter 0 = 6.
Proof. reflexivity. Qed.

Lemma lx_LSH_iter_prev : forall i, (8 <= i < 44)%nat -> nth i LSH_iter 0 = 0.
Proof.
  intros i Hi. unfold LSH_iter.
  rewrite app_nth2 by (cbn [length]; lia). cbn [length].
  rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.

(* mac (F + 32 .. F + 37) and prev (F + 64 .. F + 351) while a loop turn has them in scope (LSH_iter). *)
Lemma lx_shent_frame : forall Ex lo hi,
  U Ex (SOff LA_SB 0) = SHADOW_OFF -> U Ex (SOff LA_F 0) = lF cx fp ->
  lshadow cx fp W3 ms3 LSH_iter ->
  ((lo = 32 /\ 32 <= hi <= 38) \/ (64 <= lo /\ lo <= hi <= 352)) ->
  shent_ok SEGS (SOff LA_SB 0) Ex M3 (mkSHE LA_F lo hi).
Proof.
  intros Ex lo hi HBx HF Hsh Hlh.
  pose proof lx_F_facts as (HF0 & HFc & HFia & _ & Hal64 & HSHeq).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (Hal8 : lF cx fp mod 8 = 0).
  { pose proof (Z.div_mod (lF cx fp) 64 ltac:(lia)) as D. rewrite Hal64, Z.add_0_r in D.
    rewrite D. replace (64 * (lF cx fp / 64)) with ((8 * (lF cx fp / 64)) * 8) by lia.
    apply Z_mod_mult. }
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, HF.
  rewrite <- (aview_rd_of SEGS). split.
  - intros x Hx.
    assert (Hs : shadow_of_addr SHADOW_OFF x = lSH cx fp + (x - lF cx fp) / 8).
    { unfold shadow_of_addr. rewrite HSHeq.
      replace x with (lF cx fp + (x - lF cx fp)) at 1 by lia.
      pose proof (shadow_of_addr_aligned_off 0 (lF cx fp) (x - lF cx fp) Hal8) as Ho.
      unfold shadow_of_addr in Ho. lia. }
    assert (Hm8 : x mod 8 = (x - lF cx fp) mod 8).
    { replace x with ((x - lF cx fp) + lF cx fp) at 1 by lia.
      rewrite Z.add_mod, Hal8, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
    set (i := (x - lF cx fp) / 8) in *.
    assert (Hi0 : 0 <= i < 64) by (subst i; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    pose proof (Hsh (Z.to_nat i)) as Hb. unfold lview in Hb.
    rewrite Z2Nat.id in Hb by lia. rewrite Hs.
    destruct Hlh as [(-> & Hh) | (Hl & Hh)].
    + assert (Hi4 : i = 4) by (subst i; symmetry; apply Z.div_unique with (r := x - lF cx fp - 32); lia).
      rewrite Hi4 in Hb |- *. specialize (Hb ltac:(cbv; lia)). change (Z.to_nat 4) with 4%nat in Hb.
      rewrite lx_LSH_iter_mac in Hb. exists 6. split; [exact Hb|].
      right. split; [|lia]. rewrite Hm8.
      assert (Hr : (x - lF cx fp) mod 8 = x - lF cx fp - 32) by (symmetry; apply Z.mod_unique with (q := 4); lia). lia.
    + assert (Hi8 : 8 <= i < 44) by (subst i; split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
      specialize (Hb ltac:(cbv [LSH_iter length repeat app]; lia)).
      rewrite lx_LSH_iter_prev in Hb by lia. exists 0. split; [exact Hb | left; reflexivity].
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert HFia HF0 HFc Hlh C1 C3 C5. clear. intros. lia.
Qed.

End e.

End d.

End c.
End b.
End a.
