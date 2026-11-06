(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 274 of its 316 lines of code are new or changed and 1882 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcRel.v; 582 of its 621 lines of code are new or changed and 277 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcScan.v, with its module names and numbers changed; 783 of its 938 lines of code are new or changed and 466 lines of the source are left out. *)
(* io_send_seg_loop: the command count loop of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v), from 0x831a8 = transport_text +
   IOS_LOOP to its exit 0x8329c = transport_text + IOS_CMDS (fuzz_transport.c:858-862, tagged_of :609-615 inlined;
   the model is lib/TModel/TCb.v cmds_loop and tagged_of_m). The lemma is stated on its own premises (a Section
   with Variables and Hypotheses, as decode's DgnBcScan.v), so that the DATA segment can apply it.

   The code (listing offsets from io_send's entry; registers a1 = cmds, a3 = at, s2 = body_len, s4 = the shadow
   base):
     +0x448 .. +0x464  a3 = 0, a4 = f.body (the 8-byte load at sp + 56), a5 = 3, a6 = 160 (TAG), a7 = the upper part
                       of g_ncmd's address (IOS_NCMD_HI = TA_g_ncmd - 1992), t0 = 40, t1 = g_cmd (TA_g_cmd); a1 = 0
                       was set at +0x440, before the cut;
     +0x468 .. +0x46c  the head of a round: t2 = body_len - at, `bltu t2,a5` to +0x4ec (step = t2);
     +0x470 .. +0x4c8  a0 = body + at; the checked loads of body[at] (`bne a2,a6` to +0x4ec), body[at + 1] and
                       body[at + 2]; serial = body[at + 2] << 7 | body[at + 1]; t3 = the 4-byte load of g_ncmd (lw at
                       a7 + 1992); `bgeu a0,t3` to +0x4ec;
     +0x4cc .. +0x4e8  a0 = t1 + 40 * serial + 36, the checked load of g_cmd[serial].len into t2;
     +0x4ec .. +0x4f8  a3 = a3 + t2, a1 = a1 + 1 (addiw), `bltu a3,s2` back to +0x468, else `j` +0x53c;
     +0x4fc .. +0x528  the slow paths of the four instrumented checks and their error calls (0x834b0, 0x834b8,
                       0x834c0 and 0x83288).
   How it is proved. Each stretch is a run of the PA engine with its token shadow checks (PaShadow.v) from a fresh
   symbolic state whose regions are read-only, so the run leaves the memory as it was (lp_run, DgnBcScan.v's
   bcs_run) and changes only the model's materialized part (the caller's J keeps it):
     lp_pre         +0x448: the slot sp + 56 as a region at sp (atom 32 = body); to +0x468;
     ios_loop_turn  +0x468: one round's head, split on `bltu t2,a5`; to +0x4ec (step = body_len - at) or +0x474;
     lp_body        +0x474: the three body bytes as a region at a0 = body + at (atoms 32 .. 34), g_ncmd's 4 bytes as
                    a region at a7 (atom 35), the shadow entry [a0, a0 + 3) (range_addressable of the body, a
                    premise), so the engine decides the three checks; split on `bne` and on `bgeu`; to +0x4ec or
                    +0x4d8;
     lp_len         +0x4d8: g_cmd[serial].len as a region at a0 (atom 32), the shadow entry [a0, a0 + 1) inside
                    g_cmd's payload (range_addressable of [TA_g_cmd, TA_g_cmd + 40960), a premise); to +0x4ec;
     lp_bump        +0x4ec: split on `bltu a3,s2`; to +0x468 or +0x53c.
   No error path is reached: every instrumented check is decided by its shadow entry. The model's None cases are the
   branches the machine cannot take: tagged_of_m's serial >= CMDS_MAX below g_ncmd (lp_cl_none) and a step of 0
   (lp_cl_step). The rounds are an induction on the model's fuel (ios_loop_rounds): each round passes from
   cmds_loop (S fuel) to cmds_loop fuel. The theorem of the file is ios_loop, at the end. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The points of the loop and its symbolic states                      *)
(* ------------------------------------------------------------------ *)

(* The head of a round, the body loads after a0 = body + at, g_cmd[serial].len's address in a0, the step. *)
Definition IOS_TURN : Z := IOS_AT 0x468.
Definition IOS_TAGB : Z := IOS_AT 0x474.
Definition IOS_LEN : Z := IOS_AT 0x4d8.
Definition IOS_STEP : Z := IOS_AT 0x4ec.
(* a7 after `PHi a7 56`: g_ncmd is at a7 + 1992. *)
Definition IOS_NCMD_HI : Z := TA_g_ncmd - 1992.

(* The registers the loop does not write (ra, sp, gp, tp, s0 .. s11, t5, t6); the ones it carries from round to
   round (t0 = 40, t1 = g_cmd, a1 = cmds, a3 = at, a4 = body, a5 = 3, a6 = 160, a7 = IOS_NCMD_HI); and those of
   them a round does not change (all but a1 and a3). *)
Definition IOS_LP_KP : list (bv 5) :=
  [1%bv; 2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv;
   30%bv; 31%bv].
Definition IOS_LP_LR : list (bv 5) := [5%bv; 6%bv; 11%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv].
Definition IOS_LP_LK : list (bv 5) := [5%bv; 6%bv; 14%bv; 15%bv; 16%bv; 17%bv].

Ltac lp_kin := unfold IOS_LP_KP, IOS_LP_LR, IOS_LP_LK; cbn [In]; repeat (first [left; reflexivity | right]).

(* s4 holds the shadow base; the shadow span of the token engine; the bound of a pointer register. *)
Definition lp_Bx : sv := SOff 20 0.
Definition lp_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition lp_PTRHI : Z := 2 ^ 47 - 4.
Definition lp_PTR : afact := mkAF 0 lp_PTRHI 0.

(* +0x448: the slot sp + 56 (f.body) as atom 32. *)
Definition lpp_rg : YP09.region := YP09.mkRegion (Some 2%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition lpp_ss : sstate := mkSS IOS_LOOP sr_atoms [lpp_rg] None (mkFacts [] [] []).
(* +0x468 and +0x4ec: no region. *)
Definition lph_ss : sstate := mkSS IOS_TURN sr_atoms [] None (mkFacts [] [] []).
Definition lps_ss : sstate := mkSS IOS_STEP sr_atoms [] None (mkFacts [] [] []).
(* +0x474: body[at], body[at + 1], body[at + 2] at a0 (atoms 32, 33, 34), g_ncmd at a7 + 1992 (atom 35). *)
Definition lpb_rg : YP09.region := YP09.mkRegion (Some 10%nat) 0 3 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition lpn_rg : YP09.region := YP09.mkRegion (Some 17%nat) 1992 1996 0 0 [YP09.mkChunk 1992 (CVal 4 (SOff 35 0))].
Definition lpb_G : facts := mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, lp_PTR);
  (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 4294967295 0)] [] [].
Definition lpb_ss : sstate := mkSS IOS_TAGB sr_atoms [lpb_rg; lpn_rg] None lpb_G.
Definition lpb_SH : list shent := [mkSHE 10 0 3].
(* +0x4d8: g_cmd[serial].len at a0 (atom 32). *)
Definition lpc_rg : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition lpc_G : facts := mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, lp_PTR);
  (32%nat, mkAF 0 255 0)] [] [].
Definition lpc_ss : sstate := mkSS IOS_LEN sr_atoms [lpc_rg] None lpc_G.
Definition lpc_SH : list shent := [mkSHE 10 0 1].

(* ------------------------------------------------------------------ *)
(* The model: tagged_of_m and one round of cmds_loop                   *)
(* ------------------------------------------------------------------ *)

Lemma lp_nth_skipn : forall {A : Type} (l : list A) (n k : nat) (d : A), nth k (skipn n l) d = nth (n + k) l d.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l k d; [reflexivity|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma lp_len_skipn : forall {A : Type} (l : list A) (n : nat), length (skipn n l) = (length l - n)%nat.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l; [cbn [skipn]; symmetry; apply Nat.sub_0_r|].
  destruct l as [|x l]; [reflexivity|]. cbn [skipn length]. apply IH.
Qed.

Lemma lp_at8_skipn : forall (l : list byte) (n k : nat), DSpec.at8 (skipn n l) k = DSpec.at8 l (n + k).
Proof. intros l n k. unfold DSpec.at8. rewrite lp_nth_skipn. reflexivity. Qed.

Lemma lp_tof_short : forall B b n, n < 3 -> TC.tagged_of_m B b n = Some (B, None).
Proof. intros B b n H. unfold TC.tagged_of_m. replace (n <? 3) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma lp_tof_notag : forall B b n, 3 <= n -> (1 <= length b)%nat -> DSpec.at8 b 0 <> TC.TAG ->
  TC.tagged_of_m B b n = Some (B, None).
Proof.
  intros B b n H L T. unfold TC.tagged_of_m.
  replace (n <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (length b <? 1)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (DSpec.at8 b 0 =? TC.TAG) with false by (symmetry; apply Z.eqb_neq; exact T).
  reflexivity.
Qed.

Lemma lp_tof_tag : forall B b n, 3 <= n -> (3 <= length b)%nat -> DSpec.at8 b 0 = TC.TAG ->
  TC.tagged_of_m B b n =
    (if Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) <? TW.g_ncmd B then
       (if TC.CMDS_MAX <=? Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) then None
        else Some (B, Some (Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7))))
     else Some (B, None)).
Proof.
  intros B b n H L T. unfold TC.tagged_of_m.
  replace (n <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (length b <? 1)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (DSpec.at8 b 0 =? TC.TAG) with true by (symmetry; apply Z.eqb_eq; exact T).
  replace (length b <? 3)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Lemma lp_tof_big : forall B b n, 3 <= n -> (3 <= length b)%nat -> DSpec.at8 b 0 = TC.TAG ->
  Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) < TW.g_ncmd B ->
  TC.CMDS_MAX <= Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) -> TC.tagged_of_m B b n = None.
Proof.
  intros B b n H L T H1 H2. rewrite (lp_tof_tag B b n H L T).
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma lp_tof_in : forall B b n, 3 <= n -> (3 <= length b)%nat -> DSpec.at8 b 0 = TC.TAG ->
  Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) < TW.g_ncmd B ->
  Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) < TC.CMDS_MAX ->
  TC.tagged_of_m B b n = Some (B, Some (Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7))).
Proof.
  intros B b n H L T H1 H2. rewrite (lp_tof_tag B b n H L T).
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_gt _ _) H2). reflexivity.
Qed.

Lemma lp_tof_out : forall B b n, 3 <= n -> (3 <= length b)%nat -> DSpec.at8 b 0 = TC.TAG ->
  TW.g_ncmd B <= Z.lor (DSpec.at8 b 1) (Z.shiftl (DSpec.at8 b 2) 7) -> TC.tagged_of_m B b n = Some (B, None).
Proof.
  intros B b n H L T H1. rewrite (lp_tof_tag B b n H L T).
  rewrite (proj2 (Z.ltb_ge _ _) H1). reflexivity.
Qed.

(* One round at pos < blen, given what tagged_of_m answers there. *)
Lemma lp_cl_step : forall fuel B body blen pos cmds r t, pos < blen ->
  TC.tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos) = Some (B, t) ->
  TC.cmds_loop (S fuel) B body blen pos cmds = Some r ->
  (match t with Some s => TW.Cmd_len B s | None => blen - pos end) <> 0 /\
  TC.cmds_loop fuel B body blen (pos + match t with Some s => TW.Cmd_len B s | None => blen - pos end)
    (DSpec.u32 (cmds + 1)) = Some r.
Proof.
  intros fuel B body blen pos cmds r t Hp Ht H. cbn [TC.cmds_loop] in H.
  rewrite (proj2 (Z.ltb_lt pos blen) Hp), Ht in H. cbv beta iota zeta in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Z0 end; [discriminate H|].
  split; [apply Z.eqb_neq; exact Z0 | exact H].
Qed.

Lemma lp_cl_none : forall fuel B body blen pos cmds r, pos < blen ->
  TC.tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos) = None ->
  TC.cmds_loop (S fuel) B body blen pos cmds = Some r -> False.
Proof.
  intros fuel B body blen pos cmds r Hp Ht H. cbn [TC.cmds_loop] in H.
  rewrite (proj2 (Z.ltb_lt pos blen) Hp), Ht in H. discriminate H.
Qed.

Lemma lp_cl_end : forall fuel B body blen pos cmds r, blen <= pos ->
  TC.cmds_loop fuel B body blen pos cmds = Some r -> r = cmds.
Proof.
  intros fuel B body blen pos cmds r Hp H. destruct fuel as [|fuel]; cbn [TC.cmds_loop] in H; [discriminate H|].
  rewrite (proj2 (Z.ltb_ge pos blen) Hp) in H. injection H as <-. reflexivity.
Qed.

(* The world accessors the loop reads, at their numeral offsets in g_ncmd's and g_cmd's rows. *)
Lemma lp_ncmd_at : forall B, TW.g_ncmd B = TW.u_at B (TW.OFF_g_ncmd + 0) 4.
Proof. intros B. unfold TW.g_ncmd. rewrite Z.add_0_r. reflexivity. Qed.

Lemma lp_clen_at : forall B s, TW.Cmd_len B s = TW.u_at B (TW.OFF_g_cmd + (40 * s + 36)) 1.
Proof. intros B s. unfold TW.Cmd_len, TW.A_Cmd_len. f_equal. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Values of the symbolic expressions the runs leave                    *)
(* ------------------------------------------------------------------ *)

Lemma lp_den0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, Z.add_0_r, unsigned_lit_small by lia. reflexivity. Qed.

Lemma lp_U_add : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y ->
  x + y < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = x + y.
Proof.
  intros E a b x y Ha Hb Hx Hy Hxy. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* t2 = s2 - a3, as the engine writes it: a3 * -1 + s2. *)
Lemma lp_U_sub : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x <= y -> y < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SOff b 0)) = y - x.
Proof.
  intros E a b x y Ha Hb Hxy Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia. rewrite U_SLit.
  change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon, M64.
  rewrite Zplus_mod_idemp_l. replace (x * (2 ^ 64 - 1) + y) with ((y - x) + x * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma lp_swrap_mod : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma lp_mod64_32 : forall a, a mod 2 ^ 64 mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
  intros a. rewrite (Z.mod_eq a (2 ^ 64)) by lia. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
  replace (a - 2 ^ 32 * 2 ^ 32 * (a / (2 ^ 32 * 2 ^ 32))) with (a + (- (2 ^ 32 * (a / (2 ^ 32 * 2 ^ 32)))) * 2 ^ 32)
    by ring.
  apply Z_mod_plus_full.
Qed.

(* a1 = a1 + 1, 32-bit and sign-extended (addiw), on a1 = cmds sign-extended. *)
Lemma lp_den_addw : forall E c, ew E 11 = Z_to_bv 64 (bv_swrap 32 c) ->
  sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit 1)) = Z_to_bv 64 (bv_swrap 32 (DSpec.u32 (c + 1))).
Proof.
  intros E c H.
  assert (X : U E (SOff 11 0) mod 2 ^ 32 = c mod 2 ^ 32).
  { rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Zmod_mod, lp_mod64_32. apply lp_swrap_mod. }
  rewrite (denot_lit_U E). apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
  rewrite U_SLit. change (zcanon 1 mod 2 ^ 32) with 1.
  unfold bv_wrap. rewrite Zmod_mod. f_equal.
  apply bv_swrap_congr. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite X, Zplus_mod_idemp_l. unfold DSpec.u32. rewrite Zmod_mod. reflexivity.
Qed.

(* serial = b2 << 7 | b1. *)
Lemma lp_U_serial : forall E b1 b2, ew E 33 = Z_to_bv 64 b1 -> ew E 34 = Z_to_bv 64 b2 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 7)) (SOff 33 0)) = Z.lor b1 (Z.shiftl b2 7) /\
  0 <= Z.lor b1 (Z.shiftl b2 7) < 2 ^ 15.
Proof.
  intros E b1 b2 H1 H2 R1 R2.
  assert (S2 : Z.shiftl b2 7 = b2 * 2 ^ 7) by (apply Z.shiftl_mul_pow2; lia).
  assert (RB : 0 <= Z.lor b1 (Z.shiftl b2 7) < 2 ^ 15)
    by (apply fp_Z_lor_range; [lia | lia | rewrite S2; lia]).
  split; [|exact RB].
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 33 b1 H1) by lia. rewrite (U_atom E 34 b2 H2) by lia. rewrite U_SLit.
  change (Z.land (zcanon 7) 63) with 7.
  rewrite (zcanon_id (Z.shiftl b2 7)) by (unfold M64; rewrite S2; lia).
  rewrite Z.lor_comm. apply zcanon_id. unfold M64. lia.
Qed.

(* The 4-byte signed load of g_ncmd, compared (unsigned) with a serial below 2 ^ 31. *)
Lemma lp_ltu_ncmd : forall E n s, ew E 35 = Z_to_bv 64 n -> 0 <= n < 2 ^ 32 -> 0 <= s < 2 ^ 31 ->
  (s <? U E (SExt true 32 (SOff 35 0))) = (s <? n).
Proof.
  intros E n s Hn Rn Rs. rewrite U_SExt. rewrite (U_atom E 35 n Hn) by lia.
  change (Z.of_N 32) with 32. rewrite (Z.mod_small n (2 ^ 32)) by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  unfold zcanon, M64.
  destruct (Z.ltb_spec n (2 ^ 31)) as [Hl|Hl].
  - rewrite (Z.mod_small (n + 2 ^ 31) (2 ^ 32)) by lia.
    replace (n + 2 ^ 31 - 2 ^ 31) with n by ring. rewrite Z.mod_small by lia. reflexivity.
  - replace ((n + 2 ^ 31) mod 2 ^ 32) with (n + 2 ^ 31 - 2 ^ 32).
    + replace ((n + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (n - 2 ^ 32 + 2 ^ 64).
      * destruct (Z.ltb_spec s (n - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec s n); first [reflexivity | lia].
      * replace (n + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((n - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
        rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
    + symmetry. assert (E1 : n + 2 ^ 31 = (n + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by ring.
      rewrite E1 at 1. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* a0 = t1 + serial * t0 + 36 = &g_cmd[serial].len. *)
Lemma lp_U_lenaddr : forall E b1 b2 g, ew E 33 = Z_to_bv 64 b1 -> ew E 34 = Z_to_bv 64 b2 ->
  ew E 6 = Z_to_bv 64 g -> ew E 5 = Z_to_bv 64 40 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= g < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 6 0)
        (SMd M_MUL (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 7)) (SOff 33 0)) (SOff 5 0))) (SLit 36))
    = g + 40 * Z.lor b1 (Z.shiftl b2 7) + 36.
Proof.
  intros E b1 b2 g H1 H2 H6 H5 R1 R2 Rg.
  destruct (lp_U_serial E b1 b2 H1 H2 R1 R2) as [US RS].
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
  rewrite US. rewrite (U_atom E 5 40 H5) by lia. rewrite (U_atom E 6 g H6) by lia. rewrite U_SLit.
  change (zcanon 36) with 36.
  rewrite (zcanon_id (Z.lor b1 (Z.shiftl b2 7) * 40)) by (unfold M64; lia).
  rewrite (zcanon_id (g + Z.lor b1 (Z.shiftl b2 7) * 40)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). ring.
Qed.

(* ------------------------------------------------------------------ *)
(* One run of the engine over read-only regions                        *)
(* ------------------------------------------------------------------ *)

Section run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).

(* The run writes no memory (its regions are read-only), so the memory after it is the memory before; the model
   after it is the model before with its materialized part replaced (DgnBcScan.v bcs_run). *)
Lemma lp_run : forall (Bx : sv) (Bspan : Z * Z) (SH : list shent) (W : world segs) (E : env) (ss : sstate)
    (ms : machine_state) (md : Model) (K : nat) (stop : Z) (st' : shst) (r : ptrun_status tsym)
    (Q : world segs -> config -> Prop),
  (A_LIM <= K)%nat ->
  img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok transport_tpi transport_tw K Bx Bspan SH FUEL stop ss = (st', r) ->
  match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  rs_read_only (ss_mem ss) = true ->
  (forall ws ms' mat,
     length ws = sh_j st' ->
     img_env VAL A_LIM (extK E K ws) ->
     st_ok_pi segs VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
     sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
  intros Bx Bspan SH W E ss ms md K stop st' r Q HK HE HS HSH Hchk Hrun Hnc Hobl Hro HKQ.
  assert (Hrun' : sym_run_toN_pi_tok (ptree_of_list transport_listing) (tw_of 0 transport_listing)
                    K Bx Bspan SH FUEL stop ss = (st', r))
    by (rewrite (@pl_tw_eq transport_listing PL_transport); exact Hrun).
  destruct (sym_run_to_pi_tok_sound tsym _ _ VAL _ transport_listing
     (pa_fetch_ok (PI := PI_transport)) (@pa_cert _ transport_listing PI_transport)
     (@pa_B_ok _ transport_listing PI_transport)
     A_LIM A_LIM_text (@pl_lim transport_listing PL_transport) (@pl_len transport_listing PL_transport)
     K Bx Bspan SH HK FUEL stop E ss (restrict (w_H W) ms) st' r HE HS HSH Hchk Hrun' Hobl)
   as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs (@pa_wx _ transport_listing PI_transport) W ms msr' md Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  assert (Hmem : ms_mem (unrestrict (w_H W) (ms_mem ms) msr') = ms_mem ms).
  { eapply frame_of_read_only; [exact Hro|].
    cbn [unrestrict ms_mem]. apply frame_of_unrestrict.
    cbn [restrict ms_mem] in Hfr. exact Hfr. }
  apply (HKQ ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r as [ | | s | why]; cbn [ptok_post] in HP;
    [exact HP | destruct HP | destruct Hnc | exact HP].
  - rewrite Hmm. exact Hsh'.
  - exact Hmem.
Qed.

Lemma lp_agree_extK : forall E0 E K ws, (1024 <= K)%nat -> env_agree 1024 E0 E -> env_agree 1024 E0 (extK E K ws).
Proof.
  intros E0 E K ws HK [H1 H2]. destruct (env_agree_extK E K ws) as [A1 A2].
  split; [intros n Hn; rewrite (A1 n ltac:(lia)); exact (H1 n Hn) | rewrite A2; exact H2].
Qed.

Lemma lp_ewa : forall E0 E n v, env_agree 1024 E0 E -> (n < 1024)%nat -> ew E0 n = v -> ew E n = v.
Proof. intros E0 E n v [H _] Hn Hv. rewrite (H n Hn). exact Hv. Qed.

Lemma lp_ew_reg : forall (r : bvmap 5 word) extra n (x : bv 5), Z.of_nat n = bv_unsigned x ->
  ew (Eimg (PI := PI_transport) (Ereg r extra)) n = YK11.getr r x.
Proof. intros r extra n x Hx. apply ew_Eimg_Ereg_nat. exact Hx. Qed.

Lemma lp_ew_ex : forall (r : bvmap 5 word) extra j, (32 + j < 240)%nat ->
  ew (Eimg (PI := PI_transport) (Ereg r extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros r extra j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma lp_agree32 : forall (r : bvmap 5 word) extra E,
  env_agree 1024 (Eimg (PI := PI_transport) (Ereg r extra)) E -> env_agree 32 (Ereg r extra) E.
Proof.
  intros r extra E [H1 H2]. split.
  - intros n Hn. rewrite (H1 n ltac:(lia)). apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

Lemma lp_chunk1 : forall (E : env) (m : word -> option byte) (k : nat) (b o a v : Z),
  ew E k = Z_to_bv 64 v -> 0 <= v < 256 -> b + o = a -> val_mem segs m a 1 v ->
  YP09.chunk_ok segs E m b (YP09.mkChunk o (CVal 1 (SOff k 0))).
Proof.
  intros E m k b o a v Hk Hv Ha Hm.
  apply (chunk_ok_val segs E m b o 1 (SOff k 0) v).
  - cbn [sv_denot]. rewrite Hk, Z.add_0_r. rewrite unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - rewrite Ha. exact Hm.
Qed.

Lemma lp_vals : @pa_val _ transport_listing PI_transport (A_HI 56) = IOS_NCMD_HI /\
  @pa_val _ transport_listing PI_transport (A_OBJ 18) = TA_g_cmd /\
  @pa_val _ transport_listing PI_transport A_TEXT = transport_text.
Proof. vm_compute. repeat split. Qed.

End run.

(* One run to the pc stop, or to the next branch the engine cannot decide. *)
Ltac lp_step SH stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM lp_Bx SH ss) in
    let rr := eval vm_compute in (sym_run_toN_pi_tok transport_tpi transport_tw K lp_Bx lp_Bspan SH FUEL stop ss) in
    lazymatch rr with
    | (?st', ?res) =>
      lazymatch goal with
      | HSH : sh_ok _ _ _ E _, HEI : img_env _ _ E, HAG : env_agree 1024 ?E0 E |- _ =>
        apply (lp_run lp_Bx lp_Bspan SH W E ss ms md K stop st' res Q ltac:(unfold A_LIM; lia) HEI HS HSH
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I
                 ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity));
        clear HS HSH HEI;
        let ws := fresh "ws" in let msn := fresh "ms" in let mat := fresh "mat" in
        let Hlen := fresh "Hlen" in let Hm := fresh "Hmem" in
        intros ws msn mat Hlen HEI HS HSH Hm;
        rewrite ?wvb_collapse;
        apply (lp_agree_extK E0 E K ws ltac:(lia)) in HAG
      end
    end
  end.

(* The two arms of the branch the state is stuck at. *)
Ltac lp_branch SH :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM lp_Bx SH ss) in
    let why := psym_why_tok transport_tpi transport_tw K lp_Bx lp_Bspan SH (start K lp_Bx lp_Bspan SH ss) in
    lazymatch why with
    | SR_branch ?c ?a ?b =>
      apply (paj_branch (PI := PI_transport) W E ss ms md Q c a b HS); clear HS;
      let Hc := fresh "Hc" in intros Hc HS
    end
  end.

(* The value of register r in the machine state HS describes. *)
Ltac lp_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The registers of l the run kept, from the entry registers r0 (env Eimg (Ereg r0 ex)). *)
Ltac lp_kr r0 ex l KR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HAG : env_agree 1024 _ ?Ex |- _ =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wx) msx) r0 ex l HS (lp_agree32 r0 ex Ex HAG)
      ltac:(vm_compute; reflexivity)) as KR
  end.

(* The machine state at the stop: its shape and its memory. *)
Ltac lp_shape :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
  repeat match goal with H : ms_mem ?a = ms_mem ?b |- _ => rewrite H end;
  cbn [ms_mem YK11.mkst].

(* ------------------------------------------------------------------ *)
(* The loop                                                            *)
(* ------------------------------------------------------------------ *)

Section loop. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The state at the loop's cut: the view W / mem (the loop writes no memory), io_send's registers regs at
   transport_text + IOS_LOOP, f.body = bp, f.body_len = blen, the body's bytes (ios_body frame), the world Bm the
   model's loop reads (ios_B0 Bw), the model's result final, and what the code after the loop needs (J of the model,
   preserved by the runs' materialization; Q). *)
Variables (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word).
Variables (bp blen final : Z) (body Bm : list byte).
Variable Q : world segs -> config -> Prop.
Variable J : Model -> Prop.
Hypothesis HJmat : forall md X, J md -> J (with_vm_backing (m_vm_lazy md) X md).
Hypothesis Htw : tw_at TMAP_A (aview segs (w_H W) mem) Bm.
Hypothesis HG : garr8 segs (mrestrict (w_H W) mem) bp (map DSpec.bz body).
Hypothesis HBL : blen <= Z.of_nat (length body).
Hypothesis Hbp : 0 <= bp.
Hypothesis HAM : amem_range bp blen.
Hypothesis HRAB : range_addressable (aview segs (w_H W) mem) SHADOW_OFF bp blen.
Hypothesis HRAC : range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_g_cmd TW.SZ_g_cmd.
Hypothesis HDJ : bp + blen <= TA_g_ncmd \/ TA_g_ncmd + TW.SZ_g_ncmd <= bp.
Hypothesis HR18 : YK11.getr regs 18 = w64 blen.
Hypothesis HR20 : YK11.getr regs 20 = w64 SHADOW_OFF.
Hypothesis HCMDS : forall (regs2 : bvmap 5 word) (md2 : Model),
  YK11.getr regs2 11 = w64 (bv_swrap 32 final) -> 0 <= final < 2 ^ 32 ->
  (forall x, In x IOS_LP_KP -> YK11.getr regs2 x = YK11.getr regs x) -> J md2 ->
  SRr segs W (@cfg_at fx segs (transport_text + IOS_CMDS) regs2 mem md2) Q.

Local Abbreviation lp_at pc r md :=
  (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs)) md).

Lemma lp_bhi : 0 <= blen -> bp + blen <= 2 ^ 47 - 1.
Proof. intros H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM. lia. Qed.

Lemma lp_app : forall x, bp <= x < bp + blen -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM. unfold SHADOW_OFF. lia. Qed.

(* The registers io_send keeps through the loop, and the loop's own at the head of a round. *)
Definition lp_kept (r : bvmap 5 word) : Prop := forall x, In x IOS_LP_KP -> YK11.getr r x = YK11.getr regs x.
Definition lp_inv (r : bvmap 5 word) (pos cmds : Z) : Prop :=
  YK11.getr r 13 = w64 pos /\ YK11.getr r 11 = w64 (bv_swrap 32 cmds) /\ YK11.getr r 14 = w64 bp /\
  YK11.getr r 15 = w64 3 /\ YK11.getr r 16 = w64 160 /\ YK11.getr r 17 = w64 IOS_NCMD_HI /\
  YK11.getr r 5 = w64 40 /\ YK11.getr r 6 = w64 TA_g_cmd /\ lp_kept r.

(* What the next round gives. *)
Definition lp_K (fuel : nat) : Prop :=
  forall (r : bvmap 5 word) (md : Model) (pos cmds : Z), 0 <= pos < blen -> 0 <= cmds < 2 ^ 32 ->
    lp_inv r pos cmds -> TC.cmds_loop fuel Bm body blen pos cmds = Some final -> J md ->
    SRr segs W (lp_at IOS_TURN r md) Q.

(* A state whose loop registers are r0's. *)
Lemma lp_inv_kept : forall r0 r1 pos cmds, lp_inv r0 pos cmds ->
  (forall x, In x IOS_LP_LR -> YK11.getr r1 x = YK11.getr r0 x) ->
  (forall x, In x IOS_LP_KP -> YK11.getr r1 x = YK11.getr r0 x) -> lp_inv r1 pos cmds.
Proof.
  intros r0 r1 pos cmds (R13 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & HK) K1 K2.
  split; [rewrite K1; [exact R13 | lp_kin]|].
  split; [rewrite K1; [exact R11 | lp_kin]|].
  split; [rewrite K1; [exact R14 | lp_kin]|].
  split; [rewrite K1; [exact R15 | lp_kin]|].
  split; [rewrite K1; [exact R16 | lp_kin]|].
  split; [rewrite K1; [exact R17 | lp_kin]|].
  split; [rewrite K1; [exact R5 | lp_kin]|].
  split; [rewrite K1; [exact R6 | lp_kin]|].
  intros x Hx. rewrite (K2 x Hx). exact (HK x Hx).
Qed.

(* The next round's registers: a3 and a1 new, the others r0's. *)
Lemma lp_inv_next : forall r0 r1 pos cmds pos' cmds', lp_inv r0 pos cmds ->
  (forall x, In x IOS_LP_LK -> YK11.getr r1 x = YK11.getr r0 x) ->
  (forall x, In x IOS_LP_KP -> YK11.getr r1 x = YK11.getr r0 x) ->
  YK11.getr r1 13 = w64 pos' -> YK11.getr r1 11 = w64 (bv_swrap 32 cmds') -> lp_inv r1 pos' cmds'.
Proof.
  intros r0 r1 pos cmds pos' cmds' (R13 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & HK) K1 K2 Q13 Q11.
  split; [exact Q13|]. split; [exact Q11|].
  split; [rewrite K1; [exact R14 | lp_kin]|].
  split; [rewrite K1; [exact R15 | lp_kin]|].
  split; [rewrite K1; [exact R16 | lp_kin]|].
  split; [rewrite K1; [exact R17 | lp_kin]|].
  split; [rewrite K1; [exact R5 | lp_kin]|].
  split; [rewrite K1; [exact R6 | lp_kin]|].
  intros x Hx. rewrite (K2 x Hx). exact (HK x Hx).
Qed.

(* The valuation of a fresh state: the registers r and the extra atoms ex from 32 on. *)
Definition lp_E (r : bvmap 5 word) (ex : list word) : env := Eimg (PI := PI_transport) (Ereg r ex).

Lemma lp_Ereg : forall (r : bvmap 5 word) ex n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr r x = w64 v ->
  ew (lp_E r ex) n = Z_to_bv 64 v.
Proof. intros r ex n x v Hn H. unfold lp_E. rewrite (lp_ew_reg r ex n x Hn). exact H. Qed.

Lemma lp_img_den : forall E a v, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> VAL a = v ->
  sv_denot E (SOff a 0) = Z_to_bv 64 v.
Proof. intros E a v HE Ha Hv. cbn [sv_denot]. rewrite (HE a Ha), Z.add_0_r, Hv. reflexivity. Qed.

(* +0x4ec .. +0x4f8: a3 = at + step, a1 = cmds + 1; `bltu a3,s2` to the next round, else the exit. *)
Lemma lp_bump : forall (fuel : nat) (r0 : bvmap 5 word) (md : Model) (pos cmds step : Z),
  0 <= pos < blen -> 1 <= step <= blen + 255 -> 0 <= cmds < 2 ^ 32 ->
  lp_inv r0 pos cmds -> YK11.getr r0 7 = w64 step ->
  TC.cmds_loop fuel Bm body blen (pos + step) (DSpec.u32 (cmds + 1)) = Some final ->
  J md -> lp_K fuel -> SRr segs W (lp_at IOS_STEP r0 md) Q.
Proof.
  intros fuel r0 md pos cmds step Hpos Hst Hcm Hinv R7 Hm HJ HK.
  pose proof Hinv as (R13 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & HKP).
  assert (R18 : YK11.getr r0 18 = w64 blen) by (rewrite (HKP 18%bv ltac:(lp_kin)); exact HR18).
  pose proof (lp_bhi ltac:(lia)) as Hbh.
  assert (HS : st_ok_pi segs VAL (lp_E r0 []) lps_ss
    (restrict (w_H W) (@YK11.mkst fx r0 (Z_to_bv 64 (BASE + IOS_STEP)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lps_ss, lp_E. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs lp_Bx [] (lp_E r0 []) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (lp_E r0 [])) by (unfold lp_E; apply Eimg_env).
  pose proof (env_agree_refl 1024 (lp_E r0 [])) as HAG.
  pose proof (lp_Ereg r0 [] 7 7%bv step eq_refl R7) as X7.
  pose proof (lp_Ereg r0 [] 13 13%bv pos eq_refl R13) as X13.
  pose proof (lp_Ereg r0 [] 11 11%bv (bv_swrap 32 cmds) eq_refl R11) as X11.
  pose proof (lp_Ereg r0 [] 18 18%bv blen eq_refl R18) as X18.
  lp_step ([] : list shent) IOS_TURN.
  lp_branch ([] : list shent).
  - (* at + step < body_len: the next round *)
    rewrite branch_ltu_U in Hc.
    rewrite (lp_U_add _ 7 13 step pos (lp_ewa _ _ 7 _ HAG ltac:(lia) X7) (lp_ewa _ _ 13 _ HAG ltac:(lia) X13))
      in Hc by lia.
    rewrite (U_atom _ 18 blen (lp_ewa _ _ 18 _ HAG ltac:(lia) X18)) in Hc by lia.
    apply Z.ltb_lt in Hc.
    lp_step ([] : list shent) IOS_TURN.
    lp_reg HS (13%bv : bv 5) (w64 (pos + step)) Q13
      ltac:(rewrite (denot_lit_U _); unfold w64; f_equal;
            rewrite (lp_U_add _ 7 13 step pos (lp_ewa _ _ 7 _ HAG ltac:(lia) X7)
                       (lp_ewa _ _ 13 _ HAG ltac:(lia) X13)) by lia; ring).
    lp_reg HS (11%bv : bv 5) (w64 (bv_swrap 32 (DSpec.u32 (cmds + 1)))) Q11
      ltac:(apply lp_den_addw; exact (lp_ewa _ _ 11 _ HAG ltac:(lia) X11)).
    lp_kr r0 ([] : list word) IOS_LP_LK KR1. lp_kr r0 ([] : list word) IOS_LP_KP KR2.
    lp_shape.
    apply (HK _ _ (pos + step) (DSpec.u32 (cmds + 1))).
    + lia.
    + unfold DSpec.u32. apply Z.mod_pos_bound. lia.
    + exact (lp_inv_next r0 _ pos cmds _ _ Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx) Q13 Q11).
    + exact Hm.
    + apply HJmat. exact HJ.
  - (* at + step >= body_len: the exit, a1 = cmds + 1 = the model's result *)
    rewrite branch_ltu_U in Hc.
    rewrite (lp_U_add _ 7 13 step pos (lp_ewa _ _ 7 _ HAG ltac:(lia) X7) (lp_ewa _ _ 13 _ HAG ltac:(lia) X13))
      in Hc by lia.
    rewrite (U_atom _ 18 blen (lp_ewa _ _ 18 _ HAG ltac:(lia) X18)) in Hc by lia.
    apply Z.ltb_ge in Hc.
    lp_step ([] : list shent) IOS_CMDS.
    lp_reg HS (11%bv : bv 5) (w64 (bv_swrap 32 (DSpec.u32 (cmds + 1)))) Q11
      ltac:(apply lp_den_addw; exact (lp_ewa _ _ 11 _ HAG ltac:(lia) X11)).
    lp_kr r0 ([] : list word) IOS_LP_KP KR2.
    lp_shape.
    assert (Ef : final = DSpec.u32 (cmds + 1)) by exact (lp_cl_end fuel Bm body blen (pos + step) _ final ltac:(lia) Hm).
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ _ _) ?mm) _ =>
      change (SRr segs W (@cfg_at fx segs (transport_text + IOS_CMDS) rr mem mm) Q) end.
    apply HCMDS.
    + rewrite Ef. exact Q11.
    + rewrite Ef. unfold DSpec.u32. apply Z.mod_pos_bound. lia.
    + intros x Hx. etransitivity; [exact (KR2 x Hx) | exact (HKP x Hx)].
    + apply HJmat. exact HJ.
Qed.

(* +0x4d8 .. +0x4e8: the checked load of g_cmd[s].len at a0 into t2. *)
Lemma lp_len : forall (fuel : nat) (r0 : bvmap 5 word) (md : Model) (pos cmds s : Z),
  0 <= pos < blen -> 0 <= cmds < 2 ^ 32 -> 0 <= s < TC.CMDS_MAX ->
  lp_inv r0 pos cmds -> YK11.getr r0 10 = w64 (TA_g_cmd + 40 * s + 36) ->
  TW.Cmd_len Bm s <> 0 ->
  TC.cmds_loop fuel Bm body blen (pos + TW.Cmd_len Bm s) (DSpec.u32 (cmds + 1)) = Some final ->
  J md -> lp_K fuel -> SRr segs W (lp_at IOS_LEN r0 md) Q.
Proof.
  intros fuel r0 md pos cmds s Hpos Hcm Hs Hinv R10 Hnz Hm HJ HK.
  pose proof Hinv as (R13 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & HKP).
  assert (R20 : YK11.getr r0 20 = w64 SHADOW_OFF) by (rewrite (HKP 20%bv ltac:(lp_kin)); exact HR20).
  pose proof (lp_bhi ltac:(lia)) as Hbh.
  assert (EA : TA_g_cmd = 6181888) by reflexivity.
  assert (HSZ : TW.SZ_g_cmd = 40960) by reflexivity.
  unfold TC.CMDS_MAX in Hs.
  pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bm TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 36) 1
    TMAP_A_ok Htw TMAP_A_g_cmd ltac:(lia) ltac:(rewrite HSZ; lia)) as Vc.
  rewrite <- lp_clen_at in Vc.
  pose proof (TWL.u_at_range Bm (TW.OFF_g_cmd + (40 * s + 36)) 1) as Rc. rewrite <- lp_clen_at in Rc.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Rc.
  remember (TW.Cmd_len Bm s) as cl eqn:Ecl.
  pose proof (lp_Ereg r0 [w64 cl] 10 10%bv _ eq_refl R10) as X10.
  pose proof (lp_Ereg r0 [w64 cl] 20 20%bv _ eq_refl R20) as X20.
  assert (X32 : ew (lp_E r0 [w64 cl]) 32 = Z_to_bv 64 cl) by exact (lp_ew_ex r0 [w64 cl] 0 ltac:(lia)).
  assert (U10 : bv_unsigned (ew (lp_E r0 [w64 cl]) 10) = TA_g_cmd + 40 * s + 36)
    by (rewrite X10; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew (lp_E r0 [w64 cl]) 20) = SHADOW_OFF)
    by (rewrite X20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (lp_E r0 [w64 cl]) 32) = cl) by (rewrite X32; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL (lp_E r0 [w64 cl]) lpc_ss
    (restrict (w_H W) (@YK11.mkst fx r0 (Z_to_bv 64 (BASE + IOS_LEN)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lpc_ss. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold lpc_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (lp_chunk1 _ _ 32 (TA_g_cmd + 40 * s + 36) 0 (TA_g_cmd + (40 * s + 36)) cl);
        [exact X32 | lia | lia | exact Vc].
    - exact (conj I I).
    - unfold facts_ok, lpc_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok, lp_PTR, lp_PTRHI. cbn [af_lo af_hi af_al2].
      rewrite U20, U10, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; try exact I; lia. }
  assert (HSH : sh_ok segs lp_Bx lpc_SH (lp_E r0 [w64 cl]) (mrestrict (w_H W) mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W) mem (lp_E r0 [w64 cl]) lp_Bx 10%nat TA_g_cmd TW.SZ_g_cmd
      (TA_g_cmd + 40 * s + 36) 0 1 HRAC).
    - unfold lp_Bx. apply U_atom; [exact X20 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact X10 | lia].
    - lia.
    - rewrite HSZ. lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia. }
  assert (HEI : img_env VAL A_LIM (lp_E r0 [w64 cl])) by (unfold lp_E; apply Eimg_env).
  pose proof (env_agree_refl 1024 (lp_E r0 [w64 cl])) as HAG.
  lp_step lpc_SH IOS_STEP.
  lp_reg HS (7%bv : bv 5) (w64 cl) Q7 ltac:(exact (lp_den0 _ 32 cl (lp_ewa _ _ 32 _ HAG ltac:(lia) X32) ltac:(lia))).
  lp_kr r0 [w64 cl] IOS_LP_LR KR1. lp_kr r0 [w64 cl] IOS_LP_KP KR2.
  lp_shape.
  apply (lp_bump fuel _ _ pos cmds cl Hpos ltac:(lia) Hcm).
  - exact (lp_inv_kept r0 _ pos cmds Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx)).
  - exact Q7.
  - exact Hm.
  - apply HJmat. exact HJ.
  - exact HK.
Qed.

Lemma lp_nth_bz : forall (l : list byte) j, nth j (map DSpec.bz l) 0 = DSpec.at8 l j.
Proof. intros l j. unfold DSpec.at8. rewrite <- (map_nth DSpec.bz l (DSpec.b8 0) j). reflexivity. Qed.

(* +0x474 .. +0x4c8: the checked loads of body[at], body[at + 1], body[at + 2]; `bne` on body[at] = TAG; serial and
   the load of g_ncmd; `bgeu serial,g_ncmd`. *)
Lemma lp_body : forall (fuel : nat) (r0 : bvmap 5 word) (md : Model) (pos cmds : Z),
  0 <= pos -> pos + 3 <= blen -> 0 <= cmds < 2 ^ 32 ->
  lp_inv r0 pos cmds -> YK11.getr r0 10 = w64 (bp + pos) -> YK11.getr r0 7 = w64 (blen - pos) ->
  TC.cmds_loop (S fuel) Bm body blen pos cmds = Some final ->
  J md -> lp_K fuel -> SRr segs W (lp_at IOS_TAGB r0 md) Q.
Proof.
  intros fuel r0 md pos cmds Hpos H3 Hcm Hinv R10 R7 Hm HJ HK.
  pose proof Hinv as (R13 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & HKP).
  assert (R20 : YK11.getr r0 20 = w64 SHADOW_OFF) by (rewrite (HKP 20%bv ltac:(lp_kin)); exact HR20).
  pose proof (lp_bhi ltac:(lia)) as Hbh.
  assert (ENC : TA_g_ncmd = 6158720) by reflexivity.
  assert (EGC : TA_g_cmd = 6181888) by reflexivity.
  (* the three body bytes *)
  assert (HB : forall j : nat, (j < 3)%nat ->
    val_mem segs (mrestrict (w_H W) mem) (bp + pos + Z.of_nat j) 1 (DSpec.at8 body (Z.to_nat pos + j)) /\
    0 <= DSpec.at8 body (Z.to_nat pos + j) < 256).
  { intros j Hj. assert (Hj' : (Z.to_nat pos + j < length (map DSpec.bz body))%nat) by (rewrite length_map; lia).
    destruct (HG _ Hj') as [Hv Hr]. rewrite lp_nth_bz in Hv, Hr.
    replace (bp + pos + Z.of_nat j) with (bp + Z.of_nat (Z.to_nat pos + j)) by lia. exact (conj Hv Hr). }
  destruct (HB 0%nat ltac:(lia)) as [V0 B0]. destruct (HB 1%nat ltac:(lia)) as [V1 B1].
  destruct (HB 2%nat ltac:(lia)) as [V2 B2]. clear HB.
  rewrite Nat.add_0_r in V0, B0.
  remember (DSpec.at8 body (Z.to_nat pos)) as b0 eqn:Eb0.
  remember (DSpec.at8 body (Z.to_nat pos + 1)) as b1 eqn:Eb1.
  remember (DSpec.at8 body (Z.to_nat pos + 2)) as b2 eqn:Eb2.
  (* g_ncmd *)
  pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bm TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 4
    TMAP_A_ok Htw TMAP_A_g_ncmd ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)) as Vn.
  rewrite <- lp_ncmd_at in Vn.
  pose proof (TWL.u_at_range Bm (TW.OFF_g_ncmd + 0) 4) as Rn. rewrite <- lp_ncmd_at in Rn.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rn.
  remember (TW.g_ncmd Bm) as nc eqn:Enc.
  (* the model's view of the three bytes *)
  assert (L3 : (3 <= length (skipn (Z.to_nat pos) body))%nat) by (rewrite lp_len_skipn; lia).
  assert (A0 : DSpec.at8 (skipn (Z.to_nat pos) body) 0 = b0) by (rewrite lp_at8_skipn, Nat.add_0_r; symmetry; exact Eb0).
  assert (A1 : DSpec.at8 (skipn (Z.to_nat pos) body) 1 = b1) by (rewrite lp_at8_skipn; symmetry; exact Eb1).
  assert (A2 : DSpec.at8 (skipn (Z.to_nat pos) body) 2 = b2) by (rewrite lp_at8_skipn; symmetry; exact Eb2).
  (* the fresh state *)
  set (ex := [w64 b0; w64 b1; w64 b2; w64 nc]).
  pose proof (lp_Ereg r0 ex 10 10%bv _ eq_refl R10) as X10.
  pose proof (lp_Ereg r0 ex 20 20%bv _ eq_refl R20) as X20.
  pose proof (lp_Ereg r0 ex 16 16%bv _ eq_refl R16) as X16.
  pose proof (lp_Ereg r0 ex 17 17%bv _ eq_refl R17) as X17.
  pose proof (lp_Ereg r0 ex 5 5%bv _ eq_refl R5) as X5.
  pose proof (lp_Ereg r0 ex 6 6%bv _ eq_refl R6) as X6.
  pose proof (lp_Ereg r0 ex 7 7%bv _ eq_refl R7) as X7.
  assert (X32 : ew (lp_E r0 ex) 32 = Z_to_bv 64 b0) by exact (lp_ew_ex r0 ex 0 ltac:(lia)).
  assert (X33 : ew (lp_E r0 ex) 33 = Z_to_bv 64 b1) by exact (lp_ew_ex r0 ex 1 ltac:(lia)).
  assert (X34 : ew (lp_E r0 ex) 34 = Z_to_bv 64 b2) by exact (lp_ew_ex r0 ex 2 ltac:(lia)).
  assert (X35 : ew (lp_E r0 ex) 35 = Z_to_bv 64 nc) by exact (lp_ew_ex r0 ex 3 ltac:(lia)).
  assert (U10 : bv_unsigned (ew (lp_E r0 ex) 10) = bp + pos) by (rewrite X10; apply unsigned_lit_small; lia).
  assert (U17 : bv_unsigned (ew (lp_E r0 ex) 17) = IOS_NCMD_HI)
    by (rewrite X17; apply unsigned_lit_small; unfold IOS_NCMD_HI; lia).
  assert (U20 : bv_unsigned (ew (lp_E r0 ex) 20) = SHADOW_OFF)
    by (rewrite X20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (lp_E r0 ex) 32) = b0) by (rewrite X32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew (lp_E r0 ex) 33) = b1) by (rewrite X33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew (lp_E r0 ex) 34) = b2) by (rewrite X34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew (lp_E r0 ex) 35) = nc) by (rewrite X35; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL (lp_E r0 ex) lpb_ss
    (restrict (w_H W) (@YK11.mkst fx r0 (Z_to_bv 64 (BASE + IOS_TAGB)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lpb_ss. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold lpb_rg, YP09.region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * apply (lp_chunk1 _ _ 32 (bp + pos) 0 (bp + pos + Z.of_nat 0) b0); [exact X32 | lia | lia | exact V0].
        * apply (lp_chunk1 _ _ 33 (bp + pos) 1 (bp + pos + Z.of_nat 1) b1); [exact X33 | lia | lia | exact V1].
        * apply (lp_chunk1 _ _ 34 (bp + pos) 2 (bp + pos + Z.of_nat 2) b2); [exact X34 | lia | lia | exact V2].
      + unfold lpn_rg, YP09.region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U17.
        unfold IOS_NCMD_HI. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs _ _ (TA_g_ncmd - 1992) 1992 4 (SOff 35 0) nc).
        * exact (lp_den0 _ 35 nc X35 ltac:(lia)).
        * cbn. lia.
        * cbn. lia.
        * replace (TA_g_ncmd - 1992 + 1992) with (TA_g_ncmd + 0) by ring. exact Vn.
    - apply pairwise_disjoint_of_extents. unfold lpb_rg, lpn_rg, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U17.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold IOS_NCMD_HI. unfold TW.SZ_g_ncmd in HDJ.
      split; [split; [|exact I] | split; exact I].
      destruct HDJ as [D|D]; [left | right]; lia.
    - unfold facts_ok, lpb_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok, lp_PTR, lp_PTRHI. cbn [af_lo af_hi af_al2].
      rewrite U20, U10, U32, U33, U34, U35. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; try exact I; lia. }
  assert (HSH : sh_ok segs lp_Bx lpb_SH (lp_E r0 ex) (mrestrict (w_H W) mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W) mem (lp_E r0 ex) lp_Bx 10%nat bp blen (bp + pos) 0 3 HRAB).
    - unfold lp_Bx. apply U_atom; [exact X20 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact X10 | lia].
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. apply lp_app. lia. }
  assert (HEI : img_env VAL A_LIM (lp_E r0 ex)) by (unfold lp_E; apply Eimg_env).
  pose proof (env_agree_refl 1024 (lp_E r0 ex)) as HAG.
  lp_step lpb_SH IOS_STEP.
  lp_branch lpb_SH.
  - (* body[at] <> TAG: step = body_len - at *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 32 b0 (lp_ewa _ _ 32 _ HAG ltac:(lia) X32)) in Hc by lia.
    rewrite (U_atom _ 16 160 (lp_ewa _ _ 16 _ HAG ltac:(lia) X16)) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Ht : TC.tagged_of_m Bm (skipn (Z.to_nat pos) body) (blen - pos) = Some (Bm, None)).
    { apply lp_tof_notag; [lia | lia | rewrite A0; unfold TC.TAG; exact Hc]. }
    destruct (lp_cl_step fuel Bm body blen pos cmds final None ltac:(lia) Ht Hm) as [_ Hm'].
    lp_step lpb_SH IOS_STEP.
    lp_reg HS (7%bv : bv 5) (w64 (blen - pos)) Q7
      ltac:(exact (lp_den0 _ 7 _ (lp_ewa _ _ 7 _ HAG ltac:(lia) X7) ltac:(lia))).
    lp_kr r0 ex IOS_LP_LR KR1. lp_kr r0 ex IOS_LP_KP KR2.
    lp_shape.
    apply (lp_bump fuel _ _ pos cmds (blen - pos) ltac:(lia) ltac:(lia) Hcm).
    + exact (lp_inv_kept r0 _ pos cmds Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx)).
    + exact Q7.
    + exact Hm'.
    + apply HJmat. exact HJ.
    + exact HK.
  - (* body[at] = TAG *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 32 b0 (lp_ewa _ _ 32 _ HAG ltac:(lia) X32)) in Hc by lia.
    rewrite (U_atom _ 16 160 (lp_ewa _ _ 16 _ HAG ltac:(lia) X16)) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Htag.
    assert (T0 : DSpec.at8 (skipn (Z.to_nat pos) body) 0 = TC.TAG) by (rewrite A0; unfold TC.TAG; exact Htag).
    lp_step lpb_SH IOS_STEP.
    lp_branch lpb_SH.
    + (* serial >= g_ncmd: step = body_len - at *)
      rewrite branch_geu_U in Hc.
      destruct (lp_U_serial _ b1 b2 (lp_ewa _ _ 33 _ HAG ltac:(lia) X33) (lp_ewa _ _ 34 _ HAG ltac:(lia) X34) B1 B2)
        as [US RS].
      rewrite US in Hc.
      rewrite (lp_ltu_ncmd _ nc (Z.lor b1 (Z.shiftl b2 7)) (lp_ewa _ _ 35 _ HAG ltac:(lia) X35) Rn ltac:(lia)) in Hc.
      apply negb_true_iff, Z.ltb_ge in Hc.
      assert (Ht : TC.tagged_of_m Bm (skipn (Z.to_nat pos) body) (blen - pos) = Some (Bm, None)).
      { apply lp_tof_out; [lia | exact L3 | exact T0 | rewrite A1, A2, <- Enc; exact Hc]. }
      destruct (lp_cl_step fuel Bm body blen pos cmds final None ltac:(lia) Ht Hm) as [_ Hm'].
      lp_step lpb_SH IOS_STEP.
      lp_reg HS (7%bv : bv 5) (w64 (blen - pos)) Q7
        ltac:(exact (lp_den0 _ 7 _ (lp_ewa _ _ 7 _ HAG ltac:(lia) X7) ltac:(lia))).
      lp_kr r0 ex IOS_LP_LR KR1. lp_kr r0 ex IOS_LP_KP KR2.
      lp_shape.
      apply (lp_bump fuel _ _ pos cmds (blen - pos) ltac:(lia) ltac:(lia) Hcm).
      * exact (lp_inv_kept r0 _ pos cmds Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx)).
      * exact Q7.
      * exact Hm'.
      * apply HJmat. exact HJ.
      * exact HK.
    + (* serial < g_ncmd: the model has serial < CMDS_MAX; step = g_cmd[serial].len *)
      rewrite branch_geu_U in Hc.
      destruct (lp_U_serial _ b1 b2 (lp_ewa _ _ 33 _ HAG ltac:(lia) X33) (lp_ewa _ _ 34 _ HAG ltac:(lia) X34) B1 B2)
        as [US RS].
      rewrite US in Hc.
      rewrite (lp_ltu_ncmd _ nc (Z.lor b1 (Z.shiftl b2 7)) (lp_ewa _ _ 35 _ HAG ltac:(lia) X35) Rn ltac:(lia)) in Hc.
      apply negb_false_iff, Z.ltb_lt in Hc.
      assert (Hs : Z.lor b1 (Z.shiftl b2 7) < TC.CMDS_MAX).
      { destruct (Z_lt_le_dec (Z.lor b1 (Z.shiftl b2 7)) TC.CMDS_MAX) as [Hl|Hl]; [exact Hl|]. exfalso.
        apply (lp_cl_none fuel Bm body blen pos cmds final ltac:(lia)); [|exact Hm].
        apply lp_tof_big; [lia | exact L3 | exact T0 | rewrite A1, A2, <- Enc; exact Hc | rewrite A1, A2; exact Hl]. }
      assert (Ht : TC.tagged_of_m Bm (skipn (Z.to_nat pos) body) (blen - pos)
                   = Some (Bm, Some (Z.lor b1 (Z.shiftl b2 7)))).
      { rewrite <- A1, <- A2. apply lp_tof_in; [lia | exact L3 | exact T0 | rewrite A1, A2, <- Enc; exact Hc |
          rewrite A1, A2; exact Hs]. }
      destruct (lp_cl_step fuel Bm body blen pos cmds final _ ltac:(lia) Ht Hm) as [Hnz Hm'].
      lp_step lpb_SH IOS_LEN.
      lp_reg HS (10%bv : bv 5) (w64 (TA_g_cmd + 40 * Z.lor b1 (Z.shiftl b2 7) + 36)) Q10
        ltac:(rewrite (denot_lit_U _); unfold w64; f_equal;
              apply (lp_U_lenaddr _ b1 b2 TA_g_cmd (lp_ewa _ _ 33 _ HAG ltac:(lia) X33)
                       (lp_ewa _ _ 34 _ HAG ltac:(lia) X34) (lp_ewa _ _ 6 _ HAG ltac:(lia) X6)
                       (lp_ewa _ _ 5 _ HAG ltac:(lia) X5) B1 B2); lia).
      lp_kr r0 ex IOS_LP_LR KR1. lp_kr r0 ex IOS_LP_KP KR2.
      lp_shape.
      unfold TC.CMDS_MAX in Hs.
      apply (lp_len fuel _ _ pos cmds (Z.lor b1 (Z.shiftl b2 7)) ltac:(lia) Hcm ltac:(unfold TC.CMDS_MAX; lia)).
      * exact (lp_inv_kept r0 _ pos cmds Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx)).
      * exact Q10.
      * exact Hnz.
      * exact Hm'.
      * apply HJmat. exact HJ.
      * exact HK.
Qed.

(* +0x468 .. +0x470: t2 = body_len - at; `bltu t2,a5` (body_len - at < 3) to the step, else a0 = body + at. *)
Lemma ios_loop_turn : forall (fuel : nat) (r0 : bvmap 5 word) (md : Model) (pos cmds : Z),
  0 <= pos < blen -> 0 <= cmds < 2 ^ 32 -> lp_inv r0 pos cmds ->
  TC.cmds_loop (S fuel) Bm body blen pos cmds = Some final -> J md -> lp_K fuel ->
  SRr segs W (lp_at IOS_TURN r0 md) Q.
Proof.
  intros fuel r0 md pos cmds Hpos Hcm Hinv Hm HJ HK.
  pose proof Hinv as (R13 & R11 & R14 & R15 & R16 & R17 & R5 & R6 & HKP).
  assert (R18 : YK11.getr r0 18 = w64 blen) by (rewrite (HKP 18%bv ltac:(lp_kin)); exact HR18).
  pose proof (lp_bhi ltac:(lia)) as Hbh.
  assert (HS : st_ok_pi segs VAL (lp_E r0 []) lph_ss
    (restrict (w_H W) (@YK11.mkst fx r0 (Z_to_bv 64 (BASE + IOS_TURN)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lph_ss, lp_E. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs lp_Bx [] (lp_E r0 []) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (lp_E r0 [])) by (unfold lp_E; apply Eimg_env).
  pose proof (env_agree_refl 1024 (lp_E r0 [])) as HAG.
  pose proof (lp_Ereg r0 [] 13 13%bv pos eq_refl R13) as X13.
  pose proof (lp_Ereg r0 [] 14 14%bv bp eq_refl R14) as X14.
  pose proof (lp_Ereg r0 [] 15 15%bv 3 eq_refl R15) as X15.
  pose proof (lp_Ereg r0 [] 18 18%bv blen eq_refl R18) as X18.
  lp_step ([] : list shent) IOS_TAGB.
  lp_branch ([] : list shent).
  - (* body_len - at < 3: step = body_len - at *)
    rewrite branch_ltu_U in Hc.
    rewrite (lp_U_sub _ 13 18 pos blen (lp_ewa _ _ 13 _ HAG ltac:(lia) X13) (lp_ewa _ _ 18 _ HAG ltac:(lia) X18))
      in Hc by lia.
    rewrite (U_atom _ 15 3 (lp_ewa _ _ 15 _ HAG ltac:(lia) X15)) in Hc by lia.
    apply Z.ltb_lt in Hc.
    assert (Ht : TC.tagged_of_m Bm (skipn (Z.to_nat pos) body) (blen - pos) = Some (Bm, None))
      by (apply lp_tof_short; lia).
    destruct (lp_cl_step fuel Bm body blen pos cmds final None ltac:(lia) Ht Hm) as [_ Hm'].
    lp_step ([] : list shent) IOS_STEP.
    lp_reg HS (7%bv : bv 5) (w64 (blen - pos)) Q7
      ltac:(rewrite (denot_lit_U _); unfold w64; f_equal;
            apply (lp_U_sub _ 13 18 pos blen (lp_ewa _ _ 13 _ HAG ltac:(lia) X13)
                     (lp_ewa _ _ 18 _ HAG ltac:(lia) X18)); lia).
    lp_kr r0 ([] : list word) IOS_LP_LR KR1. lp_kr r0 ([] : list word) IOS_LP_KP KR2.
    lp_shape.
    apply (lp_bump fuel _ _ pos cmds (blen - pos) ltac:(lia) ltac:(lia) Hcm).
    + exact (lp_inv_kept r0 _ pos cmds Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx)).
    + exact Q7.
    + exact Hm'.
    + apply HJmat. exact HJ.
    + exact HK.
  - (* body_len - at >= 3: a0 = body + at, the checked loads *)
    rewrite branch_ltu_U in Hc.
    rewrite (lp_U_sub _ 13 18 pos blen (lp_ewa _ _ 13 _ HAG ltac:(lia) X13) (lp_ewa _ _ 18 _ HAG ltac:(lia) X18))
      in Hc by lia.
    rewrite (U_atom _ 15 3 (lp_ewa _ _ 15 _ HAG ltac:(lia) X15)) in Hc by lia.
    apply Z.ltb_ge in Hc.
    lp_step ([] : list shent) IOS_TAGB.
    lp_reg HS (10%bv : bv 5) (w64 (bp + pos)) Q10
      ltac:(rewrite (denot_lit_U _); unfold w64; f_equal;
            rewrite (lp_U_add _ 13 14 pos bp (lp_ewa _ _ 13 _ HAG ltac:(lia) X13)
                       (lp_ewa _ _ 14 _ HAG ltac:(lia) X14)) by lia; ring).
    lp_reg HS (7%bv : bv 5) (w64 (blen - pos)) Q7
      ltac:(rewrite (denot_lit_U _); unfold w64; f_equal;
            apply (lp_U_sub _ 13 18 pos blen (lp_ewa _ _ 13 _ HAG ltac:(lia) X13)
                     (lp_ewa _ _ 18 _ HAG ltac:(lia) X18)); lia).
    lp_kr r0 ([] : list word) IOS_LP_LR KR1. lp_kr r0 ([] : list word) IOS_LP_KP KR2.
    lp_shape.
    apply (lp_body fuel _ _ pos cmds ltac:(lia) ltac:(lia) Hcm).
    + exact (lp_inv_kept r0 _ pos cmds Hinv (fun x Hx => KR1 x Hx) (fun x Hx => KR2 x Hx)).
    + exact Q10.
    + exact Q7.
    + exact Hm.
    + apply HJmat. exact HJ.
    + exact HK.
Qed.

(* The rounds, by induction on the model's fuel: each round passes from cmds_loop (S fuel) to cmds_loop fuel. *)
Lemma ios_loop_rounds : forall fuel, lp_K fuel.
Proof.
  induction fuel as [|fuel IH]; intros r md pos cmds Hpos Hcm Hinv Hm HJ.
  - cbn [TC.cmds_loop] in Hm. discriminate Hm.
  - exact (ios_loop_turn fuel r md pos cmds Hpos Hcm Hinv Hm HJ IH).
Qed.

(* +0x448 .. +0x464: the loop's registers from io_send's (a1 = 0, set at +0x440), then the rounds from at = 0. *)
Lemma lp_pre : forall (fuel : nat) (md : Model),
  0 < blen -> YK11.getr regs 11 = w64 0 -> spZ regs <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (spZ regs + 56) = Some bp ->
  TC.cmds_loop fuel Bm body blen 0 0 = Some final -> J md ->
  SRr segs W (lp_at IOS_LOOP regs md) Q.
Proof.
  intros fuel md Hb R11 Hsp Hslot Hm HJ.
  pose proof (lp_bhi ltac:(lia)) as Hbh.
  pose proof (lp_Ereg regs [w64 bp] 11 11%bv 0 eq_refl R11) as X11.
  assert (X32 : ew (lp_E regs [w64 bp]) 32 = Z_to_bv 64 bp) by exact (lp_ew_ex regs [w64 bp] 0 ltac:(lia)).
  assert (U2 : bv_unsigned (ew (lp_E regs [w64 bp]) 2) = spZ regs)
    by (unfold lp_E; rewrite (lp_ew_reg regs [w64 bp] 2 2%bv eq_refl); reflexivity).
  pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in Rsp.
  assert (HS : st_ok_pi segs VAL (lp_E regs [w64 bp]) lpp_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_LOOP)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lpp_ss. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold lpp_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ (spZ regs) 56 8 (SOff 32 0) bp).
      + exact (lp_den0 _ 32 bp X32 ltac:(lia)).
      + cbn. lia.
      + cbn. lia.
      + exact (val_mem_of_rdword segs (w_H W) mem _ _ Hslot).
    - exact (conj I I).
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs lp_Bx [] (lp_E regs [w64 bp]) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (lp_E regs [w64 bp])) by (unfold lp_E; apply Eimg_env).
  pose proof (env_agree_refl 1024 (lp_E regs [w64 bp])) as HAG.
  lp_step ([] : list shent) IOS_TURN.
  lp_reg HS (13%bv : bv 5) (w64 0) Q13 ltac:(reflexivity).
  lp_reg HS (11%bv : bv 5) (w64 0) Q11 ltac:(exact (lp_den0 _ 11 0 (lp_ewa _ _ 11 _ HAG ltac:(lia) X11) ltac:(lia))).
  lp_reg HS (14%bv : bv 5) (w64 bp) Q14 ltac:(exact (lp_den0 _ 32 bp (lp_ewa _ _ 32 _ HAG ltac:(lia) X32) ltac:(lia))).
  lp_reg HS (15%bv : bv 5) (w64 3) Q15 ltac:(reflexivity).
  lp_reg HS (16%bv : bv 5) (w64 160) Q16 ltac:(reflexivity).
  lp_reg HS (17%bv : bv 5) (w64 IOS_NCMD_HI) Q17
    ltac:(exact (lp_img_den _ 456 IOS_NCMD_HI HEI ltac:(unfold A_TEXT, A_LIM; lia) (proj1 lp_vals))).
  lp_reg HS (5%bv : bv 5) (w64 40) Q5 ltac:(reflexivity).
  lp_reg HS (6%bv : bv 5) (w64 TA_g_cmd) Q6
    ltac:(exact (lp_img_den _ 259 TA_g_cmd HEI ltac:(unfold A_TEXT, A_LIM; lia) (proj1 (proj2 lp_vals)))).
  lp_kr regs [w64 bp] IOS_LP_KP KR2.
  lp_shape.
  apply (ios_loop_rounds fuel _ _ 0 0 ltac:(lia) ltac:(lia)); [| exact Hm | apply HJmat; exact HJ].
  unfold lp_inv. split; [exact Q13|]. split; [exact Q11|]. split; [exact Q14|]. split; [exact Q15|].
  split; [exact Q16|]. split; [exact Q17|]. split; [exact Q5|]. split; [exact Q6|].
  intros x Hx. exact (KR2 x Hx).
Qed.

(* The loop at its cut, in the form of the statement's cfg_at. *)
Lemma lp_loop : forall (fuel : nat) (md : Model),
  0 < blen -> YK11.getr regs 11 = w64 0 -> spZ regs <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (spZ regs + 56) = Some bp ->
  TC.cmds_loop fuel Bm body blen 0 0 = Some final -> J md ->
  SRr segs W (@cfg_at fx segs (transport_text + IOS_LOOP) regs mem md) Q.
Proof using rc HJmat Htw HG HBL Hbp HAM HRAB HRAC HDJ HR18 HR20 HCMDS.
  intros fuel md Hb R11 Hsp Hslot Hm HJ.
  change (SRr segs W (lp_at IOS_LOOP regs md) Q).
  exact (lp_pre fuel md Hb R11 Hsp Hslot Hm HJ).
Qed.

End loop.

(* ------------------------------------------------------------------ *)
(* The theorem                                                        *)
(* ------------------------------------------------------------------ *)

(* The command count loop of io_send's image-A walk, from 0x831a8 = transport_text + IOS_LOOP to its exit
   0x8329c = transport_text + IOS_CMDS, on its own premises:
   - J: what the code after the loop needs of the model, kept by the runs' materialization (with_vm_backing);
   - the world relation at Bm (the world the model's loop reads: io_send_m's B3 = ios_B0 Bw), for g_ncmd and the
     lengths g_cmd[s].len;
   - the body's bytes at bp (ios_body frame, f.body = p + 30), blen <= their number, 0 <= bp, [bp, bp + blen) in
     application memory and addressable (its shadow decides the checks of body[at] .. body[at + 2]), apart from
     g_ncmd's 4 bytes;
   - g_cmd's payload addressable (its shadow decides the check of g_cmd[serial].len);
   - the registers: a1 = 0 (set at +0x440), s2 = blen, s4 = the shadow base, sp <= 2 ^ 47 with f.body = bp in the
     8 bytes at sp + 56;
   - the model's loop from at = 0, cmds = 0 with any fuel (io_send_m's is S (Z.to_nat blen)) answering final.
   The continuation at IOS_CMDS gets a1 = final (sign-extended from 32 bits, as check_latest_frame_cg.v's argument
   a1 = bv_swrap 32 cmds), 0 <= final < 2 ^ 32, the registers of IOS_LP_KP (ra, sp, gp, tp, s0 .. s11, t5, t6) as
   they were, the same memory, and J of its model. *)
Theorem ios_loop : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (W : world tfibsegs) (mem : word -> option byte)
    (regs : bvmap 5 word) (md : Model) (bp blen final : Z) (body Bm : list byte) (fuel : nat)
    (J : Model -> Prop) (Q : world tfibsegs -> config -> Prop),
  (forall md' X, J md' -> J (with_vm_backing (m_vm_lazy md') X md')) ->
  tw_at TMAP_A (aview tfibsegs (w_H W) mem) Bm ->
  garr8 tfibsegs (mrestrict (w_H W) mem) bp (map DSpec.bz body) ->
  0 < blen -> blen <= Z.of_nat (length body) ->
  0 <= bp -> amem_range bp blen ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF bp blen ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF TA_g_cmd TW.SZ_g_cmd ->
  (bp + blen <= TA_g_ncmd \/ TA_g_ncmd + TW.SZ_g_ncmd <= bp) ->
  YK11.getr regs 11 = w64 0 -> YK11.getr regs 18 = w64 blen -> YK11.getr regs 20 = w64 SHADOW_OFF ->
  spZ regs <= 2 ^ 47 -> rdword (aview tfibsegs (w_H W) mem) (spZ regs + 56) = Some bp ->
  TC.cmds_loop fuel Bm body blen 0 0 = Some final ->
  J md ->
  (forall (regs2 : bvmap 5 word) (md2 : Model),
     YK11.getr regs2 11 = w64 (bv_swrap 32 final) -> 0 <= final < 2 ^ 32 ->
     (forall x, In x IOS_LP_KP -> YK11.getr regs2 x = YK11.getr regs x) -> J md2 ->
     SRr tfibsegs W (@cfg_at fx tfibsegs (transport_text + IOS_CMDS) regs2 mem md2) Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs (transport_text + IOS_LOOP) regs mem md) Q.
Proof.
  intros fx rc W mem regs md bp blen final body Bm fuel J Q HJmat Htw HG Hb HBL Hbp HAM HRAB HRAC HDJ
    R11 HR18 HR20 Hsp Hslot Hm HJ HCMDS.
  exact (@lp_loop fx rc W mem regs bp blen final body Bm Q J HJmat Htw HG HBL Hbp HAM HRAB HRAC HDJ HR18 HR20 HCMDS
    fuel md Hb R11 Hsp Hslot Hm HJ).
Qed.
