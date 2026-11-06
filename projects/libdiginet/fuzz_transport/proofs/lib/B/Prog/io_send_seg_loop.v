(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 1149 of its 1210 lines of code are new or changed and 704 lines of the source are left out. *)
(* io_send_seg_loop: the command count loop of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f,
   entry 0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), from the cut
   0x83198 = transportb_text + IOS_LOOP to its exit 0x83220 = transportb_text + IOS_CMDS (fuzz_transport.c:858-862);
   the segment statement is lib/B/Prog/io_send_seg_cut.v ios_loop_stmt, proved here as ios_loop.

   The code (offsets from io_send's entry; s2 = cmds, s7 = at, a1 = body_len at the head of a round, s4 = the shadow
   base; io_send_cg.v header, lines 120-127 and 221-228):
     +0x19c .. +0x1a0  s2 = 0, s7 = 0;
     +0x1a4 .. +0x1c0  the head of a round: a2 = f.body (the 8-byte load at sp + 56), a0 = s7 + a2; `bltu a0,a2` to the
                       trap word 0x83358 (the sum wraps); `beq ((a2 <> 0) xor (a0 = 0)),0` to the trap word;
                       a1 = a1 - s7;
     +0x1c4            `jal` tagged_of (0x846a0 = transportb_sigma TB_tagged_of), return address 0x831c4;
     +0x1c8 .. +0x1ec  t = a0: t = 0 goes to +0x1f0; else `bne (t & 3),0` to the trap word, the instrumented 1-byte
                       load of t->len at t + 36 (its slow path +0x20c .. +0x214 and the call of __asan_report_load1),
                       `j` +0x1f8;
     +0x1f0 .. +0x1f4  a0 = body_len (the 8-byte load at sp + 64) - s7;
     +0x1f8 .. +0x208  a1 = body_len (sp + 64), s7 = a0 + s7, s2 = s2 + 1 (addiw), `bltu s7,a1` to the head, else `j`
                       IOS_CMDS.
   How it is proved. Each straight stretch is a run of the PA engine with its token shadow checks
   (lib/A/Prog/PaShadow.v) over the walk's G journal (lib/B/Prog/TransportGRunB.v paj_run_x), from a fresh symbolic
   state whose regions are read-only, so the run keeps the memory. The call of tagged_of is its leaf statement
   (lib/B/Prog/tagged_of_cg.v, read at this unit's model by DgnTransportBCg.v transport_leaf_at) at the walk's journal,
   through TransportGCg.v gx_call_leaf and the leaf bridge DgnTransportBLeafb.v decode_leafb_journal (lp_tagged, the
   form of check_latest_sent_seg_cj.v cls_tagged of 3e843999860a): it keeps every byte outside its ESTACK window below
   sp, so every byte the loop reads, and every byte of io_send's frame and of G, stays as it was at the cut (lp_mem).
     lp_pre       +0x19c: s2 = 0, s7 = 0; to the head;
     lp_head      +0x1a4: f.body (atom 32) at sp + 56; facts at <= 2 ^ 32 and 4096 <= f.body decide the second
                  pointer check; the wrap branch is refuted (at < body_len, f.body + body_len <= 2 ^ 47); a0 = f.body + at,
                  a1 = body_len - at; then the call of tagged_of (the round's tagged_of_m of the model);
     lp_ret_none  +0x1c8, t = 0: the zero branch (its other arm refuted); a0 = body_len - at; to +0x1f8;
     lp_ret_some  +0x1c8, t = g_cmd + 40 s, s < CMDS_MAX: facts (t inside g_cmd's payload, 8-aligned) decide the zero
                  branch and the alignment branch, the shadow entry of g_cmd's payload (shadow 0: trans_iosend_cells)
                  decides the check, a0 = t->len (atom 32, the world's Cmd_len); to +0x1f8;
     lp_bump      +0x1f8: at += step, cmds += 1 (addiw: u32 (cmds + 1) sign-extended), split on `bltu`; to the head
                  or to IOS_CMDS.
   The rounds are an induction on the model's fuel (lp_rounds): each round passes from TCb.v cmds_loop (S fuel) to
   cmds_loop fuel. tagged_of_m's None and a step of 0 are the model's None cases, which the premise excludes; the
   trap word and the error path are never reached. At the exit the cut's facts iod_at carry to the last memory
   (ios_loop, with lp_kept_win for the running kept fact). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require PropExec MState Mem Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB m_set_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBLeafb TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit AsanKA tagged_of_c tagged_of_cg
  check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module FCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module TOC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_c.
Module LTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The points of the loop and its symbolic states                      *)
(* ------------------------------------------------------------------ *)

(* The head of a round (0x831a0), the return of tagged_of (0x831c4), the step (0x831f4). *)
Definition IOS_LPH : Z := IOS_AT 0x1a4.
Definition IOS_LPR : Z := IOS_AT 0x1c8.
Definition IOS_LPS : Z := IOS_AT 0x1f8.

Lemma lp_addrs : transportb_text + IOS_LPH = 0x831a0 /\ transportb_text + IOS_LPR = 0x831c4 /\
  transportb_text + IOS_LPS = 0x831f4.
Proof. repeat split; reflexivity. Qed.

(* The registers the loop keeps from the cut: sp, gp, tp, s0, s1, s3 .. s6, s8 .. s11. *)
Definition LP_KP : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
(* The loop's own counters across a call or a run: s2 = cmds, s7 = at. *)
Definition LP_SC : list (bv 5) := [18; 23]%bv.

Ltac lp_kin := unfold LP_KP; cbn [In]; repeat (first [left; reflexivity | right]).

(* s4 holds the shadow base: the token engine's base. *)
Definition lp_Bx : sv := SOff 20 0.

(* +0x19c: no region (the run stops at the head's load). *)
Definition lpl_ss : sstate := mkSS IOS_LOOP sr_atoms [] None (mkFacts [] [] []).
(* +0x1a4: f.body at sp + 56 (atom 32); at = s7 below 2 ^ 32, 4096 <= f.body <= 2 ^ 47. *)
Definition lph_rg : YP09.region := YP09.mkRegion (Some 2%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition lph_G : facts := mkFacts [(23%nat, mkAF 0 (2 ^ 32) 0); (32%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition lph_ss : sstate := mkSS IOS_LPH sr_atoms [lph_rg] None lph_G.
(* +0x1c8 (t = 0) and +0x1f8: f.body_len at sp + 64 (atom 32). *)
Definition lpb_rg : YP09.region := YP09.mkRegion (Some 2%nat) 64 72 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
Definition lpn_ss : sstate := mkSS IOS_LPR sr_atoms [lpb_rg] None (mkFacts [] [] []).
Definition lps_ss : sstate := mkSS IOS_LPS sr_atoms [lpb_rg] None (mkFacts [] [] []).
(* +0x1c8 (t = g_cmd + 40 s): t->len at t + 36 (atom 32); t inside g_cmd's payload and 8-aligned; the shadow entry
   of [t + 36, t + 37). *)
Definition lpt_rg : YP09.region := YP09.mkRegion (Some 10%nat) 36 37 0 0 [YP09.mkChunk 36 (CVal 1 (SOff 32 0))].
Definition lpt_G : facts := mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (10%nat, mkAF TB_g_cmd (TB_g_cmd + 40 * 1023) 3); (32%nat, mkAF 0 255 0)] [] [].
Definition lpt_ss : sstate := mkSS IOS_LPR sr_atoms [lpt_rg] None lpt_G.
Definition lpt_SH : list shent := [mkSHE 10 36 37].

(* ------------------------------------------------------------------ *)
(* The model: tagged_of_m and one round of cmds_loop                   *)
(* ------------------------------------------------------------------ *)

Lemma lp_some_inv : forall (x y : list byte) (a b : option Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as E1 E2. split; [exact (eq_sym E1) | exact (eq_sym E2)]. Qed.

Lemma lp_at8_nonneg : forall l j, 0 <= DSpec.at8 l j.
Proof.
  intros l j. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth j l (DSpec.b8 0))) as R. lia.
Qed.

(* tagged_of_m keeps the world, and a serial it answers is below CMDS_MAX. *)
Lemma lp_tof : forall B b n B' t, TC.tagged_of_m B b n = Some (B', t) ->
  B' = B /\ (forall s, t = Some s -> 0 <= s < TC.CMDS_MAX).
Proof.
  intros B b n B' t H. unfold TC.tagged_of_m in H. cbv zeta in H.
  repeat (match type of H with context [if ?c then _ else _] =>
            let E := fresh "Ec" in destruct c eqn:E; cbv beta iota in H end).
  all: try discriminate H.
  all: destruct (lp_some_inv _ _ _ _ H) as [Ea Eb]; split; [exact Ea|]; intros s Hs; rewrite Eb in Hs;
    try discriminate Hs.
  injection Hs as <-.
  match goal with Ex : (TC.CMDS_MAX <=? _) = false |- _ => apply Z.leb_gt in Ex; split; [|exact Ex] end.
  apply Z.lor_nonneg. split; [apply lp_at8_nonneg | apply Z.shiftl_nonneg; apply lp_at8_nonneg].
Qed.

(* A round at pos < blen asks tagged_of_m of the bytes from pos, which answers at the same world. *)
Lemma lp_cl_tof : forall fuel B body blen pos cmds r, pos < blen ->
  TC.cmds_loop (S fuel) B body blen pos cmds = Some r ->
  exists t, TC.tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos) = Some (B, t).
Proof.
  intros fuel B body blen pos cmds r Hp H. cbn [TC.cmds_loop] in H.
  rewrite (proj2 (Z.ltb_lt pos blen) Hp) in H.
  destruct (TC.tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos)) as [[B' t]|] eqn:Ht; [|discriminate H].
  exists t. rewrite (proj1 (lp_tof _ _ _ _ _ Ht)). reflexivity.
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

Lemma lp_cl_end : forall fuel B body blen pos cmds r, blen <= pos ->
  TC.cmds_loop fuel B body blen pos cmds = Some r -> r = cmds.
Proof.
  intros fuel B body blen pos cmds r Hp H. destruct fuel as [|fuel]; cbn [TC.cmds_loop] in H; [discriminate H|].
  rewrite (proj2 (Z.ltb_ge pos blen) Hp) in H. injection H as <-. reflexivity.
Qed.

(* The length byte of command s, at its numeral offset in g_cmd's row. *)
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

(* y - x as the engine writes it: x * -1 + y, and y + x * -1. *)
Lemma lp_U_sub : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x <= y -> y < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SOff b 0)) = y - x.
Proof.
  intros E a b x y Ha Hb Hxy Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia. rewrite U_SLit.
  change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon, M64.
  rewrite Zplus_mod_idemp_l. replace (x * (2 ^ 64 - 1) + y) with ((y - x) + x * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma lp_U_sub2 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x <= y -> y < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff b 0) (SMd M_MUL (SOff a 0) (SLit (-1)))) = y - x.
Proof.
  intros E a b x y Ha Hb Hxy Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia. rewrite U_SLit.
  change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon, M64.
  rewrite Zplus_mod_idemp_r. replace (y + x * (2 ^ 64 - 1)) with ((y - x) + x * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* The same three as register values. *)
Lemma lp_den_add : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y ->
  x + y < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = w64 (y + x).
Proof.
  intros E a b x y Ha Hb Hx Hy Hxy. rewrite (denot_lit_U E). unfold w64. f_equal.
  rewrite (lp_U_add E a b x y Ha Hb Hx Hy Hxy). ring.
Qed.

Lemma lp_den_sub : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x <= y -> y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SOff b 0)) = w64 (y - x).
Proof.
  intros E a b x y Ha Hb Hxy Hy. rewrite (denot_lit_U E). unfold w64. f_equal. exact (lp_U_sub E a b x y Ha Hb Hxy Hy).
Qed.

Lemma lp_den_sub2 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x <= y -> y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff b 0) (SMd M_MUL (SOff a 0) (SLit (-1)))) = w64 (y - x).
Proof.
  intros E a b x y Ha Hb Hxy Hy. rewrite (denot_lit_U E). unfold w64. f_equal. exact (lp_U_sub2 E a b x y Ha Hb Hxy Hy).
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

(* s2 = s2 + 1, 32-bit and sign-extended (addiw), on s2 = cmds sign-extended. *)
Lemma lp_den_addw : forall E n c, ew E n = Z_to_bv 64 (bv_swrap 32 c) ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (bv_swrap 32 (DSpec.u32 (c + 1))).
Proof.
  intros E n c H.
  assert (X : U E (SOff n 0) mod 2 ^ 32 = c mod 2 ^ 32).
  { rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Zmod_mod, lp_mod64_32. apply lp_swrap_mod. }
  rewrite (denot_lit_U E). apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
  rewrite U_SLit. change (zcanon 1 mod 2 ^ 32) with 1.
  unfold bv_wrap. rewrite Zmod_mod. f_equal.
  apply bv_swrap_congr. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite X, Zplus_mod_idemp_l. unfold DSpec.u32. rewrite Zmod_mod. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Memory: what a read-only run and a leaf keep                        *)
(* ------------------------------------------------------------------ *)

(* A run whose regions have no write window keeps every byte. *)
Lemma lp_ro_frame : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
  intros E rs m m' H Hro x. apply H. intros (r & Hr & Ha).
  pose proof (proj1 (forallb_forall _ _) Hro r Hr) as Hw. cbv beta in Hw. apply Z.leb_le in Hw. lia.
Qed.

Lemma lp_aview_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a Hx. unfold aview, YP09.mbyte, mrestrict. rewrite Hx. reflexivity. Qed.

Lemma lp_present_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a Hx [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hx. exact Hb. Qed.

Lemma lp_rdword_eq : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) ->
  rdword r' a = rdword r a.
Proof.
  intros r r' a H. unfold rdword.
  assert (E0 : r' a = r a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma lp_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) base l,
  (forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m) base l -> garr8 tfibsegs (mrestrict H m') base l.
Proof.
  intros H m m' base l Heq HG. apply (garr8_frame tfibsegs _ _ base l HG).
  intros a Ha. apply (mbyte_of_aview tfibsegs). apply Heq. exact Ha.
Qed.

Lemma lp_val_kept : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
  intros H m m' a n v Heq HV j Hj. rewrite (mbyte_of_aview tfibsegs H H m m' (a + Z.of_nat j)).
  - exact (HV j Hj).
  - apply Heq. lia.
Qed.

Lemma lp_sframe_kept : forall (W : world tfibsegs) mem mem' p fa f,
  (forall a, p <= a < p + 80 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  trans_sframe_at W mem p fa f -> trans_sframe_at W mem' p fa f.
Proof.
  intros W mem mem' p fa f Heq (H0 & H8 & SB & HG & HL & R). split; [exact H0|]. split; [exact H8|].
  exists SB. split; [|split; [exact HL | exact R]].
  apply (lp_garr8_kept _ mem mem' p _); [|exact HG].
  intros a Ha. rewrite length_map, HL in Ha. change (Z.of_nat 80) with 80 in Ha. apply Heq. exact Ha.
Qed.

Lemma lp_saved_kept : forall (W : world tfibsegs) mem mem' regs,
  (forall a, spZ regs - 72 <= a < spZ regs -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ios_saved W mem regs -> ios_saved W mem' regs.
Proof.
  intros W mem mem' regs Heq HS. unfold ios_saved in *. rewrite Forall_forall in HS |- *.
  intros o Ho. rewrite <- (HS o Ho). apply lp_rdword_eq. intros i Hi. apply Heq.
  unfold IOS_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho.
Qed.

(* Byte j of the little-endian value of a byte list of n bytes, and of the n-byte field at offset k of a list. *)
Lemma lp_le_byte_n : forall (l : list byte) (n j : nat) d, length l = n -> (j < n)%nat ->
  YO0f.le_byte (bytes_le_to_Z l) n j = bv_unsigned (nth j l d).
Proof. intros l n j d <- Hj. exact (tw_le_byte_ble l j d Hj). Qed.

Lemma lp_u_at_byte : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (j < n)%nat ->
  YO0f.le_byte (TW.u_at L (Z.of_nat k) n) n j = bv_unsigned (nth (k + j) L (Z_to_bv 8 0)).
Proof.
  intros L k n j Hkn Hj.
  assert (HL : length (TW.sub L (Z.of_nat k) n) = n) by (apply TWL.length_sub; lia).
  unfold TW.u_at.
  rewrite (lp_le_byte_n (TW.sub L (Z.of_nat k) n) n j (Z_to_bv 8 0) HL Hj).
  rewrite (tw_nth_sub L (Z.of_nat k) n j (Z_to_bv 8 0) ltac:(lia) Hj ltac:(lia)).
  replace (Z.to_nat (Z.of_nat k) + j)%nat with (k + j)%nat by lia. reflexivity.
Qed.

(* The n-byte field at offset k of a byte list the view shows at q, as a chunk value. *)
Lemma lp_val_of_garr8 : forall (mm : word -> option byte) q (L : list byte) (k n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> (k + n <= length L)%nat ->
  YI04.val_mem tfibsegs mm (q + Z.of_nat k) n (TW.u_at L (Z.of_nat k) n).
Proof.
  intros mm q L k n Hg Hkn j Hj.
  assert (Hj2 : (k + j < length (map DSpec.bz L))%nat) by (rewrite length_map; lia).
  pose proof (garr8_mbyte tfibsegs mm q (map DSpec.bz L) (k + j) Hg Hj2) as Hm.
  replace (q + Z.of_nat k + Z.of_nat j) with (q + Z.of_nat (k + j)) by lia.
  rewrite Hm. f_equal. f_equal.
  rewrite (lp_u_at_byte L k n j Hkn Hj).
  change (nth (k + j) (map DSpec.bz L) 0) with (nth (k + j) (map DSpec.bz L) (DSpec.bz (Z_to_bv 8 0))).
  rewrite map_nth. reflexivity.
Qed.

Lemma lp_val_at : forall (mm : word -> option byte) q (L : list byte) (k : Z) (n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  YI04.val_mem tfibsegs mm (q + k) n (TW.u_at L k n).
Proof.
  intros mm q L k n Hg Hk Hkn. replace k with (Z.of_nat (Z.to_nat k)) by lia.
  apply (lp_val_of_garr8 mm q L (Z.to_nat k) n Hg). lia.
Qed.

(* The struct's body pointer at a parse that succeeded: the frame's byte 30. *)
Lemma lp_sf_body : forall (fa : Z) (frame : list byte), DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK ->
  TCt.sf_ptr fa (TC.rf frame) (DSpec.sf_body (TC.rf frame)) = fa + 30.
Proof.
  intros fa frame HOK.
  destruct (ios_fields frame HOK)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fbody & _ & _ & _).
  unfold TCt.sf_ptr. rewrite HOK, Z.eqb_refl. cbv iota. rewrite Fbody. reflexivity.
Qed.

(* The bytes from k on of a garr8 array, and the raw bytes of a garr8 array of the view. *)
Lemma lp_garr8_skipn : forall (mm : word -> option byte) q (l : list Z) k,
  garr8 tfibsegs mm q l -> garr8 tfibsegs mm (q + Z.of_nat k) (skipn k l).
Proof.
  intros mm q l k HG j Hj. rewrite length_skipn in Hj.
  assert (Hj' : (k + j < length l)%nat) by lia.
  destruct (HG (k + j)%nat Hj') as [Hv Hr].
  rewrite nth_skipn. replace (q + Z.of_nat k + Z.of_nat j) with (q + Z.of_nat (k + j)) by lia.
  exact (conj Hv Hr).
Qed.

Lemma lp_bytes_of_garr8 : forall (W : world tfibsegs) mem q (L : list byte),
  garr8 tfibsegs (mrestrict (w_H W) mem) q (map DSpec.bz L) -> 0 <= q -> q + Z.of_nat (length L) <= 2 ^ 64 ->
  LMem.bytes_at rsegs mem q L.
Proof.
  intros W mem q L Hg Hq Ht. exact (decode_leafb_bytes_garr8 W mem q L Hg Hq Ht).
Qed.

(* ------------------------------------------------------------------ *)
(* The world at the image view and at the machine view                 *)
(* ------------------------------------------------------------------ *)

(* a byte of G_HARNESS_B is an image byte, so no world hides it *)
Lemma lp_vis_G : forall (W : world tfibsegs) x, inG TG.G_HARNESS_B x -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx.
  pose proof (trans_g_img x Hx) as Hi.
  pose proof (transportb_segs_low x Hi) as Hl. unfold kLowMemEnd in Hl.
  apply (hidden_not_img tfibsegs W (Z_to_bv 64 x)).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hi.
Qed.

Lemma lp_vis : forall (W : world tfibsegs) x, tw_in TMAP_B x -> w_H W (Z_to_bv 64 x) = false.
Proof. intros W x Hx. exact (lp_vis_G W x (ios_tw_in_G x Hx)). Qed.

(* a visible byte: the image view is the machine view *)
Lemma lp_aview_csw : forall (W : world tfibsegs) (m : word -> option byte) x, w_H W (Z_to_bv 64 x) = false ->
  aview tfibsegs (w_H W) m x = CSW.csw_view m x.
Proof.
  intros W m x Hx. unfold CSW.csw_view, aview, mbyte, mrestrict, LMem.mrd, LMem.wa.
  rewrite Hx. reflexivity.
Qed.

Lemma lp_tw_raw : forall (W : world tfibsegs) (m : word -> option byte) Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_B (CSW.csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_B (aview tfibsegs (w_H W) m) (CSW.csw_view m) Bw H).
  intros x Hx. symmetry. exact (lp_aview_csw W m x (lp_vis W x Hx)).
Qed.

(* ------------------------------------------------------------------ *)
(* The call of tagged_of                                               *)
(* ------------------------------------------------------------------ *)

Section tg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B).

(* tagged_of's leaf statement, read at the walk's own G journal (gx_call_leaf over the leaf bridge
   decode_leafb_journal): the journal and every byte outside the leaf's ESTACK window below sp are kept, the
   callee-saved registers are kept, and a0 is tagged_of_res t. The leaf's own premises are the call state's facts
   (a0 = b, a1 = n, the bytes l at b, the world, tagged_of_m), the stack and runtime cells the journal gives, and
   when 3 <= n the three bytes at b: off the leaf's frame, addressable, visible with their shadow bytes. *)
Lemma lp_tagged :
  forall (STK sp0 : Z) FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (o b n : Z) (l Bw : list byte) (t : option Z),
  transport_cells B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx') ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsT 1) ->
  YK11.getr regsT 10 = Z_to_bv 64 b -> YK11.getr regsT 11 = Z_to_bv 64 n ->
  0 <= n < 2 ^ 64 -> 0 < b ->
  LMem.bytes_at rsegs memT b l ->
  tw_at TMAP_B (CSW.csw_view memT) Bw ->
  TC.tagged_of_m Bw l n = Some (Bw, t) ->
  (3 <= n -> b + 3 <= spZ regsT - 16 \/ spZ regsT <= b) ->
  (3 <= n -> FCB.addressable memT b 3) ->
  (3 <= n -> forall i, 0 <= i < 3 -> w_H W (Z_to_bv 64 (b + i)) = false) ->
  (3 <= n -> forall s, FCB.shadow_addr b <= s <= FCB.shadow_addr (b + 2) -> w_H W (Z_to_bv 64 s) = false) ->
  SRr tfibsegs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 TOC.TAGGED_OF) memT (YK11.seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom tfibsegs)) md2 /\
       ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 (TOC.tagged_of_res t) /\
        (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
           aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
        (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT o b n l Bw t
    HCELLS LEAF HJ Hsp Hal Hneg Hbud Hgp Htp Hra H10 H11 Hn Hb0 HBL HTW HTM HOFFB HADB HVB HVS.
  apply (@gx_call_leaf fx rc tfib_sink_head tfibsegs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ (YK11.getr regsT 1)
           (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 (TOC.tagged_of_res t) /\
              (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
                 aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
              (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)) HJ).
  intros memS HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  eapply SRr_mono.
  { apply (@decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k o TOC.TAGGED_OF (Some (TOC.tagged_of_res t)) [] (fun _ => Bw = Bw) HJi
             Hsp Hal Hneg Hbud Hra Hgp Htp).
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold transport_leaf_at, LTO.transport_tagged_of_cg in LF.
      specialize (LF lyc Sc W regsT memT mdc (sp0 - STK) Bw Bw b n l t HPRE).
      cbv zeta in LF.
      assert (HSP : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
      unfold ESTACK in Hbud.
      apply LF; clear LF.
      + exact H10.
      + exact H11.
      + exact Hn.
      + exact Hb0.
      + exact HBL.
      + exact HTW.
      + exact HTM.
      + rewrite HSP. apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi); lia.
      + rewrite HSP. unfold TOC.TAGGED_OF_FRAME. lia.
      + unfold AKA.off_stk. rewrite HSP.
        unfold TOC.TAGGED_OF_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
      + exact (decode_leafb_asan_cells B HCELLS lyc Sc W memT mdc (proj1 HPRE)).
      + rewrite HSP. apply (@decode_leafb_app_stack rc). unfold TOC.TAGGED_OF_FRAME. lia.
      + rewrite HSP. apply (@decode_leafb_app_stack rc). lia.
      + unfold AKA.off_stk. rewrite HSP. unfold TOC.TAGGED_OF_FRAME, FCB.GOT_CELL_K. lia.
      + unfold AKA.off_stk. rewrite HSP. unfold TOC.TAGGED_OF_FRAME, FCB.CELL_K. lia.
      + intros H3. unfold AKA.off_stk. rewrite HSP. unfold TOC.TAGGED_OF_FRAME.
        specialize (HOFFB H3). rewrite Hsp in HOFFB. lia.
      + exact HADB.
      + rewrite HSP. apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi);
          unfold TOC.TAGGED_OF_FRAME; lia.
      + exact (proj1 (decode_leafb_rng_cells W)).
      + exact (proj2 (decode_leafb_rng_cells W)).
      + apply decode_rng_vis; [unfold TOC.TAGGED_OF_NCMD, TB_g_ncmd; lia | unfold TOC.TAGGED_OF_NCMD, TB_g_ncmd; lia |].
        intros i Hi. apply lp_vis. exists TW.OFF_g_ncmd, TB_g_ncmd, TW.SZ_g_ncmd.
        split; [exact TMAP_B_g_ncmd | unfold TOC.TAGGED_OF_NCMD, TW.SZ_g_ncmd in *; lia].
      + intros H3. destruct (HADB H3) as (_ & _ & Hend & _). unfold FCB.APPMEM_END in Hend.
        apply decode_rng_vis; [lia | lia | exact (HVB H3)].
      + intros H3. destruct (HADB H3) as (_ & _ & Hend & _). unfold FCB.APPMEM_END in Hend.
        apply decode_rng_vis.
        * unfold FCB.shadow_addr, FCB.ASAN_K. pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)). lia.
        * unfold FCB.shadow_addr, FCB.ASAN_K. Z.div_mod_to_equations. lia.
        * intros i Hi. apply (HVS H3).
          assert (FCB.shadow_addr b <= FCB.shadow_addr (b + 2))
            by (unfold FCB.shadow_addr; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
          lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & HJ2 & HP & Hres & Heff & Hgr & _).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  split; [exact HP|]. split; [exact (Hres _ eq_refl)|]. split; [|exact Hgr].
  intros a Ha Hw. apply (Heff a Ha Hw). intros Hx. unfold LCK.in_wr in Hx. inversion Hx.
Qed.

End tg.

(* ------------------------------------------------------------------ *)
(* Valuations, registers and the callee-saved set                      *)
(* ------------------------------------------------------------------ *)

Lemma lp_ew_set : forall E n w i, i <> n -> ew (ewset E n w) i = ew E i.
Proof. intros E n w i H. unfold ewset. cbn [ew]. destruct (Nat.eqb_spec i n); [contradiction | reflexivity]. Qed.

Lemma lp_agree_set : forall A E n w, env_agree 32 A E -> (32 <= n)%nat -> env_agree 32 A (ewset E n w).
Proof.
  intros A E n w [H1 H2] Hn. split; [|exact H2].
  intros i Hi. rewrite lp_ew_set by lia. exact (H1 i Hi).
Qed.

(* A register of the callee-saved set, kept by a call (aregs_preserved). *)
Lemma lp_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

Ltac lp_cs :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.

Lemma lp_skipn_map : forall {A C : Type} (f : A -> C) (l : list A) k, skipn k (map f l) = map f (skipn k l).
Proof. intros A C f l. induction l as [|x l IH]; intros k; destruct k; cbn; [reflexivity .. | apply IH]. Qed.

(* The registers the loop keeps, as numerals of the callee-saved set and of LP_KP. *)
Lemma lp_kp_cs : forall x, In x LP_KP -> acallee_saved (bv_unsigned x).
Proof.
  intros x Hx. unfold LP_KP in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [lp_cs |]). destruct Hx.
Qed.

Lemma lp_kp_24 : forall r, 24 <= r <= 27 -> In (Z_to_bv 5 r) LP_KP.
Proof.
  intros r Hr. assert (E : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct E as [-> | [-> | [-> | ->]]]; unfold LP_KP; cbn [In];
    repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* The write rights of a run whose regions are all read-only. *)
Ltac lp_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The value of register r in the machine state HS describes (st_ok_pi, or st_ok at a call). *)
Ltac lp_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The valuation of a fresh state: the registers r and the extra atoms ex from 32 on. *)
Section ev. Context {rc : YM05.RunCeil}.
Definition lp_E (r : bvmap 5 word) (ex : list word) : env := Eimg (PI := PI_transportb) (Ereg r ex).

Lemma lp_Ereg : forall (r : bvmap 5 word) ex n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr r x = w64 v ->
  ew (lp_E r ex) n = Z_to_bv 64 v.
Proof. intros r ex n x v Hn H. unfold lp_E. rewrite (ew_Eimg_Ereg_nat r ex n x Hn). exact H. Qed.

Lemma lp_ew_ex : forall (r : bvmap 5 word) ex j, (32 + j < 240)%nat ->
  ew (lp_E r ex) (32 + j) = nth j ex (Z_to_bv 64 0).
Proof. intros r ex j Hj. unfold lp_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma lp_agree0 : forall (r : bvmap 5 word) ex, env_agree 32 (Ereg r ex) (lp_E r ex).
Proof.
  intros r ex. split; [intros n Hn; unfold lp_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.
End ev.

Ltac lp_agree := first [exact (lp_agree0 _ _) | apply lp_agree_set; [lp_agree | lia]].

(* The registers of l a run kept, from the start registers r0 (valuation lp_E r0 ex, perhaps extended). *)
Ltac lp_kr r0 ex l KR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) |- _ =>
    assert (KR : forall x, In x l -> YK11.getr (ms_regs msx) x = YK11.getr r0 x)
      by exact (regs_kept_of_st_ok_pi Ex ssx (restrict Hh msx) r0 ex l HS ltac:(lp_agree)
                  ltac:(vm_compute; reflexivity))
  | HS : OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) |- _ =>
    assert (KR : forall x, In x l -> YK11.getr (ms_regs msx) x = YK11.getr r0 x)
      by exact (regs_kept_of_st_ok sg Ex ssx (restrict Hh msx) r0 ex l HS ltac:(lp_agree)
                  ltac:(vm_compute; reflexivity))
  end.

Section loop. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HGX : gx_ok segs B TG.G_HARNESS_B.
Hypothesis HCELLS : transport_cells B.
Hypothesis LEAF : forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx'.
Hypothesis HZC : decode_zshadow_at B TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
(* The journal's fixed part; the cut's state (ly2, S2, W2, mem2) and registers regs2 (sp = the walk's sp); the body
   (bp = f.body, blen = f.body_len, body = its bytes, to the frame's end), the world Bm the model's loop reads, and the
   model's answer final; the continuation Q. *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)).
Variables (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (k : Z).
Variable regs2 : bvmap 5 word.
Variables (bp blen final : Z) (body Bm : list byte).
Variable Q : world segs -> config -> Prop.
Hypothesis Hal : (spZ regs2 - sp0) mod 16 = 0.
Hypothesis Hsp1 : spZ regs2 <= sp0.
Hypothesis Hsp2 : sp0 - STK + ESTACK <= spZ regs2.
Hypothesis Hlow : 0x7fff7f800000 <= sp0 - STK.
Hypothesis H47 : sp0 <= 2 ^ 47.
Hypothesis R3 : YK11.getr regs2 3 = w64 (as_gp B).
Hypothesis R4 : YK11.getr regs2 4 = w64 (as_tp B).
Hypothesis R20 : YK11.getr regs2 20 = w64 SHADOW_OFF.
Hypothesis Htw : tw_at TMAP_B (aview segs (w_H W2) mem2) Bm.
Hypothesis HGB : garr8 segs (mrestrict (w_H W2) mem2) bp (map DSpec.bz body).
Hypothesis HBL : blen <= Z.of_nat (length body).
Hypothesis Hbp : 4096 <= bp.
Hypothesis Hbe : bp + Z.of_nat (length body) <= 2 ^ 47.
Hypothesis Hblen : 0 < blen < 2 ^ 32.
Hypothesis HAM : amem_range bp blen.
Hypothesis HRAB : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF bp blen.
Hypothesis HOFF : bp + Z.of_nat (length body) <= spZ regs2 - ESTACK \/ spZ regs2 <= bp.
Hypothesis HS56 : val_mem segs (mrestrict (w_H W2) mem2) (spZ regs2 + 56) 8 bp.
Hypothesis HS64 : val_mem segs (mrestrict (w_H W2) mem2) (spZ regs2 + 64) 8 blen.

Local Abbreviation lp_at pc r m md := (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) m (YK11.seg_rom segs)) md).

(* What holds of the memory at every point of the loop: the journal, every byte outside tagged_of's window
   [sp - ESTACK, sp) as at the cut, every byte present at the cut present. *)
Definition lp_mem (m : word -> option byte) (md : Model) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m md k /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs2 - ESTACK <= a < spZ regs2) ->
     aview segs (w_H W2) m a = aview segs (w_H W2) mem2 a) /\
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m a).
(* The registers the loop keeps; s7 = at, s2 = cmds (sign-extended) at a round's step; and a1 = body_len at its head. *)
Definition lp_kept (r : bvmap 5 word) : Prop := forall x, In x LP_KP -> YK11.getr r x = YK11.getr regs2 x.
Definition lp_invS (r : bvmap 5 word) (pos cmds : Z) : Prop :=
  YK11.getr r 23 = w64 pos /\ YK11.getr r 18 = w64 (bv_swrap 32 cmds) /\ lp_kept r.
Definition lp_inv (r : bvmap 5 word) (pos cmds : Z) : Prop := lp_invS r pos cmds /\ YK11.getr r 11 = w64 blen.
(* What the next round gives. *)
Definition lp_K (fuel : nat) : Prop :=
  forall (r : bvmap 5 word) (m : word -> option byte) (md : Model) (pos cmds : Z),
    0 <= pos < blen -> 0 <= cmds < 2 ^ 32 -> lp_inv r pos cmds -> lp_mem m md ->
    TC.cmds_loop fuel Bm body blen pos cmds = Some final -> SRr segs W2 (lp_at IOS_LPH r m md) Q.

Hypothesis HCMDS : forall (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model),
  lp_mem mem3 md3 -> YK11.getr regs3 18 = w64 (bv_swrap 32 final) -> 0 <= final < 2 ^ 32 -> lp_kept regs3 ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) regs3 mem3 md3) Q.

(* ---- the bytes the loop reads, at every memory of lp_mem ---- *)

Lemma lp_geo : 0x7fff7f800000 + ESTACK <= spZ regs2 /\ spZ regs2 <= 2 ^ 47 /\ ESTACK = 4096.
Proof. pose proof Hsp1. pose proof Hsp2. pose proof Hlow. pose proof H47. split; [lia | split; [lia | reflexivity]]. Qed.

Lemma lp_out_hi : forall a, spZ regs2 <= a < 2 ^ 64 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs2 - ESTACK <= a < spZ regs2).
Proof. intros a Ha. pose proof lp_geo as (G1 & G2 & G3). lia. Qed.

Lemma lp_out_lo : forall a, 0 <= a < 0x7fff7f800000 ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs2 - ESTACK <= a < spZ regs2).
Proof. intros a Ha. pose proof lp_geo as (G1 & G2 & G3). lia. Qed.

Lemma lp_out_body : forall a, bp <= a < bp + Z.of_nat (length body) ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs2 - ESTACK <= a < spZ regs2).
Proof.
  intros a Ha. pose proof lp_geo as (G1 & G2 & G3). pose proof Hbp. pose proof Hbe. pose proof HOFF as [HO|HO]; lia.
Qed.

Lemma lp_mem_ext : forall m m' md md', lp_mem m md -> (forall x, m' x = m x) ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m' md' k -> lp_mem m' md'.
Proof.
  intros m m' md md' (HJ & HK & HG) Hx HJ'. split; [exact HJ'|]. split.
  - intros a Ha Hn. rewrite (lp_aview_ext _ m m' a Hx). exact (HK a Ha Hn).
  - intros a Ha. apply (lp_present_ext _ m m' a Hx). exact (HG a Ha).
Qed.

Lemma lp_mem_call : forall m md m' md', lp_mem m md ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs2 - ESTACK <= a < spZ regs2) ->
     aview segs (w_H W2) m' a = aview segs (w_H W2) m a) ->
  (forall a, apresent (w_H W2) m a -> apresent (w_H W2) m' a) -> lp_mem m' md'.
Proof.
  intros m md m' md' (HJ & HK & HG) HJ' HK' HG'. split; [exact HJ'|]. split.
  - intros a Ha Hn. rewrite (HK' a Ha Hn). exact (HK a Ha Hn).
  - intros a Ha. exact (HG' a (HG a Ha)).
Qed.

Lemma lp_val56 : forall m md, lp_mem m md -> val_mem segs (mrestrict (w_H W2) m) (spZ regs2 + 56) 8 bp.
Proof.
  intros m md (_ & HK & _). apply (lp_val_kept (w_H W2) mem2 m (spZ regs2 + 56) 8 bp); [|exact HS56].
  intros i Hi. pose proof lp_geo as (G1 & G2 & G3).
  destruct (lp_out_hi (spZ regs2 + 56 + i) ltac:(lia)) as [A1 A2].
  exact (HK _ A1 A2).
Qed.

Lemma lp_val64 : forall m md, lp_mem m md -> val_mem segs (mrestrict (w_H W2) m) (spZ regs2 + 64) 8 blen.
Proof.
  intros m md (_ & HK & _). apply (lp_val_kept (w_H W2) mem2 m (spZ regs2 + 64) 8 blen); [|exact HS64].
  intros i Hi. pose proof lp_geo as (G1 & G2 & G3).
  destruct (lp_out_hi (spZ regs2 + 64 + i) ltac:(lia)) as [A1 A2].
  exact (HK _ A1 A2).
Qed.

Lemma lp_tw_m : forall m md, lp_mem m md -> tw_at TMAP_B (aview segs (w_H W2) m) Bm.
Proof.
  intros m md (_ & HK & _). apply (tw_kept TMAP_B _ _ Bm Htw). intros x Hx.
  pose proof (inG_G_HARNESS_hull x (ios_tw_in_G x Hx)) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  destruct (lp_out_lo x ltac:(lia)) as [A1 A2]. exact (HK x A1 A2).
Qed.

Lemma lp_garr_m : forall m md, lp_mem m md -> garr8 segs (mrestrict (w_H W2) m) bp (map DSpec.bz body).
Proof.
  intros m md (_ & HK & _). apply (lp_garr8_kept _ mem2 m bp _); [|exact HGB].
  intros a Ha. rewrite length_map in Ha. destruct (lp_out_body a Ha) as [A1 A2]. exact (HK a A1 A2).
Qed.

Lemma lp_ra_m : forall m md, lp_mem m md -> range_addressable (aview segs (w_H W2) m) SHADOW_OFF bp blen.
Proof.
  intros m md (_ & HK & _) x Hx. destruct (HRAB x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  pose proof Hbe. pose proof HBL.
  assert (Hd : x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
  unfold shadow_of_addr in Hsv |- *.
  destruct (lp_out_lo (SHADOW_OFF + x / 8) ltac:(unfold SHADOW_OFF; lia)) as [A1 A2].
  rewrite (HK _ A1 A2). exact Hsv.
Qed.

Lemma lp_app : forall i, 0 <= i < blen -> FCB.app_mem (bp + i).
Proof.
  intros i Hi. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof Hbp.
  unfold FCB.app_mem, FCB.LOWMEM_END, FCB.HIGHMEM_BEG, FCB.APPMEM_END.
  pose proof HAM as HA. unfold amem_range in HA. destruct HA as [HA|HA]; [left | right]; lia.
Qed.

Lemma lp_body_vis : forall i, 0 <= i < Z.of_nat (length body) -> w_H W2 (Z_to_bv 64 (bp + i)) = false.
Proof.
  intros i Hi.
  assert (Hj : (Z.to_nat i < length (map DSpec.bz body))%nat) by (rewrite length_map; lia).
  pose proof (garr8_mbyte segs _ bp _ (Z.to_nat i) HGB Hj) as Hm.
  rewrite Z2Nat.id in Hm by lia.
  exact (decode_leafb_mbyte_vis W2 mem2 _ _ Hm).
Qed.

Lemma lp_sh_vis : forall x, bp <= x < bp + blen -> w_H W2 (Z_to_bv 64 (FCB.shadow_addr x)) = false.
Proof.
  intros x Hx. destruct (HRAB x Hx) as (sv & Hsv & _).
  assert (E : FCB.shadow_addr x = shadow_of_addr SHADOW_OFF x)
    by (unfold FCB.shadow_addr, FCB.ASAN_K, shadow_of_addr, SHADOW_OFF; lia).
  rewrite E. exact (decode_leafb_aview_vis W2 mem2 _ _ Hsv).
Qed.

(* ---- the step: +0x1f8 .. +0x208 ---- *)

(* a1 = body_len, at += step, cmds += 1 (addiw), `bltu at,a1` to the next round's head, else `j` IOS_CMDS. *)
Lemma lp_bump : forall (fuel : nat) (r : bvmap 5 word) (m : word -> option byte) (md : Model) (pos cmds step : Z),
  0 <= pos < blen -> 1 <= step <= blen + 255 -> 0 <= cmds < 2 ^ 32 ->
  lp_invS r pos cmds -> YK11.getr r 10 = w64 step -> lp_mem m md ->
  TC.cmds_loop fuel Bm body blen (pos + step) (DSpec.u32 (cmds + 1)) = Some final ->
  lp_K fuel -> SRr segs W2 (lp_at IOS_LPS r m md) Q.
Proof.
  intros fuel r m md pos cmds step Hpos Hst Hcm Hinv R10 HM Hm HK.
  pose proof Hinv as (R23 & R18 & HKP).
  pose proof HM as (HJ & _ & _).
  pose proof lp_geo as (G1 & G2 & G3).
  assert (Usp : spZ r = spZ regs2) by (unfold spZ; rewrite (HKP 2%bv ltac:(lp_kin)); reflexivity).
  pose proof (lp_val64 m md HM) as V64.
  pose proof (lp_Ereg r [w64 blen] 10 10%bv step eq_refl R10) as X10.
  pose proof (lp_Ereg r [w64 blen] 23 23%bv pos eq_refl R23) as X23.
  pose proof (lp_Ereg r [w64 blen] 18 18%bv (bv_swrap 32 cmds) eq_refl R18) as X18.
  assert (X32 : ew (lp_E r [w64 blen]) 32 = Z_to_bv 64 blen) by exact (lp_ew_ex r [w64 blen] 0 ltac:(lia)).
  assert (U2 : bv_unsigned (ew (lp_E r [w64 blen]) 2) = spZ regs2)
    by (unfold lp_E; rewrite (ew_Eimg_Ereg_nat r [w64 blen] 2 2%bv eq_refl); exact Usp).
  assert (HS : st_ok_pi segs VAL (lp_E r [w64 blen]) lps_ss
    (restrict (w_H W2) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_LPS)) m (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lps_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold lpb_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ (spZ regs2) 64 8 (SOff 32 0) blen);
        [exact (lp_den0 _ 32 blen X32 ltac:(lia)) | cbn; lia | cbn; lia | exact V64].
    - exact (conj I I).
    - exact (conj I (conj I I)). }
  assert (HEI : img_env VAL A_LIM (lp_E r [w64 blen])) by (unfold lp_E; apply Eimg_env).
  assert (SHOK : sh_ok segs lp_Bx [] (lp_E r [w64 blen]) (mrestrict (w_H W2) m)) by apply Forall_nil.
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transportb)) as BR.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lp_awr. }
  pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm1.
  clear HF HFr HG.
  rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* at + step < body_len: the next round *)
    rewrite branch_ltu_U in Hc.
    rewrite (lp_U_add _ 10 23 step pos X10 X23) in Hc by lia.
    rewrite (U_atom _ 32 blen X32) in Hc by lia.
    apply Z.ltb_lt in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { lp_awr. }
    pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm2.
    clear HF HFr HG.
    lp_reg HS (23%bv : bv 5) (w64 (pos + step)) Q23
      ltac:(exact (lp_den_add _ 10 23 step pos X10 X23 ltac:(lia) ltac:(lia) ltac:(lia))).
    lp_reg HS (18%bv : bv 5) (w64 (bv_swrap 32 (DSpec.u32 (cmds + 1)))) Q18 ltac:(apply lp_den_addw; exact X18).
    lp_reg HS (11%bv : bv 5) (w64 blen) Q11 ltac:(exact (lp_den0 _ 32 blen X32 ltac:(lia))).
    lp_kr r [w64 blen] LP_KP KR.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ ?mm _) ?mdx) _ =>
      change (SRr segs W2 (lp_at IOS_LPH rr mm mdx) Q) end.
    apply (HK _ _ _ (pos + step) (DSpec.u32 (cmds + 1))).
    + lia.
    + unfold DSpec.u32. apply Z.mod_pos_bound. lia.
    + split; [split; [exact Q23 | split; [exact Q18 |]] | exact Q11].
      intros x Hx. rewrite (KR x Hx). exact (HKP x Hx).
    + apply (lp_mem_ext m _ md _ HM); [intros x; rewrite Hm2, Hm1; reflexivity | exact HJ].
    + exact Hm.
  - (* at + step >= body_len: the exit, s2 = cmds + 1 = the model's answer *)
    rewrite branch_ltu_U in Hc.
    rewrite (lp_U_add _ 10 23 step pos X10 X23) in Hc by lia.
    rewrite (U_atom _ 32 blen X32) in Hc by lia.
    apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_CMDS.
    { lp_awr. }
    pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm2.
    clear HF HFr HG.
    lp_reg HS (18%bv : bv 5) (w64 (bv_swrap 32 (DSpec.u32 (cmds + 1)))) Q18 ltac:(apply lp_den_addw; exact X18).
    lp_kr r [w64 blen] LP_KP KR.
    pmkst HS.
    assert (Ef : final = DSpec.u32 (cmds + 1))
      by exact (lp_cl_end fuel Bm body blen (pos + step) _ final ltac:(lia) Hm).
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ ?mm _) ?mdx) _ =>
      change (SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_CMDS) rr mm mdx) Q) end.
    apply HCMDS.
    + apply (lp_mem_ext m _ md _ HM); [intros x; rewrite Hm2, Hm1; reflexivity | exact HJ].
    + rewrite Ef. exact Q18.
    + rewrite Ef. unfold DSpec.u32. apply Z.mod_pos_bound. lia.
    + intros x Hx. rewrite (KR x Hx). exact (HKP x Hx).
Qed.

(* ---- the return of tagged_of: +0x1c8 ---- *)

(* t = 0: `beq a0,zero` to +0x1f0 (its other arm refuted), a0 = body_len - at; to the step. *)
Lemma lp_ret_none : forall (fuel : nat) (r : bvmap 5 word) (m : word -> option byte) (md : Model) (pos cmds : Z),
  0 <= pos < blen -> 0 <= cmds < 2 ^ 32 ->
  lp_invS r pos cmds -> YK11.getr r 10 = w64 0 -> lp_mem m md ->
  TC.cmds_loop fuel Bm body blen (pos + (blen - pos)) (DSpec.u32 (cmds + 1)) = Some final ->
  lp_K fuel -> SRr segs W2 (lp_at IOS_LPR r m md) Q.
Proof.
  intros fuel r m md pos cmds Hpos Hcm Hinv R10 HM Hm HK.
  pose proof Hinv as (R23 & R18 & HKP).
  pose proof HM as (HJ & _ & _).
  pose proof lp_geo as (G1 & G2 & G3).
  assert (Usp : spZ r = spZ regs2) by (unfold spZ; rewrite (HKP 2%bv ltac:(lp_kin)); reflexivity).
  pose proof (lp_val64 m md HM) as V64.
  pose proof (lp_Ereg r [w64 blen] 10 10%bv 0 eq_refl R10) as X10.
  pose proof (lp_Ereg r [w64 blen] 23 23%bv pos eq_refl R23) as X23.
  assert (X32 : ew (lp_E r [w64 blen]) 32 = Z_to_bv 64 blen) by exact (lp_ew_ex r [w64 blen] 0 ltac:(lia)).
  assert (U2 : bv_unsigned (ew (lp_E r [w64 blen]) 2) = spZ regs2)
    by (unfold lp_E; rewrite (ew_Eimg_Ereg_nat r [w64 blen] 2 2%bv eq_refl); exact Usp).
  assert (HS : st_ok_pi segs VAL (lp_E r [w64 blen]) lpn_ss
    (restrict (w_H W2) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_LPR)) m (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lpn_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold lpb_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ (spZ regs2) 64 8 (SOff 32 0) blen);
        [exact (lp_den0 _ 32 blen X32 ltac:(lia)) | cbn; lia | cbn; lia | exact V64].
    - exact (conj I I).
    - exact (conj I (conj I I)). }
  assert (HEI : img_env VAL A_LIM (lp_E r [w64 blen])) by (unfold lp_E; apply Eimg_env).
  assert (SHOK : sh_ok segs lp_Bx [] (lp_E r [w64 blen]) (mrestrict (w_H W2) m)) by apply Forall_nil.
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transportb)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* t = 0: a0 = body_len - at *)
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_LPS.
    { lp_awr. }
    pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm1.
    clear HF HFr HG.
    lp_reg HS (10%bv : bv 5) (w64 (blen - pos)) Q10
      ltac:(exact (lp_den_sub _ 23 32 pos blen X23 X32 ltac:(lia) ltac:(lia))).
    lp_kr r [w64 blen] LP_KP KR.
    lp_kr r [w64 blen] LP_SC KR2.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ ?mm _) ?mdx) _ =>
      change (SRr segs W2 (lp_at IOS_LPS rr mm mdx) Q) end.
    apply (lp_bump fuel _ _ _ pos cmds (blen - pos) Hpos ltac:(lia) Hcm).
    + split; [rewrite (KR2 23%bv ltac:(unfold LP_SC; cbn [In]; auto)); exact R23|].
      split; [rewrite (KR2 18%bv ltac:(unfold LP_SC; cbn [In]; auto)); exact R18|].
      intros x Hx. rewrite (KR x Hx). exact (HKP x Hx).
    + exact Q10.
    + apply (lp_mem_ext m _ md _ HM); [intros x; rewrite Hm1; reflexivity | exact HJ].
    + exact Hm.
    + exact HK.
  - (* t <> 0: never *)
    exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom _ 10 0 X10) in Hc by lia. rewrite U_SLit in Hc.
    vm_compute in Hc. discriminate Hc.
Qed.

(* t = g_cmd + 40 s, s < CMDS_MAX: the facts of t decide `beq a0,zero` and `bne (t & 3),0`, the shadow entry of
   g_cmd's payload decides the check of t + 36; a0 = t->len (the world's Cmd_len); to the step. *)
Lemma lp_ret_some : forall (fuel : nat) (r : bvmap 5 word) (m : word -> option byte) (md : Model) (pos cmds s : Z),
  0 <= pos < blen -> 0 <= cmds < 2 ^ 32 -> 0 <= s < TC.CMDS_MAX ->
  lp_invS r pos cmds -> YK11.getr r 10 = w64 (TB_g_cmd + 40 * s) -> lp_mem m md ->
  TW.Cmd_len Bm s <> 0 ->
  TC.cmds_loop fuel Bm body blen (pos + TW.Cmd_len Bm s) (DSpec.u32 (cmds + 1)) = Some final ->
  lp_K fuel -> SRr segs W2 (lp_at IOS_LPR r m md) Q.
Proof.
  intros fuel r m md pos cmds s Hpos Hcm Hs Hinv R10 HM Hnz Hm HK.
  pose proof Hinv as (R23 & R18 & HKP).
  pose proof HM as (HJ & _ & _).
  pose proof lp_geo as (G1 & G2 & G3).
  pose proof (ajournal_gx_AR tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (EGC : TB_g_cmd = 6180992) by reflexivity.
  assert (HSZ : TW.SZ_g_cmd = 40960) by reflexivity.
  unfold TC.CMDS_MAX in Hs.
  pose proof (lp_tw_m m md HM) as Htwm.
  pose proof (tw_read_val segs (mrestrict (w_H W2) m) TMAP_B Bm TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 36) 1
    TMAP_B_ok Htwm TMAP_B_g_cmd ltac:(lia) ltac:(rewrite HSZ; lia)) as Vc.
  rewrite <- lp_clen_at in Vc.
  pose proof (TWL.u_at_range Bm (TW.OFF_g_cmd + (40 * s + 36)) 1) as Rc. rewrite <- lp_clen_at in Rc.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Rc.
  remember (TW.Cmd_len Bm s) as cl eqn:Ecl.
  destruct (decode_zshadow_ra B ly2 S2 W2 m _ TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) TB_g_cmd TW.SZ_g_cmd HAR HZC
      ltac:(rewrite HSZ; lia) ltac:(rewrite EGC; vm_compute; discriminate)
      ltac:(rewrite EGC, HSZ; vm_compute; discriminate)) as [HRAC _].
  assert (R20' : YK11.getr r 20 = w64 SHADOW_OFF) by (rewrite (HKP 20%bv ltac:(lp_kin)); exact R20).
  pose proof (lp_Ereg r [w64 cl] 10 10%bv _ eq_refl R10) as X10.
  pose proof (lp_Ereg r [w64 cl] 20 20%bv _ eq_refl R20') as X20.
  pose proof (lp_Ereg r [w64 cl] 23 23%bv pos eq_refl R23) as X23.
  assert (X32 : ew (lp_E r [w64 cl]) 32 = Z_to_bv 64 cl) by exact (lp_ew_ex r [w64 cl] 0 ltac:(lia)).
  assert (U10 : bv_unsigned (ew (lp_E r [w64 cl]) 10) = TB_g_cmd + 40 * s)
    by (rewrite X10; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew (lp_E r [w64 cl]) 20) = SHADOW_OFF)
    by (rewrite X20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (lp_E r [w64 cl]) 32) = cl) by (rewrite X32; apply unsigned_lit_small; lia).
  assert (HAL : (TB_g_cmd + 40 * s) mod 2 ^ 3 = 0).
  { rewrite EGC. replace (6180992 + 40 * s) with ((772624 + 5 * s) * 2 ^ 3) by ring. apply Z_mod_mult. }
  assert (HS : st_ok_pi segs VAL (lp_E r [w64 cl]) lpt_ss
    (restrict (w_H W2) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_LPR)) m (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lpt_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold lpt_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ (TB_g_cmd + 40 * s) 36 1 (SOff 32 0) cl);
        [exact (lp_den0 _ 32 cl X32 ltac:(lia)) | cbn; lia | cbn; lia |].
      replace (TB_g_cmd + 40 * s + 36) with (TB_g_cmd + (40 * s + 36)) by ring. exact Vc.
    - exact (conj I I).
    - unfold facts_ok, lpt_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U20, U10, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite HAL.
      unfold SHADOW_OFF. repeat split; try exact I; lia. }
  assert (HSH : sh_ok segs lp_Bx lpt_SH (lp_E r [w64 cl]) (mrestrict (w_H W2) m)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W2) m (lp_E r [w64 cl]) lp_Bx 10%nat TB_g_cmd TW.SZ_g_cmd
      (TB_g_cmd + 40 * s) 36 37 HRAC).
    - unfold lp_Bx. apply U_atom; [exact X20 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact X10 | lia].
    - lia.
    - rewrite HSZ. lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia. }
  assert (HEI : img_env VAL A_LIM (lp_E r [w64 cl])) by (unfold lp_E; apply Eimg_env).
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUNTO.
  paj_run_to_tok RUNTO HS HJ HSH YC4b.Bspan IOS_LPS.
  { lp_awr. }
  pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm1.
  clear HF HFr HG.
  lp_reg HS (10%bv : bv 5) (w64 cl) Q10
    ltac:(cbn [sv_denot]; rewrite ?lp_ew_set by lia; rewrite X32, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
  lp_kr r [w64 cl] LP_KP KR.
  lp_kr r [w64 cl] LP_SC KR2.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ ?mm _) ?mdx) _ =>
    change (SRr segs W2 (lp_at IOS_LPS rr mm mdx) Q) end.
  apply (lp_bump fuel _ _ _ pos cmds cl Hpos ltac:(lia) Hcm).
  - split; [rewrite (KR2 23%bv ltac:(unfold LP_SC; cbn [In]; auto)); exact R23|].
    split; [rewrite (KR2 18%bv ltac:(unfold LP_SC; cbn [In]; auto)); exact R18|].
    intros x Hx. rewrite (KR x Hx). exact (HKP x Hx).
  - exact Q10.
  - apply (lp_mem_ext m _ md _ HM); [intros x; rewrite Hm1; reflexivity | exact HJ].
  - exact Hm.
  - exact HK.
Qed.

(* ---- the head of a round: +0x1a4 .. +0x1c4, and the call of tagged_of ---- *)

(* a2 = f.body, a0 = f.body + at: the wrap branch to the trap word is refuted, the second pointer check is decided by
   the facts; a1 = body_len - at; the call of tagged_of with the round's tagged_of_m; then its return. *)
Lemma lp_head : forall (fuel : nat) (r : bvmap 5 word) (m : word -> option byte) (md : Model) (pos cmds : Z),
  0 <= pos < blen -> 0 <= cmds < 2 ^ 32 -> lp_inv r pos cmds -> lp_mem m md ->
  TC.cmds_loop (Datatypes.S fuel) Bm body blen pos cmds = Some final -> lp_K fuel ->
  SRr segs W2 (lp_at IOS_LPH r m md) Q.
Proof.
  intros fuel r m md pos cmds Hpos Hcm Hinv HM Hm HK.
  pose proof Hinv as ((R23 & R18 & HKP) & R11).
  pose proof HM as (HJ & _ & _).
  pose proof lp_geo as (G1 & G2 & G3).
  pose proof Hbp as Hbp'. pose proof Hbe as Hbe'. pose proof HBL as HBL'. pose proof Hblen as Hblen'.
  assert (Usp : spZ r = spZ regs2) by (unfold spZ; rewrite (HKP 2%bv ltac:(lp_kin)); reflexivity).
  pose proof (lp_val56 m md HM) as V56.
  destruct (lp_cl_tof fuel Bm body blen pos cmds final ltac:(lia) Hm) as (t & Ht).
  pose proof (lp_Ereg r [w64 bp] 23 23%bv pos eq_refl R23) as X23.
  pose proof (lp_Ereg r [w64 bp] 11 11%bv blen eq_refl R11) as X11.
  assert (X32 : ew (lp_E r [w64 bp]) 32 = Z_to_bv 64 bp) by exact (lp_ew_ex r [w64 bp] 0 ltac:(lia)).
  assert (U2 : bv_unsigned (ew (lp_E r [w64 bp]) 2) = spZ regs2)
    by (unfold lp_E; rewrite (ew_Eimg_Ereg_nat r [w64 bp] 2 2%bv eq_refl); exact Usp).
  assert (U23 : bv_unsigned (ew (lp_E r [w64 bp]) 23) = pos) by (rewrite X23; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew (lp_E r [w64 bp]) 32) = bp) by (rewrite X32; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL (lp_E r [w64 bp]) lph_ss
    (restrict (w_H W2) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_LPH)) m (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lph_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold lph_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ (spZ regs2) 56 8 (SOff 32 0) bp);
        [exact (lp_den0 _ 32 bp X32 ltac:(lia)) | cbn; lia | cbn; lia | exact V56].
    - exact (conj I I).
    - unfold facts_ok, lph_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U23, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try exact I; lia. }
  assert (HEI : img_env VAL A_LIM (lp_E r [w64 bp])) by (unfold lp_E; apply Eimg_env).
  assert (SHOK : sh_ok segs lp_Bx [] (lp_E r [w64 bp]) (mrestrict (w_H W2) m)) by apply Forall_nil.
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  pose proof (paj_branch (PI := PI_transportb)) as BR.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lp_awr. }
  pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm1.
  clear HF HFr HG.
  rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { (* f.body + at < f.body: never, the sum does not wrap *)
    exfalso. rewrite branch_ltu_U in Hc.
    rewrite (lp_U_add _ 23 32 pos bp X23 X32) in Hc by lia.
    rewrite (U_atom _ 32 bp X32) in Hc by lia.
    apply Z.ltb_lt in Hc. lia. }
  (* the second pointer check (decided), a1 = body_len - at, `jal` tagged_of *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lp_awr. }
  pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm2.
  clear HF HFr HG.
  lp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_LPR)) Q1 ltac:(apply codeptr_val; exact HEI).
  lp_reg HS (10%bv : bv 5) (w64 (bp + pos)) Q10
    ltac:(exact (lp_den_add _ 23 32 pos bp X23 X32 ltac:(lia) ltac:(lia) ltac:(lia))).
  lp_reg HS (11%bv : bv 5) (w64 (blen - pos)) Q11
    ltac:(exact (lp_den_sub2 _ 23 11 pos blen X23 X11 ltac:(lia) ltac:(lia))).
  lp_kr r [w64 bp] LP_KP KR.
  lp_kr r [w64 bp] LP_SC KR2.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ ?mm _) ?mdx) _ =>
    change (SRr segs W2 (mkCfg (@YK11.mkst fx rr (Z_to_bv 64 TOC.TAGGED_OF) mm (YK11.seg_rom segs)) mdx) Q) end.
  assert (SP0 : spZ (ms_regs ms) = spZ regs2).
  { unfold spZ. rewrite (KR 2%bv ltac:(lp_kin)), (HKP 2%bv ltac:(lp_kin)). reflexivity. }
  assert (Hmc : forall x, ms_mem ms x = m x) by (intros x; rewrite Hm2, Hm1; reflexivity).
  pose proof (lp_mem_ext m (ms_mem ms) md _ HM Hmc HJ) as HMc.
  pose proof Hsp1 as Hsp1'. pose proof Hsp2 as Hsp2'.
  eapply SRr_bind.
  { apply (@lp_tagged fx rc B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms) _ k (ms_regs ms)
             (spZ regs2 - sp0) (bp + pos) (blen - pos) (skipn (Z.to_nat pos) body) Bm t HCELLS LEAF HJ).
    - rewrite SP0. lia.
    - exact Hal.
    - lia.
    - lia.
    - rewrite (KR 3%bv ltac:(lp_kin)), (HKP 3%bv ltac:(lp_kin)). exact R3.
    - rewrite (KR 4%bv ltac:(lp_kin)), (HKP 4%bv ltac:(lp_kin)). exact R4.
    - rewrite Q1. apply (@ret_ok_codeptr_v rc transportb_listing PI_transportb);
        [unfold IOS_LPR, IOS_AT, DgnTransportBList.AF_io_send; lia | reflexivity].
    - exact Q10.
    - exact Q11.
    - lia.
    - lia.
    - pose proof (lp_garr8_skipn _ bp _ (Z.to_nat pos) (lp_garr_m _ _ HMc)) as Hgs.
      rewrite lp_skipn_map, Z2Nat.id in Hgs by lia.
      apply (lp_bytes_of_garr8 W2 (ms_mem ms) (bp + pos) (skipn (Z.to_nat pos) body) Hgs); [lia|].
      rewrite length_skipn. lia.
    - exact (lp_tw_raw W2 (ms_mem ms) Bm (lp_tw_m _ _ HMc)).
    - exact Ht.
    - intros H3. rewrite SP0. pose proof HOFF as [HO|HO]; [left | right]; lia.
    - intros H3. apply (decode_leafb_addressable W2 (ms_mem ms) (bp + pos) 3).
      + apply (range_addressable_sub _ _ bp blen); [exact (lp_ra_m _ _ HMc) | lia | lia].
      + lia.
      + lia.
      + unfold FCB.APPMEM_END. lia.
      + intros i Hi. replace (bp + pos + i) with (bp + (pos + i)) by lia. apply lp_app. lia.
    - intros H3 i Hi. replace (bp + pos + i) with (bp + (pos + i)) by lia. apply lp_body_vis. lia.
    - intros H3 x Hx.
      assert (Ex : x = FCB.shadow_addr (bp + pos) \/ x = FCB.shadow_addr (bp + pos + 2))
        by (unfold FCB.shadow_addr in Hx |- *; Z.div_mod_to_equations; lia).
      destruct Ex as [-> | ->]; apply lp_sh_vis; lia. }
  cbv beta. intros W3 c3 _ (-> & rg & mem3 & md3 & -> & HJ3 & HP3 & HR3 & HK3 & HG3).
  rewrite Q1.
  assert (HM3 : lp_mem mem3 md3).
  { apply (lp_mem_call (ms_mem ms) _ mem3 md3 HMc HJ3); [|exact HG3].
    intros a Ha Hn. apply (HK3 a Ha). rewrite SP0. exact Hn. }
  assert (Hinv3 : lp_invS rg pos cmds).
  { split; [rewrite (lp_ap _ _ 23%bv HP3 ltac:(lp_cs)), (KR2 23%bv ltac:(unfold LP_SC; cbn [In]; auto)); exact R23|].
    split; [rewrite (lp_ap _ _ 18%bv HP3 ltac:(lp_cs)), (KR2 18%bv ltac:(unfold LP_SC; cbn [In]; auto)); exact R18|].
    intros x Hx. rewrite (lp_ap _ _ x HP3 (lp_kp_cs x Hx)), (KR x Hx). exact (HKP x Hx). }
  destruct t as [s|].
  - destruct (lp_tof _ _ _ _ _ Ht) as [_ Hs]. specialize (Hs s eq_refl).
    destruct (lp_cl_step fuel Bm body blen pos cmds final (Some s) ltac:(lia) Ht Hm) as [Hnz Hm'].
    exact (lp_ret_some fuel rg mem3 md3 pos cmds s Hpos Hcm Hs Hinv3 HR3 HM3 Hnz Hm' HK).
  - destruct (lp_cl_step fuel Bm body blen pos cmds final None ltac:(lia) Ht Hm) as [_ Hm'].
    exact (lp_ret_none fuel rg mem3 md3 pos cmds Hpos Hcm Hinv3 HR3 HM3 Hm' HK).
Qed.

(* The rounds, by induction on the model's fuel: each round passes from cmds_loop (S fuel) to cmds_loop fuel. *)
Lemma lp_rounds : forall fuel, lp_K fuel.
Proof.
  induction fuel as [|fuel IH]; intros r m md pos cmds Hpos Hcm Hinv HM Hm.
  - cbn [TC.cmds_loop] in Hm. discriminate Hm.
  - exact (lp_head fuel r m md pos cmds Hpos Hcm Hinv HM Hm IH).
Qed.

(* +0x19c .. +0x1a0: s2 = 0, s7 = 0; then the rounds from at = 0, cmds = 0. *)
Lemma lp_pre : forall (fuel : nat) (md : Model),
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md k ->
  YK11.getr regs2 11 = w64 blen ->
  TC.cmds_loop fuel Bm body blen 0 0 = Some final ->
  SRr segs W2 (@cfg_at fx segs (transportb_text + IOS_LOOP) regs2 mem2 md) Q.
Proof.
  intros fuel md HJ R11 Hm.
  pose proof Hblen as Hblen'.
  assert (HM : lp_mem mem2 md) by (split; [exact HJ | split; [intros a _ _; reflexivity | intros a Ha; exact Ha]]).
  pose proof (lp_Ereg regs2 [] 11 11%bv blen eq_refl R11) as X11.
  assert (HS : st_ok_pi segs VAL (lp_E regs2 []) lpl_ss
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_LOOP)) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold lpl_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - unfold lp_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - exact (conj I (conj I I)). }
  assert (HEI : img_env VAL A_LIM (lp_E regs2 [])) by (unfold lp_E; apply Eimg_env).
  assert (SHOK : sh_ok segs lp_Bx [] (lp_E regs2 []) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  unfold cfg_at.
  change (SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_LOOP)) mem2 (YK11.seg_rom segs)) md) Q).
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lp_awr. }
  pose proof (lp_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm1.
  clear HF HFr HG.
  lp_reg HS (23%bv : bv 5) (w64 0) Q23 ltac:(reflexivity).
  lp_reg HS (18%bv : bv 5) (w64 (bv_swrap 32 0)) Q18 ltac:(reflexivity).
  lp_reg HS (11%bv : bv 5) (w64 blen) Q11 ltac:(exact (lp_den0 _ 11 blen X11 ltac:(lia))).
  lp_kr regs2 ([] : list word) LP_KP KR.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rr _ ?mm _) ?mdx) _ =>
    change (SRr segs W2 (lp_at IOS_LPH rr mm mdx) Q) end.
  apply (lp_rounds fuel _ _ _ 0 0 ltac:(lia) ltac:(lia)).
  - split; [split; [exact Q23 | split; [exact Q18 | exact KR]] | exact Q11].
  - apply (lp_mem_ext mem2 _ md _ HM); [intros x; rewrite Hm1; reflexivity | exact HJ].
  - exact Hm.
Qed.

End loop.

(* ------------------------------------------------------------------ *)
(* The cut's facts at the exit                                         *)
(* ------------------------------------------------------------------ *)

Lemma lp_mod16 : forall x y, x mod 16 = 0 -> y mod 16 = 0 -> (x - 160 - y) mod 16 = 0.
Proof.
  intros x y Hx Hy.
  apply (Z.mod_divide _ 16 ltac:(lia)) in Hx. apply (Z.mod_divide _ 16 ltac:(lia)) in Hy.
  destruct Hx as [a ->]. destruct Hy as [b ->].
  replace (a * 16 - 160 - b * 16) with ((a - 10 - b) * 16) by ring. apply Z_mod_mult.
Qed.

Section exit. Context {rc : YM05.RunCeil}.

(* A stretch that changes only bytes of a window [zlo, zhi) inside the call's stack window [slo, shi) keeps the
   running kept fact (lib/A/Prog/TransportGCg.v acall_kept_g). *)
Lemma lp_kept_win : forall (B : asyms) G lyc Sc (W : world tfibsegs) memc mdc (W2 : world tfibsegs) mem2 mem3
    slo shi zlo zhi (E : Z -> Prop),
  AR_laws tfibsegs B -> @AR rc tfibsegs B lyc Sc W memc mdc ->
  acall_kept_g tfibsegs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (zlo <= a < zhi) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  slo <= zlo -> zhi <= shi -> alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g tfibsegs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros B G lyc Sc W memc mdc W2 mem2 mem3 slo shi zlo zhi E LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr
    Hz1 Hz2 Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia | lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | lia].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia | lia].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia | lia].
  - intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

End exit.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* IOS_LOOP .. IOS_CMDS: from the cut iod_at with a1 = body_len > 0 to IOS_CMDS with s2 = the model's cmds
   (sign-extended), the cut's facts at the last memory. The loop's section hypotheses are the cut's facts: the frame's
   placement (trans_src_ok_place, decode_rd_ok of the frame, decode_off_win), the struct's f.body = p + 30 and
   f.body_len (trans_sframe_at, lp_sf_body), the body = skipn 30 frame (io_send_seg_frm.v ios_body_len). *)
Lemma ios_loop : @ios_loop_stmt fx rc B MT.
Proof.
  unfold ios_loop_stmt.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw final ly2 S2 W2 mem2 md2 regs2 Q
    HL HFX HCSFm HIOD R11 Hb0 Hm HK.
  pose proof HL as (HCELLS & HIOC & HRU & HRE & LAWS & MTL & HGX & HGE & HSRF & HCSFc & HAF & HLC & HCIR & HSW & HIN2
    & HTO & HLF & HKD & HCLS & HLD & HAI1).
  pose proof HFX as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
    & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
  pose proof HIOD as (HE2 & HS5 & HS6).
  pose proof HE2 as (HCUR & HSAV & HREG & HS811 & HSF & HSFsrc & HGARR & HSRC & HTW).
  pose proof HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
  pose proof (ajournal_gx_AR tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof HJ as (HSTK & _ & (memS0 & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  clear HJi memS0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (FS : IOSEND_STK = 8512) by reflexivity.
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
  (* the frame and the model *)
  pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HL60.
  pose proof (ios_sf_code (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HOK.
  pose proof (ios_len_lt32 (ios_B0 Bw) frame (ios_B0 Bw) HCSFm) as HL32.
  destruct (ios_body_len frame HOK) as (EB & EBL & EBp & EBl).
  assert (Hplen : 4096 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 47).
  { destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length frame)) HAR2 HSRC ltac:(lia))
      as [Hpl | Hpl]; lia. }
  destruct Hplen as (Hp1 & Hp2).
  destruct (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length frame)) HAR2 HSRC ltac:(lia))
    as (_ & HRAf & _ & HAMf & _ & _).
  assert (SP2 : spZ regs2 = spZ regs - IOSEND_FRAME).
  { unfold spZ at 1. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
  (* the struct's f.body and f.body_len at sp + 56 and sp + 64 *)
  pose proof HSF as (Hfp0 & Hfp8 & SB & HGsb & HLSB & F0 & F8 & F16 & F24 & F26 & F28 & F30 & F32 & F36 & F40 & F41 &
    F48 & F56 & F64 & F72).
  assert (HS56 : val_mem segs (mrestrict (w_H W2) mem2) (spZ regs2 + 56) 8 (p + 30)).
  { replace (spZ regs2 + 56) with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 48) by (unfold IOS_F_OFF; lia).
    rewrite <- (lp_sf_body p frame HOK), <- F48.
    apply (lp_val_at _ _ SB 48 8 HGsb); [lia | rewrite HLSB; cbn; lia]. }
  assert (HS64 : val_mem segs (mrestrict (w_H W2) mem2) (spZ regs2 + 64) 8 (ios_blen frame)).
  { replace (spZ regs2 + 64) with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 56) by (unfold IOS_F_OFF; lia).
    unfold ios_blen. rewrite <- F56.
    apply (lp_val_at _ _ SB 56 8 HGsb); [lia | rewrite HLSB; cbn; lia]. }
  (* the body's bytes at p + 30 *)
  assert (HGB : garr8 segs (mrestrict (w_H W2) mem2) (p + 30) (map DSpec.bz (ios_body frame))).
  { pose proof (lp_garr8_skipn _ p _ 30 HGARR) as Hgs. rewrite lp_skipn_map, <- EB in Hgs. exact Hgs. }
  assert (HRAB : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (p + 30) (ios_blen frame)).
  { apply (range_addressable_sub _ _ p (Z.of_nat (length frame))); [exact HRAf | lia | lia]. }
  assert (HAM : amem_range (p + 30) (ios_blen frame)).
  { unfold amem_range in HAMf |- *. destruct HAMf as [Ha|Ha]; [left | right]; lia. }
  assert (HOFF : p + 30 + Z.of_nat (length (ios_body frame)) <= spZ regs2 - ESTACK \/ spZ regs2 <= p + 30).
  { unfold decode_off_win in Hoff. destruct Hoff as [Ho|Ho]; [left | right]; lia. }
  (* the loop, then the cut's facts at the exit *)
  eapply (@lp_pre fx rc B LAWS HGX HCELLS (HTO) (proj1 HIOC) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 (k + 0)
    regs2 (p + 30) (ios_blen frame) final (ios_body frame) (ios_B0 Bw) Q).
  - rewrite SP2, FF. apply lp_mod16; [exact Hsp16 | exact Hsp0a].
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R20.
  - exact HTW.
  - exact HGB.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact HAM.
  - exact HRAB.
  - exact HOFF.
  - exact HS56.
  - exact HS64.
  - (* the exit: iod_at at the last memory *)
    intros regs3 mem3 md3 (HJ3 & HK3 & HG3) R18 Hfr HKP3.
    assert (KA : forall a, (spZ regs2 <= a < 2 ^ 64) \/ (0 <= a < 0x7fff7f800000) ->
      aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
    { intros a Ha. apply HK3; destruct Ha as [Ha|Ha]; lia. }
    apply HK; [| exact R18 | exact Hfr].
    split; [|split].
    + split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      * (* ios_cur *)
        split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact Hmo|].
        apply (lp_kept_win B TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3 (spZ regs - IOSEND_STK) (spZ regs)
          (spZ regs2 - ESTACK) (spZ regs2) _ LAWS HAR0 HKEPT HK3 HG3); lia.
      * (* the nine saved words *)
        apply (lp_saved_kept W2 mem2 mem3 regs); [|exact HSAV].
        intros a Ha. apply KA. left. lia.
      * (* the registers *)
        split; [rewrite (HKP3 2%bv ltac:(lp_kin)); exact R2|].
        split; [rewrite (HKP3 3%bv ltac:(lp_kin)); exact R3|].
        split; [rewrite (HKP3 4%bv ltac:(lp_kin)); exact R4|].
        split; [rewrite (HKP3 8%bv ltac:(lp_kin)); exact R8|].
        split; [rewrite (HKP3 9%bv ltac:(lp_kin)); exact R9|].
        split; [rewrite (HKP3 19%bv ltac:(lp_kin)); exact R19|].
        rewrite (HKP3 20%bv ltac:(lp_kin)); exact R20.
      * intros rr Hr. rewrite (HKP3 _ (lp_kp_24 rr Hr)). exact (HS811 rr Hr).
      * (* the struct *)
        apply (lp_sframe_kept W2 mem2 mem3 _ p _); [|exact HSF].
        intros a Ha. apply KA. left. unfold IOS_F_OFF in Ha. lia.
      * apply (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ HSFsrc).
        -- intros a Ha. apply KA. left. unfold IOS_F_OFF, SF_SIZE in Ha. lia.
        -- intros s Hs. apply KA. right. lia.
      * (* the frame *)
        apply (lp_garr8_kept _ mem2 mem3 p _); [|exact HGARR].
        intros a Ha. rewrite length_map in Ha. apply HK3; [lia|].
        unfold decode_off_win in Hoff. destruct Hoff as [Ho|Ho]; lia.
      * apply (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ HSRC).
        -- intros a Ha. apply HK3; [lia|]. unfold decode_off_win in Hoff. destruct Hoff as [Ho|Ho]; lia.
        -- intros s Hs. apply KA. right. lia.
      * (* the world *)
        apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx.
        pose proof (inG_G_HARNESS_hull x (ios_tw_in_G x Hx)) as Hh.
        unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        apply KA. right. lia.
    + rewrite (HKP3 21%bv ltac:(lp_kin)). exact HS5.
    + rewrite (HKP3 22%bv ltac:(lp_kin)). exact HS6.
  - exact HJ2.
  - exact R11.
  - exact Hm.
Qed.

End top.
