(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 2256 of its 2344 lines of code are new or changed and 677 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4a: Lemma lc_op4a_ok : lc_op4a_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP4A of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput: +0x48c .. +0xb08 of the listing
   lib/A/Prog/DgnTransportList.v (0x816f0 .. 0x81d6c), from the cut lc_st_arm cx op 4 to lc_st_subr (+0xb0c) or
   lc_st_subt (+0xb40).

   What the code does.
     +0x48c .. +0x4c0  c's four shadow bytes (frame shadow 4 .. 7) := 0; a0 = g_s (spill 112(s1)), s3 = the `lw` of
                       g_s.queued (g_s + 18144, sign-extended); s6 = OW; `jal __asan_memset` (OW, 0, 304);
     +0x4c4 .. +0x4d4  `jal __asan_memset` (GOT, 0, 224);
     +0x4d8 .. +0x4fc  the byte g_fail_next (s4 = its page), OW.desk_off := -1 (OW + 232), M.fail := g_fail_next
                       (M from 184(s1), M + 88), s6 = c = F + 32 (168(s1)), `jal __asan_memset` (c, 0, 32);
     +0x500 .. +0xaf8  144(s1) := s3; the key and display bytes at the cursor (s8 / s9, bytes left s7 = s11 - 1):
                       `beqz s7` (no byte: key 1 << 16, +0x734), else the checked load of the kind byte (+0x508, slow
                       path +0x1350, report 0x82c38), `bne s11, 2`, the checked load of the address byte (+0x894, slow
                       path +0x13bc, report 0x82c48), the key at c + 28, `bne s11, 3`, the checked load of the display
                       byte (+0xadc, slow path +0x1458, report 0x82c6c); s3 = the bytes left, s8 the cursor, s7 = c,
                       s6 = 19, a1 = the display bit;
     +0xafc .. +0xb08  g_raw (the page at 120(s1)), c + 25 := display, `beqz a0`: SUBT (+0xb40) or SUBR (+0xb0c).

   How it is proved. Five symbolic runs of lib/A/Prog/PaShadow.v over the G journal (lib/A/Prog/TransportGRunA.v
   paj_run_x / paj_run_to_x), each from a fresh state whose atoms are the registers at its pc, and the three calls
   of __asan_memset through lib/A/Prog/TransportGCg.v gx_intrin_at (OW and GOT in G: their shadow facts from
   receive_cg.v trans_recv_cells over a cover list (DgnTransportCgX.v trans_sh_any_cells); c in the own class-2 frame:
   shadow bytes 4 .. 7 zero after the first run). The run from +0x500 is split by the bytes left n before the op byte:
   n = 1, 2, 3 (the registers s7 / s11 pinned to literals, so the engine decides the branches) and n >= 4 (atom
   ranges); each input byte read is a checked load the token engine decides from a shadow entry of the input block
   (range_addressable_of_block), so no report call is reached. The model: TCb.v op_begin_m is the two memsets, the
   desk_off store and the fail store (TWorldG.v tw_fill_set / tw_write); TOps.v op_submit_m's key and display bytes
   are segs.v lc_sub_kd (op_kd1 .. op_kd4). op4_main composes the steps at the arm's machine state; lc_op4a_ok opens
   lc_st_arm and closes lc_sub_common, its core by op_core_kept (st.v lc_core_kept's transfer for a step that writes
   c, the frame's shadow and 144(s1), and changes s3, s6, s7, s8). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG AF0x AE36.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaBase DgnTransportCg DgnTransportCgX TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA SlostNtc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 0. The offsets, the addresses and the symbolic states               *)
(* ------------------------------------------------------------------ *)

(* The pcs (offsets from the entry): the arm, the three returns of __asan_memset, the join of the key paths, the
   `beqz` on g_raw. *)
Definition O_ARM : Z := 0x48c.
Definition O_R1 : Z := 0x4c4.
Definition O_R2 : Z := 0x4d8.
Definition O_R3 : Z := 0x500.
Definition O_J : Z := 0xafc.
Definition O_BR : Z := 0xb08.
Lemma op4_offs : lo_arm 4 = O_ARM /\ O_R1 = O_ARM + 0x38 /\ LO_SUBR = O_BR + 4 /\ LO_SUBT = 0xb40.
Proof. repeat split; reflexivity. Qed.

(* g_s.queued, and the pages the code keeps in s4 (g_fail_next) and at 120(s1) (g_raw). *)
Definition Q_A : Z := TA_g_s + 18144.
Definition PG_GFN : Z := 0x5df554.
Definition PG_RAW : Z := 0x5df514.
Lemma op4_pages : LF_S4 = PG_GFN /\ transport_hi 8 = PG_RAW.
Proof. split; reflexivity. Qed.

(* Run 1, +0x48c .. the call at +0x4c0: the frame's shadow bytes 4 .. 7 at s2 (atom 18, written); the spill
   112(s1) (atom 9) holding g_s; g_s.queued (4 bytes, atom 32). *)
Definition s1_R_sh : YP09.region := YP09.mkRegion (Some 18%nat) 4 8 4 8 [].
Definition s1_R_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 112 120 0 0 [YP09.mkChunk 112 (YP09.CVal 8 (SLit TA_g_s))].
Definition s1_R_q : YP09.region :=
  YP09.mkRegion None Q_A (Q_A + 4) 0 0 [YP09.mkChunk Q_A (YP09.CVal 4 (SOff 32 0))].
Definition s1_F : facts :=
  mkFacts [(18%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_s1 : sstate := mkSS O_ARM sr_atoms [s1_R_sh; s1_R_sp; s1_R_q] None s1_F.

(* Run 2, +0x4c4 .. the call at +0x4d4: no memory. *)
Definition ss_s2 : sstate := mkSS O_R1 sr_atoms [] None (mkFacts [] [] []).

(* Run 3, +0x4d8 .. the call at +0x4fc: s4 = g_fail_next's page and s6 = OW pinned; the byte g_fail_next (atom 32),
   OW.desk_off (written), the spills 168(s1) (c, atom 33) and 184(s1) (M), M.fail (written). *)
Definition s3_regs : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit PG_GFN)) (Z_to_bv 5 22) (SLit TA_OW).
Definition s3_rs : smem :=
  [YP09.mkRegion None TA_g_fail_next (TA_g_fail_next + 1) 0 0
     [YP09.mkChunk TA_g_fail_next (YP09.CVal 1 (SOff 32 0))];
   YP09.mkRegion None (TA_OW + 232) (TA_OW + 236) (TA_OW + 232) (TA_OW + 236) [];
   YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (YP09.CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (YP09.CVal 8 (SLit TA_M))];
   YP09.mkRegion None (TA_M + 88) (TA_M + 92) (TA_M + 88) (TA_M + 92) []].
Definition s3_F : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_s3 : sstate := mkSS O_R2 s3_regs s3_rs None s3_F.

(* Run 4, +0x500 .. the join +0xafc, by the bytes left n before the op byte (s11, atom 27; s7 = n - 1, atom 23):
   the spill 144(s1) (written), 168(s1) (c = s6, atom 22), c's bytes 24 .. 31 (written); the input bytes read: the
   kind byte at s8 (atom 24, the atom 32), the address byte at s9 + 2 (atom 25, the atom 33) and the display byte at
   s9 + 3 (the atom 34). n = 1: s7 = 0 pinned; n = 2, 3: s11 pinned; n >= 4: atom ranges. The shadow entries: c's
   bytes 24 .. 31 and the input bytes read; the shadow base s10 (atom 26). *)
Definition s4_rs0 : smem :=
  [YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
   YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (YP09.CVal 8 (SOff 22 0))];
   YP09.mkRegion (Some 22%nat) 28 32 28 32 []].
Definition s4_kb : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 32 0))].
Definition s4_ab : YP09.region := YP09.mkRegion (Some 25%nat) 2 3 0 0 [YP09.mkChunk 2 (YP09.CVal 1 (SOff 33 0))].
Definition s4_db : YP09.region := YP09.mkRegion (Some 25%nat) 3 4 0 0 [YP09.mkChunk 3 (YP09.CVal 1 (SOff 34 0))].
Definition PTRF : Z := 140737479966720.
Definition s4_at0 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 4096 PTRF 5); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (24%nat, mkAF 4096 PTRF 0); (25%nat, mkAF 4096 PTRF 0)].
Definition ss_s4a : sstate :=
  mkSS O_R3 (sr_set sr_atoms (Z_to_bv 5 23) (SLit 0)) s4_rs0 None (mkFacts s4_at0 [] []).
Definition ss_s4b : sstate :=
  mkSS O_R3 (sr_set sr_atoms (Z_to_bv 5 27) (SLit 2)) (s4_rs0 ++ [s4_kb]) None
    (mkFacts (s4_at0 ++ [(23%nat, mkAF 1 (2 ^ 26) 0); (32%nat, mkAF 0 255 0)]) [] []).
Definition ss_s4c : sstate :=
  mkSS O_R3 (sr_set sr_atoms (Z_to_bv 5 27) (SLit 3)) (s4_rs0 ++ [s4_kb; s4_ab]) None
    (mkFacts (s4_at0 ++ [(23%nat, mkAF 1 (2 ^ 26) 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)]) [] []).
Definition ss_s4d : sstate :=
  mkSS O_R3 sr_atoms (s4_rs0 ++ [s4_kb; s4_ab; s4_db]) None
    (mkFacts (s4_at0 ++ [(23%nat, mkAF 3 (2 ^ 26) 0); (27%nat, mkAF 4 (2 ^ 26) 0); (32%nat, mkAF 0 255 0);
                         (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)]) [] []).
Definition s4_Bx : sv := SOff 26 0.
Definition SH_B : list shent := [mkSHE 22 28 32; mkSHE 24 0 1].
Definition SH_C : list shent := [mkSHE 22 28 32; mkSHE 24 0 1; mkSHE 25 2 3].
Definition SH_D : list shent := [mkSHE 22 28 32; mkSHE 24 0 1; mkSHE 25 2 4].
Definition B0 : Z * Z := (0, 0).

(* Run 5, +0xafc .. +0xb08 and on to SUBR / SUBT: the spill 120(s1) (g_raw's page), g_raw (atom 32), c + 25 at s7
   (atom 23, written). *)
Definition s5_rs : smem :=
  [YP09.mkRegion (Some 9%nat) 120 128 0 0 [YP09.mkChunk 120 (YP09.CVal 8 (SLit PG_RAW))];
   YP09.mkRegion None TA_g_raw (TA_g_raw + 4) 0 0 [YP09.mkChunk TA_g_raw (YP09.CVal 4 (SOff 32 0))];
   YP09.mkRegion (Some 23%nat) 25 26 25 26 []].
Definition ss_s5 : sstate :=
  mkSS O_J sr_atoms s5_rs None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (23%nat, mkAF 4096 PTRF 5)] [] []).

Section env. Context {rc : YM05.RunCeil}.
(* The valuation of a fresh state: the 32 registers, then the extra atoms. *)
Definition op_E (r : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg r extra).
Lemma op_ew : forall r extra n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (op_E r extra) n = YK11.getr r x.
Proof. intros r extra n x Hn. unfold op_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op_ewx : forall r extra j, (j < 8)%nat -> ew (op_E r extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros r extra j Hj. unfold op_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma op_env : forall r extra, img_env (@pa_val _ transport_listing PI_transport) A_LIM (op_E r extra).
Proof. intros r extra. unfold op_E. apply Eimg_env. Qed.
Lemma op_agree : forall r extra E, (forall m, (m < 1024)%nat -> ew E m = ew (op_E r extra) m) ->
  ed E = ed (op_E r extra) -> env_agree 32 (Ereg r extra) E.
Proof.
intros r extra E H1 H2. split.
- intros m Hm. rewrite (H1 m ltac:(lia)). unfold op_E. apply Eimg_low. unfold A_TEXT. lia.
- rewrite H2. reflexivity.
Qed.
Lemma op_base : @pa_val _ transport_listing PI_transport A_TEXT = transport_text.
Proof. vm_compute. reflexivity. Qed.
Lemma op_objs : @pa_val _ transport_listing PI_transport (A_OBJ 12) = TA_OW /\
  @pa_val _ transport_listing PI_transport (A_OBJ 13) = TA_GOT.
Proof. split; vm_compute; reflexivity. Qed.
End env.

(* A word that wraps its value. *)
Lemma op_zbv : forall z, Z_to_bv 64 (zcanon z) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

(* A 32-bit value sign-extended is 0 exactly when it is 0. *)
Lemma op_swrap_z : forall g, 0 <= g < 2 ^ 32 ->
  (zcanon (bv_swrap 32 g) = 0 <-> g = 0) /\ (bv_swrap 32 g = 0 <-> g = 0).
Proof.
intros g Hg.
assert (Hs : bv_swrap 32 g = if g <? 2 ^ 31 then g else g - 2 ^ 32).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32 / 2) with (2 ^ 31) by reflexivity. replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec g (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (g + 2 ^ 31) with ((g - 2 ^ 31) + 1 * 2 ^ 32) by ring. rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
rewrite Hs. unfold zcanon, M64. destruct (Z.ltb_spec g (2 ^ 31)).
- rewrite Z.mod_small by lia. tauto.
- replace (g - 2 ^ 32) with ((g - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by ring.
  rewrite Z_mod_plus_full, Z.mod_small by lia. split; split; intros; lia.
Qed.
(* The key the code computes from the kind byte (atom 32) at +0x520 .. +0x540: (b - 9 * ((57 * b) >> 9) + 1) & 255
   shifted by 16, then or'ed with the address byte (atom 33). *)
Definition kexpr : sv :=
  SAlu ALU_SLL
    (SAlu ALU_AND
       (SAlu ALU_ADD
          (SAlu ALU_SUB
             (SAlu ALU_SUB (SOff 32 0) (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 57)) (SLit 9)))
             (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 57)) (SLit 9)) (SLit 3)))
          (SLit 1))
       (SLit 255))
    (SLit 16).
Definition kexprC : sv := SAlu ALU_OR kexpr (SOff 33 0).

Lemma kexpr_U : forall E kb, U E (SOff 32 0) = kb -> 0 <= kb < 256 -> U E kexpr = (kb mod 9 + 1) * 65536.
Proof.
intros E kb Hk Hb. unfold kexpr. rewrite !U_SAlu, !U_SMd, !U_SLit, Hk.
assert (Hn : exists m : nat, kb = Z.of_nat m /\ (m < 256)%nat) by (exists (Z.to_nat kb); lia).
destruct Hn as (m & -> & Hm). clear Hk Hb.
do 256 (destruct m as [|m]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma op_lor_shift : forall k y, 0 <= k -> 0 <= y < 65536 -> Z.lor (k * 65536) y = k * 65536 + y.
Proof.
intros k y Hk Hy.
assert (Hand : Z.land (k * 65536) y = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0. change 65536 with (2 ^ 16).
  rewrite <- Z.shiftl_mul_pow2 by lia. destruct (Z.lt_ge_cases i 16) as [Hl | Hg].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec y 0) as [-> | Hy0]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 y i); [apply andb_false_r | lia |].
    assert (Hlg : Z.log2 y < 16) by (apply Z.log2_lt_pow2; lia). lia. }
rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand. reflexivity.
Qed.

Lemma op_key_val : forall kb ab, 0 <= kb < 256 -> 0 <= ab < 256 ->
  DSpec.KEY (kb mod 9 + 1) ab = (kb mod 9 + 1) * 65536 + ab /\ 0 <= DSpec.KEY (kb mod 9 + 1) ab < 2 ^ 32.
Proof.
intros kb ab Hk Ha. unfold DSpec.KEY.
change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small ab) by lia.
pose proof (Z.mod_pos_bound kb 9 ltac:(lia)).
rewrite op_lor_shift by lia. lia.
Qed.

Lemma kexprC_U : forall E kb ab, U E (SOff 32 0) = kb -> U E (SOff 33 0) = ab -> 0 <= kb < 256 -> 0 <= ab < 256 ->
  U E kexprC = DSpec.KEY (kb mod 9 + 1) ab.
Proof.
intros E kb ab Hk Ha Hkb Hab. unfold kexprC. rewrite U_SAlu, (kexpr_U E kb Hk Hkb), Ha. cbn [zalu_raw].
pose proof (Z.mod_pos_bound kb 9 ltac:(lia)).
rewrite op_lor_shift by lia. destruct (op_key_val kb ab Hkb Hab) as (EK & BK). rewrite EK.
apply zcanon_id. unfold M64. lia.
Qed.

(* The model's fuzz_u8 on a cursor with bytes left / with none. *)
Lemma op_u8 : forall D off n, n <> 0 ->
  TOP.fuzz_u8_m D (TOP.FuzzIn off n) = (TOP.FuzzIn (off + 1) (n - 1), DSpec.at8 D (Z.to_nat off)).
Proof.
intros D off n Hn. unfold TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. rewrite (proj2 (Z.eqb_neq n 0) Hn). reflexivity.
Qed.
Lemma op_u80 : forall D off n, n = 0 -> TOP.fuzz_u8_m D (TOP.FuzzIn off n) = (TOP.FuzzIn off n, 0).
Proof. intros D off n Hn. subst n. reflexivity. Qed.

(* segs.v lc_sub_kd after the op byte, by the bytes left n0 before it: 1, 2, 3, 4 or more. *)
Lemma op_kd1 : forall D off0,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 1)) = mkLsv (DSpec.KEY 1 0) 0 (TOP.FuzzIn (off0 + 1) 0).
Proof.
intros D off0. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 1) by lia. cbn [fst].
rewrite (op_u80 D (off0 + 1) (1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1) (1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1) (1 - 1)) by lia. cbv beta iota zeta. reflexivity.
Qed.
Lemma op_kd2 : forall D off0,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 2)) =
  mkLsv (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) 0) 0 (TOP.FuzzIn (off0 + 2) 0).
Proof.
intros D off0. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 2) by lia. cbn [fst].
rewrite (op_u8 D (off0 + 1) (2 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1 + 1) (2 - 1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1 + 1) (2 - 1 - 1)) by lia. cbv beta iota zeta.
replace (off0 + 1 + 1) with (off0 + 2) by lia. reflexivity.
Qed.
Lemma op_kd3 : forall D off0,
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 3)) =
  mkLsv (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) (DSpec.at8 D (Z.to_nat (off0 + 2)))) 0
    (TOP.FuzzIn (off0 + 3) 0).
Proof.
intros D off0. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 3) by lia. cbn [fst].
rewrite (op_u8 D (off0 + 1) (3 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off0 + 1 + 1) (3 - 1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u80 D (off0 + 1 + 1 + 1) (3 - 1 - 1 - 1)) by lia. cbv beta iota zeta.
replace (off0 + 1 + 1 + 1) with (off0 + 3) by lia. replace (off0 + 1 + 1) with (off0 + 2) by lia. reflexivity.
Qed.
Lemma op_kd4 : forall D off0 n0, 4 <= n0 ->
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 n0)) =
  mkLsv (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) (DSpec.at8 D (Z.to_nat (off0 + 2))))
    (Z.land (DSpec.at8 D (Z.to_nat (off0 + 3))) 1) (TOP.FuzzIn (off0 + 4) (n0 - 4)).
Proof.
intros D off0 n0 Hn. unfold lc_sub_kd, lc_oc. rewrite (op_u8 D off0 n0) by lia. cbn [fst].
rewrite (op_u8 D (off0 + 1) (n0 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off0 + 1 + 1) (n0 - 1 - 1)) by lia. cbv beta iota zeta.
rewrite (op_u8 D (off0 + 1 + 1 + 1) (n0 - 1 - 1 - 1)) by lia. cbv beta iota zeta.
replace (off0 + 1 + 1 + 1 + 1) with (off0 + 4) by lia. replace (off0 + 1 + 1 + 1) with (off0 + 3) by lia.
replace (off0 + 1 + 1) with (off0 + 2) by lia. replace (n0 - 1 - 1 - 1 - 1) with (n0 - 4) by lia. reflexivity.
Qed.

(* Byte j of c as segs.v lc_sub_common states it: cmd_struct (24 zeros) 0 display key. *)
Lemma op_cmd_nth : forall disp key (j : nat), 0 <= disp < 256 -> (j < 32)%nat ->
  nth j (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 disp key)) 0 =
  if (j =? 25)%nat then disp else if (j <? 28)%nat then 0 else YO0f.le_byte key 4 (j - 28).
Proof.
intros disp key j Hd Hj. unfold TW.zs, TOP.cmd_struct.
rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0)))
  by (rewrite length_map, !length_app, repeat_length, TWL.length_put; cbn [length]; lia).
rewrite map_nth.
destruct (Nat.lt_ge_cases j 28) as [Hl | Hg].
- rewrite app_assoc, app_nth1 by (rewrite length_app, repeat_length; cbn [length]; lia).
  do 28 (destruct j as [|j]; [cbn [nth repeat app Nat.eqb Nat.ltb Nat.leb];
    first [reflexivity | unfold DSpec.b8; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
           apply Z.mod_small; lia] |]).
  lia.
- rewrite app_assoc, app_nth2 by (rewrite length_app, repeat_length; cbn [length]; lia).
  rewrite length_app, repeat_length. cbn [length].
  replace (j - (24 + 4))%nat with (j - 28)%nat by lia.
  rewrite tw_le_byte_put by lia.
  destruct (Nat.eqb_spec j 25) as [E | E]; [lia|]. destruct (Nat.ltb_spec j 28) as [E2 | E2]; [lia|]. reflexivity.
Qed.

(* The frame's shadow map with c in scope differs from the one without only at bytes 4 .. 7, which are 0. *)
Lemma lf_shm_tf : forall i, 0 <= i < 32 -> ~ (4 <= i < 8) ->
  nth (Z.to_nat i) (lf_shm true false) 0 = nth (Z.to_nat i) (lf_shm false false) 0.
Proof.
intros i Hi Hn. assert (Hk : (Z.to_nat i < 32)%nat) by lia. assert (Hn' : ~ (4 <= Z.to_nat i < 8)%nat) by lia.
revert Hk Hn'. generalize (Z.to_nat i) as k. intros k Hk Hn'.
do 32 (destruct k as [|k]; [first [reflexivity | exfalso; lia] |]). lia.
Qed.
Lemma lf_shm_tc : forall i, 4 <= i < 8 -> nth (Z.to_nat i) (lf_shm true false) 0 = 0.
Proof.
intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

(* The shadow cells of the record that cover OW's and GOT's 64-byte hulls (receive_cg.v trans_recv_cells): the zero
   granules of OW, GOT and g_rx_len, g_rx_len's three guard granules, OW's first six guard granules after its payload
   and g_s's last four guard granules before GOT. *)
Definition cs_ow : list (Z * Z) :=
  trans_zgran TA_OW (TA_OW + TW.SZ_OW) ++ trans_zgran TA_g_rx_len (TA_g_rx_len + TW.SZ_g_rx_len) ++
  map (fun a => (a, 0xf9)) [TA_g_rx_len + 8; TA_g_rx_len + 16; TA_g_rx_len + 24; TA_OW + TW.SZ_OW;
    TA_OW + TW.SZ_OW + 8; TA_OW + TW.SZ_OW + 16; TA_OW + TW.SZ_OW + 24; TA_OW + TW.SZ_OW + 32; TA_OW + TW.SZ_OW + 40].
Definition cs_got : list (Z * Z) :=
  trans_zgran TA_GOT (TA_GOT + TW.SZ_GOT) ++ map (fun a => (a, 0xf9)) [TA_GOT - 32; TA_GOT - 24; TA_GOT - 16; TA_GOT - 8].
Lemma cs_ow_cover : trans_cs_cover cs_ow TA_OW 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cs_got_cover : trans_cs_cover cs_got TA_GOT 224 = true.
Proof. vm_compute. reflexivity. Qed.

Section cov. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma op_ow_sh : trans_recv_cells B -> trans_sh_any B TA_OW 304.
Proof.
intros (HZo & _ & HZr & HC). apply (trans_sh_any_cells B cs_ow); [|exact cs_ow_cover].
unfold cs_ow. apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZo | reflexivity]|].
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZr | reflexivity]|].
apply trans_sh_cells_const; [|lia]. intros ly a Ha. pose proof (HC ly) as H.
cbn [In] in Ha. repeat (destruct Ha as [<- | Ha]; [tauto|]). destruct Ha.
Qed.
Lemma op_got_sh : trans_recv_cells B -> trans_sh_any B TA_GOT 224.
Proof.
intros (_ & HZg & _ & HC). apply (trans_sh_any_cells B cs_got); [|exact cs_got_cover].
unfold cs_got. apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZg | reflexivity]|].
apply trans_sh_cells_const; [|lia]. intros ly a Ha. pose proof (HC ly) as H.
cbn [In] in Ha. repeat (destruct Ha as [<- | Ha]; [tauto|]). destruct Ha.
Qed.

(* A register whose symbolic value is still its own atom holds its value at the run's start. *)
Lemma op_kr : forall E (regs : bvmap 5 word) extra (s : list sv) (v : word) (r : bv 5),
  (forall m, (m < 32)%nat -> ew E m = ew (op_E regs extra) m) ->
  v = sv_denot E (sr_get s r) -> sr_get s r = SOff (Z.to_nat (bv_unsigned r)) 0 -> v = YK11.getr regs r.
Proof.
intros E regs extra s v r HE Hv Hs. rewrite Hv, Hs. cbn [sv_denot].
pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite (HE (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite (op_ew regs extra (Z.to_nat (bv_unsigned r)) r ltac:(lia)).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End cov.

(* The registers a step keeps: those of l, read through the machine state's symbolic state (HKR: op_kr at it). *)
Ltac op_keep_list HKR :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [apply HKR; vm_compute; reflexivity |]); destruct Hr.

(* ------------------------------------------------------------------ *)
(* 1. The runs and the three calls of __asan_memset                     *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac op_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "op_reg: no match for" T; fail
  end.

(* The region list of an awr obligation, computed. *)
Ltac op_awr_norm :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A read-only region: no writable byte. *)
Ltac op_awr_ro :=
  apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].

Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HGX : gx_ok segs B TG.G_HARNESS.
Hypothesis HMS : @aintrin_realizes fx rc segs B OSet (transport_sigma TS___asan_memset).
Hypothesis HRC : trans_recv_cells B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (ly : alayout) (S : astate) (W : world segs)
  (k : Z).
(* The class-2 frame F at position pos, owned by the journal; the realigned sp1. *)
Variables (F sp1 pos : Z).
Hypothesis HOWN : In (LF_CID, pos) own.
Hypothesis HFIN : In (LF_CID, pos) (frames S).
Hypothesis HFA : frame_addr ly LF_CID pos = F.
Hypothesis HF0 : 4096 <= F.
Hypothesis HF64 : F mod 64 = 0.
Hypothesis HFC : F + 256 <= alloc_ceiling.
Hypothesis HSPC : alloc_ceiling + 32432 <= sp1.
Hypothesis HSP47 : sp0 <= 2 ^ 47.
Hypothesis HSP32 : sp1 mod 32 = 0.
Hypothesis HSP0 : sp0 - 336 <= sp1 <= sp0 - 320.
Hypothesis HSP016 : sp0 mod 16 = 0.
Hypothesis HSTK : ESTACK + 336 <= STK.

Local Abbreviation J m md :=
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W m md k).
Local Abbreviation at_ pc r m md := (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) m (YK11.seg_rom segs)) md).
Local Abbreviation SHF := (SHADOW_OFF + F / 8).
Local Abbreviation rdv m := (aview segs (w_H W) m).

Lemma op_F8 : F / 8 = 8 * (F / 64) /\ F mod 8 = 0 /\ 512 <= F / 8 <= 2 ^ 44.
Proof.
pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. pose proof asan_consts as ((C1 & C2) & _).
split; [rewrite D at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia|].
split; [rewrite D; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.mod_mul; lia|].
split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia].
Qed.

(* The frame's bytes and shadow bytes present, at a memory of the journal. *)
Lemma op_frame_pres : forall m md, J m md ->
  (forall a, F <= a < F + 256 -> apresent (w_H W) m a) /\
  (forall i, 0 <= i < 32 -> apresent (w_H W) m (SHF + i)) /\ in_app F 256.
Proof.
intros m md HJ. pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_frames _ _ LAWS ly S W m md LF_CID pos HAR HFIN) as (_ & Happ & HFb & HFsh).
rewrite HFA in Happ, HFb, HFsh. change (fs_frame_bytes LF_CID) with 256 in Happ, HFb.
change (fs_frame_bytes LF_CID / 8) with 32 in HFsh.
split; [intros a Ha; exact (proj1 (HFb a Ha))|]. split; [intros i Hi; exact (proj1 (HFsh i Hi)) | exact Happ].
Qed.

(* Run 1's state at the arm. *)
Lemma s1_entry : forall regs mem q,
  YK11.getr regs 18 = w64 SHF -> YK11.getr regs 9 = w64 sp1 ->
  rdword (rdv mem) (sp1 + 112) = Some TA_g_s ->
  val_mem segs (mrestrict (w_H W) mem) Q_A 4 q -> 0 <= q < 2 ^ 32 ->
  (forall i, 4 <= i < 8 -> apresent (w_H W) mem (SHF + i)) ->
  st_ok_pi segs VAL (op_E regs [w64 q]) ss_s1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_ARM)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem q R18 R9 HSP HQV HQ HPS.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
set (E := op_E regs [w64 q]).
assert (U18 : bv_unsigned (ew E 18) = SHF)
  by (unfold E; rewrite (op_ew regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 q) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = q) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_s1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks s1_R_sh s1_R_sp s1_R_q base_val];
    rewrite ?U18, ?U9.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HPS. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 112 8 (SLit TA_g_s) TA_g_s); [reflexivity | unfold TA_g_s; cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs _ _ _ _ HSP).
  + split; [unfold Q_A, TA_g_s; lia|]. split; [unfold Q_A, TA_g_s; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 Q_A 4 (SOff 32 0) q); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HQV].
    cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, s1_R_sh, s1_R_sp, s1_R_q.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold Q_A, TA_g_s, SHADOW_OFF in *. repeat split; first [exact I | lia].
- unfold s1_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U9, U32.
  change (2 ^ 3) with 8. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  assert (M8 : SHF mod 8 = 0).
  { rewrite F8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
    apply Z.mod_mul. lia. }
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* An image object's atom denotes its address. *)
Lemma op_atom_obj : forall E (i : nat) v, img_env VAL A_LIM E -> VAL (A_OBJ i) = v -> 0 <= v < 2 ^ 64 ->
  (A_OBJ i < A_LIM)%nat -> sv_denot E (SOff (A_OBJ i) 0) = w64 v.
Proof.
intros E i v HE Hv Hr Hl. cbn [sv_denot]. rewrite (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)), Hv.
rewrite Z.add_0_r. reflexivity.
Qed.

(* The callee-saved registers, case by case. *)
Lemma op_saved_cases : forall (P : Z -> Prop), P 2 -> P 3 -> P 4 -> P 8 -> P 9 -> P 18 -> P 19 -> P 20 -> P 21 ->
  P 22 -> P 23 -> P 24 -> P 25 -> P 26 -> P 27 -> forall r, acallee_saved r -> P r.
Proof.
intros P H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
             r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc]; [assumption|]). subst r. assumption.
Qed.

(* __asan_memset (d, 0, n) at sp1 through TransportGCg.v gx_intrin_at: [d, d + n) := 0, every other byte but the
   ESTACK bytes below sp1 kept, the callee-saved registers kept. *)
Lemma op_memset : forall regsT memT mdc d n raw (Q : world segs -> config -> Prop),
  J memT mdc ->
  YK11.getr regsT 10 = w64 d -> YK11.getr regsT 11 = w64 0 -> YK11.getr regsT 12 = w64 n ->
  YK11.getr regsT 2 = w64 sp1 -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  (forall a, d <= a < d + n ->
     (awr_byte STK sp0 FP (ablocks B ly0 S0) (ablocks B ly S) ly own a /\ ~ (sp1 - ESTACK <= a < sp1)) \/
     inG TG.G_HARNESS a) ->
  amem_range d n -> range_addressable (rdv memT) SHADOW_OFF d n -> shadow_hull_vis (rdv memT) d n ->
  (forall regs2 mem2 md2, J mem2 md2 -> aregs_preserved regsT regs2 ->
     (forall i, 0 <= i < n -> rdv mem2 (d + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___asan_memset)) memT (YK11.seg_rom segs))
    mdc) Q.
Proof.
intros regsT memT mdc d n raw Q HJ R10 R11 R12 R2 R3 R4 R1 Hraw Hn Hd0 Hdn Hwr Hamr Hra Hhull HK.
assert (USP : spZ regsT = sp1).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. pose proof asan_consts as ((C1 & C2) & _). lia. }
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    HMS TG.G_HARNESS W regsT memT STK sp0 FP ly0 S0 W0 mem0 md0 own ly S mdc k d 0 n (sp1 - sp0) raw HGX
    G_HARNESS_rw HJ R10 R11 R12).
  - exact Hn.
  - exact Hd0.
  - exact Hdn.
  - rewrite USP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HSP32, Z.add_0_r in D1. rewrite HSP016, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hraw.
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. rewrite USP. exact Hwr.
  - exact Hamr.
  - exact Hra.
  - intros _. exact Hhull.
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- intros i Hi. rewrite (Hset2 i Hi). reflexivity.
- intros a Ha H1 H2. apply Heff2; [exact Ha | exact H1 | lia].
- exact Hgr2.
Qed.

(* Run 1 and __asan_memset (OW, 0, 304): from the arm to the memset's return +0x4c4. *)
Lemma op4_s1 : forall regs mem md q (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 SHF ->
  rdword (rdv mem) (sp1 + 112) = Some TA_g_s ->
  val_mem segs (mrestrict (w_H W) mem) Q_A 4 q -> 0 <= q < 2 ^ 32 ->
  (forall regs2 mem2 md2, J mem2 md2 ->
     YK11.getr regs2 19 = Z_to_bv 64 (bv_swrap 32 q) -> YK11.getr regs2 22 = w64 TA_OW ->
     (forall r, acallee_saved r -> r <> 19 -> r <> 22 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     (forall i, 4 <= i < 8 -> rdv mem2 (SHF + i) = Some 0) ->
     (forall i, 0 <= i < 304 -> rdv mem2 (TA_OW + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (SHF + 4 <= a < SHF + 8) -> ~ (TA_OW <= a < TA_OW + 304) ->
        ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (at_ O_R1 regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_ARM regs mem md) Q.
Proof.
intros regs mem md q Q HJ R2 R3 R4 R9 R18 HSP HQV HQ HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
destruct (op_frame_pres mem md HJ) as (_ & HFsh & _).
pose proof (s1_entry regs mem q R18 R9 HSP HQV HQ ltac:(intros i Hi; apply HFsh; lia)) as HS.
set (E0 := op_E regs [w64 q]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (U18 : bv_unsigned (ew E0 18) = SHF)
  by (unfold E0; rewrite (op_ew regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (unfold E0; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E0 32 = w64 q) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID / 8) with 32. lia. }
  op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHF + 4 <= a < SHF + 8) -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHF + 4 <= x < SHF + 8) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U18 in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 8 -> rdv (ms_mem ms) (SHF + i) = Some 0).
{ intros i Hi. rewrite <- U18.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi' as [-> | [-> | [-> | ->]]];
  apply (sn_chunk0 E0 (w_H W) (ms_mem ms) (Some 18%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pmkst HS.
op_reg HS (Z_to_bv 5 10) (w64 TA_OW) Q10
  ltac:(exact (op_atom_obj _ 12 TA_OW HEI (proj1 op_objs) ltac:(unfold TA_OW; lia) ltac:(unfold A_OBJ, A_LIM; lia))).
op_reg HS (Z_to_bv 5 22) (w64 TA_OW) Q22
  ltac:(exact (op_atom_obj _ 12 TA_OW HEI (proj1 op_objs) ltac:(unfold TA_OW; lia) ltac:(unfold A_OBJ, A_LIM; lia))).
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 304) Q12 ltac:(reflexivity).
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O_R1)) Q1 ltac:(apply codeptr_val; exact HEI).
op_reg HS (Z_to_bv 5 19) (Z_to_bv 64 (bv_swrap 32 q)) Q19
  ltac:(rewrite denot_lit_U, U_SExt, U_SOff, E32; unfold w64; rewrite unsigned_lit_small by lia;
        rewrite Z.add_0_r, (zcanon_id q) by (unfold M64; lia); rewrite Z.mod_small by lia; apply op_zbv).
assert (KR : forall r, acallee_saved r -> r <> 19 -> r <> 22 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 q] (ss_regs ssx) _ r (fun m _ => eq_refl)
      (st_ok_restrict_reg segs Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H19 H22;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity]. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Qx) end.
apply (op_memset (ms_regs ms) (ms_mem ms) md1 TA_OW 304 (Z_to_bv 64 (BASE + O_R1)) Q HJ Q10 Q11 Q12
  (eq_trans (KR 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)
  (eq_trans (KR 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)
  (eq_trans (KR 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4) Q1).
- apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold O_R1; lia | reflexivity].
- lia.
- unfold TA_OW; lia.
- unfold TA_OW; lia.
- intros a Ha. right. unfold inG. apply Exists_exists. exists (TA_OW, TW.SZ_OW).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
- left. unfold kLowMemEnd, TA_OW. lia.
- exact (proj1 (op_ow_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- exact (proj2 (op_ow_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- intros regs2 mem2 md2 HJ2 HP2 HZ2 HK2 HG2.
  apply (HK regs2 mem2 md2 HJ2).
  + exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) Q19).
  + exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) Q22).
  + intros r Hr H19 H22. exact (eq_trans (HP2 r Hr) (KR r Hr H19 H22)).
  + intros i Hi. rewrite HK2 by (unfold ESTACK, SHADOW_OFF, TA_OW in *; lia). exact (ZS1 i Hi).
  + intros i Hi. exact (HZ2 i Hi).
  + intros a Ha H1 H2 H3. rewrite (HK2 a Ha H2 H3). exact (KR1 a Ha H1).
  + intros a Ha. exact (HG2 a (GA1 a Ha)).
Qed.

(* Run 2's state at +0x4c4: no memory. *)
Lemma s2_entry : forall regs mem,
  st_ok_pi segs VAL (op_E regs []) ss_s2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R1)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem. rewrite restrict_mkst_fx. unfold ss_s2.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- exact (conj I (conj I I)).
Qed.

(* Run 2 and __asan_memset (GOT, 0, 224): from +0x4c4 to the memset's return +0x4d8. *)
Lemma op4_s2 : forall regs mem md (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  (forall regs2 mem2 md2, J mem2 md2 ->
     (forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     (forall i, 0 <= i < 224 -> rdv mem2 (TA_GOT + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_GOT <= a < TA_GOT + 224) -> ~ (sp1 - ESTACK <= a < sp1) ->
        rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (at_ O_R2 regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_R1 regs mem md) Q.
Proof.
intros regs mem md Q HJ R2 R3 R4 HK.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (s2_entry regs mem) as HS.
set (E0 := op_E regs []) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
op_reg HS (Z_to_bv 5 10) (w64 TA_GOT) Q10
  ltac:(exact (op_atom_obj _ 13 TA_GOT HEI (proj2 op_objs) ltac:(unfold TA_GOT; lia) ltac:(unfold A_OBJ, A_LIM; lia))).
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 224) Q12 ltac:(reflexivity).
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O_R2)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (KR : forall r, acallee_saved r -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [] (ss_regs ssx) _ r (fun m _ => eq_refl)
      (st_ok_restrict_reg segs Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; apply HKR; vm_compute; reflexivity. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Qx) end.
apply (op_memset (ms_regs ms) (ms_mem ms) md1 TA_GOT 224 (Z_to_bv 64 (BASE + O_R2)) Q HJ Q10 Q11 Q12
  (eq_trans (KR 2 ltac:(unfold acallee_saved; lia)) R2)
  (eq_trans (KR 3 ltac:(unfold acallee_saved; lia)) R3)
  (eq_trans (KR 4 ltac:(unfold acallee_saved; lia)) R4) Q1).
- apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold O_R2; lia | reflexivity].
- lia.
- unfold TA_GOT; lia.
- unfold TA_GOT; lia.
- intros a Ha. right. unfold inG. apply Exists_exists. exists (TA_GOT, TW.SZ_GOT).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_GOT) | unfold in_zr, TW.SZ_GOT; cbn [fst snd]; lia].
- left. unfold kLowMemEnd, TA_GOT. lia.
- exact (proj1 (op_got_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- exact (proj2 (op_got_sh B HRC ly S W (ms_mem ms) md1 (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
- intros regs2 mem2 md2 HJ2 HP2 HZ2 HK2 HG2.
  apply (HK regs2 mem2 md2 HJ2).
  + intros r Hr. exact (eq_trans (HP2 r Hr) (KR r Hr)).
  + exact HZ2.
  + intros a Ha H1 H2. rewrite (HK2 a Ha H1 H2). exact (KR1 a Ha).
  + intros a Ha. exact (HG2 a (GA1 a Ha)).
Qed.

(* A byte of a value in memory, as the view reads it. *)
Lemma op_vm_av : forall (H : word -> bool) m a (n : nat) v (j : nat),
  val_mem segs (mrestrict H m) a n v -> (j < n)%nat -> aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* A payload byte of a global is a byte of G; a byte of G lies in low memory and outside the frame. *)
Lemma op_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma op_G_low : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. exact (inG_low segs B transport_segs_low _ a HGX Ha). Qed.
Lemma op_G_frame : forall m md, J m md -> forall a, inG TG.G_HARNESS a -> ~ (F <= a < F + 256).
Proof.
intros m md HJ a Ha Hf.
apply (frm_img segs B LAWS ly S W m md LF_CID pos a (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HFIN);
  [rewrite HFA; change (fs_frame_bytes LF_CID) with 256; lia|].
exact (trans_g_img a Ha).
Qed.

(* Run 3's state at +0x4d8 (s4 and s6 pinned). *)
Lemma s3_entry : forall regs mem gfn,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 PG_GFN -> YK11.getr regs 22 = w64 TA_OW ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_fail_next 1 gfn -> 0 <= gfn < 256 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) -> rdword (rdv mem) (sp1 + 184) = Some TA_M ->
  st_ok_pi segs VAL (op_E regs [w64 gfn; w64 (F + 32)]) ss_s3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R2)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem gfn R9 R20 R22 HGV HGB H168 H184.
pose proof asan_consts as ((C1 & C2) & _).
set (E := op_E regs [w64 gfn; w64 (F + 32)]).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 gfn) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E 33 = w64 (F + 32)) by (unfold E; exact (op_ewx regs _ 1 ltac:(lia))).
assert (H0 : st_ok_pi segs VAL E (mkSS O_R2 sr_atoms s3_rs None s3_F)
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R2)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s3_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9.
    + split; [unfold TA_g_fail_next; lia|]. split; [unfold TA_g_fail_next; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TA_g_fail_next 1 (SOff 32 0) gfn); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HGV].
      cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply (op_inG_row _ _ _ _ TMAP_A_OW). unfold TA_OW, TW.SZ_OW in *. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 168 8 (SOff 33 0) (F + 32)); [| cbn; lia | cbn; lia |].
      * cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      * exact (val_mem_of_rdword segs _ _ _ _ H168).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 184 8 (SLit TA_M) TA_M); [reflexivity | unfold TA_M; cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword segs _ _ _ _ H184).
    + split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply (op_inG_row _ _ _ _ TMAP_A_M). unfold TA_M, TW.SZ_M in *. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, s3_rs.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TA_g_fail_next, TA_OW, TA_M in *. repeat split; first [exact I | lia].
  - unfold s3_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    assert (U32 : bv_unsigned (ew E 32) = gfn) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
    rewrite U32. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) PG_GFN H0 R20 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) TA_OW H1 R22 eq_refl) as H2.
exact H2.
Qed.

(* Run 3 and __asan_memset (c, 0, 32): from +0x4d8 to the memset's return +0x500. *)
Lemma op4_s3 : forall regs mem md gfn (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 PG_GFN -> YK11.getr regs 22 = w64 TA_OW ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_fail_next 1 gfn -> 0 <= gfn < 256 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) -> rdword (rdv mem) (sp1 + 184) = Some TA_M ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  (forall regs2 mem2 md2, J mem2 md2 ->
     YK11.getr regs2 22 = w64 (F + 32) ->
     (forall r, acallee_saved r -> r <> 22 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     (forall j, (j < 4)%nat -> rdv mem2 (TA_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte 4294967295 4 j)) ->
     (forall j, (j < 4)%nat -> rdv mem2 (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte gfn 4 j)) ->
     (forall i, 0 <= i < 32 -> rdv mem2 (F + 32 + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 232 <= a < TA_OW + 236) -> ~ (TA_M + 88 <= a < TA_M + 92) ->
        ~ (F + 32 <= a < F + 64) -> ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (at_ O_R3 regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_R2 regs mem md) Q.
Proof.
intros regs mem md gfn Q HJ R2 R3 R4 R9 R20 R22 HGV HGB H168 H184 HZS HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (s3_entry regs mem gfn R9 R20 R22 HGV HGB H168 H184) as HS.
set (E0 := op_E regs [w64 gfn; w64 (F + 32)]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (E32 : ew E0 32 = w64 gfn) by (unfold E0; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E0 33 = w64 (F + 32)) by (unfold E0; exact (op_ewx regs _ 1 ltac:(lia))).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm. op_awr_ro.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    apply (op_inG_row _ _ _ _ TMAP_A_OW). unfold TA_OW, TW.SZ_OW in *. lia. }
  op_awr_ro. op_awr_ro.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  apply (op_inG_row _ _ _ _ TMAP_A_M). unfold TA_M, TW.SZ_M in *. lia. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 232 <= a < TA_OW + 236) -> ~ (TA_M + 88 <= a < TA_M + 92) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 232 <= x < TA_OW + 236) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(unfold TA_OW, TA_M; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
pose proof (st_ok_region_nth _ _ _ 4 _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
pose proof (sn_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6238536 4 (SLit 18446744073709551615) RG1
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VOW.
pose proof (sn_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6156728 4 (SOff 32 0) RG4
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VM.
cbn [base_val] in VOW, VM.
change (bv_unsigned (sv_denot E0 (SLit 18446744073709551615)) mod 2 ^ (8 * Z.of_N 4)) with 4294967295 in VOW.
replace (bv_unsigned (sv_denot E0 (SOff 32 0)) mod 2 ^ (8 * Z.of_N 4)) with gfn in VM
  by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; unfold w64; rewrite unsigned_lit_small by lia;
      change (2 ^ (8 * Z.of_N 4)) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
change (N.to_nat 4) with 4%nat in VOW, VM.
clear HF HFr HG RG1 RG4.
destruct (op_frame_pres (ms_mem ms) md1 HJ) as (_ & HFsh1 & Happ).
pmkst HS.
op_reg HS (Z_to_bv 5 10) (w64 (F + 32)) Q10
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
op_reg HS (Z_to_bv 5 22) (w64 (F + 32)) Q22
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 12) (w64 32) Q12 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 20) (w64 PG_GFN) Q20 ltac:(reflexivity).
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O_R3)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (KR : forall r, acallee_saved r -> r <> 22 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 gfn; w64 (F + 32)] (ss_regs ssx) _ r (fun m _ => eq_refl)
      (st_ok_restrict_reg segs Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H22;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity | exact (eq_trans Q20 (eq_sym R20))]. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Qx) end.
apply (op_memset (ms_regs ms) (ms_mem ms) md1 (F + 32) 32 (Z_to_bv 64 (BASE + O_R3)) Q HJ Q10 Q11 Q12
  (eq_trans (KR 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) R2)
  (eq_trans (KR 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) R3)
  (eq_trans (KR 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) R4) Q1).
- apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold O_R3; lia | reflexivity].
- lia.
- lia.
- lia.
- intros a Ha. left. split.
  + unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, pos. split; [exact HOWN|].
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia.
  + unfold ESTACK. lia.
- exact (amem_range_sub_app F 256 (F + 32) 32 Happ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
- apply (frame_ra_zero _ F (F + 32) 32 4 8); [lia | exact F8m | lia | lia |].
  intros i Hi. rewrite KR1 by (unfold TA_OW, TA_M, SHADOW_OFF in *; lia). exact (HZS i Hi).
- apply (frame_hull_vis _ F 256 (F + 32) 32); [lia | exact HF64 | reflexivity | lia | lia | lia |].
  intros i Hi. apply can_aview_vis. exact (HFsh1 i Hi).
- intros regs2 mem2 md2 HJ2 HP2 HZ2 HK2 HG2.
  assert (OUTW : forall a, inG TG.G_HARNESS a -> ~ (F + 32 <= a < F + 64) /\ ~ (sp1 - ESTACK <= a < sp1)).
  { intros a Ha. pose proof (op_G_low a Ha) as Hl. pose proof (op_G_frame _ _ HJ a Ha) as Hf.
    unfold kLowMemEnd, ESTACK in *. split; lia. }
  apply (HK regs2 mem2 md2 HJ2).
  + exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) Q22).
  + intros r Hr H22. exact (eq_trans (HP2 r Hr) (KR r Hr H22)).
  + intros j Hj.
    assert (HG1 : inG TG.G_HARNESS (TA_OW + 232 + Z.of_nat j))
      by (apply (op_inG_row _ _ _ _ TMAP_A_OW); unfold TA_OW, TW.SZ_OW; lia).
    destruct (OUTW _ HG1) as (O1 & O2). pose proof (op_G_low _ HG1) as Hl. unfold kLowMemEnd in Hl.
    rewrite (HK2 (TA_OW + 232 + Z.of_nat j) ltac:(lia) ltac:(lia) O2). exact (op_vm_av _ _ _ _ _ j VOW Hj).
  + intros j Hj.
    assert (HG1 : inG TG.G_HARNESS (TA_M + 88 + Z.of_nat j))
      by (apply (op_inG_row _ _ _ _ TMAP_A_M); unfold TA_M, TW.SZ_M; lia).
    destruct (OUTW _ HG1) as (O1 & O2). pose proof (op_G_low _ HG1) as Hl. unfold kLowMemEnd in Hl.
    rewrite (HK2 (TA_M + 88 + Z.of_nat j) ltac:(lia) ltac:(lia) O2). exact (op_vm_av _ _ _ _ _ j VM Hj).
  + intros i Hi. replace (F + 32 + i) with (F + 32 + i) by reflexivity. exact (HZ2 i Hi).
  + intros a Ha H1 H2 H3 H4. rewrite (HK2 a Ha ltac:(lia) H4). exact (KR1 a Ha H1 H2).
  + intros a Ha. exact (HG2 a (GA1 a Ha)).
Qed.

(* The machine stack of the journal's window is present. *)
Lemma op_stack_pres : forall m md, J m md -> forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) m a.
Proof.
intros m md HJ a Ha. pose proof HJ as (HSTKJ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact (Hpres a Ha).
Qed.

(* The input's bytes, as garr8 of the caller's input states them. *)
Lemma op_g8 : forall m p (D : list byte) (j : nat),
  garr8 segs (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) D) -> (j < length D)%nat ->
  val_mem segs (mrestrict (w_H W) m) (p + Z.of_nat j) 1 (DSpec.at8 D j) /\ 0 <= DSpec.at8 D j < 256.
Proof.
intros m p D j HG Hj. rewrite <- (length_map (fun b : byte => bv_unsigned b) D) in Hj.
destruct (HG j Hj) as [Hv Hr].
assert (E : nth j (map (fun b : byte => bv_unsigned b) D) 0 = DSpec.at8 D j).
{ unfold DSpec.at8, DSpec.bz. rewrite <- (map_nth (fun b : byte => bv_unsigned b) D (DSpec.b8 0) j). reflexivity. }
rewrite E in Hv, Hr. exact (conj Hv Hr).
Qed.

(* What run 4 leaves at the join +0xafc: a1 = the display bit, s3 = the bytes left, s8 = the cursor, s7 = c, s6 = 19,
   the key at c + 28, s3's old value at 144(s1), every other byte and callee-saved register kept. *)
Definition s4_post (regs : bvmap 5 word) (mem : word -> option byte) (disp nr cur key : Z)
    (Q : world segs -> config -> Prop) : Prop :=
  forall regs2 mem2 md2, J mem2 md2 ->
    YK11.getr regs2 11 = w64 disp -> YK11.getr regs2 19 = w64 nr -> YK11.getr regs2 24 = w64 cur ->
    YK11.getr regs2 23 = w64 (F + 32) -> YK11.getr regs2 22 = w64 19 ->
    (forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
       YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    (forall j, (j < 4)%nat -> rdv mem2 (F + 60 + Z.of_nat j) = Some (YO0f.le_byte key 4 j)) ->
    rdword (rdv mem2) (sp1 + 144) = Some (bv_unsigned (YK11.getr regs 19)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 144 <= a < sp1 + 152) ->
       rdv mem2 a = rdv mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
    SRr segs W (at_ O_J regs2 mem2 md2) Q.

(* Run 4's state at +0x500 when four or more bytes were left before the op byte. *)
Lemma s4d_entry : forall regs mem p off0 n0 kb ab db,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) ->
  YK11.getr regs 23 = w64 (n0 - 1) -> YK11.getr regs 27 = w64 n0 -> 4 <= n0 <= 2 ^ 26 ->
  4096 <= p -> 0 <= off0 -> p + off0 + 4 <= alloc_ceiling ->
  (p + off0 + 4 <= F + 60 \/ F + 64 <= p + off0 + 1) ->
  val_mem segs (mrestrict (w_H W) mem) (p + off0 + 1) 1 kb -> val_mem segs (mrestrict (w_H W) mem) (p + off0 + 2) 1 ab ->
  val_mem segs (mrestrict (w_H W) mem) (p + off0 + 3) 1 db ->
  0 <= kb < 256 -> 0 <= ab < 256 -> 0 <= db < 256 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall a, sp1 + 144 <= a < sp1 + 152 -> apresent (w_H W) mem a) ->
  (forall a, F + 60 <= a < F + 64 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (op_E regs [w64 kb; w64 ab; w64 db]) ss_s4d
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem p off0 n0 kb ab db R9 R22 R26 R24 R25 R23 R27 Hn0 Hp Hoff Hpc Hdj Vkb Vab Vdb Bkb Bab Bdb H168 Psp Pc.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (MF : (F + 32) mod 32 = 0).
{ rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
set (E := op_E regs [w64 kb; w64 ab; w64 db]).
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v)
  by (intros n x v Hn Hx Hv; unfold E; rewrite (op_ew regs _ n x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
pose proof (UR 26%nat 26%bv SHADOW_OFF eq_refl R26 ltac:(unfold SHADOW_OFF; lia)) as U26.
pose proof (UR 24%nat 24%bv (p + off0 + 1) eq_refl R24 ltac:(lia)) as U24.
pose proof (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) as U25.
pose proof (UR 23%nat 23%bv (n0 - 1) eq_refl R23 ltac:(lia)) as U23.
pose proof (UR 27%nat 27%bv n0 eq_refl R27 ltac:(lia)) as U27.
assert (EX : forall j v, (j < 3)%nat -> nth j [w64 kb; w64 ab; w64 db] (Z_to_bv 64 0) = w64 v -> 0 <= v < 256 ->
  ew E (32 + j) = w64 v /\ bv_unsigned (ew E (32 + j)) = v).
{ intros j v Hj Hv Hb. unfold E. rewrite (op_ewx regs _ j ltac:(lia)), Hv. split; [reflexivity|].
  unfold w64. apply unsigned_lit_small. lia. }
destruct (EX 0%nat kb ltac:(lia) eq_refl Bkb) as (E32 & U32).
destruct (EX 1%nat ab ltac:(lia) eq_refl Bab) as (E33 & U33).
destruct (EX 2%nat db ltac:(lia) eq_refl Bdb) as (E34 & U34).
cbn [Nat.add] in E32, U32, E33, U33, E34, U34.
assert (DV : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (E22 : ew E 22 = w64 (F + 32)) by (unfold E; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22).
rewrite restrict_mkst_fx. unfold ss_s4d, s4_rs0, s4_kb, s4_ab, s4_db. cbn [app].
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U9, ?U22, ?U24, ?U25.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Psp. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 168 8 (SOff 22 0) (F + 32)); [exact (DV 22%nat _ E22 ltac:(lia)) | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs _ _ _ _ H168).
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Pc. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (p + off0 + 1) 0 1 (SOff 32 0) kb); [exact (DV 32%nat _ E32 ltac:(lia)) | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vkb.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (p + off0) 2 1 (SOff 33 0) ab); [exact (DV 33%nat _ E33 ltac:(lia)) | cbn; lia | cbn; lia |].
    exact Vab.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (p + off0) 3 1 (SOff 34 0) db); [exact (DV 34%nat _ E34 ltac:(lia)) | cbn; lia | cbn; lia |].
    exact Vdb.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U24, U25.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok s4_at0 app].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U22, U26, U24, U25, U23, U27, U32, U33, U34.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold PTRF, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* Run 4 when four or more bytes were left before the op byte: the kind, address and display bytes read. *)
Lemma op4_s4d : forall regs mem md p n (D : list byte) off0 n0 (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) ->
  YK11.getr regs 23 = w64 (n0 - 1) -> YK11.getr regs 27 = w64 n0 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  In (p, n) (ablocks B ly S) -> n = Z.of_nat (length D) -> n < 2 ^ 26 -> 0 <= off0 -> off0 + n0 = n -> 4 <= n0 ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) D) ->
  s4_post regs mem (Z.land (DSpec.at8 D (Z.to_nat (off0 + 3))) 1) (n0 - 4) (p + off0 + 4)
    (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) (DSpec.at8 D (Z.to_nat (off0 + 2)))) Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md p n D off0 n0 Q HJ R9 R22 R26 R24 R25 R23 R27 H168 HZS Hin HnD Hn26 Hoff Hon Hn0 HG8 HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
pose proof (sep_block_frame segs B LAWS ly S W mem md p n LF_CID pos HAR Hin HFIN) as Hsep.
rewrite HFA in Hsep. change (fs_frame_bytes LF_CID) with 256 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (op_frame_pres mem md HJ) as (HFb & HFsh & HFapp). assert (EST : ESTACK = 4096) by reflexivity.
assert (HjD : forall kk, 1 <= kk <= 3 -> (Z.to_nat (off0 + kk) < length D)%nat) by (intros kk Hkk; lia).
destruct (op_g8 mem p D (Z.to_nat (off0 + 1)) HG8 (HjD 1 ltac:(lia))) as (Vkb & Bkb).
destruct (op_g8 mem p D (Z.to_nat (off0 + 2)) HG8 (HjD 2 ltac:(lia))) as (Vab & Bab).
destruct (op_g8 mem p D (Z.to_nat (off0 + 3)) HG8 (HjD 3 ltac:(lia))) as (Vdb & Bdb).
rewrite Z2Nat.id in Vkb, Vab, Vdb by lia. rewrite Z.add_assoc in Vkb, Vab, Vdb.
set (kb := DSpec.at8 D (Z.to_nat (off0 + 1))) in *. set (ab := DSpec.at8 D (Z.to_nat (off0 + 2))) in *.
set (db := DSpec.at8 D (Z.to_nat (off0 + 3))) in *.
pose proof (s4d_entry regs mem p off0 n0 kb ab db R9 R22 R26 R24 R25 R23 R27 ltac:(lia) Hp4096 Hoff ltac:(lia)
  ltac:(lia) Vkb Vab Vdb Bkb Bab Bdb H168 ltac:(intros a Ha; apply (op_stack_pres mem md HJ); lia)
  ltac:(intros a Ha; apply HFb; lia)) as HS.
set (E0 := op_E regs [w64 kb; w64 ab; w64 db]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E0 n) = v)
  by (intros n0' x v Hn Hx Hv; unfold E0; rewrite (op_ew regs _ n0' x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
assert (SHOK : sh_ok segs s4_Bx SH_D E0 (mrestrict (w_H W) mem)).
{ unfold SH_D. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 22%nat (F + 60) 4 (F + 32) 28 32).
    + apply (frame_ra_zero _ F (F + 60) 4 7 8); [lia | exact F8m | lia | lia |].
      intros i Hi. exact (HZS i ltac:(lia)).
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 24%nat (p + off0 + 1) 1 (p + off0 + 1) 0 1).
    + apply (range_addressable_of_block segs B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 25%nat (p + off0 + 2) 2 (p + off0) 2 4).
    + apply (range_addressable_of_block segs B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 25 25%bv eq_refl); exact R25 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_J.
{ op_awr_norm.
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  op_awr_ro.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
  op_awr_ro. op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 144 <= a < sp1 + 152) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 60 <= x < F + 64) \/ (sp1 + 144 <= x < sp1 + 152)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U9, ?U22 in Hx; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 144 8 (SOff 19 0) RG0
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VSP.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 28 4 kexprC RG2
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VKEY.
cbn [base_val] in VSP, VKEY. rewrite (HE1 9%nat) in VSP by lia. rewrite (HE1 22%nat) in VKEY by lia.
rewrite U9 in VSP. rewrite U22 in VKEY.
assert (U32 : U E1 (SOff 32 0) = kb).
{ apply U_atom; [rewrite (HE1 32%nat) by lia; unfold E0; exact (op_ewx regs _ 0 ltac:(lia)) | lia]. }
assert (U33 : U E1 (SOff 33 0) = ab).
{ apply U_atom; [rewrite (HE1 33%nat) by lia; unfold E0; exact (op_ewx regs _ 1 ltac:(lia)) | lia]. }
assert (U34 : U E1 (SOff 34 0) = db).
{ apply U_atom; [rewrite (HE1 34%nat) by lia; unfold E0; exact (op_ewx regs _ 2 ltac:(lia)) | lia]. }
change (bv_unsigned (sv_denot E1 kexprC)) with (U E1 kexprC) in VKEY.
rewrite (kexprC_U E1 kb ab U32 U33 Bkb Bab) in VKEY.
destruct (op_key_val kb ab Bkb Bab) as (_ & BK).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in VKEY. rewrite Z.mod_small in VKEY by exact BK.
change (N.to_nat 4) with 4%nat in VKEY.
assert (E19 : ew E0 19 = YK11.getr regs 19) by (unfold E0; exact (op_ew regs _ 19 19%bv eq_refl)).
replace (bv_unsigned (sv_denot E1 (SOff 19 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 19)) in VSP.
2: { cbn [sv_denot]. rewrite (HE1 19%nat) by lia. rewrite E19.
     rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
     change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
     rewrite Z.mod_small by lia. reflexivity. }
change (N.to_nat 8) with 8%nat in VSP.
clear HF HFr HG RG0 RG2.
pmkst HS.
assert (SD : forall nn c v, (nn < 32)%nat -> bv_unsigned (ew E0 nn) = v -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E1 (SOff nn c) = w64 (v + c)).
{ intros nn c v Hnn Hv Hvc. cbn [sv_denot]. rewrite (HE1 nn) by lia. rewrite Hv. reflexivity. }
op_reg HS (Z_to_bv 5 11) (w64 (Z.land db 1)) Q11
  ltac:(rewrite denot_lit_U, U_and_lit, U34 by lia; reflexivity).
op_reg HS (Z_to_bv 5 19) (w64 (n0 - 4)) Q19
  ltac:(rewrite (SD 27%nat (-4) n0 ltac:(lia) (UR 27%nat 27%bv n0 eq_refl R27 ltac:(lia)) ltac:(lia)); f_equal; lia).
op_reg HS (Z_to_bv 5 24) (w64 (p + off0 + 4)) Q24
  ltac:(rewrite (SD 25%nat 4 (p + off0) ltac:(lia) (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) ltac:(lia)); reflexivity).
op_reg HS (Z_to_bv 5 23) (w64 (F + 32)) Q23
  ltac:(rewrite (SD 22%nat 0 (F + 32) ltac:(lia) U22 ltac:(lia)); f_equal; lia).
op_reg HS (Z_to_bv 5 22) (w64 19) Q22 ltac:(reflexivity).
assert (KR : forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb; w64 ab; w64 db] (ss_regs ssx) _ r
      (fun m Hm => HE1 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H19 H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity]. }
apply (HK (ms_regs ms) (ms_mem ms) md1 HJ Q11 Q19 Q24 Q23 Q22 KR).
- intros j Hj. replace (F + 60 + Z.of_nat j) with (F + 32 + 28 + Z.of_nat j) by lia.
  exact (op_vm_av _ _ _ _ _ j VKEY Hj).
- apply AF0x.val_mem_rdword; [|exact VSP]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
- exact KR1.
- exact GA1.
Qed.

(* Run 4's state at +0x500 when three bytes were left before the op byte (s11 pinned to 3). *)
Lemma s4c_entry : forall regs mem p off0 kb ab,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) ->
  YK11.getr regs 23 = w64 2 -> YK11.getr regs 27 = w64 3 ->
  4096 <= p -> 0 <= off0 -> p + off0 + 3 <= alloc_ceiling ->
  (p + off0 + 3 <= F + 60 \/ F + 64 <= p + off0 + 1) ->
  val_mem segs (mrestrict (w_H W) mem) (p + off0 + 1) 1 kb -> val_mem segs (mrestrict (w_H W) mem) (p + off0 + 2) 1 ab ->
  0 <= kb < 256 -> 0 <= ab < 256 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall a, sp1 + 144 <= a < sp1 + 152 -> apresent (w_H W) mem a) ->
  (forall a, F + 60 <= a < F + 64 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (op_E regs [w64 kb; w64 ab]) ss_s4c
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem p off0 kb ab R9 R22 R26 R24 R25 R23 R27 Hp Hoff Hpc Hdj Vkb Vab Bkb Bab H168 Psp Pc.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (MF : (F + 32) mod 32 = 0).
{ rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
set (E := op_E regs [w64 kb; w64 ab]).
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v)
  by (intros n x v Hn Hx Hv; unfold E; rewrite (op_ew regs _ n x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
pose proof (UR 26%nat 26%bv SHADOW_OFF eq_refl R26 ltac:(unfold SHADOW_OFF; lia)) as U26.
pose proof (UR 24%nat 24%bv (p + off0 + 1) eq_refl R24 ltac:(lia)) as U24.
pose proof (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) as U25.
pose proof (UR 23%nat 23%bv 2 eq_refl R23 ltac:(lia)) as U23.
assert (E32 : ew E 32 = w64 kb) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (E33 : ew E 33 = w64 ab) by (unfold E; exact (op_ewx regs _ 1 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = kb) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = ab) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (DV : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (E22 : ew E 22 = w64 (F + 32)) by (unfold E; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22).
assert (H0 : st_ok_pi segs VAL E (mkSS O_R3 sr_atoms (s4_rs0 ++ [s4_kb; s4_ab]) None
    (mkFacts (s4_at0 ++ [(23%nat, mkAF 1 (2 ^ 26) 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)]) [] []))
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold s4_rs0, s4_kb, s4_ab. cbn [app].
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U22, ?U24, ?U25.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Psp. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 168 8 (SOff 22 0) (F + 32)); [exact (DV 22%nat _ E22 ltac:(lia)) | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword segs _ _ _ _ H168).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Pc. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (p + off0 + 1) 0 1 (SOff 32 0) kb); [exact (DV 32%nat _ E32 ltac:(lia)) | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vkb.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (p + off0) 2 1 (SOff 33 0) ab); [exact (DV 33%nat _ E33 ltac:(lia)) | cbn; lia | cbn; lia |].
      exact Vab.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U24, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok s4_at0 app].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U22, U26, U24, U25, U23, U32, U33.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold PTRF, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) 3 H0 R27 eq_refl).
Qed.

(* Run 4 when three bytes were left before the op byte: the kind and address bytes read, display 0. *)
Lemma op4_s4c : forall regs mem md p n (D : list byte) off0 (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) ->
  YK11.getr regs 23 = w64 2 -> YK11.getr regs 27 = w64 3 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  In (p, n) (ablocks B ly S) -> n = Z.of_nat (length D) -> n < 2 ^ 26 -> 0 <= off0 -> off0 + 3 = n ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) D) ->
  s4_post regs mem 0 0 (p + off0 + 3)
    (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) (DSpec.at8 D (Z.to_nat (off0 + 2)))) Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md p n D off0 Q HJ R9 R22 R26 R24 R25 R23 R27 H168 HZS Hin HnD Hn26 Hoff Hon HG8 HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
pose proof (sep_block_frame segs B LAWS ly S W mem md p n LF_CID pos HAR Hin HFIN) as Hsep.
rewrite HFA in Hsep. change (fs_frame_bytes LF_CID) with 256 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (op_frame_pres mem md HJ) as (HFb & HFsh & HFapp). assert (EST : ESTACK = 4096) by reflexivity.
assert (HjD : forall kk, 1 <= kk <= 2 -> (Z.to_nat (off0 + kk) < length D)%nat) by (intros kk Hkk; lia).
destruct (op_g8 mem p D (Z.to_nat (off0 + 1)) HG8 (HjD 1 ltac:(lia))) as (Vkb & Bkb).
destruct (op_g8 mem p D (Z.to_nat (off0 + 2)) HG8 (HjD 2 ltac:(lia))) as (Vab & Bab).
rewrite Z2Nat.id in Vkb, Vab by lia. rewrite Z.add_assoc in Vkb, Vab.
set (kb := DSpec.at8 D (Z.to_nat (off0 + 1))) in *. set (ab := DSpec.at8 D (Z.to_nat (off0 + 2))) in *.
pose proof (s4c_entry regs mem p off0 kb ab R9 R22 R26 R24 R25 R23 R27 Hp4096 Hoff ltac:(lia)
  ltac:(lia) Vkb Vab Bkb Bab H168 ltac:(intros a Ha; apply (op_stack_pres mem md HJ); lia)
  ltac:(intros a Ha; apply HFb; lia)) as HS.
set (E0 := op_E regs [w64 kb; w64 ab]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E0 n) = v)
  by (intros n0' x v Hn Hx Hv; unfold E0; rewrite (op_ew regs _ n0' x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
assert (SHOK : sh_ok segs s4_Bx SH_C E0 (mrestrict (w_H W) mem)).
{ unfold SH_C. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 22%nat (F + 60) 4 (F + 32) 28 32).
    + apply (frame_ra_zero _ F (F + 60) 4 7 8); [lia | exact F8m | lia | lia |].
      intros i Hi. exact (HZS i ltac:(lia)).
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 24%nat (p + off0 + 1) 1 (p + off0 + 1) 0 1).
    + apply (range_addressable_of_block segs B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 25%nat (p + off0 + 2) 1 (p + off0) 2 3).
    + apply (range_addressable_of_block segs B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 25 25%bv eq_refl); exact R25 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_J.
{ op_awr_norm.
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  op_awr_ro.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
  op_awr_ro. op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 144 <= a < sp1 + 152) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 60 <= x < F + 64) \/ (sp1 + 144 <= x < sp1 + 152)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U9, ?U22 in Hx; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 144 8 (SOff 19 0) RG0
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VSP.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 28 4 kexprC RG2
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VKEY.
cbn [base_val] in VSP, VKEY. rewrite (HE1 9%nat) in VSP by lia. rewrite (HE1 22%nat) in VKEY by lia.
rewrite U9 in VSP. rewrite U22 in VKEY.
assert (U32 : U E1 (SOff 32 0) = kb).
{ apply U_atom; [rewrite (HE1 32%nat) by lia; unfold E0; exact (op_ewx regs _ 0 ltac:(lia)) | lia]. }
assert (U33 : U E1 (SOff 33 0) = ab).
{ apply U_atom; [rewrite (HE1 33%nat) by lia; unfold E0; exact (op_ewx regs _ 1 ltac:(lia)) | lia]. }
change (bv_unsigned (sv_denot E1 kexprC)) with (U E1 kexprC) in VKEY.
rewrite (kexprC_U E1 kb ab U32 U33 Bkb Bab) in VKEY.
destruct (op_key_val kb ab Bkb Bab) as (_ & BK).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in VKEY. rewrite Z.mod_small in VKEY by exact BK.
change (N.to_nat 4) with 4%nat in VKEY.
assert (E19 : ew E0 19 = YK11.getr regs 19) by (unfold E0; exact (op_ew regs _ 19 19%bv eq_refl)).
replace (bv_unsigned (sv_denot E1 (SOff 19 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 19)) in VSP.
2: { cbn [sv_denot]. rewrite (HE1 19%nat) by lia. rewrite E19.
     rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
     change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
     rewrite Z.mod_small by lia. reflexivity. }
change (N.to_nat 8) with 8%nat in VSP.
clear HF HFr HG RG0 RG2.
pmkst HS.
assert (SD : forall nn c v, (nn < 32)%nat -> bv_unsigned (ew E0 nn) = v -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E1 (SOff nn c) = w64 (v + c)).
{ intros nn c v Hnn Hv Hvc. cbn [sv_denot]. rewrite (HE1 nn) by lia. rewrite Hv. reflexivity. }
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 19) (w64 0) Q19 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 24) (w64 (p + off0 + 3)) Q24
  ltac:(rewrite (SD 25%nat 3 (p + off0) ltac:(lia) (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) ltac:(lia)); reflexivity).
op_reg HS (Z_to_bv 5 23) (w64 (F + 32)) Q23
  ltac:(rewrite (SD 22%nat 0 (F + 32) ltac:(lia) U22 ltac:(lia)); f_equal; lia).
op_reg HS (Z_to_bv 5 22) (w64 19) Q22 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 27) (w64 3) Q27 ltac:(reflexivity).
assert (KR : forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb; w64 ab] (ss_regs ssx) _ r
      (fun m Hm => HE1 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H19 H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity | exact (eq_trans Q27 (eq_sym R27))]. }
apply (HK (ms_regs ms) (ms_mem ms) md1 HJ Q11 Q19 Q24 Q23 Q22 KR).
- intros j Hj. replace (F + 60 + Z.of_nat j) with (F + 32 + 28 + Z.of_nat j) by lia.
  exact (op_vm_av _ _ _ _ _ j VKEY Hj).
- apply AF0x.val_mem_rdword; [|exact VSP]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
- exact KR1.
- exact GA1.
Qed.

(* Run 4's state at +0x500 when two bytes were left before the op byte (s11 pinned to 2). *)
Lemma s4b_entry : forall regs mem p off0 kb,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) ->
  YK11.getr regs 23 = w64 1 -> YK11.getr regs 27 = w64 2 ->
  4096 <= p -> 0 <= off0 -> p + off0 + 2 <= alloc_ceiling ->
  (p + off0 + 2 <= F + 60 \/ F + 64 <= p + off0 + 1) ->
  val_mem segs (mrestrict (w_H W) mem) (p + off0 + 1) 1 kb -> 0 <= kb < 256 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall a, sp1 + 144 <= a < sp1 + 152 -> apresent (w_H W) mem a) ->
  (forall a, F + 60 <= a < F + 64 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (op_E regs [w64 kb]) ss_s4b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem p off0 kb R9 R22 R26 R24 R25 R23 R27 Hp Hoff Hpc Hdj Vkb Bkb H168 Psp Pc.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (MF : (F + 32) mod 32 = 0).
{ rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
set (E := op_E regs [w64 kb]).
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v)
  by (intros n x v Hn Hx Hv; unfold E; rewrite (op_ew regs _ n x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
pose proof (UR 26%nat 26%bv SHADOW_OFF eq_refl R26 ltac:(unfold SHADOW_OFF; lia)) as U26.
pose proof (UR 24%nat 24%bv (p + off0 + 1) eq_refl R24 ltac:(lia)) as U24.
pose proof (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) as U25.
pose proof (UR 23%nat 23%bv 1 eq_refl R23 ltac:(lia)) as U23.
assert (E32 : ew E 32 = w64 kb) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = kb) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (DV : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (E22 : ew E 22 = w64 (F + 32)) by (unfold E; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22).
assert (H0 : st_ok_pi segs VAL E (mkSS O_R3 sr_atoms (s4_rs0 ++ [s4_kb]) None
    (mkFacts (s4_at0 ++ [(23%nat, mkAF 1 (2 ^ 26) 0); (32%nat, mkAF 0 255 0)]) [] []))
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold s4_rs0, s4_kb. cbn [app].
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U22, ?U24.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Psp. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 168 8 (SOff 22 0) (F + 32)); [exact (DV 22%nat _ E22 ltac:(lia)) | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword segs _ _ _ _ H168).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Pc. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (p + off0 + 1) 0 1 (SOff 32 0) kb); [exact (DV 32%nat _ E32 ltac:(lia)) | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vkb.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok s4_at0 app].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U22, U26, U24, U25, U23, U32.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold PTRF, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) 2 H0 R27 eq_refl).
Qed.

(* Run 4 when two bytes were left before the op byte: the kind byte read, address and display 0. *)
Lemma op4_s4b : forall regs mem md p n (D : list byte) off0 (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) ->
  YK11.getr regs 23 = w64 1 -> YK11.getr regs 27 = w64 2 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall i, 4 <= i < 8 -> rdv mem (SHF + i) = Some 0) ->
  In (p, n) (ablocks B ly S) -> n = Z.of_nat (length D) -> n < 2 ^ 26 -> 0 <= off0 -> off0 + 2 = n ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) D) ->
  s4_post regs mem 0 0 (p + off0 + 2) (DSpec.KEY (DSpec.at8 D (Z.to_nat (off0 + 1)) mod 9 + 1) 0) Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md p n D off0 Q HJ R9 R22 R26 R24 R25 R23 R27 H168 HZS Hin HnD Hn26 Hoff Hon HG8 HK.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
pose proof (sep_block_frame segs B LAWS ly S W mem md p n LF_CID pos HAR Hin HFIN) as Hsep.
rewrite HFA in Hsep. change (fs_frame_bytes LF_CID) with 256 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (op_frame_pres mem md HJ) as (HFb & HFsh & HFapp). assert (EST : ESTACK = 4096) by reflexivity.
destruct (op_g8 mem p D (Z.to_nat (off0 + 1)) HG8 ltac:(lia)) as (Vkb & Bkb).
rewrite Z2Nat.id in Vkb by lia. rewrite Z.add_assoc in Vkb.
set (kb := DSpec.at8 D (Z.to_nat (off0 + 1))) in *.
pose proof (s4b_entry regs mem p off0 kb R9 R22 R26 R24 R25 R23 R27 Hp4096 Hoff ltac:(lia)
  ltac:(lia) Vkb Bkb H168 ltac:(intros a Ha; apply (op_stack_pres mem md HJ); lia)
  ltac:(intros a Ha; apply HFb; lia)) as HS.
set (E0 := op_E regs [w64 kb]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E0 n) = v)
  by (intros n0' x v Hn Hx Hv; unfold E0; rewrite (op_ew regs _ n0' x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
assert (SHOK : sh_ok segs s4_Bx SH_B E0 (mrestrict (w_H W) mem)).
{ unfold SH_B. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 22%nat (F + 60) 4 (F + 32) 28 32).
    + apply (frame_ra_zero _ F (F + 60) 4 7 8); [lia | exact F8m | lia | lia |].
      intros i Hi. exact (HZS i ltac:(lia)).
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E0 s4_Bx 24%nat (p + off0 + 1) 1 (p + off0 + 1) 0 1).
    + apply (range_addressable_of_block segs B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
    + unfold s4_Bx. apply U_atom; [unfold E0; rewrite (op_ew regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
    + apply U_atom; [unfold E0; rewrite (op_ew regs _ 24 24%bv eq_refl); exact R24 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan O_J.
{ op_awr_norm.
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  op_awr_ro.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
  op_awr_ro. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 144 <= a < sp1 + 152) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 60 <= x < F + 64) \/ (sp1 + 144 <= x < sp1 + 152)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U9, ?U22 in Hx; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 144 8 (SOff 19 0) RG0
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VSP.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 28 4 kexpr RG2
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VKEY.
cbn [base_val] in VSP, VKEY. rewrite (HE1 9%nat) in VSP by lia. rewrite (HE1 22%nat) in VKEY by lia.
rewrite U9 in VSP. rewrite U22 in VKEY.
assert (U32 : U E1 (SOff 32 0) = kb).
{ apply U_atom; [rewrite (HE1 32%nat) by lia; unfold E0; exact (op_ewx regs _ 0 ltac:(lia)) | lia]. }
change (bv_unsigned (sv_denot E1 kexpr)) with (U E1 kexpr) in VKEY.
rewrite (kexpr_U E1 kb U32 Bkb) in VKEY.
destruct (op_key_val kb 0 Bkb ltac:(lia)) as (EK & BK). rewrite Z.add_0_r in EK. rewrite <- EK in VKEY.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in VKEY. rewrite Z.mod_small in VKEY by exact BK.
change (N.to_nat 4) with 4%nat in VKEY.
assert (E19 : ew E0 19 = YK11.getr regs 19) by (unfold E0; exact (op_ew regs _ 19 19%bv eq_refl)).
replace (bv_unsigned (sv_denot E1 (SOff 19 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 19)) in VSP.
2: { cbn [sv_denot]. rewrite (HE1 19%nat) by lia. rewrite E19.
     rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
     change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
     rewrite Z.mod_small by lia. reflexivity. }
change (N.to_nat 8) with 8%nat in VSP.
clear HF HFr HG RG0 RG2.
pmkst HS.
assert (SD : forall nn c v, (nn < 32)%nat -> bv_unsigned (ew E0 nn) = v -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E1 (SOff nn c) = w64 (v + c)).
{ intros nn c v Hnn Hv Hvc. cbn [sv_denot]. rewrite (HE1 nn) by lia. rewrite Hv. reflexivity. }
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 19) (w64 0) Q19 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 24) (w64 (p + off0 + 2)) Q24
  ltac:(rewrite (SD 25%nat 2 (p + off0) ltac:(lia) (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) ltac:(lia)); reflexivity).
op_reg HS (Z_to_bv 5 23) (w64 (F + 32)) Q23
  ltac:(rewrite (SD 22%nat 0 (F + 32) ltac:(lia) U22 ltac:(lia)); f_equal; lia).
op_reg HS (Z_to_bv 5 22) (w64 19) Q22 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 27) (w64 2) Q27 ltac:(reflexivity).
assert (KR : forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 kb] (ss_regs ssx) _ r
      (fun m Hm => HE1 m ltac:(lia)) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H19 H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity | exact (eq_trans Q27 (eq_sym R27))]. }
apply (HK (ms_regs ms) (ms_mem ms) md1 HJ Q11 Q19 Q24 Q23 Q22 KR).
- intros j Hj. replace (F + 60 + Z.of_nat j) with (F + 32 + 28 + Z.of_nat j) by lia.
  exact (op_vm_av _ _ _ _ _ j VKEY Hj).
- apply AF0x.val_mem_rdword; [|exact VSP]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
- exact KR1.
- exact GA1.
Qed.

(* Run 4's state at +0x500 when one byte was left before the op byte (s7 pinned to 0). *)
Lemma s4a_entry : forall regs mem p off0,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) -> YK11.getr regs 23 = w64 0 ->
  4096 <= p -> 0 <= off0 -> p + off0 + 1 <= alloc_ceiling ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  (forall a, sp1 + 144 <= a < sp1 + 152 -> apresent (w_H W) mem a) ->
  (forall a, F + 60 <= a < F + 64 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (op_E regs []) ss_s4a
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem p off0 R9 R22 R26 R24 R25 R23 Hp Hoff Hpc H168 Psp Pc.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (MF : (F + 32) mod 32 = 0).
{ rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
set (E := op_E regs []).
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v)
  by (intros n x v Hn Hx Hv; unfold E; rewrite (op_ew regs _ n x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
pose proof (UR 26%nat 26%bv SHADOW_OFF eq_refl R26 ltac:(unfold SHADOW_OFF; lia)) as U26.
pose proof (UR 24%nat 24%bv (p + off0 + 1) eq_refl R24 ltac:(lia)) as U24.
pose proof (UR 25%nat 25%bv (p + off0) eq_refl R25 ltac:(lia)) as U25.
assert (DV : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (E22 : ew E 22 = w64 (F + 32)) by (unfold E; rewrite (op_ew regs _ 22 22%bv eq_refl); exact R22).
assert (H0 : st_ok_pi segs VAL E (mkSS O_R3 sr_atoms s4_rs0 None (mkFacts s4_at0 [] []))
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_R3)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold s4_rs0.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U22.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Psp. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 168 8 (SOff 22 0) (F + 32)); [exact (DV 22%nat _ E22 ltac:(lia)) | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword segs _ _ _ _ H168).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Pc. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok s4_at0 app].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U22, U26, U24, U25.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold PTRF, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) 0 H0 R23 eq_refl).
Qed.

(* Run 4 when one byte was left before the op byte: no byte read, key 1 << 16, display 0. *)
Lemma op4_s4a : forall regs mem md p n off0 (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 (F + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (p + off0 + 1) -> YK11.getr regs 25 = w64 (p + off0) -> YK11.getr regs 23 = w64 0 ->
  rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  In (p, n) (ablocks B ly S) -> 0 <= off0 -> off0 + 1 = n ->
  s4_post regs mem 0 0 (p + off0 + 1) (DSpec.KEY 1 0) Q ->
  SRr segs W (at_ O_R3 regs mem md) Q.
Proof.
intros regs mem md p n off0 Q HJ R9 R22 R26 R24 R25 R23 H168 Hin Hoff Hon HK.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
destruct (op_frame_pres mem md HJ) as (HFb & HFsh & HFapp). assert (EST : ESTACK = 4096) by reflexivity.
pose proof (s4a_entry regs mem p off0 R9 R22 R26 R24 R25 R23 Hp4096 Hoff ltac:(lia) H168
  ltac:(intros a Ha; apply (op_stack_pres mem md HJ); lia) ltac:(intros a Ha; apply HFb; lia)) as HS.
set (E0 := op_E regs []) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (UR : forall n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr regs x = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E0 n) = v)
  by (intros n0' x v Hn Hx Hv; unfold E0; rewrite (op_ew regs _ n0' x Hn), Hx; unfold w64; apply unsigned_lit_small; lia).
pose proof (UR 9%nat 9%bv sp1 eq_refl R9 ltac:(lia)) as U9.
pose proof (UR 22%nat 22%bv (F + 32) eq_refl R22 ltac:(lia)) as U22.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK B0 O_J.
{ op_awr_norm.
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  op_awr_ro.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 <= a < F + 64) -> ~ (sp1 + 144 <= a < sp1 + 152) ->
  rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 60 <= x < F + 64) \/ (sp1 + 144 <= x < sp1 + 152)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U9, ?U22 in Hx; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
pose proof (sn_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 144 8 (SOff 19 0) RG0
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VSP.
pose proof (sn_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 28 4 (SLit 65536) RG2
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VKEY.
cbn [base_val] in VSP, VKEY. rewrite U9 in VSP. rewrite U22 in VKEY.
change (bv_unsigned (sv_denot E0 (SLit 65536)) mod 2 ^ (8 * Z.of_N 4)) with (DSpec.KEY 1 0) in VKEY.
change (N.to_nat 4) with 4%nat in VKEY.
assert (E19 : ew E0 19 = YK11.getr regs 19) by (unfold E0; exact (op_ew regs _ 19 19%bv eq_refl)).
replace (bv_unsigned (sv_denot E0 (SOff 19 0)) mod 2 ^ (8 * Z.of_N 8)) with (bv_unsigned (YK11.getr regs 19)) in VSP.
2: { cbn [sv_denot]. rewrite E19.
     rewrite Z.add_0_r, Z_to_bv_bv_unsigned. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
     change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
     rewrite Z.mod_small by lia. reflexivity. }
change (N.to_nat 8) with 8%nat in VSP.
clear HF HFr HG RG0 RG2.
pmkst HS.
op_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 19) (w64 0) Q19 ltac:(reflexivity).
op_reg HS (Z_to_bv 5 24) (w64 (p + off0 + 1)) Q24
  ltac:(cbn [sv_denot]; rewrite (UR 24%nat 24%bv (p + off0 + 1) eq_refl R24 ltac:(lia)), Z.add_0_r; reflexivity).
op_reg HS (Z_to_bv 5 23) (w64 (F + 32)) Q23
  ltac:(cbn [sv_denot]; rewrite U22, Z.add_0_r; reflexivity).
op_reg HS (Z_to_bv 5 22) (w64 19) Q22 ltac:(reflexivity).
assert (KR : forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [] (ss_regs ssx) _ r
      (fun m Hm => eq_refl) (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR end.
  intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; intros H19 H22 H23 H24;
    first [exfalso; lia | apply HKR; vm_compute; reflexivity]. }
apply (HK (ms_regs ms) (ms_mem ms) md1 HJ Q11 Q19 Q24 Q23 Q22 KR).
- intros j Hj. replace (F + 60 + Z.of_nat j) with (F + 32 + 28 + Z.of_nat j) by lia.
  exact (op_vm_av _ _ _ _ _ j VKEY Hj).
- apply AF0x.val_mem_rdword; [|exact VSP]. pose proof (bv_unsigned_in_range 64 (YK11.getr regs 19)) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
- exact KR1.
- exact GA1.
Qed.

(* Run 5's state at the join +0xafc. *)
Lemma s5_entry : forall regs mem graw,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 23 = w64 (F + 32) ->
  rdword (rdv mem) (sp1 + 120) = Some PG_RAW ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_raw 4 graw -> 0 <= graw < 2 ^ 32 ->
  apresent (w_H W) mem (F + 57) ->
  st_ok_pi segs VAL (op_E regs [w64 graw]) ss_s5
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O_J)) mem (YK11.seg_rom segs))).
Proof.
intros regs mem graw R9 R23 H120 HGV HG Pc.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (MF : (F + 32) mod 32 = 0).
{ rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
set (E := op_E regs [w64 graw]).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (op_ew regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = F + 32)
  by (unfold E; rewrite (op_ew regs _ 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 graw) by (unfold E; exact (op_ewx regs _ 0 ltac:(lia))).
rewrite restrict_mkst_fx. unfold ss_s5, s5_rs.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U23.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 120 8 (SLit PG_RAW) PG_RAW); [reflexivity | unfold PG_RAW; cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword segs _ _ _ _ H120).
  + split; [unfold TA_g_raw; lia|]. split; [unfold TA_g_raw; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 TA_g_raw 4 (SOff 32 0) graw); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HGV].
    cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (F + 32 + o) with (F + 57) by lia. exact Pc.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TA_g_raw in *. repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U23.
  change (2 ^ 5) with 32. unfold PTRF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* Run 5: g_raw, c + 25 := the display bit, `beqz a0`: SUBR when g_raw <> 0, SUBT when g_raw = 0. *)
Lemma op4_s5 : forall regs mem md disp graw (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 23 = w64 (F + 32) -> YK11.getr regs 11 = w64 disp -> 0 <= disp < 256 ->
  rdword (rdv mem) (sp1 + 120) = Some PG_RAW ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_raw 4 graw -> 0 <= graw < 2 ^ 32 ->
  (forall regs2 mem2 md2 pc, J mem2 md2 ->
     (forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
     rdv mem2 (F + 57) = Some disp ->
     (forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> rdv mem2 a = rdv mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     (pc = LO_SUBR /\ graw <> 0) \/ (pc = LO_SUBT /\ graw = 0) ->
     SRr segs W (at_ pc regs2 mem2 md2) Q) ->
  SRr segs W (at_ O_J regs mem md) Q.
Proof.
intros regs mem md disp graw Q HJ R9 R23 R11 Hdisp H120 HGV HGr HK.
pose proof asan_consts as ((C1 & C2) & _).
destruct (op_frame_pres mem md HJ) as (HFb & _ & _).
pose proof (s5_entry regs mem graw R9 R23 H120 HGV HGr (HFb (F + 57) ltac:(lia))) as HS.
set (E0 := op_E regs [w64 graw]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply op_env.
assert (U23 : bv_unsigned (ew E0 23) = F + 32)
  by (unfold E0; rewrite (op_ew regs _ 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : U E0 (SOff 32 0) = graw)
  by (apply U_atom; [unfold E0; exact (op_ewx regs _ 0 ltac:(lia)) | lia]).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ SHOK B0.
{ op_awr_norm. op_awr_ro. op_awr_ro.
  eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> rdv (ms_mem ms) a = rdv mem a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => x = F + 57) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U23 in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (VDx : forall Ex m b lo hi wlo whi chunks, (forall j, (j < 1024)%nat -> ew Ex j = ew E0 j) ->
  region_ok segs Ex (mrestrict (w_H W) m) (YP09.mkRegion b lo hi wlo whi chunks) -> b = Some 23%nat ->
  In (YP09.mkChunk 25 (YP09.CVal 1 (SOff 11 0))) chunks -> rdv m (F + 57) = Some disp).
{ intros Ex m b lo hi wlo whi chunks HEx RG Hb Hin. subst b.
  pose proof (sn_chunk_val Ex (w_H W) m _ _ _ _ _ _ 25 1 (SOff 11 0) RG Hin ltac:(lia)) as VD.
  cbn [base_val] in VD. rewrite (HEx 23%nat) in VD by lia. rewrite U23 in VD.
  replace (bv_unsigned (sv_denot Ex (SOff 11 0)) mod 2 ^ (8 * Z.of_N 1)) with disp in VD.
  2: { cbn [sv_denot]. rewrite (HEx 11%nat) by lia. unfold E0.
       rewrite (op_ew regs _ 11 11%bv eq_refl), R11, Z.add_0_r. unfold w64.
       rewrite Z_to_bv_bv_unsigned, unsigned_lit_small by lia. change (2 ^ (8 * Z.of_N 1)) with 256.
       rewrite Z.mod_small by lia. reflexivity. }
  change (N.to_nat 1) with 1%nat in VD.
  pose proof (op_vm_av _ _ _ _ _ 0 VD ltac:(lia)) as V. cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
  replace (F + 32 + 25) with (F + 57) in V by lia. rewrite V. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity. }
clear HF HFr HG.
rename ms into ms1.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
  by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U23' : bv_unsigned (ew E1 23) = F + 32) by (rewrite (HE1 23%nat) by lia; exact U23).
assert (U32' : U E1 (SOff 32 0) = graw)
  by (apply U_atom; [rewrite (HE1 32%nat) by lia; unfold E0; exact (op_ewx regs _ 0 ltac:(lia)) | lia]).
psrr_branch_tok RUN BR HS SHOK B0.
- (* g_raw = 0: SUBT *)
  destruct (op_swrap_z graw HGr) as ((S1 & _) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small graw) in Hc by lia.
  apply Z.eqb_eq in Hc. apply S1 in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK B0 LO_SUBT.
  { op_awr_norm. op_awr_ro. op_awr_ro.
    eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U23', ?U23 in Ha.
      left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
    apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U23'' : bv_unsigned (ew E2 23) = F + 32) by (rewrite (HE2 23%nat) by lia; exact U23).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1.
    apply (kept_of_frame _ _ _ _ _ (fun x => x = F + 57) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U23'', ?U23', ?U23 in Hx; lia). }
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  pose proof (VDx _ _ _ _ _ _ _ _ HE2 RG2 eq_refl ltac:(cbn [In]; left; reflexivity)) as VD1.
  assert (GA2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 graw] (ss_regs ssx) _ r (fun m Hm => HE2 m ltac:(lia))
      (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR2 end.
  pmkst HS. apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBT HJ).
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; apply HKR2; vm_compute; reflexivity.
  + exact VD1.
  + intros a Ha H1. rewrite (KR2 a Ha H1). exact (KR1 a Ha H1).
  + exact GA2.
  + right. split; [reflexivity | exact Hc].
- (* g_raw <> 0: SUBR *)
  destruct (op_swrap_z graw HGr) as ((_ & S1) & _).
  rewrite branch_eq_U, U_SExt, U32' in Hc. rewrite (U_lit E1 0) in Hc by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite (Z.mod_small graw) in Hc by lia.
  apply Z.eqb_neq in Hc.
  assert (Hc' : graw <> 0) by (intros Eg; apply Hc; exact (S1 Eg)).
  paj_run_to_tok RUNTO HS HJ SHOK B0 LO_SUBR.
  { op_awr_norm. op_awr_ro. op_awr_ro.
    eapply awr_ok_x_cons_own with (cid := LF_CID) (pos := pos); [exact HOWN | |].
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U23', ?U23 in Ha.
      left. unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes LF_CID) with 256. lia. }
    apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
  assert (U23'' : bv_unsigned (ew E2 23) = F + 32) by (rewrite (HE2 23%nat) by lia; exact U23).
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> a <> F + 57 -> rdv (ms_mem ms) a = rdv (ms_mem ms1) a).
  { intros a Ha H1.
    apply (kept_of_frame _ _ _ _ _ (fun x => x = F + 57) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U23'', ?U23', ?U23 in Hx; lia). }
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  pose proof (VDx _ _ _ _ _ _ _ _ HE2 RG2 eq_refl ltac:(cbn [In]; left; reflexivity)) as VD1.
  assert (GA2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG RG2.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (fun r => op_kr Ex regs [w64 graw] (ss_regs ssx) _ r (fun m Hm => HE2 m ltac:(lia))
      (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)) as HKR2 end.
  pmkst HS. apply (HK (ms_regs ms) (ms_mem ms) md2 LO_SUBR HJ).
  + intros r Hr. pattern r. revert Hr. revert r. apply op_saved_cases; apply HKR2; vm_compute; reflexivity.
  + exact VD1.
  + intros a Ha H1. rewrite (KR2 a Ha H1). exact (KR1 a Ha H1).
  + exact GA2.
  + left. split; [reflexivity | exact Hc'].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The five steps composed: the arm to SUBR / SUBT                  *)
(* ------------------------------------------------------------------ *)

Lemma op_twin_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof. intros x (o & b & n & Hin & Hx). exact (op_inG_row o b n x Hin Hx). Qed.
Lemma op_inG_OW : forall a, TA_OW <= a < TA_OW + 304 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_A_OW). unfold TW.SZ_OW. lia. Qed.
Lemma op_inG_GOT : forall a, TA_GOT <= a < TA_GOT + 224 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_A_GOT). unfold TW.SZ_GOT. lia. Qed.
Lemma op_inG_M : forall a, TA_M + 88 <= a < TA_M + 92 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (op_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia. Qed.

(* Where the bytes of G, the frame's shadow, the stack from sp1 to sp0, the blocks and the frame past c lie: apart
   from what the segment writes outside G (the shadow bytes 4 .. 7, c, 144(s1), the memsets' stack window). *)
Lemma op_G_apart : forall m md, J m md -> forall a, inG TG.G_HARNESS a ->
  0 <= a < 2 ^ 64 /\ ~ (SHF + 4 <= a < SHF + 8) /\ ~ (F + 32 <= a < F + 64) /\
  ~ (sp1 + 144 <= a < sp1 + 152) /\ ~ (sp1 - ESTACK <= a < sp1).
Proof.
intros m md HJ a Ha. pose proof (op_G_low a Ha) as Hl. pose proof (op_G_frame m md HJ a Ha) as Hf.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (_ & _ & F8b).
unfold kLowMemEnd, ESTACK, SHADOW_OFF in *. repeat split; lia.
Qed.
Lemma op_SH_apart : forall m md, J m md -> forall i, 0 <= i < 32 ->
  0 <= SHF + i < 2 ^ 64 /\ ~ inG TG.G_HARNESS (SHF + i) /\ ~ (F + 32 <= SHF + i < F + 64) /\
  ~ (sp1 + 144 <= SHF + i < sp1 + 152) /\ ~ (sp1 - ESTACK <= SHF + i < sp1).
Proof.
intros m md HJ i Hi. destruct (op_frame_pres m md HJ) as (_ & _ & Happ).
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (NG : ~ inG TG.G_HARNESS (SHF + i)).
{ intros HG. pose proof (op_G_low _ HG) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold ESTACK, SHADOW_OFF in *.
split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.
Lemma op_stk_apart : forall a, sp1 <= a <= sp0 ->
  0 <= a < 2 ^ 64 /\ ~ inG TG.G_HARNESS a /\ ~ (SHF + 4 <= a < SHF + 8) /\ ~ (F + 32 <= a < F + 64) /\
  ~ (sp1 - ESTACK <= a < sp1).
Proof.
intros a Ha. pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (_ & _ & F8b).
assert (NG : ~ inG TG.G_HARNESS a) by (intros HG; pose proof (op_G_low _ HG) as Hl; unfold kLowMemEnd in *; lia).
unfold ESTACK, SHADOW_OFF. split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.
Lemma op_blk_apart : forall m md b n, J m md -> In (b, n) (ablocks B ly S) -> forall j, 0 <= j < req_size n ->
  0 <= b + j < 2 ^ 64 /\ ~ inG TG.G_HARNESS (b + j) /\ ~ (SHF + 4 <= b + j < SHF + 8) /\
  ~ (F + 32 <= b + j < F + 64) /\ ~ (sp1 + 144 <= b + j < sp1 + 152) /\ ~ (sp1 - ESTACK <= b + j < sp1).
Proof.
intros m md b n HJ Hin j Hj.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof (sep_block_frame segs B LAWS ly S W m md b n LF_CID pos HAR Hin HFIN) as Hsep.
rewrite HFA in Hsep. change (fs_frame_bytes LF_CID) with 256 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (NG : ~ inG TG.G_HARNESS (b + j)).
{ intros HG. apply (blk_img segs B LAWS ly S W m md b n (b + j) HAR Hin ltac:(lia)). exact (trans_g_img _ HG). }
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold ESTACK, SHADOW_OFF in *.
split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.
Lemma op_ftail_apart : forall m md a, J m md -> F + 64 <= a < F + 256 ->
  0 <= a < 2 ^ 64 /\ ~ inG TG.G_HARNESS a /\ ~ (SHF + 4 <= a < SHF + 8) /\ ~ (F + 32 <= a < F + 64) /\
  ~ (sp1 + 144 <= a < sp1 + 152) /\ ~ (sp1 - ESTACK <= a < sp1).
Proof.
intros m md a HJ Ha. destruct (op_frame_pres m md HJ) as (_ & _ & Happ).
pose proof asan_consts as ((C1 & C2) & _). pose proof op_F8 as (F8 & F8m & F8b).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (NG : ~ inG TG.G_HARNESS a) by (intros HG; exact (op_G_frame m md HJ a HG ltac:(lia))).
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold ESTACK, SHADOW_OFF in *.
split; [lia|]. split; [exact NG|]. repeat split; lia.
Qed.

Lemma op_rdw_kept : forall m m' a v, (forall k, 0 <= k < 8 -> rdv m' (a + k) = rdv m (a + k)) ->
  rdword (rdv m) a = Some v -> rdword (rdv m') a = Some v.
Proof. intros m m' a v Hk Hv. rewrite (rdword_ext (rdv m) (rdv m') a Hk). exact Hv. Qed.

(* Byte j of c at a memory. *)
Lemma op_c_garr8 : forall m disp key, 0 <= disp < 256 ->
  (forall j, (j < 32)%nat -> rdv m (F + 32 + Z.of_nat j) =
     Some (if (j =? 25)%nat then disp else if (j <? 28)%nat then 0 else YO0f.le_byte key 4 (j - 28))) ->
  garr8 segs (mrestrict (w_H W) m) (F + 32) (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 disp key)).
Proof.
intros m disp key Hd Hv. unfold garr8. intros j Hj.
assert (HL : length (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, repeat_length, TWL.length_put. reflexivity. }
rewrite HL in Hj. rewrite (op_cmd_nth disp key j Hd Hj).
split.
- apply AE36.val_mem1_of_aview. exact (Hv j Hj).
- destruct (j =? 25)%nat; [lia|]. destruct (j <? 28)%nat; [lia|]. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* What the segment leaves for the cut at SUBR / SUBT, from the arm's registers regs and memory mem, the start world Bw,
   the input D at p and the cursor c0 before the op byte. *)
Definition op4_post (regs : bvmap 5 word) (mem : word -> option byte) (Bw : list byte) (p : Z) (D : list byte)
    (c0 : TOP.fuzz_in) (Q : world segs -> config -> Prop) : Prop :=
  forall regs2 mem2 md2 pc B4, J mem2 md2 ->
    TC.op_begin_m Bw = Some (B4, tt) ->
    (pc = LO_SUBR /\ TW.g_raw B4 <> 0) \/ (pc = LO_SUBT /\ TW.g_raw B4 = 0) ->
    (forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
       YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
    YK11.getr regs2 23 = w64 (F + 32) -> YK11.getr regs2 22 = w64 19 ->
    YK11.getr regs2 24 = w64 (p + TOP.fi_off (sv_c (lc_sub_kd D (lc_oc D c0)))) ->
    YK11.getr regs2 19 = w64 (TOP.fi_n (sv_c (lc_sub_kd D (lc_oc D c0)))) ->
    tw_at TMAP_A (rdv mem2) B4 ->
    garr8 segs (mrestrict (w_H W) mem2) (F + 32)
      (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display (lc_sub_kd D (lc_oc D c0)))
        (sv_key (lc_sub_kd D (lc_oc D c0))))) ->
    rdword (rdv mem2) (sp1 + 144) = Some (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued Bw)))) ->
    (forall i, 4 <= i < 8 -> rdv mem2 (SHF + i) = Some 0) ->
    (forall i, 0 <= i < 32 -> ~ (4 <= i < 8) -> rdv mem2 (SHF + i) = rdv mem (SHF + i)) ->
    (forall a, sp1 <= a <= sp0 -> ~ (sp1 + 144 <= a < sp1 + 152) -> rdv mem2 a = rdv mem a) ->
    (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m -> rdv mem2 (b + i) = rdv mem (b + i)) ->
    (forall a, F + 64 <= a < F + 256 -> rdv mem2 a = rdv mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
    SRr segs W (at_ pc regs2 mem2 md2) Q.

Lemma op4_main : forall regs mem md (Bw : list byte) p n (D : list byte) (c0 : TOP.fuzz_in)
    (Q : world segs -> config -> Prop),
  J mem md ->
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 SHF -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 20 = w64 PG_GFN ->
  YK11.getr regs 25 = w64 (p + TOP.fi_off c0) -> YK11.getr regs 27 = w64 (TOP.fi_n c0) ->
  YK11.getr regs 24 = w64 (p + TOP.fi_off (lc_oc D c0)) -> YK11.getr regs 23 = w64 (TOP.fi_n (lc_oc D c0)) ->
  rdword (rdv mem) (sp1 + 112) = Some TA_g_s -> rdword (rdv mem) (sp1 + 168) = Some (F + 32) ->
  rdword (rdv mem) (sp1 + 184) = Some TA_M -> rdword (rdv mem) (sp1 + 120) = Some PG_RAW ->
  tw_at TMAP_A (rdv mem) Bw ->
  In (p, n) (ablocks B ly S) -> n = Z.of_nat (length D) -> n < 2 ^ 26 ->
  QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) D) ->
  op4_post regs mem Bw p D c0 Q ->
  SRr segs W (at_ O_ARM regs mem md) Q.
Proof using All.
intros regs mem md Bw p n D c0 Q HJ R2 R3 R4 R9 R18 R26 R20 R25 R27 R24 R23 H112 H168 H184 H120 HTW Hin HnD Hn26
  HFI Hn0 HG8 HK.
destruct c0 as [off0 n0]. unfold QF.fuzz_in_ok in HFI. cbn [TOP.fi_off TOP.fi_n] in HFI, R25, R27, Hn0.
destruct HFI as (Hoff & Hnn & Hon). rewrite <- HnD in Hon.
unfold lc_oc in R24, R23. rewrite (op_u8 D off0 n0 Hn0) in R24, R23. cbn [fst TOP.fi_off TOP.fi_n] in R24, R23.
rewrite Z.add_assoc in R24.
unfold op4_post in HK.
pose proof asan_consts as ((C1 & C2) & _).
assert (EST : ESTACK = 4096) by reflexivity.
pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
pose proof (tw_len _ _ _ HTW) as HLB.
(* ---- the queue length the `lw` at +0x4a8 reads ---- *)
pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 18144 4%nat TMAP_A_ok HTW
  TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as VQ.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 18144) 4) as RQ.
change (TW.u_at Bw (TW.OFF_g_s + 18144) 4) with (TW.S_queued Bw) in VQ, RQ.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
(* ---- run 1, the memset of OW ---- *)
apply (op4_s1 regs mem md (TW.S_queued Bw) Q HJ R2 R3 R4 R9 R18 H112 VQ RQ).
intros regs1 mem1 md1 HJ1 Q19 Q22 KR1 ZS1 ZOW KA1 GA1.
set (B1 := TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW))).
assert (TW1 : tw_at TMAP_A (rdv mem1) B1).
{ pose proof (tw_fill_set TMAP_A (rdv mem) (rdv mem1) Bw TW.OFF_OW TA_OW TW.SZ_OW 0 0 304 TMAP_A_ok HTW TMAP_A_OW
    ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as T.
  rewrite !Z.add_0_r in T. refine (T _ _).
  - intros i Hi. rewrite (ZOW i Hi). reflexivity.
  - intros x Hx Hnx. destruct (op_G_apart mem md HJ x (op_twin_G x Hx)) as (A0 & A1 & _ & _ & A4).
    exact (KA1 x A0 A1 Hnx A4). }
(* ---- run 2, the memset of GOT ---- *)
apply (op4_s2 regs1 mem1 md1 Q HJ1
  (eq_trans (KR1 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)
  (eq_trans (KR1 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)
  (eq_trans (KR1 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4)).
intros regs2 mem2 md2 HJ2 KR2 ZGOT KA2 GA2.
set (B2 := TW.upd B1 TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT))).
assert (TW2 : tw_at TMAP_A (rdv mem2) B2).
{ pose proof (tw_fill_set TMAP_A (rdv mem1) (rdv mem2) B1 TW.OFF_GOT TA_GOT TW.SZ_GOT 0 0 224 TMAP_A_ok TW1 TMAP_A_GOT
    ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as T.
  rewrite !Z.add_0_r in T. refine (T _ _).
  - intros i Hi. rewrite (ZGOT i Hi). reflexivity.
  - intros x Hx Hnx. destruct (op_G_apart mem md HJ x (op_twin_G x Hx)) as (A0 & _ & _ & _ & A4).
    exact (KA2 x A0 Hnx A4). }
pose proof (tw_len _ _ _ TW2) as LB2.
assert (KR12 : forall r, acallee_saved r -> r <> 19 -> r <> 22 ->
  YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr H19 H22; exact (eq_trans (KR2 r Hr) (KR1 r Hr H19 H22))).
assert (K02 : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (SHF + 4 <= a < SHF + 8) ->
  ~ (sp1 - ESTACK <= a < sp1) -> rdv mem2 a = rdv mem a).
{ intros a A0 A1 A2 A4. rewrite (KA2 a A0 (fun Hc => A1 (op_inG_GOT a Hc)) A4).
  exact (KA1 a A0 A2 (fun Hc => A1 (op_inG_OW a Hc)) A4). }
assert (ZS2 : forall i, 4 <= i < 8 -> rdv mem2 (SHF + i) = Some 0).
{ intros i Hi. destruct (op_SH_apart mem md HJ i ltac:(lia)) as (A0 & A1 & _ & _ & A4).
  rewrite (KA2 _ A0 (fun Hc => A1 (op_inG_GOT _ Hc)) A4). exact (ZS1 i Hi). }
(* ---- run 3: g_fail_next, OW.desk_off, M.fail, the memset of c ---- *)
pose proof (tw_read_val segs (mrestrict (w_H W) mem2) TMAP_A B2 TW.OFF_g_fail_next TA_g_fail_next 1 0 1%nat TMAP_A_ok
  TW2 TMAP_A_g_fail_next ltac:(lia) ltac:(lia)) as VG.
rewrite !Z.add_0_r in VG.
pose proof (TWL.u_at_range B2 TW.OFF_g_fail_next 1) as RG. change (2 ^ (8 * Z.of_nat 1)) with 256 in RG.
set (gfn := TW.u_at B2 TW.OFF_g_fail_next 1) in VG, RG.
assert (SP2 : forall a, sp1 <= a <= sp0 -> rdv mem2 a = rdv mem a).
{ intros a Ha. destruct (op_stk_apart a Ha) as (A0 & A1 & A2 & _ & A4). exact (K02 a A0 A1 A2 A4). }
apply (op4_s3 regs2 mem2 md2 gfn Q HJ2
  (eq_trans (KR12 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)
  (eq_trans (KR12 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)
  (eq_trans (KR12 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4)
  (eq_trans (KR12 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R9)
  (eq_trans (KR12 20 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R20)
  (eq_trans (KR2 22 ltac:(unfold acallee_saved; lia)) Q22) VG RG
  (op_rdw_kept mem mem2 (sp1 + 168) (F + 32) (fun k Hk => SP2 (sp1 + 168 + k) ltac:(lia)) H168)
  (op_rdw_kept mem mem2 (sp1 + 184) TA_M (fun k Hk => SP2 (sp1 + 184 + k) ltac:(lia)) H184) ZS2).
intros regs3 mem3 md3 HJ3 Q22c KR3 VOW3 VM3 ZC3 KA3 GA3.
(* the world after op_begin *)
set (B3 := TW.set_OW_desk_off B2 (-1)).
set (B4 := TW.set_M_fail B3 (TW.g_fail_next B3)).
assert (EG3 : TW.g_fail_next B3 = gfn).
{ unfold B3, TW.set_OW_desk_off, TW.g_fail_next, gfn. apply TWL.u_at_upd_out.
  - unfold TW.A_OW_desk_off, TW.OFF_OW. lia.
  - unfold TW.OFF_g_fail_next. lia.
  - left. unfold TW.OFF_g_fail_next, TW.A_OW_desk_off, TW.OFF_OW. cbn [Z.of_nat]. lia.
  - rewrite TWL.length_put, LB2. change (Z.of_nat (Z.to_nat TW.W_LEN)) with 65616. unfold TW.A_OW_desk_off, TW.OFF_OW.
    cbn [Z.of_nat]. lia. }
set (rdm := fun x => if (TA_M + 88 <=? x) && (x <? TA_M + 92) then rdv mem2 x else rdv mem3 x).
assert (RM1 : forall x, ~ (TA_M + 88 <= x < TA_M + 92) -> rdm x = rdv mem3 x).
{ intros x Hx. unfold rdm. destruct (Z.leb_spec (TA_M + 88) x); destruct (Z.ltb_spec x (TA_M + 92));
    cbn [andb]; first [reflexivity | lia]. }
assert (RM2 : forall x, TA_M + 88 <= x < TA_M + 92 -> rdm x = rdv mem2 x).
{ intros x Hx. unfold rdm. destruct (Z.leb_spec (TA_M + 88) x); destruct (Z.ltb_spec x (TA_M + 92));
    cbn [andb]; first [reflexivity | lia]. }
assert (TWa : tw_at TMAP_A rdm B3).
{ pose proof (tw_write TMAP_A (rdv mem2) rdm B2 TW.OFF_OW TA_OW TW.SZ_OW 232 4 (-1) TMAP_A_ok TW2 TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia)) as T.
  refine (T _ _).
  - intros j Hj. rewrite RM1 by (unfold TA_OW, TA_M; lia).
    assert (EL : YO0f.le_byte 4294967295 4 j = YO0f.le_byte (-1) 4 j).
    { assert (Hj' : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
      destruct Hj' as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
    exact (eq_trans (VOW3 j Hj) (f_equal Some EL)).
  - intros x Hx Hnx. destruct (Z.leb_spec (TA_M + 88) x) as [Hm1 | Hm1];
      [destruct (Z.ltb_spec x (TA_M + 92)) as [Hm2 | Hm2]|].
    + exact (RM2 x (conj Hm1 Hm2)).
    + rewrite (RM1 x ltac:(lia)).
      destruct (op_G_apart mem md HJ x (op_twin_G x Hx)) as (A0 & _ & A2 & _ & A4).
      exact (KA3 x A0 ltac:(cbn [Z.of_nat] in Hnx; lia) ltac:(lia) A2 A4).
    + rewrite (RM1 x ltac:(lia)).
      destruct (op_G_apart mem md HJ x (op_twin_G x Hx)) as (A0 & _ & A2 & _ & A4).
      exact (KA3 x A0 ltac:(cbn [Z.of_nat] in Hnx; lia) ltac:(lia) A2 A4). }
assert (TW3 : tw_at TMAP_A (rdv mem3) B4).
{ pose proof (tw_write TMAP_A rdm (rdv mem3) B3 TW.OFF_M TA_M TW.SZ_M 88 4 gfn TMAP_A_ok TWa TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia)) as T.
  unfold B4. rewrite EG3. refine (T _ _).
  - intros j Hj. exact (VM3 j Hj).
  - intros x Hx Hnx. symmetry. apply RM1. cbn [Z.of_nat] in Hnx. lia. }
assert (EOB : TC.op_begin_m Bw = Some (B4, tt)) by reflexivity.
assert (KR123 : forall r, acallee_saved r -> r <> 19 -> r <> 22 ->
  YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr H19 H22; exact (eq_trans (KR3 r Hr H22) (KR12 r Hr H19 H22))).
assert (K03 : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (SHF + 4 <= a < SHF + 8) ->
  ~ (F + 32 <= a < F + 64) -> ~ (sp1 - ESTACK <= a < sp1) -> rdv mem3 a = rdv mem a).
{ intros a A0 A1 A2 A3 A4.
  rewrite (KA3 a A0 (fun Hc => A1 (op_inG_OW a ltac:(lia))) (fun Hc => A1 (op_inG_M a Hc)) A3 A4).
  exact (K02 a A0 A1 A2 A4). }
assert (ZS3 : forall i, 4 <= i < 8 -> rdv mem3 (SHF + i) = Some 0).
{ intros i Hi. destruct (op_SH_apart mem md HJ i ltac:(lia)) as (A0 & A1 & A2 & _ & A4).
  rewrite (KA3 _ A0 (fun Hc => A1 (op_inG_OW (SHF + i) ltac:(lia))) (fun Hc => A1 (op_inG_M _ Hc)) A2 A4).
  exact (ZS2 i Hi). }
assert (SP3 : forall a, sp1 <= a <= sp0 -> rdv mem3 a = rdv mem a).
{ intros a Ha. destruct (op_stk_apart a Ha) as (A0 & A1 & A2 & A3 & A4). exact (K03 a A0 A1 A2 A3 A4). }
assert (HG83 : garr8 segs (mrestrict (w_H W) mem3) p (map (fun b : byte => bv_unsigned b) D)).
{ apply (lc_garr8_kept (w_H W) (w_H W) mem mem3 p _); [|exact HG8].
  intros j Hj. rewrite length_map, <- HnD in Hj.
  destruct (op_blk_apart mem md p n HJ Hin j ltac:(lia)) as (A0 & A1 & A2 & A3 & _ & A5).
  exact (K03 _ A0 A1 A2 A3 A5). }
assert (R3_9 : YK11.getr regs3 9 = w64 sp1)
  by exact (eq_trans (KR123 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R9).
assert (R3_26 : YK11.getr regs3 26 = w64 SHADOW_OFF)
  by exact (eq_trans (KR123 26 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R26).
assert (R3_24 : YK11.getr regs3 24 = w64 (p + off0 + 1))
  by exact (eq_trans (KR123 24 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R24).
assert (R3_25 : YK11.getr regs3 25 = w64 (p + off0))
  by exact (eq_trans (KR123 25 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R25).
assert (R3_23 : YK11.getr regs3 23 = w64 (n0 - 1))
  by exact (eq_trans (KR123 23 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R23).
assert (R3_27 : YK11.getr regs3 27 = w64 n0)
  by exact (eq_trans (KR123 27 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R27).
assert (H168_3 : rdword (rdv mem3) (sp1 + 168) = Some (F + 32))
  by exact (op_rdw_kept mem mem3 (sp1 + 168) (F + 32) (fun k Hk => SP3 (sp1 + 168 + k) ltac:(lia)) H168).
assert (R3_19 : YK11.getr regs3 19 = Z_to_bv 64 (bv_swrap 32 (TW.S_queued Bw)))
  by exact (eq_trans (KR3 19 ltac:(unfold acallee_saved; lia) ltac:(lia))
                     (eq_trans (KR2 19 ltac:(unfold acallee_saved; lia)) Q19)).
(* ---- run 5 and the cut, from any of run 4's four cases ---- *)
assert (TAIL : forall disp nr off3 key, 0 <= disp < 256 ->
  lc_sub_kd D (lc_oc D (TOP.FuzzIn off0 n0)) = mkLsv key disp (TOP.FuzzIn off3 nr) ->
  s4_post regs3 mem3 disp nr (p + off3) key Q).
{ intros disp nr off3 key Hd EKD regs4 mem4 md4 HJ4 Q11 Q19d Q24 Q23 Q22d KR4 VKEY4 VSP4 KA4 GA4.
  rewrite EKD in HK. cbn [sv_c sv_key sv_display TOP.fi_off TOP.fi_n] in HK.
  assert (TW4 : tw_at TMAP_A (rdv mem4) B4).
  { apply (tw_kept TMAP_A (rdv mem3) (rdv mem4) B4 TW3). intros x Hx.
    destruct (op_G_apart mem md HJ x (op_twin_G x Hx)) as (A0 & _ & A2 & A3 & _).
    apply KA4; [exact A0 | lia | exact A3]. }
  pose proof (tw_read_val segs (mrestrict (w_H W) mem4) TMAP_A B4 TW.OFF_g_raw TA_g_raw TW.SZ_g_raw 0 4%nat TMAP_A_ok
    TW4 TMAP_A_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)) as VR.
  rewrite !Z.add_0_r in VR.
  pose proof (TWL.u_at_range B4 TW.OFF_g_raw 4) as RR. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RR.
  set (graw := TW.u_at B4 TW.OFF_g_raw 4) in VR, RR.
  assert (SP4 : forall a, sp1 <= a <= sp0 -> ~ (sp1 + 144 <= a < sp1 + 152) -> rdv mem4 a = rdv mem a).
  { intros a Ha Hn. rewrite (KA4 a ltac:(lia) ltac:(lia) Hn). exact (SP3 a Ha). }
  assert (H120_4 : rdword (rdv mem4) (sp1 + 120) = Some PG_RAW)
    by exact (op_rdw_kept mem mem4 (sp1 + 120) PG_RAW (fun k Hk => SP4 (sp1 + 120 + k) ltac:(lia) ltac:(lia)) H120).
  apply (op4_s5 regs4 mem4 md4 disp graw Q HJ4
    (eq_trans (KR4 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) R3_9)
    Q23 Q11 Hd H120_4 VR RR).
  intros regs5 mem5 md5 pc HJ5 KR5 VD5 KA5 GA5 Hbr.
  assert (KR45 : forall r, acallee_saved r -> r <> 19 -> r <> 22 -> r <> 23 -> r <> 24 ->
    YK11.getr regs5 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
    by (intros r Hr H19 H22 H23 H24;
        exact (eq_trans (KR5 r Hr) (eq_trans (KR4 r Hr H19 H22 H23 H24) (KR123 r Hr H19 H22)))).
  assert (K54 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 64) -> ~ (sp1 + 144 <= a < sp1 + 152) ->
    rdv mem5 a = rdv mem3 a).
  { intros a A0 A2 A3. rewrite (KA5 a A0 ltac:(lia)). exact (KA4 a A0 ltac:(lia) A3). }
  apply (HK regs5 mem5 md5 pc B4 HJ5 EOB).
  - destruct (op_swrap_z graw RR) as (_ & S2).
    change (TW.g_raw B4) with (bv_swrap 32 graw).
    destruct Hbr as [[-> Hg] | [-> Hg]]; [left | right]; (split; [reflexivity|]).
    + intros Hz. exact (Hg (proj1 S2 Hz)).
    + exact (proj2 S2 Hg).
  - exact KR45.
  - exact (eq_trans (KR5 23 ltac:(unfold acallee_saved; lia)) Q23).
  - exact (eq_trans (KR5 22 ltac:(unfold acallee_saved; lia)) Q22d).
  - exact (eq_trans (KR5 24 ltac:(unfold acallee_saved; lia)) Q24).
  - exact (eq_trans (KR5 19 ltac:(unfold acallee_saved; lia)) Q19d).
  - apply (tw_kept TMAP_A (rdv mem4) (rdv mem5) B4 TW4). intros x Hx.
    destruct (op_G_apart mem md HJ x (op_twin_G x Hx)) as (A0 & _ & A2 & _ & _).
    exact (KA5 x A0 ltac:(lia)).
  - apply (op_c_garr8 mem5 disp key Hd). intros j Hj.
    destruct (Nat.eqb_spec j 25) as [-> | Hj25].
    + replace (F + 32 + Z.of_nat 25) with (F + 57) by (cbn [Z.of_nat]; lia). exact VD5.
    + destruct (Nat.ltb_spec j 28) as [Hj28 | Hj28].
      * rewrite (KA5 (F + 32 + Z.of_nat j) ltac:(lia) ltac:(lia)).
        rewrite (KA4 (F + 32 + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia)).
        exact (ZC3 (Z.of_nat j) ltac:(lia)).
      * rewrite (KA5 (F + 32 + Z.of_nat j) ltac:(lia) ltac:(lia)).
        replace (F + 32 + Z.of_nat j) with (F + 60 + Z.of_nat (j - 28)) by lia. exact (VKEY4 (j - 28)%nat ltac:(lia)).
  - rewrite <- R3_19.
    exact (op_rdw_kept mem4 mem5 (sp1 + 144) _ (fun k Hk => KA5 (sp1 + 144 + k) ltac:(lia) ltac:(lia)) VSP4).
  - intros i Hi. destruct (op_SH_apart mem md HJ i ltac:(lia)) as (A0 & _ & A2 & A3 & _).
    rewrite (K54 _ A0 A2 A3). exact (ZS3 i Hi).
  - intros i Hi Hn. destruct (op_SH_apart mem md HJ i Hi) as (A0 & A1 & A2 & A3 & A4).
    rewrite (K54 _ A0 A2 A3). exact (K03 _ A0 A1 ltac:(lia) A2 A4).
  - intros a Ha Hn. destruct (op_stk_apart a Ha) as (A0 & A1 & A2 & A3 & A4).
    rewrite (K54 a A0 A3 Hn). exact (K03 a A0 A1 A2 A3 A4).
  - intros b m i Hbm Hi. destruct (op_blk_apart mem md b m HJ Hbm i Hi) as (A0 & A1 & A2 & A3 & A4 & A5).
    rewrite (K54 _ A0 A3 A4). exact (K03 _ A0 A1 A2 A3 A5).
  - intros a Ha. destruct (op_ftail_apart mem md a HJ Ha) as (A0 & A1 & A2 & A3 & A4 & A5).
    rewrite (K54 _ A0 A3 A4). exact (K03 _ A0 A1 A2 A3 A5).
  - intros a Ha. exact (GA5 a (GA4 a (GA3 a (GA2 a (GA1 a Ha))))). }
(* ---- run 4, by the bytes left before the op byte ---- *)
assert (Hcase : n0 = 1 \/ n0 = 2 \/ n0 = 3 \/ 4 <= n0) by lia.
destruct Hcase as [-> | [-> | [-> | H4]]].
- apply (op4_s4a regs3 mem3 md3 p n off0 Q HJ3 R3_9 Q22c R3_26 R3_24 R3_25 R3_23 H168_3 Hin Hoff Hon).
  pose proof (TAIL 0 0 (off0 + 1) (DSpec.KEY 1 0) ltac:(lia) (op_kd1 D off0)) as T.
  replace (p + (off0 + 1)) with (p + off0 + 1) in T by lia. exact T.
- apply (op4_s4b regs3 mem3 md3 p n D off0 Q HJ3 R3_9 Q22c R3_26 R3_24 R3_25 R3_23 R3_27 H168_3 ZS3 Hin HnD Hn26
    Hoff Hon HG83).
  pose proof (TAIL 0 0 (off0 + 2) _ ltac:(lia) (op_kd2 D off0)) as T.
  replace (p + (off0 + 2)) with (p + off0 + 2) in T by lia. exact T.
- apply (op4_s4c regs3 mem3 md3 p n D off0 Q HJ3 R3_9 Q22c R3_26 R3_24 R3_25 R3_23 R3_27 H168_3 ZS3 Hin HnD Hn26
    Hoff Hon HG83).
  pose proof (TAIL 0 0 (off0 + 3) _ ltac:(lia) (op_kd3 D off0)) as T.
  replace (p + (off0 + 3)) with (p + off0 + 3) in T by lia. exact T.
- apply (op4_s4d regs3 mem3 md3 p n D off0 n0 Q HJ3 R3_9 Q22c R3_26 R3_24 R3_25 R3_23 R3_27 H168_3 ZS3 Hin HnD
    Hn26 Hoff Hon H4 HG83).
  assert (Hd : 0 <= Z.land (DSpec.at8 D (Z.to_nat (off0 + 3))) 1 < 256).
  { assert (E1 : Z.land (DSpec.at8 D (Z.to_nat (off0 + 3))) 1 = DSpec.at8 D (Z.to_nat (off0 + 3)) mod 2 ^ 1)
      by exact (Z.land_ones _ 1 ltac:(lia)).
    rewrite E1. pose proof (Z.mod_pos_bound (DSpec.at8 D (Z.to_nat (off0 + 3))) (2 ^ 1) ltac:(lia)). lia. }
  pose proof (TAIL _ (n0 - 4) (off0 + 4) _ Hd (op_kd4 D off0 n0 H4)) as T.
  replace (p + (off0 + 4)) with (p + off0 + 4) in T by lia. exact T.
Qed.
End pc.

(* ------------------------------------------------------------------ *)
(* 3. The segment lemma                                                *)
(* ------------------------------------------------------------------ *)

Section main. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* st.v lc_core_kept for a step that writes the frame below its last word (c), its shadow and 144(s1), and changes
   callee-saved registers lc_core does not name: it keeps sp, s0, s1, gp and tp, the stack from sp1 + 192 to sp0, the
   blocks, the frame's last word, and every present byte. *)
Lemma op_core_kept : forall cx ly' S' W' regs' mem' md' e regs2 mem2 md2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' mem2 md2 e ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  (forall a, lc_sp1 cx + 192 <= a <= lc_sp0 cx -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W') mem2 (b + i) = aview segs (w_H W') mem' (b + i)) ->
  (forall a, lc_F cx + LF_FBYTES - 8 <= a < lc_F cx + LF_FBYTES ->
     aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem2 a) ->
  @lc_core rc B cx ly' S' W' regs2 mem2 md2 e.
Proof.
intros cx ly' S' W' regs' mem' md' e regs2 mem2 md2 LAWS HB HC HJ2 HR KA KB KF GA.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
split; [exact HJ2|].
split; [exact Hfrs|].
split; [exact HlyF|].
split; [exact HPERM|].
split; [exact (eq_trans (HR 2 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) Rsp)|].
split; [exact (eq_trans (HR 8 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R8)|].
split; [exact (eq_trans (HR 9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R9)|].
split; [exact (eq_trans (HR 3 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) Rgp)|].
split; [exact (eq_trans (HR 4 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) Rtp)|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; apply KA; unfold LF_FRAME in Hsp1; lia).
  exact (HSAV o Ho). }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split; [intros a Ha; exact (GA a (HFpres a Ha))|].
split; [rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem2) (lc_F cx + LF_FBYTES - 8))
          by (intros j Hj; apply KF; lia); exact HFL|].
destruct HIN as (HPAYg & HPAYv).
destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
- pose proof (HINg Hn0) as InP.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  split.
  + apply (lc_garr8_kept (w_H W') (w_H W') mem' mem2 (l_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj.
    exact (KB _ _ j InP ltac:(lia)).
  + intros i Hi. rewrite (KB _ _ i InP ltac:(lia)). exact (HPAYv i Hi).
- destruct Hn as (Hn1 & Hnl). split.
  + destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
  + intros i Hi. lia.
Qed.

(* OP4A: from the arm of op 4 to SUBR (g_raw <> 0) or SUBT (g_raw = 0). *)
Lemma lc_op4a_ok : lc_op4a_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4a_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Ec & Ho & HL & Htw & Hcur0 & Hcur1 & R20 & R22).
subst c'.
pose proof HL as (HC & Hfr & Hsp & Hfsh & Hopok & He & Hmet & R21).
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_memset _ _ _ _ _ HP (l_fx cx)) as HMS.
pose proof (lp_recv_cells _ _ _ _ _ HP) as HRC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof asan_consts as ((C1 & C2) & _).
pose proof Hopok as (Hagree & Hops & HFI & Hn0 & Hk).
destruct Hfr as (R18 & R26). destruct Hcur0 as (R25 & R27). destruct Hcur1 as (R24 & R23).
pose proof HIN as (HG8 & HPAYv).
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil.
assert (SPL : forall o, In o (lf_spill_loop (lc_F cx)) ->
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + fst o) = Some (snd o))
  by (intros o Ho'; unfold lc_spills in Hsp; rewrite Forall_forall in Hsp; exact (Hsp o Ho')).
pose proof (SPL (112, TA_g_s) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app In];
  repeat (first [left; reflexivity | right]))) as H112.
pose proof (SPL (168, lc_F cx + 32) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; repeat (first [left; reflexivity | right]))) as H168.
pose proof (SPL (184, TA_M) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app In];
  repeat (first [left; reflexivity | right]))) as H184.
pose proof (SPL (120, transport_hi 8) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; repeat (first [left; reflexivity | right]))) as H120.
cbn [fst snd] in H112, H168, H184, H120. rewrite (proj2 op4_pages) in H120.
assert (Hnp : 0 < l_n cx).
{ destruct HFI as (Ho0 & Hn1 & Hon). destruct Hn as (_ & Hnl). lia. }
pose proof (HINg Hnp) as Hin.
assert (EPC0 : w64 (transport_text + lo_arm 4) = Z_to_bv 64 (BASE + O_ARM))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC0.
apply (op4_main B LAWS HGX HMS HRC LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
  [(LF_CID, l_fpos cx)] ly' S' W' e (lc_F cx) (lc_sp1 cx) (l_fpos cx)
  (or_introl eq_refl) HFin HFaddr HF4096 HFal HFceil Hsp1c
  ltac:(destruct Hstk as (_ & _ & S3 & S4); lia) Hsp1al Hsp1 Hsp0al ltac:(unfold ESTACK, LLVMF_STK; lia)
  regs' mem' md' (lo_B op) (l_p cx) (l_n cx) (l_pl cx) (lo_c op) _ HJ Rsp Rgp Rtp R9 R18 R26
  (eq_trans R20 (f_equal w64 (proj1 op4_pages))) R25 R27 R24 R23 H112 H168 H184 H120 Htw Hin (proj2 Hn)
  (proj2 (proj1 Hn)) HFI Hn0 HG8).
unfold op4_post.
intros regs2 mem2 md2 pc B4 HJ2 EOB Hbr KR Q23 Q22 Q24 Q19 TW2 HC2 H144 ZSa ZSb KST KBK KFT GA.
apply SRr_ret. cbv beta.
assert (KRn : forall r, r = 18 \/ r = 20 \/ r = 21 \/ r = 26 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 ->
  YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r))
  by (intros r Hr; apply KR; first [unfold acallee_saved; lia | lia]).
assert (HCORE : @lc_core rc B cx ly' S' W' regs2 mem2 md2 e).
{ apply (op_core_kept cx ly' S' W' regs' mem' md' e regs2 mem2 md2 LAWS HB HC HJ2).
  - intros r Hr. cbn [In] in Hr. apply KRn. lia.
  - intros a Ha. apply KST; lia.
  - exact KBK.
  - intros a Ha. apply KFT. unfold LF_FBYTES in Ha. lia.
  - exact GA. }
assert (HCOM : @lc_sub_common rc B MT cx op B4 ly' S' W' regs2 mem2 md2 e).
{ unfold lc_sub_common. cbv zeta.
  split; [exact (eq_sym Ho)|].
  split.
  { unfold lc_lcore. split; [exact HCORE|].
    split; [split; [exact (eq_trans (KRn 18 ltac:(lia)) R18) | exact (eq_trans (KRn 26 ltac:(lia)) R26)]|].
    split.
    { unfold lc_spills. rewrite Forall_forall. intros o Ho'.
      pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as V. rewrite Forall_forall in V.
      destruct (V o Ho') as (_ & Vm & V8 & V192).
      assert (Hne : fst o <> 144).
      { intros E. assert (Hin' : In (fst o) (map fst (lf_spill_loop (lc_F cx)))) by (apply in_map; exact Ho').
        rewrite lf_spill_offsets, E in Hin'. cbn [In] in Hin'. repeat (destruct Hin' as [Hin' | Hin']; [lia|]).
        exact Hin'. }
      rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem2) (lc_sp1 cx + fst o))
        by (intros j Hj; apply KST; lia).
      exact (SPL o Ho'). }
    split.
    { intros i Hi. unfold lc_SH. destruct (Z_lt_le_dec i 4) as [H4 | H4];
        [|destruct (Z_lt_le_dec i 8) as [H8 | H8]].
      - rewrite (ZSb i Hi ltac:(lia)), (lf_shm_tf i Hi ltac:(lia)). exact (Hfsh i Hi).
      - rewrite (ZSa i (conj H4 H8)), (lf_shm_tc i (conj H4 H8)). reflexivity.
      - rewrite (ZSb i Hi ltac:(lia)), (lf_shm_tf i Hi ltac:(lia)). exact (Hfsh i Hi). }
    split; [exact Hopok|]. split; [exact He|]. split; [exact Hmet|].
    exact (eq_trans (KRn 21 ltac:(lia)) R21). }
  split; [exact EOB|].
  split; [exact TW2|].
  split; [exact HC2|].
  split; [exact H144|].
  split; [exact Q24 | exact Q19]. }
destruct Hbr as [[-> Hg] | [-> Hg]].
- left. unfold lc_st_subr. exists ly', S', regs2, mem2, md2, e, B4.
  assert (EPC : Z_to_bv 64 (BASE + LO_SUBR) = w64 (transport_text + LO_SUBR))
    by (unfold w64; f_equal; vm_compute; reflexivity).
  split; [unfold lc_cfg; rewrite EPC; reflexivity|].
  split; [exact HCOM|]. split; [exact Hg|].
  exact (eq_trans (KRn 20 ltac:(lia)) R20).
- right. unfold lc_st_subt. exists ly', S', regs2, mem2, md2, e, B4.
  assert (EPC : Z_to_bv 64 (BASE + LO_SUBT) = w64 (transport_text + LO_SUBT))
    by (unfold w64; f_equal; vm_compute; reflexivity).
  split; [unfold lc_cfg; rewrite EPC; reflexivity|].
  split; [exact HCOM|]. split; [exact Hg|].
  split; [exact Q23 | exact Q22].
Qed.

End main.
