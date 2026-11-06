(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1210 of its 1392 lines of code are new or changed and 957 lines of the source are left out. *)
(* on_ack_seg_head: Theorem onack_head : onack_head_stmt (lib/A/Prog/on_ack_segs.v), the head piece of the walk of
   on_ack on fuzz_transport.asan (0x8842c = transport_sigma TS_on_ack, AF_on_ack = 0x71c8 of
   lib/A/Prog/DgnTransportList.v), from the entry to the two cuts onack_ntc_at (+0x180) and onack_ign_at (+0x2b0).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []); the runs are the
   position-abstract runs of lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x:
     run 1   +0x000 .. +0x06c  the frame (`addi sp, sp, -128`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1, s4 = fp, the flag word through its GOT word (1, so `beqz a2` is not taken),
                               s9 = the shadow base, s3 = s, a0 = 160, up to `jal __asan_stack_malloc_2`;
     +0x070                    the class-2 stack malloc (lib/A/Prog/TransportGFrame.v gx_stack_malloc_at): the
                               frame F in a0, 4096 <= F;
     run 2a  +0x074 .. +0x0dc  `bnez s2` taken (the real-stack arm is not reached), the frame's 24-byte header,
                               s7 = the frame's shadow address, a0 = s + 212;
     run 2b  +0x0e0 .. +0x134  the frame's shadow bytes 0 .. 19, a1 = a0 >> 3 (+0x0f0) and a3 = a1 + s9 (+0x134,
                               the shadow address of s + 212); the run writes shadow bytes, so it carries no
                               shadow token;
     run 2c  +0x138 .. +0x144  the shadow byte at a3, read as a region cell holding 0 (the record's zero shadow of
                               g_s's payload, trans_onack_cells), so `bnez a1` at +0x140 is decided; the frame word
                               at s1 + 16; the 4-byte signed load of S_inflight Bw at s + 212;
     +0x148                    `beqz a1`: S_inflight Bw = 0 runs one instruction to +0x2b0 and concludes by
                               onack_ign_at (onack_ign's first disjunct); else run 2d;
     run 2d  +0x14c .. +0x178  the checks of the 4-byte loads at f + 24 and at s + 1744 (shadow tokens over the
                               entries ONH_SH: the shadow of f's 64 bytes from trans_dframe_at's decode_rd_ok,
                               carried across the stack malloc and the three writes; the shadow of g_s's payload
                               from trans_onack_cells), s10 = the 4-byte signed load at f + 24 and a1 = the 4-byte
                               signed load at s + 1744; both loads SIGN-EXTEND;
     +0x17c                    `bne s10, a1`: different runs one instruction to +0x2b0 and concludes by
                               onack_ign_at (onack_ign's second disjunct, through onh_eqb_swrap: bv_swrap 32 is
                               injective on [0, 2 ^ 32)); equal runs one instruction to +0x180 and concludes by
                               onack_ntc_at.
   The head stores no byte of G at all, so the facts the cuts carry hold at the ENTRY world Bw and what the call
   keeps runs over the empty written range: from the entry to the stack malloc's return (TransportGCg.v
   dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over the three ranges the head
   writes (dk_kept_own_g: the frame's header, the frame's shadow bytes, the slot s1 + 16 in the call's window).
   The cuts' acall_kept_g over onack_wr Bw b is that fact weakened (acall_kept_g_weaken). The notice cut also
   carries the current heap frame (TransportGNotice.v trans_tframe_at_kept_gx, with no written range: the head
   stores no byte of G) and the read-only bytes (trans_ro_rd_scoped), both across the stack
   malloc and the three writes. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame on_ack_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLeafb := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition ONH_B0 : Z * Z := (0, 0).

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states of the five runs                             *)
(* ------------------------------------------------------------------ *)

(* run 1, +0x000 .. +0x070: the two runtime cells through their GOT words (transport_cells rows 1, 2, 6, 7) and the
   machine frame. *)
Definition onh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 94) 0))].
Definition onh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition onh_img_regions : smem := [got_regionP; bcell_regionP 32; onh_got_uar; onh_uar_cell].
Definition onh_regions1 : smem := stack_region ONACK_FRAME :: onh_img_regions.
Definition onh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_onh1 : sstate := mkSS AF_on_ack sr_atoms onh_regions1 None onh_facts1.

(* run 2a, +0x074 .. +0x0dc: after the stack malloc, the frame F in a0 (atom 10); the run writes the frame's 24-byte
   header and stops at the first shadow store. *)
Definition ONH_C1 : Z := AF_on_ack + 0x74.
Definition onh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition onh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_onh2 : sstate := mkSS ONH_C1 sr_atoms [onh_rg_hdr] None onh_facts2.

(* run 2b, +0x0e0 .. +0x134: s7 (atom 23) holds the frame's shadow address; the run writes the frame's shadow bytes
   0 .. 19 and leaves a3 = (a0 >> 3) + s9, the shadow address of s + 212. *)
Definition ONH_C2 : Z := AF_on_ack + 0xe0.
Definition ONH_C3 : Z := AF_on_ack + 0x138.
Definition onh_rg_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 20 0 20 [].
Definition onh_facts3 : facts := mkFacts [(23%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_onh3 : sstate := mkSS ONH_C2 sr_atoms [onh_rg_sh] None onh_facts3.

(* run 2c, +0x138 .. +0x148: the shadow byte of s + 212 at a3 (atom 13), a region cell holding 0; the frame word at
   s1 + 16 (atom 9); the 4-byte load of S_inflight at a0 (atom 10, pinned to s + 212), whose value is atom 33. *)
Definition ONH_C4 : Z := AF_on_ack + 0x148.
(* the shadow byte of the granule of s + 212 (SHADOW_OFF + (ONACK_S + 212) / 8, as a numeral) *)
Definition ONH_ZS : Z := 2148220754.
Lemma onh_zs_eq : ONH_ZS = SHADOW_OFF + (ONACK_S + 212) / 8.
Proof. reflexivity. Qed.
Definition onh_rg_zs : YP09.region :=
  YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition onh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition onh_rg_inf : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition onh_regions4 : smem := [onh_rg_zs; onh_rg_slot; onh_rg_inf].
Definition onh_facts4 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF (ONACK_S + 212) (ONACK_S + 212) 2);
           (13%nat, mkAF ONH_ZS ONH_ZS 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_onh4 : sstate := mkSS ONH_C3 sr_atoms onh_regions4 None onh_facts4.

(* run 2d, +0x14c .. +0x17c: the two checked 4-byte loads, at f + 24 (s4 = atom 20 = fp, value atom 33) and at
   s + 1744 (s3 = atom 19 = s, value atom 34). Both checks read a shadow byte through s9 (atom 25): the shadow
   entries ONH_SH over the shadow base ONH_Bx. *)
Definition ONH_C5 : Z := AF_on_ack + 0x14c.
Definition ONH_C6 : Z := AF_on_ack + 0x17c.
Definition onh_rg_f : YP09.region :=
  YP09.mkRegion (Some 20%nat) 24 28 0 0 [YP09.mkChunk 24 (YP09.CVal 4 (SOff 33 0))].
Definition onh_rg_cnt : YP09.region :=
  YP09.mkRegion (Some 19%nat) 1744 1748 0 0 [YP09.mkChunk 1744 (YP09.CVal 4 (SOff 34 0))].
Definition onh_regions6 : smem := [onh_rg_f; onh_rg_cnt].
Definition onh_facts6 : facts :=
  mkFacts [(19%nat, mkAF ONACK_S ONACK_S 6); (20%nat, mkAF 4096 (2 ^ 47 - 64) 3);
           (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_onh6 : sstate := mkSS ONH_C5 sr_atoms onh_regions6 None onh_facts6.
Definition ONH_SH : list shent := [mkSHE 20 24 28; mkSHE 19 1744 1748].
Definition ONH_Bx : sv := SOff 25 0.

(* The two branch states, taken up again with no region. *)
Definition ss_onh5 : sstate := mkSS ONH_C4 sr_atoms [] None (mkFacts [] [] []).
Definition ss_onh7 : sstate := mkSS ONH_C6 sr_atoms [] None (mkFacts [] [] []).

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition onh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* ------------------------------------------------------------------ *)
(* 2. Arithmetic: the two sign-extended compares                       *)
(* ------------------------------------------------------------------ *)

Lemma onh_swrap_range : forall x, - 2 ^ 31 <= bv_swrap 32 x < 2 ^ 31.
Proof.
intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
change (bv_modulus 32) with (2 ^ 32). pose proof (Z.mod_pos_bound (x + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma onh_s32_mod32 : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
change (bv_modulus 32) with (2 ^ 32). Z.div_mod_to_equations. lia.
Qed.

Lemma onh_mod64_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> z mod 2 ^ 64 = z + (if z <? 0 then 2 ^ 64 else 0).
Proof.
intros z Hz. destruct (Z.ltb_spec z 0) as [H|H].
- rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
- rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

(* Two 32-bit signed values, each held in a 64-bit register, compare equal exactly when they are equal. *)
Lemma onh_eqb64 : forall u v, - 2 ^ 31 <= u < 2 ^ 31 -> - 2 ^ 31 <= v < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 u) (Z_to_bv 64 v) = (u =? v).
Proof.
intros u v Hu Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
rewrite (onh_mod64_small u Hu), (onh_mod64_small v Hv).
destruct (Z.eqb_spec u v) as [->|Hne].
- destruct (Z.ltb_spec v 0); apply Z.eqb_refl.
- apply Z.eqb_neq. destruct (Z.ltb_spec u 0); destruct (Z.ltb_spec v 0); lia.
Qed.

(* `beqz` on a sign-extended 32-bit load. *)
Lemma onh_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. apply onh_eqb64; [exact Hv | lia]. Qed.

(* `bne` on two sign-extended 32-bit loads: bv_swrap 32 is injective on [0, 2 ^ 32). *)
Lemma onh_eqb_swrap : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x =? y).
Proof.
intros x y Hx Hy. rewrite (onh_eqb64 _ _ (onh_swrap_range x) (onh_swrap_range y)).
destruct (Z.eqb_spec x y) as [->|Hne]; [apply Z.eqb_refl|].
apply Z.eqb_neq. intros HH. apply Hne.
pose proof (onh_s32_mod32 x) as Ex. pose proof (onh_s32_mod32 y) as Ey.
rewrite HH, Ey in Ex. rewrite (Z.mod_small x (2 ^ 32)) in Ex by lia.
rewrite (Z.mod_small y (2 ^ 32)) in Ex by lia. symmetry. exact Ex.
Qed.

Lemma onh_s_inflight_range : forall Bw, - 2 ^ 31 <= TW.S_inflight Bw < 2 ^ 31.
Proof. intros Bw. unfold TW.S_inflight, TW.s32_at. apply onh_swrap_range. Qed.

(* The ack counter of a frame is a big-endian 32-bit field. *)
Lemma onh_at8_range : forall l i, 0 <= DSpec.at8 l i < 256.
Proof.
intros l i. unfold DSpec.at8, DSpec.bz.
pose proof (bv_unsigned_in_range 8 (nth i l (DSpec.b8 0))) as H.
change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma onh_fr_ack_range : forall b, 0 <= DSpec.fr_ack b < 2 ^ 32.
Proof.
intros b. unfold DSpec.fr_ack, DSpec.be32.
pose proof (onh_at8_range b 22). pose proof (onh_at8_range b 23).
pose proof (onh_at8_range b 24). pose proof (onh_at8_range b 25). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The four bytes of h.ack_counter at f + 24                        *)
(* ------------------------------------------------------------------ *)

(* fr_code b = 0 asks for at least the 14-byte Ethernet header and the 16-byte frame header. *)
Lemma onh_blen : forall b, DSpec.fr_code b = 0 -> (30 <= length b)%nat.
Proof.
intros b H. destruct (Nat.ltb_spec (length b) 30) as [Hl|Hl]; [|exact Hl].
exfalso. unfold DSpec.fr_code in H. rewrite (proj2 (Nat.ltb_lt _ _) Hl) in H. discriminate.
Qed.

(* The byte at index 24 + k of the 64 bytes diginet_frame_parse leaves is the k-th byte of fr_ack b
   (lib/Prog/diginet_frame_parse_c.v parse_cells, the cell C4 (Z_to_bv 64 (fr_ack b)) at offset 24). *)
Lemma onh_nth_ack : forall buf b fj k, DSpec.fr_code b = 0 -> length fj = 64%nat -> (k < 4)%nat ->
  nth (24 + k) (frame_f_bytes buf b fj) 0 = YO0f.le_byte (DSpec.fr_ack b) 4 k.
Proof.
intros buf b fj k H0 HJ Hk. pose proof (onh_blen b H0) as HL.
assert (L1 : length (DSpec.fr_dst b) = 6%nat)
  by (unfold DSpec.fr_dst; rewrite firstn_length_le by lia; reflexivity).
assert (L2 : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
assert (L3 : length (firstn 2 (skipn 14 fj)) = 2%nat)
  by (rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
assert (E2 : forall v : Z, length (LMem.le2 (Z_to_bv 64 v)) = 2%nat) by (intros v; apply LMem.length_le2).
assert (E4 : forall v : Z, length (LMem.le4 (Z_to_bv 64 v)) = 4%nat) by (intros v; apply LMem.length_le4).
unfold frame_f_bytes, frame_f_cells. rewrite (proj2 (Z.eqb_eq _ _) H0).
unfold PParse.parse_cells.
rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0)))
  by (rewrite length_map; cbn [LC.cells_bytes LC.cbytes];
      rewrite !length_app, L1, L2, L3, !E2, !E4; cbn [length]; lia).
rewrite map_nth.
cbn [LC.cells_bytes LC.cbytes].
rewrite app_nth2 by (rewrite L1; lia). rewrite L1.
rewrite app_nth2 by (rewrite L2; lia). rewrite L2.
rewrite app_nth2 by (rewrite E2; lia). rewrite E2.
rewrite app_nth2 by (rewrite L3; lia). rewrite L3.
rewrite app_nth2 by (rewrite E2; lia). rewrite E2.
rewrite app_nth2 by (rewrite E2; lia). rewrite E2.
rewrite app_nth2 by (rewrite E4; lia). rewrite E4.
replace (24 + k - 6 - 6 - 2 - 2 - 2 - 2 - 4)%nat with k by lia.
rewrite app_nth1 by (rewrite E4; lia).
pose proof (DLeafb.decode_leafb_le4_byte (DSpec.fr_ack b) k Hk) as Hb.
unfold LMem.wa in Hb. rewrite (nth_error_nth' _ (DSpec.b8 0)) in Hb by (rewrite E4; lia).
cbn [option_map] in Hb. injection Hb as Hb. exact Hb.
Qed.

Lemma onh_fbytes_len : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  length (frame_f_bytes buf b fj) = 64%nat.
Proof.
intros buf b fj H0 HJ. pose proof (onh_blen b H0) as HL.
assert (L1 : length (DSpec.fr_dst b) = 6%nat)
  by (unfold DSpec.fr_dst; rewrite firstn_length_le by lia; reflexivity).
assert (L2 : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
assert (L3 : length (firstn 2 (skipn 14 fj)) = 2%nat)
  by (rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
assert (L5 : length (skipn 59 fj) = 5%nat) by (rewrite length_skipn; lia).
unfold frame_f_bytes, frame_f_cells. rewrite (proj2 (Z.eqb_eq _ _) H0).
rewrite length_map. unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes].
rewrite !length_app, L1, L2, L3, L5, !LMem.length_le2, !LMem.length_le4, !LMem.length_le8.
cbn [length]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Small memory bridges                                             *)
(* ------------------------------------------------------------------ *)

(* A view byte 0 is a one-byte region cell holding 0. *)
Lemma onh_val0_of_aview : forall H (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
intros H m a HA k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in HA. destruct (mbyte tfibsegs (mrestrict H m) a) as [c|]; [|discriminate].
cbn [option_map] in HA. injection HA as HA.
f_equal. apply bv_eq. rewrite HA. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma onh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_on_ack = transport_sigma TS_on_ack.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma onh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) onh_img_regions /\
  pairwise_disjoint E onh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct onh_vals as (V1 & V93 & V0 & V94 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 94) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold onh_img_regions, got_regionP, bcell_regionP, onh_got_uar, onh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 94) 0) (VAL (A_OBJ 94)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 94)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold onh_img_regions, got_regionP, bcell_regionP, onh_got_uar, onh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuations: the 32 registers, the shadow base (atom 32) and the loaded values. *)
Definition onh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).
Definition onh_E4 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 212) 4)]).
Definition onh_E6 (regs : bvmap 5 word) (b Bw : list byte) : env :=
  Eimg (PI := PI_transport)
    (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (DSpec.fr_ack b);
                Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 1744) 4)]).

Lemma onh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold onh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma onh_ew_32 : forall regs, ew (onh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold onh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma onh_ew_obj : forall regs i, (i < 95)%nat -> ew (onh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold onh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma onh_env_img : forall regs, img_env VAL A_LIM (onh_E regs).
Proof. intros regs. unfold onh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma onh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - ONACK_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (onh_E regs) ss_onh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_ack)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_onh1, onh_regions1.
  assert (Usp : bv_unsigned (ew (onh_E regs) 2) = spZ regs)
    by (rewrite (onh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (onh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply onh_ew_32.
  destruct (onh_img_ok ly S W mem md (onh_E regs) HCELLS HAR
    (onh_ew_obj regs 1 ltac:(lia)) (onh_ew_obj regs 93 ltac:(lia))
    (onh_ew_obj regs 0 ltac:(lia)) (onh_ew_obj regs 94 ltac:(lia)) E32) as [HRs HPd].
  destruct onh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (onh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (onh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold ONACK_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold onh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, onh_got_uar, onh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (onh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (onh_ew_obj regs 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (onh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (onh_ew_obj regs 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, ONACK_FRAME.
    repeat split; first [exact I | lia].
  - unfold onh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma onh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F mod 64 = 0 ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (onh_E regs) ss_onh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R25 Hsp Hsp32 HF0 HFs HF64 Hpframe.
  rewrite restrict_mkst_fx. unfold ss_onh2.
  assert (U2 : bv_unsigned (ew (onh_E regs) 2) = spv)
    by (rewrite (onh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (onh_E regs) 9) = spv)
    by (rewrite (onh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (onh_E regs) 10) = F)
    by (rewrite (onh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (onh_E regs) 25) = SHADOW_OFF)
    by (rewrite (onh_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (onh_E regs) 32) = SHADOW_OFF)
    by (rewrite (onh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold onh_rg_hdr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold onh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold onh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U25, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma onh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 23 = w64 SH -> SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (onh_E regs) ss_onh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R23 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_onh3.
  assert (U23 : bv_unsigned (ew (onh_E regs) 23) = SH)
    by (rewrite (onh_ew_reg regs 23 23%bv eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold onh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold onh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold onh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma onh_inG : forall a, ONACK_S <= a < ONACK_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, ONACK_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* A range of g_s's payload is addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma onh_ra : forall ly S (W : world segs) mem md q n,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  ONACK_S <= q -> q + n <= ONACK_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n HZ HAR Hqlo Hqhi x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONACK_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONACK_S + TW.SZ_g_s)
  by (unfold ONACK_S, TA_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The shadow byte of the granule of s + 212 is 0 at every AR state. *)
Lemma onh_zs0 : forall ly S (W : world segs) mem md,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  aview segs (w_H W) mem ONH_ZS = Some 0.
Proof.
intros ly S W mem md HZ HAR.
assert (Hz := decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) 6158992 HAR
  ltac:(reflexivity) ltac:(unfold ONACK_S, TA_g_s; lia) ltac:(unfold ONACK_S, TA_g_s, TW.SZ_g_s; lia) HZ).
replace ONH_ZS with (FCells.shadow_addr 6158992); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, ONH_ZS, SHADOW_OFF, ONACK_S, TA_g_s. reflexivity.
Qed.

(* The valuation of run 2c: the registers at +0x138, the shadow base (atom 32) and g_s.inflight's four bytes
   (atom 33). *)
Lemma onh_entry4 : forall ly S (W : world segs) regs mem md Bw spv,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 16 <= a < spv + 24 -> apresent (w_H W) mem a) ->
  YK11.getr regs 10 = w64 (ONACK_S + 212) -> YK11.getr regs 13 = w64 ONH_ZS ->
  st_ok_pi segs VAL (onh_E4 regs Bw) ss_onh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C3)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md Bw spv HSC HAR Htw R9 Hsp Hsp32 Hpslot R10 R13.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onh_E4 regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold onh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (onh_E4 regs Bw) 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold onh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (onh_E4 regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 212) 4))
  by (unfold onh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (CS : ONACK_S = 6158784) by reflexivity.
assert (U9 : bv_unsigned (ew (onh_E4 regs Bw) 9) = spv)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew (onh_E4 regs Bw) 10) = ONACK_S + 212)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew (onh_E4 regs Bw) 13) = ONH_ZS)
  by (rewrite (EE 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; unfold ONH_ZS; lia).
assert (U32 : bv_unsigned (ew (onh_E4 regs Bw) 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 212) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (onh_E4 regs Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 212) 4)
  by (rewrite E33; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_onh4, onh_regions4.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [onh_rg_zs onh_rg_slot onh_rg_inf
       YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U13. unfold ONH_ZS. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ ONH_ZS 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply onh_val0_of_aview. exact (onh_zs0 ly S W mem md HSC HAR).
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
  + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (ONACK_S + 212) 0 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 212) 4));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    rewrite Z.add_0_r.
    exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 212 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
- apply pairwise_disjoint_of_extents.
  unfold onh_rg_zs, onh_rg_slot, onh_rg_inf, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U10, U13. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold ONH_ZS. repeat split; first [exact I | lia].
- unfold onh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U10, U13, U32, U33.
  change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS;
  try unfold ONH_ZS; try unfold SHADOW_OFF; first [lia | reflexivity].
Qed.

(* The valuation of run 2d: the registers at +0x14c, the shadow base, h.ack_counter (atom 33) and
   g_s.inflight_counter (atom 34); and the shadow entries the two checks read. *)
Lemma onh_entry6 : forall ly S (W : world segs) regs mem md (b Bw : list byte) fp,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 20 = w64 fp -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  4096 <= fp -> fp + 64 <= 2 ^ 47 -> fp mod 8 = 0 ->
  (fp + 64 <= ONACK_S \/ ONACK_S + 18264 <= fp) ->
  (fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp) ->
  val_mem segs (mrestrict (w_H W) mem) (fp + 24) 4 (DSpec.fr_ack b) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fp + 24) 4 ->
  st_ok_pi segs VAL (onh_E6 regs b Bw) ss_onh6
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C5)) mem (YK11.seg_rom segs))) /\
  sh_ok segs ONH_Bx ONH_SH (onh_E6 regs b Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md b Bw fp HSC HAR Htw R19 R20 R25 HF0 HF47 HF8 HFPG HFPA HV HRA.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onh_E6 regs b Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold onh_E6; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (onh_E6 regs b Bw) 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold onh_E6; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (onh_E6 regs b Bw) 33 = Z_to_bv 64 (DSpec.fr_ack b))
  by (unfold onh_E6; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (onh_E6 regs b Bw) 34 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 1744) 4))
  by (unfold onh_E6; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (CS : ONACK_S = 6158784) by reflexivity.
assert (R33 : 0 <= DSpec.fr_ack b < 2 ^ 32) by apply onh_fr_ack_range.
assert (R34 : 0 <= TW.u_at Bw (TW.OFF_g_s + 1744) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U19 : bv_unsigned (ew (onh_E6 regs b Bw) 19) = ONACK_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (onh_E6 regs b Bw) 20) = fp)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (onh_E6 regs b Bw) 25) = SHADOW_OFF)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (onh_E6 regs b Bw) 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (onh_E6 regs b Bw) 33) = DSpec.fr_ack b)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (onh_E6 regs b Bw) 34) = TW.u_at Bw (TW.OFF_g_s + 1744) 4)
  by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_onh6, onh_regions6.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [onh_rg_f onh_rg_cnt YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ fp 24 4 (SOff 33 0) (DSpec.fr_ack b));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia | exact HV].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ ONACK_S 1744 4 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 1744) 4));
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | exact R34 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 1744 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold onh_rg_f, onh_rg_cnt, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite U19, U20. rewrite ?CS in *. repeat split; first [exact I | lia].
  + unfold onh_facts6, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U20, U25, U32, U33, U34.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. change (2 ^ 47) with 140737488355328.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS;
    try unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (onh_E6 regs b Bw) ONH_Bx = SHADOW_OFF).
  { unfold U, ONH_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, ONH_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W) mem _ ONH_Bx 20 (fp + 24) 4 fp 24 28 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ ONH_Bx 19 (ONACK_S + 1744) 4 ONACK_S 1744 1748
      (onh_ra ly S W mem md (ONACK_S + 1744) 4 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s, ONACK_S, TA_g_s; lia))
      UB).
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, ONACK_S, TA_g_s. lia.
Qed.

(* The branch states, with no region. *)
Lemma onh_entry5 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (onh_E regs) ss_onh5
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C4)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_onh5.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma onh_entry7 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (onh_E regs) ss_onh7
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C6)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_onh7.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma onh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The sign-extended 4-byte load of a value below 2 ^ 32. *)
Lemma onh_sext : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The facts the cuts carry move to a later memory whose view is the same at every address. *)
Lemma onh_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONACK_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

(* trans_tframe_at moves to a memory with the same view. *)
Lemma onh_tframe_move : forall lyc S2 (W : world segs) m m' regs TF,
  (forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  trans_tframe_at B lyc S2 W m regs ONACK_STK TF -> trans_tframe_at B lyc S2 W m' regs ONACK_STK TF.
Proof.
intros lyc S2 W m m' regs TF KD HT. destruct TF as [fr|]; [|exact I].
destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
split; [exact Ha0|]. split.
{ eapply garr8_frame; [exact Hg8|]. intros a Ha. apply (mbyte_of_aview segs). apply KD. }
split; [|exact Hoff].
exact (trans_src_ok_view B lyc S2 W W m m' _ _ Hsrc (fun a _ => KD a) (fun s _ => KD s)).
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac onh_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac onh_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac onh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac onh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
Ltac onh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    onh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (onh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac onh_kregE HS EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    onh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac onh_kreg4 HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    onh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac onh_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

Lemma onh_holds : @onack_head_stmt fx rc B MT.
Proof.
unfold onack_head_stmt. intros NTC IGN.
unfold transport_on_ack_cg_holds_stmt.
intros HPCS HCELLS HSC HGU HGNE HROU HRNE LAWS MTL MTF SMP ASF FFL ASM0 AI0 NT0 MO0.
unfold transport_on_ack_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi HDF Htw Hfn Hm HTF HTFG HROM HAP Hcnt Hev.
assert (HGX : gx_ok segs B TG.G_HARNESS) by (apply G_HARNESS_gx_ok; exact HGU).
assert (HGNO : gx_noerrno B TG.G_HARNESS) by (apply G_HARNESS_gx_noerrno; exact HGNE).
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDF as (Hcode & Hbuf0 & Hbufg & Hbufsrc & Hbufwin & HbufG & Hfp0 & Hfp8 & Hfjlen & Hfg & Hffake & Hfrd
  & Hfwin).
assert (FS : ONACK_STK = 8496) by reflexivity.
assert (FF : ONACK_FRAME = 128) by reflexivity.
assert (CS : ONACK_S = 6158784) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - ONACK_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (onh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (onh_E regs)) by apply onh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (onh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (onh_E regs) 2) = spZ regs)
  by (rewrite (onh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_ack)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x070 *)
paj_run_tok RUN HS HJ SHOK ONH_B0.
{ onh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia).
assert (E2' : ew (onh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (onh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
onh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 29244)) R1 ltac:(apply codeptr_val; exact HEI).
onh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (onh_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
onh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
onh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
onh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
onh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (onh_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
onh_reg HS (19%bv : bv 5) (w64 ONACK_S) R19
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
onh_reg HS (20%bv : bv 5) (w64 fp) R20
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
onh_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) R25
  ltac:(cbn [sv_denot]; rewrite (onh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the thirteen words the prologue saved, read back from the stack region the run wrote *)
onh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) onh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold onh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) onh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold onh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(onh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (onh_E regs) _ 2 (spZ regs) _ (-128) 0 (-128) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (onh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; onh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* +0x070: the class-2 stack malloc *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_2)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP ONACK_CID ASM
    ltac:(unfold ONACK_CID; lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 29244)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONACK_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ ONACK_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ ONACK_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh.
change (fs_frame_bytes ONACK_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc ONACK_CID pos) in *.
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) onh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 ONACK_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 fp)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q25 : YK11.getr regs2 25 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
clear HS.
set (memT := ms_mem ms) in *. set (regsT := ms_regs ms) in *. clearbody memT regsT. clear ms.
(* run 2a, +0x074 .. +0x0dc *)
pose proof (onh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q25 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (onh_E regs2)) by apply onh_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (onh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U10' : bv_unsigned (ew (onh_E regs2) 10) = F)
  by (rewrite (onh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK ONH_B0.
{ onh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONACK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONACK_CID) with 256.
  change (frame_addr lyc ONACK_CID pos) with F. lia. }
clear HEI0 HEI1. rename HF into HF2a, HFr into HFr2a, HG into HG2a.
assert (Hwin : forall a, spZ regs - ONACK_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 128 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memT (spZ regs - ONACK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
    (spZ regs - ONACK_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 128 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b0 m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - ONACK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W memT W mem2 (spZ regs - ONACK_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
assert (EF10 : ew (onh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (onh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF25 : ew (onh_E regs2) 25 = Z_to_bv 64 SHADOW_OFF) by (rewrite (onh_ew_reg regs2 25 25%bv eq_refl); exact Q25).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
onh_reg HS (23%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T23
  ltac:(exact (can_denot_shadow (onh_E regs2) 10 25 F SHADOW_OFF EF10 EF25 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
onh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. onh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
onh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. onh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
onh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. onh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
onh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. onh_kreg HS regs2 (25%bv : bv 5) 25%nat Q25 T25.
onh_reg HS (24%bv : bv 5) (w64 F) T24
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
onh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
onh_reg HS (10%bv : bv 5) (w64 (ONACK_S + 212)) T10
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs2 19 19%bv eq_refl), Q19; unfold w64;
        rewrite (unsigned_lit_small ONACK_S) by lia; reflexivity).
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => F <= x < F + 24) HFr2a); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U10' in Hx; lia |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* run 2b, +0x0e0 .. +0x134 *)
pmkst HS.
set (ms3 := ms) in *. clearbody ms3. clear HS.
pose proof (onh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) T23
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI3 : img_env VAL A_LIM (onh_E (ms_regs ms3))) by apply onh_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (onh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U23 : bv_unsigned (ew (onh_E (ms_regs ms3)) 23) = SHADOW_OFF + F / 8)
  by (rewrite (onh_ew_reg (ms_regs ms3) 23 23%bv eq_refl), T23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONH_C3.
{ onh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONACK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONACK_CID / 8) with 32.
  change (frame_addr lyc ONACK_CID pos) with F. unfold shadow_addr. lia. }
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U23 in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
onh_kreg HS (ms_regs ms3) (2%bv : bv 5) 2%nat T2 V2. onh_kreg HS (ms_regs ms3) (3%bv : bv 5) 3%nat T3 V3.
onh_kreg HS (ms_regs ms3) (4%bv : bv 5) 4%nat T4 V4. onh_kreg HS (ms_regs ms3) (8%bv : bv 5) 8%nat T8 V8.
onh_kreg HS (ms_regs ms3) (9%bv : bv 5) 9%nat T9 V9. onh_kreg HS (ms_regs ms3) (18%bv : bv 5) 18%nat T18 V18.
onh_kreg HS (ms_regs ms3) (19%bv : bv 5) 19%nat T19 V19. onh_kreg HS (ms_regs ms3) (20%bv : bv 5) 20%nat T20 V20.
onh_kreg HS (ms_regs ms3) (23%bv : bv 5) 23%nat T23 V23. onh_kreg HS (ms_regs ms3) (24%bv : bv 5) 24%nat T24 V24.
onh_kreg HS (ms_regs ms3) (25%bv : bv 5) 25%nat T25 V25. onh_kreg HS (ms_regs ms3) (10%bv : bv 5) 10%nat T10 V10.
assert (EA10 : ew (onh_E (ms_regs ms3)) 10 = Z_to_bv 64 (ONACK_S + 212))
  by (rewrite (onh_ew_reg (ms_regs ms3) 10 10%bv eq_refl); exact T10).
assert (EA25 : ew (onh_E (ms_regs ms3)) 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (onh_ew_reg (ms_regs ms3) 25 25%bv eq_refl); exact T25).
assert (ZS1 : 0 <= ONACK_S + 212 < 2 ^ 64) by (rewrite CS; lia).
assert (ZS2 : 0 <= SHADOW_OFF) by (unfold SHADOW_OFF; lia).
assert (ZS3 : SHADOW_OFF + (ONACK_S + 212) / 8 < 2 ^ 64) by (rewrite <- onh_zs_eq; unfold ONH_ZS; lia).
onh_reg HS (13%bv : bv 5) (Z_to_bv 64 ONH_ZS) V13
  ltac:(rewrite onh_zs_eq;
        exact (can_denot_shadow (onh_E (ms_regs ms3)) 10 25 (ONACK_S + 212) SHADOW_OFF EA10 EA25 ZS1 ZS2 ZS3)).
(* the bytes of G at +0x138 are the entry's *)
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONACK_CID pos a HAR2 Hin2 ltac:(change (fs_frame_bytes ONACK_CID) with 256; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (Htw4 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms0)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b0 + i)).
  { unfold inG. apply Exists_exists. exists (b0, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K2b (b0 + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (K2a (b0 + i) ltac:(lia) ltac:(intros Hx; exact (NGF (b0 + i) ltac:(lia) Hg))).
  exact (GK2 (b0 + i) Hg). }
(* run 2c, +0x138 .. +0x148 *)
pmkst HS.
set (ms4 := ms0) in *. clearbody ms4. clear HS SHOK.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
pose proof (onh_entry4 lyc S2 W (ms_regs ms4) (ms_mem ms4) _ Bw sp1 HSC HAR4 Htw4 V9 ltac:(lia) Hsp1al
  ltac:(intros a Ha; apply (onh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia) V10 V13) as HS.
clear HEI.
assert (HEI : img_env VAL A_LIM (onh_E4 (ms_regs ms4) Bw)) by (unfold onh_E4; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (onh_E4 (ms_regs ms4) Bw) (mrestrict (w_H W) (ms_mem ms4)))
  by constructor.
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (onh_E4 (ms_regs ms4) Bw) n = YK11.getr (ms_regs ms4) r)
  by (intros n r Hn; unfold onh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9c : bv_unsigned (ew (onh_E4 (ms_regs ms4) Bw) 9) = sp1)
  by (rewrite (EE4 9%nat 9%bv eq_refl), V9; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONH_C3)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK ONH_B0.
{ onh_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9c in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HF2c, HFr into HFr2c, HG into HG2c.
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 16 <= x < sp1 + 24) HFr2c);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9c in Hx; lia |]).
  destruct Hin. }
onh_kregE HS EE4 (2%bv : bv 5) 2%nat V2 X2. onh_kregE HS EE4 (3%bv : bv 5) 3%nat V3 X3.
onh_kregE HS EE4 (4%bv : bv 5) 4%nat V4 X4. onh_kregE HS EE4 (8%bv : bv 5) 8%nat V8 X8.
onh_kregE HS EE4 (9%bv : bv 5) 9%nat V9 X9. onh_kregE HS EE4 (18%bv : bv 5) 18%nat V18 X18.
onh_kregE HS EE4 (19%bv : bv 5) 19%nat V19 X19. onh_kregE HS EE4 (20%bv : bv 5) 20%nat V20 X20.
onh_kregE HS EE4 (23%bv : bv 5) 23%nat V23 X23. onh_kregE HS EE4 (24%bv : bv 5) 24%nat V24 X24.
onh_kregE HS EE4 (25%bv : bv 5) 25%nat V25 X25. onh_kregE HS EE4 (13%bv : bv 5) 13%nat V13 X13.
assert (E33c : ew (onh_E4 (ms_regs ms4) Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 212) 4))
  by (unfold onh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
onh_reg HS (11%bv : bv 5) (Z_to_bv 64 (TW.S_inflight Bw)) X11
  ltac:(unfold TW.S_inflight, TW.s32_at, TW.A_S_inflight;
        exact (onh_sext (onh_E4 (ms_regs ms4) Bw) 33 _ E33c (TWL.u_at_range Bw _ 4))).
(* ---- the facts both cuts carry, at the memory of +0x148 ---- *)
set (m5 := ms_mem ms) in *.
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2c a Ha ltac:(intros X; apply Hn; tauto)).
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros X; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2c). apply (apresent_grows _ _ _ a G2b).
  exact (apresent_grows _ _ _ a G2a Ha). }
assert (NGS : forall a, F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/
  sp1 + 16 <= a < sp1 + 24 -> ~ inG TG.G_HARNESS a).
{ intros a [X | [X | X]]; [apply NGF; lia | apply NGH; unfold SHADOW_OFF in *; lia | apply NGH; unfold SHADOW_OFF; lia]. }
assert (GKF : gx_kept segs TG.G_HARNESS W memc W m5).
{ intros a Hg. rewrite <- (GK2 a Hg).
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros X. exact (NGS a X Hg). }
assert (TW5 : tw_at TMAP_A (aview segs (w_H W) m5) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n i Hin Hi.
  apply GKF. unfold inG. apply Exists_exists. exists (b0, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (KGF : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m5 (spZ regs - ONACK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - ONACK_STK) (spZ regs) ONACK_CID pos F (flag_addr lyc ONACK_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes ONACK_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes ONACK_CID / 8) with 32. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) onh_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
{ unfold ONACK_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold onh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + ONACK_FBYTES - 8) = Some (flag_addr lyc ONACK_CID pos)).
{ rewrite <- Hflag. unfold ONACK_FBYTES. apply rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b0 ?g ?xo ?o ?stk ?sp ?fpx ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W m5 md5 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj _ (conj HFW5 HFL5)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - unfold ONACK_EV, MAYBEON_EV, NOTICE_EV. lia.
  - rewrite Eab2. apply Permutation_refl.
  - apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W m5 (spZ regs - ONACK_STK) (spZ regs)
      (fun _ => False) (onack_wr Bw b)); [tauto | exact KGF]. }
assert (GXE5 : gx_kept_ex segs TG.G_HARNESS (onack_wr Bw b) W memc W m5)
  by (intros a Hg _; exact (GKF a Hg)).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR5.
pose proof Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & ESHI & _).
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
(* the read-only bytes, at the +0x148 memory: image bytes outside G, the owned statics and errno *)
assert (ROM5 : trans_rom_view_rd W m5).
{ intros a Ha. rewrite <- (HROM a Ha).
  destruct (trans_ro_rd_scoped B HROU HRNE a Ha) as [Ho He].
  destruct KGF as (_ & _ & KG3 & _).
  apply (KG3 a (trans_ro_img a Ha)); [| exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia. }
assert (TFR5 : trans_tframe_at B lyc S2 W m5 regs ONACK_STK TF)
  by exact (TransportGNotice.trans_tframe_at_kept_gx B LAWS HROU HRNE lyc Sc W memc mdc lyc S2 W m5 md5
              (fun _ => False) regs regs ONACK_STK ONACK_STK TF HAR HAR5
              ltac:(intros bm Hb; rewrite Eab2; exact Hb) ltac:(intros f Hf; rewrite Hfrs2; right; exact Hf)
              (fun c p => eq_refl) eq_refl eq_refl HSTKLT KGF ltac:(intros a Ha _; exact (GKF a Ha))
              ltac:(intros fr _ a _ H; exact H) ltac:(intros a _ H; exact H) ltac:(lia) ltac:(lia) HTF).
assert (HLAWS : onack_laws B MT).
{ refine (conj HPCS (conj HCELLS (conj HSC (conj HGU (conj HGNE (conj HROU (conj HRNE _))))))).
  refine (conj LAWS (conj MTL (conj MTF (conj SMP (conj ASF (conj FFL (conj HGX HGNO))))))). }
assert (HFIX : onack_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F).
{ unfold onack_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
    (conj _ (conj Htw (conj Hfn (conj Hm (conj HTF (conj HROM (conj HAP (conj Hcnt (conj Hev
    (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp)))))))))))))))))))))))).
  - refine (conj Hcode (conj Hbuf0 (conj Hbufg (conj Hbufsrc (conj Hbufwin (conj HbufG _)))))).
    exact (conj Hfp0 (conj Hfp8 (conj Hfjlen (conj Hfg (conj Hffake (conj Hfrd Hfwin)))))).
  - unfold sp1, ONACK_FRAME. replace (spZ regs - 128) with (spZ regs + -128) by lia. reflexivity. }
assert (D11 : sv_denot (onh_E (ms_regs ms)) (SOff 11 0) = Z_to_bv 64 (TW.S_inflight Bw))
  by (cbn [sv_denot]; rewrite (onh_ew_reg (ms_regs ms) 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
(* +0x148: `beqz a1`, from a state with no region *)
pmkst HS.
clear HS SHOK.
pose proof (onh_entry5 W (ms_regs ms) m5) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (onh_E (ms_regs ms)) (mrestrict (w_H W) m5)) by constructor.
clear HEI. assert (HEI : img_env VAL A_LIM (onh_E (ms_regs ms))) by apply onh_env_img.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONH_C4)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK ONH_B0.
- (* S_inflight Bw = 0: the ignored cut *)
  cbn [branch_taken] in Hc. rewrite D11 in Hc.
  change (sv_denot (onh_E (ms_regs ms)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (onh_eqb0 _ (onh_s_inflight_range Bw)) in Hc. apply Z.eqb_eq in Hc.
  assert (HIGN : onack_ign Bw b = true)
    by (unfold onack_ign; rewrite Hc; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONACK_IGN.
  { onh_awr_rs. apply awr_ok_x_nil. }
  onh_after_cut HS W KD GR m5 msF.
  onh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Y2. onh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Y3.
  onh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Y4. onh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Y8.
  onh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Y9. onh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Y18.
  onh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat X19 Y19. onh_kreg HS (ms_regs ms) (23%bv : bv 5) 23%nat X23 Y23.
  onh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Y24. onh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Y25.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_IGN)) mm rom) mdx) Q) end.
  apply (IGN HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F S2
    (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onack_ign_cur.
    refine (conj (onh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR) (conj Eab2 (conj _ (conj _ HIGN)))).
    * intros a Hg Hn. rewrite KD. exact (GXE5 a Hg Hn).
    * apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KD x)].
  + unfold onack_regs_ign, onack_regs_rel.
    refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))) (conj Y19 Y25)).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
- (* S_inflight Bw <> 0: on to run 2d *)
  cbn [branch_taken] in Hc. rewrite D11 in Hc.
  change (sv_denot (onh_E (ms_regs ms)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (onh_eqb0 _ (onh_s_inflight_range Bw)) in Hc. apply Z.eqb_neq in Hc.
  assert (HI1 : (TW.S_inflight Bw =? 0) = false) by (apply Z.eqb_neq; exact Hc). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONH_C5.
  { onh_awr_rs. apply awr_ok_x_nil. }
  onh_after_cut HS W KD GR m5 msD.
  onh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Z2. onh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Z3.
  onh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Z4. onh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Z8.
  onh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Z9. onh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Z18.
  onh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat X19 Z19. onh_kreg HS (ms_regs ms) (20%bv : bv 5) 20%nat X20 Z20.
  onh_kreg HS (ms_regs ms) (23%bv : bv 5) 23%nat X23 Z23. onh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Z24.
  onh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Z25. onh_kreg HS (ms_regs ms) (13%bv : bv 5) 13%nat X13 Z13.
  set (m6 := ms_mem msD) in *.
  assert (KD6 : forall a, aview segs (w_H W) m6 a = aview segs (w_H W) m5 a) by exact KD.
  assert (GR6 : forall a, apresent (w_H W) m5 a -> apresent (w_H W) m6 a) by exact GR.
  pmkst HS.
  rename HF into HFc1, HFr into HFrc1, HG into HGc1, ms into ms148.
  clear HS SHOK.
  (* f lies in a frame of the call, apart from the frame this call took *)
  destruct Hffake as (cidF & posF & HinF & HFF1 & HFF2).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cidF posF HAR HinF) as (HFF0 & HFFc & _).
  unfold FRAME_F_SIZE in HFF2.
  assert (HKB : forall a, fp <= a < fp + 64 -> aview segs (w_H W) m5 a = aview segs (w_H W) memc a).
  { intros a Ha.
    exact (dk_kept_frame_byte_g segs B TG.G_HARNESS lyc Sc W memc m5
      (spZ regs - ONACK_STK) (spZ regs) (fun _ => False) cidF posF a KGF HinF ltac:(lia)
      ltac:(exact (fun H0 => H0))). }
  assert (HG6 : garr8 segs (mrestrict (w_H W) m6) fp (frame_f_bytes buf b fj)).
  { eapply garr8_frame; [exact Hfg|]. intros a Ha.
    rewrite (onh_fbytes_len buf b fj Hcode Hfjlen) in Ha.
    apply (mbyte_of_aview segs). rewrite KD6. apply HKB. lia. }
  assert (HVACK : val_mem segs (mrestrict (w_H W) m6) (fp + 24) 4 (DSpec.fr_ack b)).
  { intros kk Hk.
    pose proof (garr8_mbyte segs (mrestrict (w_H W) m6) fp (frame_f_bytes buf b fj) (24 + kk) HG6
      ltac:(rewrite (onh_fbytes_len buf b fj Hcode Hfjlen); lia)) as Hb.
    rewrite (onh_nth_ack buf b fj kk Hcode Hfjlen Hk) in Hb.
    replace (fp + 24 + Z.of_nat kk) with (fp + Z.of_nat (24 + kk)) by lia. exact Hb. }
  assert (HRA5 : range_addressable (aview segs (w_H W) m5) SHADOW_OFF (fp + 24) 4).
  { apply (dk_kept_ra_g segs B LAWS TG.G_HARNESS lyc Sc W memc mdc m5
      (spZ regs - ONACK_STK) (spZ regs) (fun _ => False) cidF posF (fp + 24) 4 HAR KGF HinF
      ltac:(lia) ltac:(lia) ltac:(intros x Hx HH; exact HH)).
    exact (range_addressable_sub (aview segs (w_H W) memc) SHADOW_OFF fp FRAME_F_SIZE (fp + 24) 4
      (proj1 (proj2 Hfrd)) ltac:(lia) ltac:(unfold FRAME_F_SIZE; lia)). }
  assert (HRA6 : range_addressable (aview segs (w_H W) m6) SHADOW_OFF (fp + 24) 4).
  { intros x Hx. destruct (HRA5 x Hx) as (s & Hs & Hok). exists s. rewrite KD6. exact (conj Hs Hok). }
  assert (Htw6 : tw_at TMAP_A (aview segs (w_H W) m6) Bw)
    by (apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KD6 x)]).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR6.
  (* run 2d, +0x14c .. +0x17c *)
  assert (HFPG : fp + 64 <= ONACK_S \/ ONACK_S + 18264 <= fp).
  { destruct (Z_le_gt_dec (fp + 64) ONACK_S) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (ONACK_S + 18264) fp) as [H2|H2]; [right; exact H2|].
    exfalso.
    apply (frm_img segs B LAWS lyc Sc W memc mdc cidF posF (Z.max fp ONACK_S) HAR HinF ltac:(lia)).
    apply trans_g_img. apply onh_inG. unfold TW.SZ_g_s. lia. }
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc cidF posF HAR HinF) as (_ & HFFapp & _ & _).
  assert (HFPA : fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp).
  { destruct HFFapp as (_ & [HL | [HH _]]); [left | right]; lia. }
  destruct (onh_entry6 lyc S2 W (ms_regs msD) m6 _ b Bw fp HSC HAR6 Htw6 Z19 Z20 Z25
    ltac:(lia) ltac:(lia) Hfp8 HFPG HFPA HVACK HRA6) as [HS SHOK].
  clear HEI.
  assert (HEI : img_env VAL A_LIM (onh_E6 (ms_regs msD) b Bw)) by (unfold onh_E6; apply Eimg_env).
  assert (EE6 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (onh_E6 (ms_regs msD) b Bw) n = YK11.getr (ms_regs msD) r)
    by (intros n r Hn; unfold onh_E6; apply can_ew_Eimg_Ereg_nat; exact Hn).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONH_C5)) mm rom) mdx) Q) end.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { onh_awr_rs.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
  match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E7 := EF) in * end.
  assert (E7lo : forall n, (n < 1024)%nat -> ew E7 n = ew (onh_E6 (ms_regs msD) b Bw) n)
    by (intros n Hn; unfold E7; rewrite !ew_ewset_other by lia; reflexivity).
  onh_kreg4 HS E7lo EE6 (2%bv : bv 5) 2%nat Z2 W2r. onh_kreg4 HS E7lo EE6 (3%bv : bv 5) 3%nat Z3 W3r.
  onh_kreg4 HS E7lo EE6 (4%bv : bv 5) 4%nat Z4 W4r. onh_kreg4 HS E7lo EE6 (8%bv : bv 5) 8%nat Z8 W8r.
  onh_kreg4 HS E7lo EE6 (9%bv : bv 5) 9%nat Z9 W9r. onh_kreg4 HS E7lo EE6 (13%bv : bv 5) 13%nat Z13 W13r.
  onh_kreg4 HS E7lo EE6 (18%bv : bv 5) 18%nat Z18 W18r. onh_kreg4 HS E7lo EE6 (19%bv : bv 5) 19%nat Z19 W19r.
  onh_kreg4 HS E7lo EE6 (20%bv : bv 5) 20%nat Z20 W20r. onh_kreg4 HS E7lo EE6 (23%bv : bv 5) 23%nat Z23 W23r.
  onh_kreg4 HS E7lo EE6 (24%bv : bv 5) 24%nat Z24 W24r. onh_kreg4 HS E7lo EE6 (25%bv : bv 5) 25%nat Z25 W25r.
  assert (E33d : ew E7 33 = Z_to_bv 64 (DSpec.fr_ack b))
    by (rewrite E7lo by lia; unfold onh_E6; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra _ _ 1)).
  assert (E34d : ew E7 34 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 1744) 4))
    by (rewrite E7lo by lia; unfold onh_E6; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra _ _ 2)).
  onh_reg HS (26%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (DSpec.fr_ack b))) W26r
    ltac:(exact (onh_sext E7 33 _ E33d (onh_fr_ack_range b))).
  onh_reg HS (11%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (TW.S_inflight_counter Bw))) W11r
    ltac:(unfold TW.S_inflight_counter, TW.A_S_inflight_counter;
          exact (onh_sext E7 34 _ E34d (TWL.u_at_range Bw _ 4))).
  (* run 2d writes nothing *)
  assert (K2d : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) m6 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros HH; exact HH].
    intros b0 wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
    destruct Hin. }
  set (m7 := ms_mem ms) in *.
  assert (KD7 : forall a, aview segs (w_H W) m7 a = aview segs (w_H W) m5 a).
  { intros a. rewrite (aview_wrap64 segs _ m7 a), (aview_wrap64 segs _ m5 a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)).
    rewrite K2d by lia. exact (KD6 _). }
  assert (GR7 : forall a, apresent (w_H W) m5 a -> apresent (w_H W) m7 a).
  { intros a Ha. apply (apresent_grows _ _ _ a HG). exact (GR6 a Ha). }
  pmkst HS. clear HS SHOK.
  pose proof (onh_entry7 W (ms_regs ms) m7) as HS.
  assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (onh_E (ms_regs ms)) (mrestrict (w_H W) m7)) by constructor.
  clear HEI. assert (HEI : img_env VAL A_LIM (onh_E (ms_regs ms))) by apply onh_env_img.
  assert (D26 : sv_denot (onh_E (ms_regs ms)) (SOff 26 0) = Z_to_bv 64 (bv_swrap 32 (DSpec.fr_ack b)))
    by (cbn [sv_denot]; rewrite (onh_ew_reg (ms_regs ms) 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact W26r).
  assert (D11d : sv_denot (onh_E (ms_regs ms)) (SOff 11 0)
                 = Z_to_bv 64 (bv_swrap 32 (TW.S_inflight_counter Bw)))
    by (cbn [sv_denot]; rewrite (onh_ew_reg (ms_regs ms) 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact W11r).
  assert (HCR : 0 <= TW.S_inflight_counter Bw < 2 ^ 32)
    by (unfold TW.S_inflight_counter; exact (TWL.u_at_range Bw _ 4)).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONH_C6)) mm rom) mdx) Q) end.
  psrr_branch_tok RUN BR HS SHOK ONH_B0.
  + (* fr_ack b <> S_inflight_counter Bw: the ignored cut *)
    cbn [branch_taken] in Hc. rewrite D26, D11d in Hc.
    rewrite (onh_eqb_swrap _ _ (onh_fr_ack_range b) HCR) in Hc.
    apply negb_true_iff in Hc.
    assert (HIGN : onack_ign Bw b = true)
      by (unfold onack_ign; rewrite Hc; apply orb_true_r).
    paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONACK_IGN.
    { onh_awr_rs. apply awr_ok_x_nil. }
    onh_after_cut HS W KDF GRF m7 msG.
    onh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat W2r Y2. onh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat W3r Y3.
    onh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat W4r Y4. onh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat W8r Y8.
    onh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat W9r Y9.
    onh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat W18r Y18.
    onh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat W19r Y19.
    onh_kreg HS (ms_regs ms) (23%bv : bv 5) 23%nat W23r Y23.
    onh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat W24r Y24.
    onh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat W25r Y25.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_IGN)) mm rom) mdx) Q) end.
    assert (KDG : forall a, aview segs (w_H W) (ms_mem msG) a = aview segs (w_H W) m5 a)
      by (intros a; rewrite (KDF a); exact (KD7 a)).
    assert (GRG : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msG) a)
      by (intros a Ha; apply GRF; exact (GR7 a Ha)).
    apply (IGN HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F S2
      (ms_mem msG) _ (ms_regs msG) HFIX).
    * unfold onack_ign_cur.
      refine (conj (onh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W m5 md5
        (ms_mem msG) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KDG GRG) (conj Eab2 (conj _ (conj _ HIGN)))).
      -- intros a Hg Hn. rewrite KDG. exact (GXE5 a Hg Hn).
      -- apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KDG x)].
    * unfold onack_regs_ign, onack_regs_rel.
      refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))) (conj Y19 Y25)).
      -- rewrite Y3. symmetry. exact Hgp.
      -- rewrite Y4. symmetry. exact Htp.
  + (* fr_ack b = S_inflight_counter Bw: the notice cut *)
    cbn [branch_taken] in Hc. rewrite D26, D11d in Hc.
    rewrite (onh_eqb_swrap _ _ (onh_fr_ack_range b) HCR) in Hc.
    apply negb_false_iff in Hc.
    assert (HNI : onack_ign Bw b = false)
      by (unfold onack_ign; rewrite HI1, Hc; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONACK_NTC.
    { onh_awr_rs. apply awr_ok_x_nil. }
    onh_after_cut HS W KDF GRF m7 msG.
    onh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat W2r Y2. onh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat W3r Y3.
    onh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat W4r Y4. onh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat W8r Y8.
    onh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat W9r Y9.
    onh_kreg HS (ms_regs ms) (13%bv : bv 5) 13%nat W13r Y13.
    onh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat W18r Y18.
    onh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat W19r Y19.
    onh_kreg HS (ms_regs ms) (20%bv : bv 5) 20%nat W20r Y20.
    onh_kreg HS (ms_regs ms) (23%bv : bv 5) 23%nat W23r Y23.
    onh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat W24r Y24.
    onh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat W25r Y25.
    onh_kreg HS (ms_regs ms) (26%bv : bv 5) 26%nat W26r Y26.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_NTC)) mm rom) mdx) Q) end.
    assert (KDG : forall a, aview segs (w_H W) (ms_mem msG) a = aview segs (w_H W) m5 a)
      by (intros a; rewrite (KDF a); exact (KD7 a)).
    assert (GRG : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msG) a)
      by (intros a Ha; apply GRF; exact (GR7 a Ha)).
    apply (NTC HLAWS AI0 NT0 MO0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw'
      pos sp1 F S2 (ms_mem msG) _ (ms_regs msG) HFIX).
    * unfold onack_ntc_cur.
      refine (conj (onh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W m5 md5
        (ms_mem msG) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KDG GRG)
        (conj Eab2 (conj _ (conj _ (conj _ (conj HTFG (conj _ HNI))))))).
      -- intros a Hg Hn. rewrite KDG. exact (GXE5 a Hg Hn).
      -- apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KDG x)].
      -- exact (onh_tframe_move lyc S2 W m5 (ms_mem msG) regs TF KDG TFR5).
      -- intros a Ha. rewrite KDG. exact (ROM5 a Ha).
    * unfold onack_regs_ntc, onack_regs_ign, onack_regs_rel.
      refine (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24)))))))
        (conj Y19 Y25)) (conj Y13 (conj Y20 Y26))).
      -- rewrite Y3. symmetry. exact Hgp.
      -- rewrite Y4. symmetry. exact Htp.
Qed.

End sh.

(* The head piece of the walk of on_ack (on_ack_segs.v onack_head_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onack_head : forall fx rc B MT, @onack_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@onh_holds fx rc B MT). Qed.
