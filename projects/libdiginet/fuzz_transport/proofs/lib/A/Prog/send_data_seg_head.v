(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 2564 of its 2742 lines of code are new or changed and 961 lines of the source are left out. *)
(* send_data_seg_head: Lemma sd_head : sd_head_stmt (lib/A/Prog/send_data_segs.v), the head piece of the image-A
   G-form walk of send_data, offsets +0x000 .. +0x17c of the listing lib/A/Prog/DgnTransportList.v
   (fuzz_transport.asan 0x8a12c .. 0x8a2a8), ending at the cut SD_FB (the return address of diginet_frame_build).

   Five runs of the position-abstract engine over the caller's G journal (TransportGRunA.v paj_run_x /
   paj_run_to_x) and three calls:
     +0x000 .. +0x044  the frame, `sd zero, 0(sp)`, the 13 saves, s0 = the entry sp, the 32-byte realign into
                       sp = s1 = sp1; it is cut at +0x048, where `sd a4, 16(s1)` has a base no region can match;
     +0x048 .. +0x07c  the two slots s1 + 16 (now) and s1 + 24 (body_len), s7 = ncmds, s6 = bodyp, the two runtime
                       cells (the use-after-return flag = 1, so `beqz a2` is not taken), s4 = the shadow base,
                       s3 = s, a0 = 64 and `jal __asan_stack_malloc_0` (TransportGFrame.v gx_stack_malloc_at);
     +0x080 .. +0x0e4  s2 = s10 = the frame F (>= 4096, so the real-stack arm at +0x094 is not entered), the slot
                       s1 + 48, s8 = hp = F + 32, the frame's 24-byte header; cut at +0x0e8, the first shadow store;
     +0x0e8 .. +0x114  the frame's 8 shadow bytes (0 .. 3 := 0xf1, 4 .. 5 := 0, 6 .. 7 := 0xf3) and the memset's
                       arguments, then `jal __asan_memset` (TransportGCg.v gx_intrin_at: hp, 0, 15);
     +0x11c .. +0x178  the store of the low byte of ncmds at hp + 15, the checked load of S_host_counter, the two
                       stores of the new counter at s + 160 and at hp + 4, the checked load of S_cfg_sum_mode and
                       the seven argument registers, then `jal diginet_frame_build` (+0x17c).
   The two instrumented checks of run 5 are decided by the token engine's shadow entry for g_s's payload (SDH_SH,
   whose shadow is 0 by trans_senddata_cells), so neither error path is reached. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA TransportGFrame CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg send_data_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TNd := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states of the five runs                             *)
(* ------------------------------------------------------------------ *)

(* The four cuts inside the head: the store `sd a4, 16(s1)` whose base is the realigned sp, the return of the stack
   malloc, the first shadow store (its base s11 is computed in the run before) and the return of the memset. *)
Definition SDH_C1 : Z := AF_send_data + 0x48.
Definition SDH_C2 : Z := AF_send_data + 0x80.
Definition SDH_C3 : Z := AF_send_data + 0xe8.
Definition SDH_C4 : Z := AF_send_data + 0x11c.
(* The degenerate shadow band of the runs that make no instrumented check (their writable regions are the frame
   and its shadow bytes, which the real band would meet). *)
Definition SDH_B0 : Z * Z := (0, 0).

(* The use-after-return flag: its GOT word (object 0) holds the cell (object 94), which holds 1 in every state. *)
Definition sdh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 94) 0))].
Definition sdh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition sdh_img_regions : smem := [got_regionP; bcell_regionP 32; sdh_got_uar; sdh_uar_cell].

(* run 1, the entry: the 160-byte frame below sp and the four image regions. *)
Definition sdh_regions1 : smem := stack_region SENDDATA_FRAME :: sdh_img_regions.
Definition sdh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sdh1 : sstate := mkSS AF_send_data sr_atoms sdh_regions1 None sdh_facts1.

(* run 2, +0x048: the two slots at the realigned sp (atom 9 = s1) and the four image regions. *)
Definition sdh_rg_slot2 : YP09.region := YP09.mkRegion (Some 9%nat) 16 32 16 32 [].
Definition sdh_regions2 : smem := sdh_rg_slot2 :: sdh_img_regions.
Definition sdh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sdh2 : sstate := mkSS SDH_C1 sr_atoms sdh_regions2 None sdh_facts2.

(* run 3, +0x080: the slot s1 + 48 and the frame's 24-byte header (atom 10 = a0 = F). *)
Definition sdh_rg_slot3 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition sdh_rg_hdr3 : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition sdh_regions3 : smem := [sdh_rg_slot3; sdh_rg_hdr3].
Definition sdh_facts3 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sdh3 : sstate := mkSS SDH_C2 sr_atoms sdh_regions3 None sdh_facts3.

(* run 4, +0x0e8: the frame's 8 shadow bytes (atom 27 = s11). *)
Definition sdh_rg_sh4 : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 0 8 [].
Definition sdh_regions4 : smem := [sdh_rg_sh4].
Definition sdh_facts4 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF (2 ^ 46) 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sdh4 : sstate := mkSS SDH_C3 sr_atoms sdh_regions4 None sdh_facts4.

(* run 5a, +0x11c: the store of the low byte of ncmds at hp + 15 = F + 47 (atom 26 = s10). The head's last stretch
   is cut into four runs so that the two runs which make an instrumented check carry no writable region of the own
   frame: the shadow band the token engine is told about would meet such a region (YP0j.v cells_safe_b). *)
Definition SDH_C5 : Z := AF_send_data + 0x120.
Definition SDH_C6 : Z := AF_send_data + 0x144.
Definition SDH_C7 : Z := AF_send_data + 0x148.
Definition sdh_rg_nc : YP09.region := YP09.mkRegion (Some 26%nat) 47 48 47 48 [].
Definition sdh_facts5a : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF 4096 (2 ^ 47) 6);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sdh5a : sstate := mkSS SDH_C4 sr_atoms [sdh_rg_nc] None sdh_facts5a.

(* run 5b, +0x120 .. +0x140: s9 = s + 160 and its shadow address, the checked load of S_host_counter (atom 33) and
   the store of the new counter at s + 160. *)
Definition sdh_rg_hc : YP09.region :=
  YP09.mkRegion (Some 19%nat) 160 164 160 164 [YP09.mkChunk 160 (CVal 4 (SOff 33 0))].
Definition sdh_facts5b : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF SENDDATA_S SENDDATA_S 6);
           (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_sdh5b : sstate := mkSS SDH_C5 sr_atoms [sdh_rg_hc] None sdh_facts5b.
Definition SDH_SHb : list shent := [mkSHE 19 160 164].
(* The shadow base the token engine reads is s4 (atom 20). *)
Definition SDH_Bx : sv := SOff 20 0.

(* run 5c, +0x144: the store of the new counter at hp + 4 (atom 24 = s8). *)
Definition sdh_rg_hp : YP09.region := YP09.mkRegion (Some 24%nat) 4 8 4 8 [].
Definition sdh_facts5c : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (24%nat, mkAF 4096 (2 ^ 47) 5);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sdh5c : sstate := mkSS SDH_C6 sr_atoms [sdh_rg_hp] None sdh_facts5c.

(* run 5d, +0x148 .. +0x178: the checked load of S_cfg_sum_mode (atom 33), the seven argument registers, the slot
   s1 + 24 (atom 34, body_len) and `jal diginet_frame_build`. *)
Definition sdh_rg_md : YP09.region :=
  YP09.mkRegion (Some 19%nat) 20 24 0 0 [YP09.mkChunk 20 (CVal 4 (SOff 33 0))].
Definition sdh_rg_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 34 0))].
Definition sdh_facts5d : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF (SENDDATA_S + 20) (SENDDATA_S + 20) 2);
           (19%nat, mkAF SENDDATA_S SENDDATA_S 6); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition ss_sdh5d : sstate := mkSS SDH_C7 sr_atoms [sdh_rg_md; sdh_rg_sl] None sdh_facts5d.
Definition SDH_SHd : list shent := [mkSHE 19 20 24; mkSHE 10 0 4].

(* ------------------------------------------------------------------ *)
(* 2. Small shared facts                                               *)
(* ------------------------------------------------------------------ *)

(* Byte j < w of a 64-bit word holding v. *)
Lemma sdh_bow : forall v j (w : nat), (j < w)%nat -> (w <= 8)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v w j.
Proof.
intros v j w Hj Hw. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The 4-byte signed load of an atom holding the unsigned int u, and the 64-bit add (m_lost_cgW.v's). *)
Lemma sdh_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (Mem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma sdh_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* One byte of a 4-byte little-endian cell, as diginet_frame_build's frame_fb_hdr_bytes writes it. *)
Lemma sdh_hdrb : forall v j, (j < 4)%nat ->
  DSpec.bz (Z_to_bv 8 (Z.shiftr (bv_unsigned (w64 v)) (8 * Z.of_nat j))) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold DSpec.bz.
change (Z_to_bv 8 (Z.shiftr (bv_unsigned (w64 v)) (8 * Z.of_nat j)))
  with (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)).
apply (sdh_bow v j 4); lia.
Qed.

(* An eight-byte word of the view kept by a step that keeps its eight bytes. *)
Lemma sdh_rdword_frame : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a Hk. unfold rdword.
  pose proof (Hk 0 ltac:(first [lia | split; lia])) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(first [lia | split; lia])), (Hk 2 ltac:(first [lia | split; lia])), (Hk 3 ltac:(first [lia | split; lia])), (Hk 4 ltac:(first [lia | split; lia])),
          (Hk 5 ltac:(first [lia | split; lia])), (Hk 6 ltac:(first [lia | split; lia])), (Hk 7 ltac:(first [lia | split; lia])). reflexivity.
Qed.

Lemma sdh_div8 : forall F x, F mod 8 = 0 -> x / 8 = F / 8 + (x - F) / 8.
Proof.
  intros F x HF. pose proof (Z.div_mod F 8 ltac:(first [lia | split; lia])) as D.
  replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma sdh_in4 : forall b a, b <= a < b + 4 -> exists j, (j < 4)%nat /\ a = b + Z.of_nat j.
Proof. intros b a H. exists (Z.to_nat (a - b)). split; lia. Qed.

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register); the cut file's
   SD_SAVED holds the same pairs as distances BELOW the entry sp. *)
Definition sdh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* The model's host-counter store: the machine adds the sign-extended load and the sign-extended ncmds, the model
   takes u32 of the unsigned sum; the two agree on four bytes (lib/Prog/T/send_data.v put_cong32, swrap32_mod,
   hc_store). *)
Lemma sdh_put_cong32 : forall u v, u mod 2 ^ 32 = v mod 2 ^ 32 -> TW.put 4 u = TW.put 4 v.
Proof.
  intros u v H. unfold TW.put.
  rewrite <- (Mem.Z_to_le_bytes_mod 4 u 32) by (cbn; lia). rewrite H.
  apply Mem.Z_to_le_bytes_mod. cbn; lia.
Qed.

Lemma sdh_swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sdh_hc_put : forall (Bw : list byte) (ncmds : Z),
  TW.put 4 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) =
  TW.put 4 (DSpec.u32 (TW.u_at Bw 1808 4 + ncmds)).
Proof.
  intros Bw ncmds. apply sdh_put_cong32. unfold DSpec.u32. rewrite Zmod_mod.
  rewrite (Zplus_mod (bv_swrap 32 (TW.u_at Bw 1808 4)) (bv_swrap 32 ncmds)), !sdh_swrap32_mod, <- Zplus_mod.
  reflexivity.
Qed.

Eval cbn in (fun send ncmds : Z => frame_fb_hdr_bytes send 0 0 TS0.DIGINET_CMD_DATA (DSpec.u8 ncmds)).

(* ------------------------------------------------------------------ *)
(* 3. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section head. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma sdh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_send_data = transport_sigma TS_send_data.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma sdh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) sdh_img_regions /\ pairwise_disjoint E sdh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct sdh_vals as (V1 & V93 & V0 & V94 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at YG0f.c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 94) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold sdh_img_regions, got_regionP, bcell_regionP, sdh_got_uar, sdh_uar_cell.
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
    unfold sdh_img_regions, got_regionP, bcell_regionP, sdh_got_uar, sdh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The environment of the runs: the 32 registers as atoms 0 .. 31, then the extra atoms. *)
Definition sdh_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).

Lemma sdh_ew_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (sdh_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold sdh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma sdh_ew_x : forall regs extra j, (j < 8)%nat ->
  ew (sdh_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
  intros regs extra j Hj. unfold sdh_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma sdh_ew_obj : forall regs extra i, (i < 95)%nat ->
  ew (sdh_E regs extra) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs extra i Hi. unfold sdh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

Lemma sdh_env_img : forall regs extra, img_env VAL A_LIM (sdh_E regs extra).
Proof. intros regs extra. unfold sdh_E. apply Eimg_env. Qed.

(* The entry state of run 1. *)
Lemma sdh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SENDDATA_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF]) ss_sdh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_send_data)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  set (E := sdh_E regs [w64 SHADOW_OFF]).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
  destruct (sdh_img_ok ly S W mem md E HCELLS HAR
    (sdh_ew_obj regs _ 1 ltac:(first [lia | split; lia])) (sdh_ew_obj regs _ 93 ltac:(first [lia | split; lia]))
    (sdh_ew_obj regs _ 0 ltac:(first [lia | split; lia])) (sdh_ew_obj regs _ 94 ltac:(first [lia | split; lia])) E32) as [HRs HPd].
  destruct sdh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_sdh1, sdh_regions1.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold SENDDATA_FRAME.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. unfold SENDDATA_FRAME. lia.
  - unfold sdh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, sdh_got_uar, sdh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (sdh_ew_obj regs _ 1 ltac:(first [lia | split; lia])))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (sdh_ew_obj regs _ 93 ltac:(first [lia | split; lia])))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (sdh_ew_obj regs _ 0 ltac:(first [lia | split; lia])))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (sdh_ew_obj regs _ 94 ltac:(first [lia | split; lia])))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94.
    unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, SENDDATA_FRAME.
    repeat split; first [exact I | lia].
  - unfold sdh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2, at +0x048: the two slots of the realigned frame and the four image regions. *)
Lemma sdh_entry2 : forall ly S (W : world segs) regs mem md (sp1 : Z),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 9 = Z_to_bv 64 sp1 ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, sp1 + 16 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF]) ss_sdh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md sp1 HCELLS HAR R2 R9 Hsp Hsp32 Hpres.
  set (E := sdh_E regs [w64 SHADOW_OFF]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
  destruct (sdh_img_ok ly S W mem md E HCELLS HAR
    (sdh_ew_obj regs _ 1 ltac:(first [lia | split; lia])) (sdh_ew_obj regs _ 93 ltac:(first [lia | split; lia]))
    (sdh_ew_obj regs _ 0 ltac:(first [lia | split; lia])) (sdh_ew_obj regs _ 94 ltac:(first [lia | split; lia])) E32) as [HRs HPd].
  destruct sdh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_sdh2, sdh_regions2.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold sdh_rg_slot2, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold sdh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold sdh_rg_slot2, got_regionP, bcell_regionP, sdh_got_uar, sdh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (sdh_ew_obj regs _ 1 ltac:(first [lia | split; lia])))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (sdh_ew_obj regs _ 93 ltac:(first [lia | split; lia])))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (sdh_ew_obj regs _ 0 ltac:(first [lia | split; lia])))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (sdh_ew_obj regs _ 94 ltac:(first [lia | split; lia])))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94.
    unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
  - unfold sdh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 3, at +0x080: the slot s1 + 48 and the frame's header (a0 = F). *)
Lemma sdh_entry3 : forall (W : world segs) regs mem (sp1 F : Z),
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 9 = Z_to_bv 64 sp1 -> YK11.getr regs 10 = w64 F ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 4096 <= F -> F + 64 <= sp1 -> F mod 64 = 0 ->
  (forall a, sp1 + 48 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF]) ss_sdh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem sp1 F R2 R9 R10 Hsp Hsp32 HF0 HFs HF64 Hpslot Hpframe.
  set (E := sdh_E regs [w64 SHADOW_OFF]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = F)
    by (unfold E; rewrite (sdh_ew_reg regs _ 10 10%bv eq_refl), R10; unfold w64;
        apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
  rewrite restrict_mkst_fx. unfold ss_sdh3, sdh_regions3.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold sdh_rg_slot3, sdh_rg_hdr3, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold sdh_rg_slot3, sdh_rg_hdr3, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold sdh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U10, E32,
      unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 4, at +0x0e8: the frame's 8 shadow bytes (s11). *)
Lemma sdh_entry4 : forall (W : world segs) regs mem (sp1 SH : Z),
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 27 = Z_to_bv 64 SH ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> SHADOW_OFF <= SH -> SH + 8 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 8 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF]) ss_sdh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem sp1 SH R2 R27 Hsp Hsp32 Hlo Hhi Hpres.
  set (E := sdh_E regs [w64 SHADOW_OFF]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SH)
    by (unfold E; rewrite (sdh_ew_reg regs _ 27 27%bv eq_refl), R27; apply unsigned_lit_small;
        unfold SHADOW_OFF in *; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
  rewrite restrict_mkst_fx. unfold ss_sdh4, sdh_regions4.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold sdh_rg_sh4, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U27. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold sdh_rg_sh4, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - unfold sdh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U27, E32,
      unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* A range inside g_s's payload, away from its end, is addressable with a visible hull at every AR state: its 64-byte
   blocks lie in the record's zero-shadow range of g_s (DgnTransportCg.v decode_zshadow_ra; g_s starts on 64). *)
Lemma sdh_gs_ra : forall ly S (W : world segs) mem md q n,
  trans_senddata_cells B -> @AR rc segs B ly S W mem md -> 0 < n ->
  SENDDATA_S <= q -> q + n <= SENDDATA_S + 18200 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview segs (w_H W) mem) q n.
Proof.
intros ly S W mem md q n HZ HAR Hn H1 H2.
apply (decode_zshadow_ra B ly S W mem md SENDDATA_S (SENDDATA_S + TW.SZ_g_s) q n HAR HZ Hn).
- assert (96231 <= q / 64) by (apply Z.div_le_lower_bound; [lia | unfold SENDDATA_S, TA_g_s in *; lia]).
  unfold SENDDATA_S, TA_g_s in *. lia.
- pose proof (Z.div_mod (q + n - 1) 64 ltac:(first [lia | split; lia])) as D.
  pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(first [lia | split; lia])) as M.
  unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia.
Qed.

(* The token engine's shadow entry [base + lo, base + hi) of g_s, at every AR state. *)
Lemma sdh_gs_shok : forall ly S (W : world segs) mem md (E : env) (mt : nat) (base lo hi : Z),
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  ew E mt = w64 base -> ew E 20 = w64 SHADOW_OFF ->
  0 <= base -> 0 <= lo ->
  SENDDATA_S <= base + lo -> lo < hi -> base + hi <= SENDDATA_S + 18200 ->
  sh_ok segs SDH_Bx [mkSHE mt lo hi] E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E mt base lo hi HSC HAR Emt E20 Hb0 Hlo0 Hlo Hlh Hhi.
assert (Hb47 : base + hi <= 2 ^ 47) by (unfold SENDDATA_S, TA_g_s in Hhi; lia).
unfold sh_ok. constructor; [|constructor].
destruct (sdh_gs_ra ly S W mem md (base + lo) (hi - lo) HSC HAR ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])) as [HRA _].
apply (shent_ok_of_range segs (w_H W) mem E SDH_Bx mt (base + lo) (hi - lo) base lo hi HRA).
- unfold U, SDH_Bx. cbn [sv_denot]. rewrite E20, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Emt, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold SENDDATA_S, TA_g_s in *. lia.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
  unfold SHADOW_OFF, SENDDATA_S, TA_g_s in *. lia.
Qed.

(* One byte of the view, as YI04.val_mem reads it (garr8's element form). *)
Lemma sdh_val1 : forall (Hh : word -> bool) m a v, 0 <= v < 256 ->
  aview segs Hh m a = Some v -> YI04.val_mem segs (mrestrict Hh m) a 1 v.
Proof.
intros Hh m a v Hv Ha j Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Ha. destruct (YP09.mbyte segs (mrestrict Hh m) a) as [b|] eqn:E;
  cbn [option_map] in Ha; [|discriminate]. injection Ha as Ha. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
pose proof (bv_unsigned_in_range 8 b) as Hb8. unfold bv_modulus in Hb8.
change (2 ^ Z.of_N 8) with 256 in Hb8.
rewrite <- Ha. change (2 ^ 8) with 256.
rewrite !Zmod_mod. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* lib/Prog/T/send_data.v's build-independent facts about the frame diginet_frame_build builds, restated here:
   that file Requires TWorldMem, which redefines the load tactics this walk uses. The proofs are its proofs. *)
Lemma sdh_skipn_split : forall (Y : list byte) n j, (j <= n)%nat -> (n <= length Y)%nat ->
  skipn j Y = skipn j (firstn n Y) ++ skipn n Y.
Proof.
  intros Y n j Hj Hn. rewrite <- (firstn_skipn n Y) at 1.
  rewrite skipn_app, length_firstn.
  replace (Nat.min n (length Y)) with n by lia.
  replace (j - n)%nat with 0%nat by lia. cbn [skipn]. reflexivity.
Qed.

Lemma sdh_upd_app_tail : forall (X v : list byte) k n,
  0 <= k -> (Z.to_nat k + n <= length X)%nat -> (length v <= n)%nat ->
  TW.upd X k (v ++ skipn (length v) (TW.sub X k n)) = TW.upd X k v.
Proof.
  intros X v k n Hk Hn Hv.
  assert (LY : length (skipn (Z.to_nat k) X) = (length X - Z.to_nat k)%nat) by apply length_skipn.
  assert (LT : length (v ++ skipn (length v) (TW.sub X k n)) = n).
  { rewrite length_app, length_skipn. unfold TW.sub. rewrite length_firstn, LY. lia. }
  unfold TW.upd. rewrite LT. f_equal. rewrite <- app_assoc. f_equal. unfold TW.sub.
  replace (Z.to_nat k + n)%nat with (n + Z.to_nat k)%nat by lia.
  replace (Z.to_nat k + length v)%nat with (length v + Z.to_nat k)%nat by lia.
  rewrite <- !skipn_skipn.
  symmetry. apply sdh_skipn_split; [lia | rewrite LY; lia].
Qed.

Lemma sdh_bc_mode : forall body cap mode,
  0 <= TNd.diginet_frame_build_code body cap mode -> mode = 0 \/ mode = 1.
Proof.
  intros body cap mode H. unfold TNd.diginet_frame_build_code in H.
  destruct ((mode =? 0) || (mode =? 1)) eqn:E; cbn [negb] in H.
  - apply orb_true_iff in E. destruct E as [E|E]; apply Z.eqb_eq in E; auto.
  - lia.
Qed.

Lemma sdh_bc_val : forall body cap mode, 0 <= TNd.diginet_frame_build_code body cap mode ->
  TNd.diginet_frame_build_code body cap mode = DSpec.frame_len (length body) /\ (length body <= 1484)%nat.
Proof.
  intros body cap mode H. unfold TNd.diginet_frame_build_code in *.
  destruct (negb ((mode =? 0) || (mode =? 1))); [lia|].
  rewrite DLib.lib_build_code_eq in *. unfold DSpec.build_code in *.
  destruct (Z.ltb_spec 1484 (Z.of_nat (length body))); [lia|].
  destruct (DSpec.system_at body); [lia|].
  destruct (cap <? DSpec.frame_len (length body)); [lia|]. split; [reflexivity | lia].
Qed.

Lemma sdh_length_lib_frame : forall dmac smac send ack retry cmd nc body mode,
  length dmac = 6%nat -> length smac = 6%nat -> mode = 0 \/ mode = 1 ->
  Z.of_nat (length (DLib.lib_frame dmac smac send ack retry cmd nc body mode))
  = DSpec.frame_len (length body).
Proof.
  intros. rewrite DLib.frame_build_bytes by assumption. apply DSpec.length_build_frame; assumption.
Qed.

Lemma sdh_bcw_eq : forall body cap mode,
  PBuildW.build_code_w body cap mode = TNd.diginet_frame_build_code body cap mode.
Proof.
  intros body cap mode. unfold PBuildW.build_code_w, TNd.diginet_frame_build_code.
  rewrite DLib.lib_build_code_eq. destruct ((mode =? 0) || (mode =? 1)); reflexivity.
Qed.

Lemma sdh_bout_eq : forall dmac smac send ack retry cmd nc bb mode oj,
  PBuildW.build_out_w dmac smac send ack retry cmd nc bb mode oj =
  (if 0 <=? TNd.diginet_frame_build_code bb (Z.of_nat (length oj)) mode
   then DLib.lib_frame dmac smac send ack retry cmd nc bb mode ++
        skipn (Z.to_nat (TNd.diginet_frame_build_code bb (Z.of_nat (length oj)) mode)) oj
   else oj).
Proof.
  intros dmac smac send ack retry cmd nc bb mode oj. unfold PBuildW.build_out_w. cbv zeta.
  rewrite sdh_bcw_eq.
  destruct (Z.leb_spec 0 (TNd.diginet_frame_build_code bb (Z.of_nat (length oj)) mode)) as [H|H];
    [|reflexivity].
  rewrite <- (DLib.frame_build_bytes dmac smac send ack retry cmd nc bb mode
                (sdh_bc_mode bb (Z.of_nat (length oj)) mode H)).
  reflexivity.
Qed.

(* The hull of the EMPTY range [q, q) inside a 64-aligned span whose shadow bytes are all visible: for q < hi it is
   the 8-byte shadow group of q (YG0s.v hull_inside at n = 1, since the hull of [q, q) sits inside the hull of
   [q, q + 1)), and for q = hi it is empty, hi being 64-aligned. This is the n = 0 case the kit's
   stack_zshadow_ra and decode_rd_ok_fake_kept leave open, and it is all an empty body needs. *)
Lemma sdh_hull0_span : forall (rd : Z -> option Z) (lo hi q : Z),
  lo mod 64 = 0 -> hi mod 64 = 0 -> 0 <= lo -> lo <= q -> q <= hi ->
  (forall g, lo <= g < hi -> rd (shadow_addr g) <> None) ->
  shadow_hull_vis rd q 0.
Proof.
intros rd lo hi q Hlo64 Hhi64 Hlo0 H1 H2 HV s Hs.
assert (Hmono : shadow_addr (q - 1) / 8 * 8 <= shadow_addr q / 8 * 8).
{ unfold shadow_addr. assert (Hd : (q - 1) / 8 <= q / 8) by (apply Z.div_le_mono; lia).
  assert ((SHADOW_OFF + (q - 1) / 8) / 8 <= (SHADOW_OFF + q / 8) / 8) by (apply Z.div_le_mono; lia). lia. }
destruct (Z.eq_dec q hi) as [Heq | Hne].
- exfalso. subst q.
  assert (Ediv : hi / 8 = 8 * (hi / 64)).
  { pose proof (Z.div_mod hi 64 ltac:(first [lia | split; lia])) as D. rewrite Hhi64, Z.add_0_r in D.
    rewrite D at 1. replace (64 * (hi / 64)) with ((8 * (hi / 64)) * 8) by lia. apply Z.div_mul. lia. }
  set (X := shadow_addr hi) in *.
  assert (EX : X mod 8 = 0).
  { unfold X, shadow_addr. rewrite Ediv. unfold SHADOW_OFF.
    replace (2147450880 + 8 * (hi / 64)) with ((268431360 + hi / 64) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod X 8 ltac:(first [lia | split; lia])) as DX. rewrite EX, Z.add_0_r in DX.
  assert (E8 : hi = 8 * (hi / 8)).
  { pose proof (Z.div_mod hi 64 ltac:(first [lia | split; lia])) as D. rewrite Hhi64, Z.add_0_r in D. rewrite Ediv. lia. }
  assert (EY : shadow_addr (hi - 1) = X - 1).
  { unfold X, shadow_addr. replace (hi - 1) with ((hi / 8 - 1) * 8 + 7) by lia.
    rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  replace (hi + 0 - 1) with (hi - 1) in Hs by lia.
  rewrite EY in Hs.
  replace ((X - 1) / 8 * 8) with (X - 8) in Hs
    by (replace (X - 1) with ((X / 8 - 1) * 8 + 7) by lia; rewrite Z.div_add_l by lia;
        change (7 / 8) with 0; lia).
  replace (X / 8 * 8) with X in Hs by lia. lia.
- assert (Hlt : q < hi) by lia.
  destruct (hull_inside lo hi q 1 s Hlo64 Hhi64 Hlo0 H1 ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])
    ltac:(replace (q + 1 - 1) with q by lia; replace (q + 0 - 1) with (q - 1) in Hs by lia; lia))
    as (g & Hg8 & Hg & ->).
  exact (HV g Hg).
Qed.

(* lib/A/Prog/DgnTransportCg.v trans_src_ok_kept with the frames of the call state only INCLUDED in those of the
   new state: the walk holds its own class-0 frame there, so frames S2 = (0, pos) :: frames Sc, not frames Sc. The
   kit's proof uses the equality for nothing else, so this is its proof with In in place of the rewrite. *)
Lemma sdh_src_kept : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  trans_src_ok B lyc Sc W memc q n -> 0 < n -> trans_src_ok B ly2 S2 W2 mem2 q n.
Proof.
intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hf Hfa Elo Ehi K1 K2 Hs Hn.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
- left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
- assert (Hrd2 : decode_rd_ok W2 mem2 q n).
  { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    - exact (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn K1 K2).
    - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
      exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd K1 Ha Hh).
    - destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia)
        ltac:(rewrite Ehi; lia)) as [Ha Hh].
      exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd K1 Ha Hh).
    - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
      exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd K1 Ha Hh). }
  exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hf Hfa Elo Ehi Hrd2
    (or_intror (conj HL Hrd))).
Qed.

(* trans_src_ok at the state in which the walk holds its own class-0 frame, for an EMPTY range (an empty body).
   The heap-block case is the structural left disjunct; the G and TRANS_RO_RD cases carry trans_sh_any, a fact of
   EVERY AR state; the caller-frame and machine-stack cases get the hull from sdh_hull0_span over a 64-aligned span
   whose shadow bytes are visible at the new state (al_frames for a frame, stack_zshadow_ra at n = 1 for the
   stack). Nothing is transported, so the stack malloc, which keeps no shadow byte of a block or of the machine
   stack, does not matter. *)
Lemma sdh_src_kept0 : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 q,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  trans_src_ok B lyc Sc W memc q 0 -> trans_src_ok B ly2 S2 W2 mem2 q 0.
Proof.
intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q HAR HAR2 Hperm Hf Hfa Elo Ehi Hs.
assert (M64 : forall x, x mod 4096 = 0 -> x mod 64 = 0).
{ intros x Hx. pose proof (Z.div_mod x 4096 ltac:(first [lia | split; lia])) as D. rewrite Hx, Z.add_0_r in D.
  rewrite D. replace (4096 * (x / 4096)) with ((64 * (x / 4096)) * 64) by lia. apply Z_mod_mult. }
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
- left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
- assert (Hhull : shadow_hull_vis (aview segs (w_H W2) mem2) q 0).
  { destruct HL as [(cid & pos & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    - assert (Hin2 : In (cid, pos) (frames S2)) by exact (Hf _ Hin).
      destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (_ & _ & _ & HFsh).
      destruct (dkg_frame_al64 segs B ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (HA64 & HS64 & HSge).
      destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (HG4096 & _ & _).
      assert (E8 : frame_addr ly2 cid pos = 8 * (frame_addr ly2 cid pos / 8)).
      { pose proof (Z.div_mod (frame_addr ly2 cid pos) 64 ltac:(first [lia | split; lia])) as D.
        rewrite HA64, Z.add_0_r in D.
        assert (frame_addr ly2 cid pos / 8 = 8 * (frame_addr ly2 cid pos / 64))
          by (rewrite D at 1; replace (64 * (frame_addr ly2 cid pos / 64))
              with ((8 * (frame_addr ly2 cid pos / 64)) * 8) by lia; apply Z.div_mul; lia).
        lia. }
      apply (sdh_hull0_span _ (frame_addr ly2 cid pos)
        (frame_addr ly2 cid pos + fs_frame_bytes cid) q HA64
        ltac:(pose proof (Z.div_mod (frame_addr ly2 cid pos) 64 ltac:(first [lia | split; lia]));
              pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(first [lia | split; lia]));
              rewrite HA64, HS64 in *;
              replace (frame_addr ly2 cid pos + fs_frame_bytes cid)
                with ((frame_addr ly2 cid pos / 64 + fs_frame_bytes cid / 64) * 64) by lia;
              apply Z_mod_mult)
        ltac:(first [lia | split; lia]) ltac:(rewrite Hfa; lia) ltac:(rewrite Hfa; lia)).
      assert (Efs8 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8)).
      { pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(first [lia | split; lia])) as D. rewrite HS64, Z.add_0_r in D.
        assert (fs_frame_bytes cid / 8 = 8 * (fs_frame_bytes cid / 64))
          by (rewrite D at 1; replace (64 * (fs_frame_bytes cid / 64))
              with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia; apply Z.div_mul; lia).
        lia. }
      intros g Hg. apply can_aview_vis.
      assert (Ed : g / 8 = frame_addr ly2 cid pos / 8 + (g - frame_addr ly2 cid pos) / 8).
      { replace g with ((g - frame_addr ly2 cid pos) + frame_addr ly2 cid pos / 8 * 8) at 1 by lia.
        rewrite Z.div_add by lia. lia. }
      assert (Eup : (g - frame_addr ly2 cid pos) / 8 < fs_frame_bytes cid / 8)
        by (apply Z.div_lt_upper_bound; lia).
      assert (Elo8 : 0 <= (g - frame_addr ly2 cid pos) / 8) by (apply Z.div_pos; lia).
      replace (shadow_addr g)
        with (shadow_addr (frame_addr ly2 cid pos) + (g - frame_addr ly2 cid pos) / 8)
        by (unfold shadow_addr; lia).
      exact (proj1 (HFsh ((g - frame_addr ly2 cid pos) / 8) ltac:(first [lia | split; lia]))).
    - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [_ Hh]. exact Hh.
    - pose proof HAR2 as HARt. destruct HARt as (M2 & _).
      pose proof (am_layout _ _ _ _ M2) as LO2.
      pose proof (lo_top _ LO2) as (_ & _ & _ & _ & Hlo4 & Hhi4 & _).
      unfold page_aligned in Hlo4, Hhi4.
      destruct (trans_stk_bounds B ly2 S2 W2 mem2 md2 HAR2) as [TK1 TK2].
      pose proof asan_consts as (AC1 & _ & _ & _ & _).
      apply (sdh_hull0_span _ (ly_stk_lo ly2) (ly_stk_hi ly2) q
        (M64 _ Hlo4) (M64 _ Hhi4) ltac:(first [lia | split; lia]) ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia)).
      intros g Hg.
      destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 g 1 HAR2 ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]))
        as [Ha _].
      destruct (Ha g ltac:(first [lia | split; lia])) as (k & Hk & _).
      unfold shadow_of_addr in Hk. unfold shadow_addr. rewrite Hk. discriminate.
    - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [_ Hh]. exact Hh. }
  destruct Hrd as (_ & _ & _ & Ham & Hq0 & Hq63).
  right. split.
  + destruct HL as [(cid & pos & Hin & F1 & F2) | [HG | [(S1 & S3) | HR]]].
    * left. exists cid, pos. rewrite !Hfa. split; [exact (Hf _ Hin) | lia].
    * right. left. exact HG.
    * right. right. left. rewrite Elo, Ehi. lia.
    * right. right. right. exact HR.
  + split; [intros a Ha; exfalso; lia |].
    split; [intros x Hx; exfalso; lia |].
    split; [exact Hhull |]. split; [exact Ham | split; [exact Hq0 | exact Hq63]].
Qed.

(* The entry state of run 5a, at +0x11c. *)
Lemma sdh_entry5a : forall (W : world segs) regs mem (sp1 F : Z),
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 26 = Z_to_bv 64 F ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 4096 <= F -> F + 64 <= sp1 -> F mod 64 = 0 ->
  (forall a, F + 47 <= a < F + 48 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF]) ss_sdh5a
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C4)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem sp1 F R2 R26 Hsp Hsp32 HF0 HFs HF64 Hpres.
  set (E := sdh_E regs [w64 SHADOW_OFF]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = F)
    by (unfold E; rewrite (sdh_ew_reg regs _ 26 26%bv eq_refl), R26; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
  rewrite restrict_mkst_fx. unfold ss_sdh5a.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold sdh_rg_nc, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U26. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold sdh_rg_nc, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - unfold sdh_facts5a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U26, E32,
      unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 5b, at +0x120, and its shadow entry. *)
Lemma sdh_entry5b : forall ly S (W : world segs) regs mem md (sp1 hc : Z),
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 19 = w64 SENDDATA_S ->
  YK11.getr regs 20 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= hc < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (SENDDATA_S + 160) 4 hc ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF; Z_to_bv 64 hc]) ss_sdh5b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C5)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SDH_Bx SDH_SHb (sdh_E regs [w64 SHADOW_OFF; Z_to_bv 64 hc]) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md sp1 hc HSC HAR R2 R19 R20 Hsp Hsp32 Hhc Vhc.
  assert (ES : SENDDATA_S = 6158784) by reflexivity. assert (ESZ : TW.SZ_g_s = 18264) by reflexivity.
  set (E := sdh_E regs [w64 SHADOW_OFF; Z_to_bv 64 hc]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (E19 : ew E 19 = w64 SENDDATA_S) by (unfold E; rewrite (sdh_ew_reg regs _ 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = w64 SHADOW_OFF) by (unfold E; rewrite (sdh_ew_reg regs _ 20 20%bv eq_refl); exact R20).
  assert (U19 : bv_unsigned (ew E 19) = SENDDATA_S)
    by (rewrite E19; unfold w64; apply unsigned_lit_small; unfold SENDDATA_S, TA_g_s; lia).
  assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
    by (rewrite E20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 hc)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF; Z_to_bv 64 hc] 1 ltac:(cbn; lia))).
  split.
  - rewrite restrict_mkst_fx. unfold ss_sdh5b.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold sdh_rg_hc, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (SENDDATA_S + o) G_HARNESS_rw).
        apply sd_inG_gs. change TA_g_s with SENDDATA_S. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val segs E _ SENDDATA_S 160 4 (SOff 33 0) hc);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vhc].
    + apply pairwise_disjoint_of_extents.
      unfold sdh_rg_hc, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
    + unfold sdh_facts5b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U19, U20, E33,
        (unsigned_lit_small hc ltac:(first [lia | split; lia])).
      change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; unfold SENDDATA_S, TA_g_s, SHADOW_OFF;
      first [lia | reflexivity].
  - exact (sdh_gs_shok ly S W mem md E 19 SENDDATA_S 160 164 HSC HAR E19 E20
      ltac:(unfold SENDDATA_S, TA_g_s; lia) ltac:(unfold SENDDATA_S, TA_g_s; lia) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])
      ltac:(unfold SENDDATA_S, TA_g_s; lia)).
Qed.

(* The entry state of run 5c, at +0x144. *)
Lemma sdh_entry5c : forall (W : world segs) regs mem (sp1 F : Z),
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 24 = Z_to_bv 64 (F + 32) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 4096 <= F -> F + 64 <= sp1 -> F mod 64 = 0 ->
  (forall a, F + 36 <= a < F + 40 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF]) ss_sdh5c
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C6)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem sp1 F R2 R24 Hsp Hsp32 HF0 HFs HF64 Hpres.
  set (E := sdh_E regs [w64 SHADOW_OFF]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = F + 32)
    by (unfold E; rewrite (sdh_ew_reg regs _ 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
  assert (HF32 : (F + 32) mod 32 = 0).
  { pose proof (Z.div_mod F 64 ltac:(first [lia | split; lia])) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by lia. apply Z_mod_mult. }
  rewrite restrict_mkst_fx. unfold ss_sdh5c.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold sdh_rg_hp, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold sdh_rg_hp, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - unfold sdh_facts5c, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U24, E32,
      unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 5d, at +0x148, and its shadow entry. *)
Lemma sdh_entry5d : forall ly S (W : world segs) regs mem md (sp1 md0 bl : Z),
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 2 = Z_to_bv 64 sp1 -> YK11.getr regs 9 = Z_to_bv 64 sp1 ->
  YK11.getr regs 19 = w64 SENDDATA_S -> YK11.getr regs 20 = w64 SHADOW_OFF ->
  YK11.getr regs 10 = w64 (SENDDATA_S + 20) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= md0 < 2 ^ 32 -> 0 <= bl < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (SENDDATA_S + 20) 4 md0 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some bl ->
  st_ok_pi segs VAL (sdh_E regs [w64 SHADOW_OFF; Z_to_bv 64 md0; Z_to_bv 64 bl]) ss_sdh5d
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SDH_C7)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SDH_Bx SDH_SHd (sdh_E regs [w64 SHADOW_OFF; Z_to_bv 64 md0; Z_to_bv 64 bl]) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md sp1 md0 bl HSC HAR R2 R9 R19 R20 R10 Hsp Hsp32 Hmd Hbl Vmd Vbl.
  assert (ES : SENDDATA_S = 6158784) by reflexivity.
  set (E := sdh_E regs [w64 SHADOW_OFF; Z_to_bv 64 md0; Z_to_bv 64 bl]).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (unfold E; rewrite (sdh_ew_reg regs _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (E19 : ew E 19 = w64 SENDDATA_S) by (unfold E; rewrite (sdh_ew_reg regs _ 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = w64 SHADOW_OFF) by (unfold E; rewrite (sdh_ew_reg regs _ 20 20%bv eq_refl); exact R20).
  assert (E10 : ew E 10 = w64 (SENDDATA_S + 20))
    by (unfold E; rewrite (sdh_ew_reg regs _ 10 10%bv eq_refl); exact R10).
  assert (U19 : bv_unsigned (ew E 19) = SENDDATA_S)
    by (rewrite E19; unfold w64; apply unsigned_lit_small; unfold SENDDATA_S, TA_g_s; lia).
  assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
    by (rewrite E20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U10 : bv_unsigned (ew E 10) = SENDDATA_S + 20)
    by (rewrite E10; unfold w64; apply unsigned_lit_small; unfold SENDDATA_S, TA_g_s; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 md0)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF; Z_to_bv 64 md0; Z_to_bv 64 bl] 1 ltac:(cbn; lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 bl)
    by (exact (sdh_ew_x regs [w64 SHADOW_OFF; Z_to_bv 64 md0; Z_to_bv 64 bl] 2 ltac:(cbn; lia))).
  split.
  - rewrite restrict_mkst_fx. unfold ss_sdh5d.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold sdh_rg_md, sdh_rg_sl, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ SENDDATA_S 20 4 (SOff 33 0) md0);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vmd].
      * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ sp1 24 8 (SOff 34 0) bl);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ Vbl).
    + apply pairwise_disjoint_of_extents.
      unfold sdh_rg_md, sdh_rg_sl, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U19, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold SENDDATA_S, TA_g_s. repeat split; first [exact I | lia].
    + unfold sdh_facts5d, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U10, U19, U20, E33, E34,
        (unsigned_lit_small md0 ltac:(first [lia | split; lia])), (unsigned_lit_small bl ltac:(first [lia | split; lia])).
      change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; unfold SENDDATA_S, TA_g_s, SHADOW_OFF;
      first [lia | reflexivity].
  - unfold SDH_SHd.
    pose proof (sdh_gs_shok ly S W mem md E 19 SENDDATA_S 20 24 HSC HAR E19 E20
      ltac:(unfold SENDDATA_S, TA_g_s; lia) ltac:(unfold SENDDATA_S, TA_g_s; lia) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])
      ltac:(unfold SENDDATA_S, TA_g_s; lia)) as HA.
    pose proof (sdh_gs_shok ly S W mem md E 10 (SENDDATA_S + 20) 0 4 HSC HAR E10 E20
      ltac:(unfold SENDDATA_S, TA_g_s; lia) ltac:(unfold SENDDATA_S, TA_g_s; lia) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])
      ltac:(unfold SENDDATA_S, TA_g_s; lia)) as HB.
    apply Forall_cons; [exact (Forall_inv HA) | apply Forall_cons; [exact (Forall_inv HB) | apply Forall_nil]].
Qed.

(* The bytes of a region chunk of width 4 or 1, read through the view (m_lost_cgW.v ml_chunk_rd). *)
Lemma sdh_chunk_rd4 : forall (E : env) (Hh : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict Hh mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview segs Hh mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E Hh mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs Hh mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict Hh mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply (sdh_bow v j 4); lia.
Qed.

Lemma sdh_chunk_rd1 : forall (E : env) (Hh : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict Hh mm) base (YP09.mkChunk off (CVal 1 e)) -> sv_denot E e = Z_to_bv 64 v ->
  aview segs Hh mm (base + off) = Some (YO0f.le_byte v 1 0).
Proof.
intros E Hh mm base off e v HC He. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC 0 ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
rewrite Z.add_0_r in Hb2.
change (aview segs Hh mm (base + off))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict Hh mm) (base + off))).
rewrite Hb2. cbn [option_map]. f_equal. exact (sdh_bow v 0 1 ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac sdh_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sdh_reg: no match for" T; fail
  end.

(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac sdh_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_region_nth Ex _ (restrict Hh msx) i _ HS eq_refl) as HR
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.

Ltac sdh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac sdh_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac sdh_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* ------------------------------------------------------------------ *)
(* 4. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Lemma sd_head : @sd_head_stmt fx rc B MT.
Proof.
intros FB.
unfold transport_send_data_cg_holds_stmt.
intros HPCS HCELLS HSDC HGU HGE HRU HRE LAWS MTL MTF SMP ASF FFL ASM0 AI0 FB0 IOS0.
unfold transport_send_data_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body TF Bw Bwf
  HJ0 Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 Hsp16 Hlo Hhi Hnc Hnow Hbodyp Hgarr Hsrc Hoffw HbodyG HBODYG
  Htw Hgf Hmodel Hrom Hinv1 Hinv4 Hcnt0 Hcnt2 Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJ0 as HJENT.
pose proof HJ0 as (HSTK & HLE0 & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof HJi as (_ & HLE0i & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct AC1 as (AC1a & AC1b).
assert (EST : ESTACK = 4096) by reflexivity.
assert (FFR : SENDDATA_FRAME = 160) by reflexivity.
(* the call's stack budget is at least its own frame and the realignment, and at least a callee's ESTACK *)
assert (HSTKlo : 176 + ESTACK <= SENDDATA_STK).
{ unfold SENDDATA_STK, SENDDATA_FRAME, SENDDATA_ALIGN.
  pose proof (Z.le_max_l ESTACK (Z.max FRAME_FB_STK IOSEND_STK)) as Hm. lia. }
assert (HFBS : FRAME_FB_STK <= SENDDATA_STK - 176).
{ unfold SENDDATA_STK, SENDDATA_FRAME, SENDDATA_ALIGN.
  pose proof (Z.le_max_r ESTACK (Z.max FRAME_FB_STK IOSEND_STK)) as Hm.
  pose proof (Z.le_max_l FRAME_FB_STK IOSEND_STK) as Hm2. lia. }
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hwin : forall a, spZ regs - SENDDATA_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
set (E0 := sdh_E regs [w64 SHADOW_OFF]).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply sdh_env_img).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E0 n = YK11.getr regs q)
  by (intros n q Hn; unfold E0; apply sdh_ew_reg; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0; exact (sdh_ew_x regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
pose proof (sdh_entry1 lyc Sc W regs memc mdc HCELLS HAR
  ltac:(intros a Ha; apply Hpres0; lia) Hspr Hsp16) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) E0 (mrestrict (w_H W) memc)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  (G_HARNESS_gx_ok B HGU) 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  (G_HARNESS_gx_ok B HGU) 0 []) as RUNTO.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_send_data)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x044: the frame, the 13 saves, s0, the realign; cut at +0x048. *)
paj_run_to_tok RUNTO HS HJ0 SHOK YC4b.Bspan SDH_C1.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite Usp in Ha; left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
rename ms into ms1.
(* sp after `addi sp, sp, -160` and `andi sp, sp, -32`. *)
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (can_sp1_facts (spZ regs + -160) ltac:(first [lia | split; lia])
  ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
assert (E2' : ew E0 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
(* the thirteen words the prologue saved, read back from the stack region the run wrote *)
sdh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (q : bv 5), In (o, q) sdh_saved -> -104 <= o <= -8).
{ intros o q Hin. unfold sdh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (q : bv 5), In (o, q) sdh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms1)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs q))).
{ intros o q Hin. unfold sdh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms1) (spZ regs + o) (bv_unsigned (YK11.getr regs q))
    ltac:(sdh_u64 (YK11.getr regs q))).
  apply (can_field_of_region E0 _ 2 (spZ regs) _ (-160) 0 (-160) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned q)) 0) (bv_unsigned (YK11.getr regs q)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (EE (Z.to_nat (bv_unsigned q)) q ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; sdh_u64 (YK11.getr regs q)
  | cbn; lia ]. }
(* the registers at +0x048 *)
sdh_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
  ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 E0 2 (spZ regs) (-160) E2' ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]))).
sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 E0 2 (spZ regs) (-160) E2' ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]))).
sdh_reg HS (Z_to_bv 5 10) (w64 SENDDATA_S) R10
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
sdh_reg HS (Z_to_bv 5 11) (w64 bodyp) R11
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
sdh_reg HS (Z_to_bv 5 13) (w64 (bv_swrap 32 ncmds)) R13
  ltac:(cbn [sv_denot]; rewrite (EE 13%nat 13%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H13).
sdh_reg HS (Z_to_bv 5 14) (w64 now) R14
  ltac:(cbn [sv_denot]; rewrite (EE 14%nat 14%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H14).
sdh_reg HS (Z_to_bv 5 12) (YK11.getr regs 12) RA12
  ltac:(cbn [sv_denot]; rewrite (EE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* what run 1 wrote: the 160 bytes of its own machine frame *)
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 160 <= x < spZ regs) HFr);
    [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* take the state up again at +0x048, with the realigned sp as its own atom *)
pmkst HS.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HAR1.
pose proof (sdh_entry2 lyc Sc W (ms_regs ms1) (ms_mem ms1) md1 sp1 HCELLS HAR1 R2 R9 ltac:(first [lia | split; lia]) Hsp1al
  ltac:(intros a Ha; apply GA1; apply Hwin; lia)) as HS2.
clear HF HFr HG.
clear HS HEI SHOK. rename HS2 into HS.
set (E1 := sdh_E (ms_regs ms1) [w64 SHADOW_OFF]) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; apply sdh_env_img).
assert (SHOK1 : sh_ok segs (SOff 32 0) (@nil shent) E1 (mrestrict (w_H W) (ms_mem ms1))) by constructor.
assert (U9' : bv_unsigned (ew E1 9) = sp1)
  by (unfold E1; rewrite (sdh_ew_reg (ms_regs ms1) _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (EE1 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E1 n = YK11.getr (ms_regs ms1) q)
  by (intros n q Hn; unfold E1; apply sdh_ew_reg; exact Hn).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx (ms_regs ms1) (Z_to_bv 64 (BASE + SDH_C1)) (ms_mem ms1)
    (YK11.seg_rom segs)) md1) Q) end.
(* run 2, +0x048 .. +0x07c: the two slots, s7 = ncmds, s6 = bodyp, the two runtime cells, s4 = the shadow base,
   s3 = s, a0 = 64, and the call of __asan_stack_malloc_0. *)
paj_run_tok RUN HS HJ0 SHOK1 YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite U9' in Ha; left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil. }
set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
rename ms into ms2.
(* what run 2 wrote: the two slots at sp1 + 16 and sp1 + 24 *)
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 32) ->
  aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) (ms_mem ms1) a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 16 <= x < sp1 + 32) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(rewrite ?U9' in Hx; lia). }
assert (GA2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
sdh_region HS 0%nat HRsl.
assert (HSLnow : rdword (aview segs (w_H W) (ms_mem ms2)) (sp1 + 16) = Some now).
{ apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms2) (sp1 + 16) now ltac:(first [lia | split; lia])).
  apply (can_field_of_region E1 _ 9 sp1 _ 16 32 16 32 16 8%N (SOff 14 0) now HRsl U9');
  [ sdh_in
  | cbn [sv_denot]; rewrite (EE1 14%nat (Z_to_bv 5 14) ltac:(vm_compute; reflexivity)), R14;
    unfold w64; rewrite (unsigned_lit_small now ltac:(first [lia | split; lia])), Z.add_0_r; reflexivity
  | cbn; lia
  | cbn; lia ]. }
pose proof (bv_unsigned_in_range 64 (YK11.getr regs (12%bv : bv 5))) as Hb12.
unfold bv_modulus in Hb12. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb12.
assert (HSLlen : rdword (aview segs (w_H W) (ms_mem ms2)) (sp1 + 24) =
  Some (bv_unsigned (YK11.getr regs (12%bv : bv 5)))).
{ apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms2) (sp1 + 24)
    (bv_unsigned (YK11.getr regs (12%bv : bv 5))) Hb12).
  apply (can_field_of_region E1 _ 9 sp1 _ 16 32 16 32 24 8%N (SOff 12 0)
    (bv_unsigned (YK11.getr regs (12%bv : bv 5))) HRsl U9');
  [ sdh_in
  | cbn [sv_denot]; rewrite (EE1 12%nat (Z_to_bv 5 12) ltac:(vm_compute; reflexivity)), RA12,
    Z.add_0_r; reflexivity
  | cbn; lia
  | cbn; lia ]. }
(* the registers at the call of __asan_stack_malloc_0 *)
sdh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + SDH_C2)) Q1 ltac:(apply codeptr_val; exact HEI1).
sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), R2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), R3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), R4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (E1_32 : ew E1 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E1; exact (sdh_ew_x (ms_regs ms1) [w64 SHADOW_OFF] 0 ltac:(cbn; lia))).
sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) Q8
  ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), R8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) Q9
  ltac:(cbn [sv_denot]; rewrite (EE1 9%nat 9%bv eq_refl), R9, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) Q19
  ltac:(cbn [sv_denot]; rewrite (EE1 10%nat (Z_to_bv 5 10) ltac:(vm_compute; reflexivity)), R10, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) Q20
  ltac:(cbn [sv_denot]; rewrite E1_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (22%bv : bv 5) (w64 bodyp) Q22
  ltac:(cbn [sv_denot]; rewrite (EE1 11%nat (Z_to_bv 5 11) ltac:(vm_compute; reflexivity)), R11, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (23%bv : bv 5) (w64 (bv_swrap 32 ncmds)) Q23
  ltac:(cbn [sv_denot]; rewrite (EE1 13%nat (Z_to_bv 5 13) ltac:(vm_compute; reflexivity)), R13, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
assert (Hsp2 : spZ (ms_regs ms2) = sp1) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; lia).
(* the class-0 stack malloc, at the pc the statement's premise names *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_0)) mm rom) mdx) Q)
end.
rewrite <- HPCS.
eapply SRr_bind.
{ eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP SENDDATA_CID ASM
    ltac:(unfold SENDDATA_CID; lia) TG.G_HARNESS W (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc md2 k (sp1 - sp0) (Z_to_bv 64 (BASE + SDH_C2)) HJ0).
  - rewrite Hsp2. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport));
    [unfold SDH_C2, AF_send_data; lia | unfold SDH_C2, AF_send_data; reflexivity].
  - exact Hcnt0. }
cbv beta.
intros W3 c3 _ (-> & S2 & regs3 & mem3 & md3 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
(* the class-0 frame the call handed back *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (SENDDATA_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ SENDDATA_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ SENDDATA_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B lyc S2 W mem3 md3 SENDDATA_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes SENDDATA_CID / 8) with 8 in HFsh.
change (fs_frame_bytes SENDDATA_CID) with 64 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc SENDDATA_CID pos) in *.
destruct HK1 as (K1a & K1b & K1c & K1d & K1e & K1f).
assert (HFsp : F + 64 <= sp1) by lia.
assert (GA3 : forall a, apresent (w_H W) (ms_mem ms2) a -> alloc_ceiling <= a < 2 ^ 64 ->
  ~ (sp1 - ESTACK <= a < sp1) -> apresent (w_H W) mem3 a)
  by (intros a Ha Hr Hn; apply (K1e a Hr); [intros Hc; apply Hn; lia | exact Ha]).
(* the registers the malloc kept *)
assert (Q2' : YK11.getr regs3 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms2) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact Q2]).
assert (Q3' : YK11.getr regs3 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms2) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
assert (Q4' : YK11.getr regs3 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms2) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
assert (Q8' : YK11.getr regs3 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms2) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
assert (Q9' : YK11.getr regs3 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms2) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact Q9]).
assert (Q19' : YK11.getr regs3 19 = w64 SENDDATA_S)
  by (transitivity (YK11.getr (ms_regs ms2) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact Q19]).
assert (Q20' : YK11.getr regs3 20 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms2) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact Q20]).
assert (Q22' : YK11.getr regs3 22 = w64 bodyp)
  by (transitivity (YK11.getr (ms_regs ms2) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact Q22]).
assert (Q23' : YK11.getr regs3 23 = w64 (bv_swrap 32 ncmds))
  by (transitivity (YK11.getr (ms_regs ms2) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact Q23]).
(* run 3, +0x080 .. +0x0e4: the frame in s2 = s10, the slot s1 + 48, s8 = hp, the frame's 24-byte header. *)
pose proof (sdh_entry3 W regs3 mem3 sp1 F Q2' Q9' Ha0 ltac:(first [lia | split; lia]) Hsp1al ltac:(first [lia | split; lia]) HFsp HF64
  ltac:(intros a Ha; apply GA3; [apply GA2; apply GA1; apply Hwin; lia | lia | lia])
  ltac:(intros a Ha; apply Hfpres; lia)) as HS3.
clear HS HEI1 SHOK1 HRsl. rename HS3 into HS.
set (E2 := sdh_E regs3 [w64 SHADOW_OFF]) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply sdh_env_img).
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) E2 (mrestrict (w_H W) mem3)) by constructor.
assert (EE2 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E2 n = YK11.getr regs3 q)
  by (intros n q Hn; unfold E2; apply sdh_ew_reg; exact Hn).
assert (U9'' : bv_unsigned (ew E2 9) = sp1)
  by (rewrite (EE2 9%nat 9%bv eq_refl), Q9'; apply unsigned_lit_small; lia).
assert (E2_10 : ew E2 10 = Z_to_bv 64 F)
  by (rewrite (EE2 10%nat 10%bv eq_refl), Ha0; reflexivity).
assert (U10'' : bv_unsigned (ew E2 10) = F)
  by (rewrite E2_10; apply unsigned_lit_small; lia).
assert (E2_20 : ew E2 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE2 20%nat 20%bv eq_refl), Q20'; reflexivity).
paj_run_to_tok RUNTO HS HJ2 SHOK2 SDH_B0 SDH_C3.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9'' in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDDATA_CID pos).
  { left. reflexivity. }
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10'' in Ha.
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDDATA_CID) with 64. fold F. lia. }
  apply awr_ok_x_nil. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
rename ms into ms4.
(* what run 3 wrote: the slot s1 + 48 and the frame's 24-byte header *)
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56) -> ~ (F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) mem3 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (sp1 + 48 <= x < sp1 + 56) \/ (F <= x < F + 24)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  sdh_win Hin Hx ltac:(rewrite ?U9'', ?U10'' in Hx; first [left; lia | right; lia]). }
assert (GA4 : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the registers at +0x0e8 *)
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Q2', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Q3', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Q4', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) T8
  ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Q8', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) T9
  ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Q9', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (18%bv : bv 5) (Z_to_bv 64 F) T18
  ltac:(cbn [sv_denot]; rewrite E2_10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) T19
  ltac:(cbn [sv_denot]; rewrite (EE2 19%nat 19%bv eq_refl), Q19', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) T20
  ltac:(cbn [sv_denot]; rewrite (EE2 20%nat 20%bv eq_refl), Q20', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (22%bv : bv 5) (w64 bodyp) T22
  ltac:(cbn [sv_denot]; rewrite (EE2 22%nat 22%bv eq_refl), Q22', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (23%bv : bv 5) (w64 (bv_swrap 32 ncmds)) T23
  ltac:(cbn [sv_denot]; rewrite (EE2 23%nat 23%bv eq_refl), Q23', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (24%bv : bv 5) (Z_to_bv 64 (F + 32)) T24
  ltac:(cbn [sv_denot]; rewrite E2_10, (unsigned_lit_small F ltac:(first [lia | split; lia])); reflexivity).
sdh_reg HS (26%bv : bv 5) (Z_to_bv 64 F) T26
  ltac:(cbn [sv_denot]; rewrite E2_10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (27%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T27
  ltac:(exact (can_denot_shadow E2 10 20 F SHADOW_OFF E2_10 E2_20 ltac:(first [lia | split; lia]) ltac:(unfold SHADOW_OFF; lia)
        ltac:(unfold SHADOW_OFF; lia))).
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
(* run 4, +0x0e8 .. +0x114: the frame's 8 shadow bytes and the memset's arguments. *)
pmkst HS.
pose proof (sdh_entry4 W (ms_regs ms4) (ms_mem ms4) sp1 (SHADOW_OFF + F / 8) T2 T27 ltac:(first [lia | split; lia]) Hsp1al
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply GA4;
        replace a with (shadow_addr F + (a - shadow_addr F)) by (rewrite ESH; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(rewrite ESH; lia))))) as HS4.
clear HS HEI2 SHOK2. rename HS4 into HS.
set (E3 := sdh_E (ms_regs ms4) [w64 SHADOW_OFF]) in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply sdh_env_img).
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) E3 (mrestrict (w_H W) (ms_mem ms4))) by constructor.
assert (EE3 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E3 n = YK11.getr (ms_regs ms4) q)
  by (intros n q Hn; unfold E3; apply sdh_ew_reg; exact Hn).
assert (U27' : bv_unsigned (ew E3 27) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 27%nat 27%bv eq_refl), T27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx (ms_regs ms4) (Z_to_bv 64 (BASE + SDH_C3)) (ms_mem ms4)
    (YK11.seg_rom segs)) md4) Q) end.
paj_run_tok RUN HS HJ2 SHOK3 SDH_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDDATA_CID pos).
  { left. reflexivity. }
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U27' in Ha.
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDDATA_CID / 8) with 8. fold F.
    rewrite ESH. lia. }
  apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
rename ms into ms5.
(* what run 4 wrote: the frame's 8 shadow bytes *)
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) ->
  aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 8) HFr);
    [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(rewrite ?U27' in Hx; lia). }
assert (GA5 : forall a, apresent (w_H W) (ms_mem ms4) a -> apresent (w_H W) (ms_mem ms5) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the frame's 8 shadow bytes are present, and bytes 4 and 5 are 0 (h is usable) *)
assert (HSHp : forall i, 0 <= i < 8 -> apresent (w_H W) (ms_mem ms5) (SHADOW_OFF + F / 8 + i)).
{ intros i Hi. apply GA5. apply GA4.
  replace (SHADOW_OFF + F / 8 + i) with (shadow_addr F + i) by (rewrite ESH; lia).
  exact (proj1 (HFsh i ltac:(first [lia | split; lia]))). }
sdh_region HS 0%nat HRsh.
assert (HSH4 : aview segs (w_H W) (ms_mem ms5) (SHADOW_OFF + F / 8 + 4) = Some 0).
{ apply (can_aview_of_val1 segs (w_H W) (ms_mem ms5) _ 0).
  apply (can_field_of_region E3 _ 27 (SHADOW_OFF + F / 8) _ 0 8 0 8 4 1%N (SLit 0) 0 HRsh U27');
  [ sdh_in | reflexivity | cbn; lia | cbn; lia ]. }
assert (HSH5 : aview segs (w_H W) (ms_mem ms5) (SHADOW_OFF + F / 8 + 5) = Some 0).
{ apply (can_aview_of_val1 segs (w_H W) (ms_mem ms5) _ 0).
  apply (can_field_of_region E3 _ 27 (SHADOW_OFF + F / 8) _ 0 8 0 8 5 1%N (SLit 0) 0 HRsh U27');
  [ sdh_in | reflexivity | cbn; lia | cbn; lia ]. }
(* the arithmetic of the frame's shadow: F is 64-aligned, so its 8 shadow bytes are one aligned group *)
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(first [lia | split; lia])) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
assert (EF8 : F / 8 = 8 * (F / 64)).
{ pose proof (Z.div_mod F 64 ltac:(first [lia | split; lia])) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
(* hp's 15 bytes lie in application memory, low or high (the frame does: in_app) *)
assert (HFamr : amem_range (F + 32) 15).
{ unfold amem_range. pose proof HFapp as HFapp'. unfold in_app, ASAN_CEIL in HFapp'.
  destruct HFapp' as (_ & [HL | (HH1 & HH2)]); [left | right];
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
assert (HRAd : range_addressable (aview segs (w_H W) (ms_mem ms5)) SHADOW_OFF (F + 32) 15).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  rewrite (sdh_div8 F x HF8), Z.add_assoc.
  assert (H4 : 4 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (H5 : (x - F) / 8 < 6) by (apply Z.div_lt_upper_bound; lia).
  assert (Hc : (x - F) / 8 = 4 \/ (x - F) / 8 = 5) by lia.
  destruct Hc as [Hc|Hc]; rewrite Hc; [exact HSH4 | exact HSH5]. }
assert (HHULL : shadow_hull_vis (aview segs (w_H W) (ms_mem ms5)) (F + 32) 15).
{ intros s Hs.
  assert (HHlo : shadow_addr (F + 32) / 8 * 8 = SHADOW_OFF + F / 8).
  { unfold shadow_addr. rewrite (sdh_div8 F (F + 32) HF8). replace (F + 32 - F) with 32 by lia.
    change (32 / 8) with 4. rewrite EF8.
    replace (SHADOW_OFF + (8 * (F / 64) + 4)) with ((268431360 + F / 64) * 8 + 4) by (unfold SHADOW_OFF; lia).
    rewrite Z.div_add_l by lia. change (4 / 8) with 0. rewrite Z.add_0_r. unfold SHADOW_OFF. lia. }
  assert (HHhi : shadow_addr (F + 32 + 15 - 1) / 8 * 8 + 8 = SHADOW_OFF + F / 8 + 8).
  { unfold shadow_addr. rewrite (sdh_div8 F (F + 32 + 15 - 1) HF8).
    replace (F + 32 + 15 - 1 - F) with 46 by lia. change (46 / 8) with 5. rewrite EF8.
    replace (SHADOW_OFF + (8 * (F / 64) + 5)) with ((268431360 + F / 64) * 8 + 5) by (unfold SHADOW_OFF; lia).
    rewrite Z.div_add_l by lia. change (5 / 8) with 0. rewrite Z.add_0_r. unfold SHADOW_OFF. lia. }
  rewrite HHlo, HHhi in Hs.
  apply can_aview_vis. replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
  apply HSHp. lia. }
(* the registers at the call of __asan_memset *)
sdh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + SDH_C4)) P1 ltac:(apply codeptr_val; exact HEI3).
sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) P2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat 2%bv eq_refl), T2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat 3%bv eq_refl), T3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat 4%bv eq_refl), T4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) P8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat 8%bv eq_refl), T8, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) P9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat 9%bv eq_refl), T9, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (18%bv : bv 5) (Z_to_bv 64 F) P18
  ltac:(cbn [sv_denot]; rewrite (EE3 18%nat 18%bv eq_refl), T18, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) P19
  ltac:(cbn [sv_denot]; rewrite (EE3 19%nat 19%bv eq_refl), T19, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) P20
  ltac:(cbn [sv_denot]; rewrite (EE3 20%nat 20%bv eq_refl), T20, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (22%bv : bv 5) (w64 bodyp) P22
  ltac:(cbn [sv_denot]; rewrite (EE3 22%nat 22%bv eq_refl), T22, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (23%bv : bv 5) (w64 (bv_swrap 32 ncmds)) P23
  ltac:(cbn [sv_denot]; rewrite (EE3 23%nat 23%bv eq_refl), T23, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (24%bv : bv 5) (Z_to_bv 64 (F + 32)) P24
  ltac:(cbn [sv_denot]; rewrite (EE3 24%nat 24%bv eq_refl), T24, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (26%bv : bv 5) (Z_to_bv 64 F) P26
  ltac:(cbn [sv_denot]; rewrite (EE3 26%nat 26%bv eq_refl), T26, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (27%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) P27
  ltac:(cbn [sv_denot]; rewrite (EE3 27%nat 27%bv eq_refl), T27, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sdh_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 32)) P10
  ltac:(cbn [sv_denot]; rewrite (EE3 24%nat 24%bv eq_refl), T24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) P11 ltac:(reflexivity).
sdh_reg HS (Z_to_bv 5 12) (Z_to_bv 64 15) P12 ltac:(reflexivity).
assert (Hsp5 : spZ (ms_regs ms5) = sp1) by (unfold spZ; rewrite P2; apply unsigned_lit_small; lia).
(* +0x118: __asan_memset (hp, 0, 15), through the G call kit *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (AI0 fx) TG.G_HARNESS W (ms_regs ms5) (ms_mem ms5) STK sp0 FP ly S W0
    mem0 md0 ((SENDDATA_CID, pos) :: own) lyc S2 md5 k (F + 32) 0 15 (sp1 - sp0)
    (Z_to_bv 64 (BASE + SDH_C4)) (G_HARNESS_gx_ok B HGU) G_HARNESS_rw HJ2 P10 P11 P12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp5. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact P3.
  - exact P4.
  - exact P1.
  - apply (ret_ok_codeptr_v (PI := PI_transport));
    [unfold SDH_C4, AF_send_data; lia | unfold SDH_C4, AF_send_data; reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. left. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists SENDDATA_CID, pos.
      split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes SENDDATA_CID) with 64. fold F. lia.
    + rewrite Hsp5. lia.
  - exact HFamr.
  - exact HRAd.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regs6 & mem6 & md6 & -> & HJ3 & HP3 & HA0M & HsetM & HeffM & HgrM).
(* no byte of G was written so far: the walk wrote its own machine frame, its side-stack frame, that frame's
   shadow bytes and the memset's destination, none of them a byte of G *)
assert (GLOW : forall a, W_journalG.inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (G_HARNESS_gx_ok B HGU a Ha)))).
assert (GNF : forall a, W_journalG.inG TG.G_HARNESS a -> ~ (F <= a < F + 64)).
{ intros a Ha Hc. apply (frm_img segs B LAWS lyc S2 W mem3 md3 SENDDATA_CID pos a HAR2 Hin2).
  - change (fs_frame_bytes SENDDATA_CID) with 64. fold F. lia.
  - exact (trans_g_img a Ha). }
assert (KG6 : forall x, W_journalG.inG TG.G_HARNESS x ->
  aview segs (w_H W) mem6 x = aview segs (w_H W) memc x).
{ intros x Hx. pose proof (GLOW x Hx) as Hl. pose proof (GNF x Hx) as Hnf.
  unfold kLowMemEnd in Hl.
  rewrite (HeffM x ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
  rewrite (KR4 x ltac:(first [lia | split; lia]) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (KR3 x ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
  rewrite (K1c x (trans_g_img x Hx) (HGU x Hx) (HGE x Hx)).
  rewrite (KR2 x ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
  exact (KR1 x ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])). }
assert (HTW6 : tw_at TMAP_A (aview segs (w_H W) mem6) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|].
  intros b n i Hbn Hi. apply KG6. unfold W_journalG.inG. apply Exists_exists. exists (b, n).
  split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]. }
(* the registers the memset kept *)
assert (M2 : YK11.getr regs6 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms5) 2); [exact (HP3 2 ltac:(unfold acallee_saved; lia)) | exact P2]).
assert (M3 : YK11.getr regs6 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms5) 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact P3]).
assert (M4 : YK11.getr regs6 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms5) 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact P4]).
assert (M8 : YK11.getr regs6 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms5) 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact P8]).
assert (M9 : YK11.getr regs6 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms5) 9); [exact (HP3 9 ltac:(unfold acallee_saved; lia)) | exact P9]).
assert (M18 : YK11.getr regs6 18 = Z_to_bv 64 F)
  by (transitivity (YK11.getr (ms_regs ms5) 18); [exact (HP3 18 ltac:(unfold acallee_saved; lia)) | exact P18]).
assert (M19 : YK11.getr regs6 19 = w64 SENDDATA_S)
  by (transitivity (YK11.getr (ms_regs ms5) 19); [exact (HP3 19 ltac:(unfold acallee_saved; lia)) | exact P19]).
assert (M20 : YK11.getr regs6 20 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms5) 20); [exact (HP3 20 ltac:(unfold acallee_saved; lia)) | exact P20]).
assert (M22 : YK11.getr regs6 22 = w64 bodyp)
  by (transitivity (YK11.getr (ms_regs ms5) 22); [exact (HP3 22 ltac:(unfold acallee_saved; lia)) | exact P22]).
assert (M23 : YK11.getr regs6 23 = w64 (bv_swrap 32 ncmds))
  by (transitivity (YK11.getr (ms_regs ms5) 23); [exact (HP3 23 ltac:(unfold acallee_saved; lia)) | exact P23]).
assert (M24 : YK11.getr regs6 24 = Z_to_bv 64 (F + 32))
  by (transitivity (YK11.getr (ms_regs ms5) 24); [exact (HP3 24 ltac:(unfold acallee_saved; lia)) | exact P24]).
assert (M26 : YK11.getr regs6 26 = Z_to_bv 64 F)
  by (transitivity (YK11.getr (ms_regs ms5) 26); [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact P26]).
assert (M27 : YK11.getr regs6 27 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (transitivity (YK11.getr (ms_regs ms5) 27); [exact (HP3 27 ltac:(unfold acallee_saved; lia)) | exact P27]).
(* the frame's bytes are present at the memset's memory *)
assert (HFp6 : forall a, F <= a < F + 64 -> apresent (w_H W) mem6 a)
  by (intros a Ha; apply HgrM; apply GA5; apply GA4; exact (proj1 (HFb a Ha))).
(* run 5a, +0x11c: the store of the low byte of ncmds at hp + 15. *)
pose proof (sdh_entry5a W regs6 mem6 sp1 F M2 M26 ltac:(first [lia | split; lia]) Hsp1al ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) HF64
  ltac:(intros a Ha; apply HFp6; lia)) as HS5a.
clear HS HEI3 SHOK3. rename HS5a into HS.
set (E4 := sdh_E regs6 [w64 SHADOW_OFF]) in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (unfold E4; apply sdh_env_img).
assert (SHOK4 : sh_ok segs (SOff 32 0) (@nil shent) E4 (mrestrict (w_H W) mem6)) by constructor.
assert (EE4 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E4 n = YK11.getr regs6 q)
  by (intros n q Hn; unfold E4; apply sdh_ew_reg; exact Hn).
assert (U26' : bv_unsigned (ew E4 26) = F)
  by (rewrite (EE4 26%nat 26%bv eq_refl), M26; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs6 (Z_to_bv 64 (BASE + SDH_C4)) mem6
    (YK11.seg_rom segs)) md6) Q) end.
paj_run_to_tok RUNTO HS HJ3 SHOK4 SDH_B0 SDH_C5.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDDATA_CID pos).
  { left. reflexivity. }
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U26' in Ha.
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDDATA_CID) with 64. fold F. lia. }
  apply awr_ok_x_nil. }
set (md7 := with_vm_backing (m_vm_lazy md6) mat md6) in *. clearbody md7. clear mat.
rename ms into ms7.
(* what run 5a wrote: the frame byte hp + 15 *)
assert (KR5a : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 47 <= a < F + 48) ->
  aview segs (w_H W) (ms_mem ms7) a = aview segs (w_H W) mem6 a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => F + 47 <= x < F + 48) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(rewrite ?U26' in Hx; lia). }
assert (GA7 : forall a, apresent (w_H W) mem6 a -> apresent (w_H W) (ms_mem ms7) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (GKEEP7 : forall x, W_journalG.inG TG.G_HARNESS x ->
  aview segs (w_H W) (ms_mem ms7) x = aview segs (w_H W) mem6 x).
{ intros x Hx. pose proof (GLOW x Hx) as Hl. pose proof (GNF x Hx) as Hnf. unfold kLowMemEnd in Hl.
  apply KR5a; lia. }
assert (HTW7 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms7)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) mem6)); [exact HTW6|].
  intros b n i Hbn Hi. apply GKEEP7. unfold W_journalG.inG. apply Exists_exists. exists (b, n).
  split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]. }
(* the world's two fields the code reads, at their numeral offsets *)
assert (EOhc : TW.OFF_g_s + 160 = 1808) by reflexivity.
assert (EOmd : TW.OFF_g_s + 20 = 1668) by reflexivity.
assert (EAhc : TW.A_S_host_counter = 1808) by reflexivity.
assert (EAmd : TW.A_S_cfg_sum_mode = 1668) by reflexivity.
pose proof (TWL.u_at_range Bw 1808 4) as Rhc. change (8 * Z.of_nat 4) with 32 in Rhc.
pose proof (TWL.u_at_range Bw 1668 4) as Rmd. change (8 * Z.of_nat 4) with 32 in Rmd.
assert (Vhc : YI04.val_mem segs (mrestrict (w_H W) (ms_mem ms7)) (SENDDATA_S + 160) 4 (TW.u_at Bw 1808 4)).
{ pose proof (tw_read_val segs (mrestrict (w_H W) (ms_mem ms7)) TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 160 4
    TMAP_A_ok HTW7 TMAP_A_g_s ltac:(first [lia | split; lia]) ltac:(unfold TW.SZ_g_s; lia)) as V.
  rewrite EOhc in V. exact V. }
(* the registers at +0x120 *)
assert (N2 : YK11.getr (ms_regs ms7) 2 = Z_to_bv 64 sp1).
{ sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 2%nat 2%bv eq_refl), M2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N19 : YK11.getr (ms_regs ms7) 19 = w64 SENDDATA_S).
{ sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 19%nat 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N20 : YK11.getr (ms_regs ms7) 20 = w64 SHADOW_OFF).
{ sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 20%nat 20%bv eq_refl), M20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N8 : YK11.getr (ms_regs ms7) 8 = w64 (spZ regs)).
{ sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 8%nat 8%bv eq_refl), M8, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N9 : YK11.getr (ms_regs ms7) 9 = Z_to_bv 64 sp1).
{ sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 9%nat 9%bv eq_refl), M9, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N18 : YK11.getr (ms_regs ms7) 18 = Z_to_bv 64 F).
{ sdh_reg HS (18%bv : bv 5) (Z_to_bv 64 F) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 18%nat 18%bv eq_refl), M18, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N22 : YK11.getr (ms_regs ms7) 22 = w64 bodyp).
{ sdh_reg HS (22%bv : bv 5) (w64 bodyp) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 22%nat 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N23 : YK11.getr (ms_regs ms7) 23 = w64 (bv_swrap 32 ncmds)).
{ sdh_reg HS (23%bv : bv 5) (w64 (bv_swrap 32 ncmds)) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 23%nat 23%bv eq_refl), M23, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N24 : YK11.getr (ms_regs ms7) 24 = Z_to_bv 64 (F + 32)).
{ sdh_reg HS (24%bv : bv 5) (Z_to_bv 64 (F + 32)) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 24%nat 24%bv eq_refl), M24, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N26 : YK11.getr (ms_regs ms7) 26 = Z_to_bv 64 F).
{ sdh_reg HS (26%bv : bv 5) (Z_to_bv 64 F) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 26%nat 26%bv eq_refl), M26, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N27 : YK11.getr (ms_regs ms7) 27 = Z_to_bv 64 (SHADOW_OFF + F / 8)).
{ sdh_reg HS (27%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 27%nat 27%bv eq_refl), M27, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N3 : YK11.getr (ms_regs ms7) 3 = w64 (as_gp B)).
{ sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 3%nat 3%bv eq_refl), M3, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
assert (N4 : YK11.getr (ms_regs ms7) 4 = w64 (as_tp B)).
{ sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) Hq
    ltac:(cbn [sv_denot]; rewrite (EE4 4%nat 4%bv eq_refl), M4, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  exact Hq. }
sdh_region HS 0%nat HRnc.
unfold region_ok in HRnc.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRnc.
rewrite U26' in HRnc.
assert (VNC : aview segs (w_H W) (ms_mem ms7) (F + 47) =
  Some (YO0f.le_byte (bv_swrap 32 ncmds) 1 0)).
{ exact (sdh_chunk_rd1 E4 (w_H W) (ms_mem ms7) F 47 (SOff 23 0) (bv_swrap 32 ncmds)
    (Forall_inv (proj2 (proj2 (proj2 HRnc))))
    ltac:(cbn [sv_denot]; rewrite (EE4 23%nat 23%bv eq_refl), M23, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity)). }
(* run 5b, +0x120 .. +0x140: the checked load of S_host_counter and the store of the new counter at s + 160. *)
pmkst HS.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR7.
destruct (sdh_entry5b lyc S2 W (ms_regs ms7) (ms_mem ms7) md7 sp1 (TW.u_at Bw 1808 4) HSDC HAR7
  N2 N19 N20 ltac:(first [lia | split; lia]) Hsp1al Rhc Vhc) as [HS5b SHOK5b].
clear HS HEI4 SHOK4. rename HS5b into HS.
set (E5 := sdh_E (ms_regs ms7) [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw 1808 4)]) in HS, SHOK5b.
assert (HEI5 : img_env VAL A_LIM E5) by (unfold E5; apply sdh_env_img).
assert (EE5 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E5 n = YK11.getr (ms_regs ms7) q)
  by (intros n q Hn; unfold E5; apply sdh_ew_reg; exact Hn).
assert (U19' : bv_unsigned (ew E5 19) = SENDDATA_S)
  by (rewrite (EE5 19%nat 19%bv eq_refl), N19; unfold w64; apply unsigned_lit_small;
      unfold SENDDATA_S, TA_g_s; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx (ms_regs ms7) (Z_to_bv 64 (BASE + SDH_C5)) (ms_mem ms7)
    (YK11.seg_rom segs)) md7) Q) end.
paj_run_to_tok RUNTO HS HJ3 SHOK5b YC4b.Bspan SDH_C6.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19' in Ha.
    apply sd_inG_gs. change TA_g_s with SENDDATA_S. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia. }
  apply awr_ok_x_nil. }
set (md8 := with_vm_backing (m_vm_lazy md7) mat md7) in *. clearbody md8. clear mat.
rename ms into ms8.
(* what run 5b wrote: the 4 bytes of S_host_counter *)
assert (KR5b : forall a, 0 <= a < 2 ^ 64 -> ~ (SENDDATA_S + 160 <= a < SENDDATA_S + 164) ->
  aview segs (w_H W) (ms_mem ms8) a = aview segs (w_H W) (ms_mem ms7) a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => SENDDATA_S + 160 <= x < SENDDATA_S + 164) HFr);
    [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(rewrite ?U19' in Hx; lia). }
assert (GA8 : forall a, apresent (w_H W) (ms_mem ms7) a -> apresent (w_H W) (ms_mem ms8) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (EX5 := EF) in HS end.
assert (EEX5 : forall n, (n < 1024)%nat -> ew EX5 n = ew E5 n)
  by (intros n Hn; unfold EX5; rewrite !ew_ewset_other by lia; reflexivity).
assert (E5_33 : ew E5 33 = Z_to_bv 64 (TW.u_at Bw 1808 4))
  by (unfold E5; exact (sdh_ew_x (ms_regs ms7) [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw 1808 4)] 1
      ltac:(cbn; lia))).
sdh_region HS 0%nat HRhc.
assert (UBX : bv_unsigned (ew EX5 19) = SENDDATA_S)
  by (rewrite (EEX5 19%nat ltac:(first [lia | split; lia])), (EE5 19%nat 19%bv eq_refl), N19; unfold w64;
      apply unsigned_lit_small; unfold SENDDATA_S, TA_g_s; lia).
unfold region_ok in HRhc.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRhc.
rewrite UBX in HRhc.
assert (VHC8 : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms8) (SENDDATA_S + 160 + Z.of_nat j) =
  Some (YO0f.le_byte (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) 4 j)).
{ apply (sdh_chunk_rd4 EX5 (w_H W) (ms_mem ms8) SENDDATA_S 160
    (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SOff 23 0))
    (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)
    (Forall_inv (proj2 (proj2 (proj2 HRhc))))).
  cbn [sv_denot].
  rewrite <- (sdh_add_den (bv_swrap 32 (TW.u_at Bw 1808 4)) (bv_swrap 32 ncmds)). f_equal.
  - change (sext 64 (bv_extract 0 32 (ew EX5 33))) with (sv_denot EX5 (SExt true 32 (SOff 33 0))).
    apply (sdh_sext_den EX5 33 (TW.u_at Bw 1808 4));
      [rewrite (EEX5 33%nat ltac:(first [lia | split; lia])); exact E5_33 | exact Rhc].
  - rewrite (EEX5 23%nat ltac:(first [lia | split; lia])), (EE5 23%nat 23%bv eq_refl), N23, Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity. }
(* the registers at +0x144 *)
assert (N2b : YK11.getr (ms_regs ms8) 2 = Z_to_bv 64 sp1).
{ sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 2%nat ltac:(first [lia | split; lia])), (EE5 2%nat 2%bv eq_refl), N2, Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N24b : YK11.getr (ms_regs ms8) 24 = Z_to_bv 64 (F + 32)).
{ sdh_reg HS (24%bv : bv 5) (Z_to_bv 64 (F + 32)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 24%nat ltac:(first [lia | split; lia])), (EE5 24%nat 24%bv eq_refl), N24, Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N21b : YK11.getr (ms_regs ms8) 21 = w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8)).
{ sdh_reg HS (21%bv : bv 5) (w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 19%nat ltac:(first [lia | split; lia])), (EE5 19%nat 19%bv eq_refl), N19,
          (EEX5 20%nat ltac:(first [lia | split; lia])), (EE5 20%nat 20%bv eq_refl), N20; vm_compute; reflexivity).
  exact Hq. }
assert (N10b : YK11.getr (ms_regs ms8) 10 = w64 (SENDDATA_S + 20)).
{ sdh_reg HS (10%bv : bv 5) (w64 (SENDDATA_S + 20)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 19%nat ltac:(first [lia | split; lia])), (EE5 19%nat 19%bv eq_refl), N19;
          vm_compute; reflexivity).
  exact Hq. }
assert (N25b : YK11.getr (ms_regs ms8) 25 = w64 (SENDDATA_S + 160)).
{ sdh_reg HS (25%bv : bv 5) (w64 (SENDDATA_S + 160)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 19%nat ltac:(first [lia | split; lia])), (EE5 19%nat 19%bv eq_refl), N19;
          vm_compute; reflexivity).
  exact Hq. }
assert (N3b : YK11.getr (ms_regs ms8) 3 = w64 (as_gp B)).
{ sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 3%nat ltac:(first [lia | split; lia])), (EE5 3%nat 3%bv eq_refl), N3,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N4b : YK11.getr (ms_regs ms8) 4 = w64 (as_tp B)).
{ sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 4%nat ltac:(first [lia | split; lia])), (EE5 4%nat 4%bv eq_refl), N4,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N8b : YK11.getr (ms_regs ms8) 8 = w64 (spZ regs)).
{ sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 8%nat ltac:(first [lia | split; lia])), (EE5 8%nat 8%bv eq_refl), N8,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N9b : YK11.getr (ms_regs ms8) 9 = Z_to_bv 64 sp1).
{ sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 9%nat ltac:(first [lia | split; lia])), (EE5 9%nat 9%bv eq_refl), N9,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N18b : YK11.getr (ms_regs ms8) 18 = Z_to_bv 64 F).
{ sdh_reg HS (18%bv : bv 5) (Z_to_bv 64 F) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 18%nat ltac:(first [lia | split; lia])), (EE5 18%nat 18%bv eq_refl), N18,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N19b : YK11.getr (ms_regs ms8) 19 = w64 SENDDATA_S).
{ sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 19%nat ltac:(first [lia | split; lia])), (EE5 19%nat 19%bv eq_refl), N19,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N20b : YK11.getr (ms_regs ms8) 20 = w64 SHADOW_OFF).
{ sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 20%nat ltac:(first [lia | split; lia])), (EE5 20%nat 20%bv eq_refl), N20,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N22b : YK11.getr (ms_regs ms8) 22 = w64 bodyp).
{ sdh_reg HS (22%bv : bv 5) (w64 bodyp) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 22%nat ltac:(first [lia | split; lia])), (EE5 22%nat 22%bv eq_refl), N22,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N23b : YK11.getr (ms_regs ms8) 23 =
  Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)).
{ sdh_reg HS (23%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)) Hq
    ltac:(cbn [sv_denot];
          rewrite <- (sdh_add_den (bv_swrap 32 (TW.u_at Bw 1808 4)) (bv_swrap 32 ncmds));
          f_equal;
          [ change (sext 64 (bv_extract 0 32 (ew EX5 33)))
              with (sv_denot EX5 (SExt true 32 (SOff 33 0)));
            apply (sdh_sext_den EX5 33 (TW.u_at Bw 1808 4));
            [rewrite (EEX5 33%nat ltac:(first [lia | split; lia])); exact E5_33 | exact Rhc]
          | rewrite (EEX5 23%nat ltac:(first [lia | split; lia])), (EE5 23%nat 23%bv eq_refl), N23, Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity ]).
  exact Hq. }
assert (N26b : YK11.getr (ms_regs ms8) 26 = Z_to_bv 64 F).
{ sdh_reg HS (26%bv : bv 5) (Z_to_bv 64 F) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 26%nat ltac:(first [lia | split; lia])), (EE5 26%nat 26%bv eq_refl), N26,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (N27b : YK11.getr (ms_regs ms8) 27 = Z_to_bv 64 (SHADOW_OFF + F / 8)).
{ sdh_reg HS (27%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX5 27%nat ltac:(first [lia | split; lia])), (EE5 27%nat 27%bv eq_refl), N27,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
(* run 5c, +0x144: the store of the new counter at hp + 4. *)
pmkst HS.
pose proof (sdh_entry5c W (ms_regs ms8) (ms_mem ms8) sp1 F N2b N24b ltac:(first [lia | split; lia]) Hsp1al ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])
  HF64 ltac:(intros a Ha; apply GA8; apply GA7; apply HFp6; lia)) as HS5c.
clear HS HEI5. rename HS5c into HS.
set (E6 := sdh_E (ms_regs ms8) [w64 SHADOW_OFF]) in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (unfold E6; apply sdh_env_img).
assert (SHOK6 : sh_ok segs (SOff 32 0) (@nil shent) E6 (mrestrict (w_H W) (ms_mem ms8))) by constructor.
assert (EE6 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E6 n = YK11.getr (ms_regs ms8) q)
  by (intros n q Hn; unfold E6; apply sdh_ew_reg; exact Hn).
assert (U24' : bv_unsigned (ew E6 24) = F + 32)
  by (rewrite (EE6 24%nat 24%bv eq_refl), N24b; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx (ms_regs ms8) (Z_to_bv 64 (BASE + SDH_C6)) (ms_mem ms8)
    (YK11.seg_rom segs)) md8) Q) end.
paj_run_to_tok RUNTO HS HJ3 SHOK6 SDH_B0 SDH_C7.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDDATA_CID pos).
  { left. reflexivity. }
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24' in Ha.
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDDATA_CID) with 64. fold F. lia. }
  apply awr_ok_x_nil. }
set (md9 := with_vm_backing (m_vm_lazy md8) mat md8) in *. clearbody md9. clear mat.
rename ms into ms9.
(* what run 5c wrote: the 4 bytes at hp + 4 *)
assert (KR5c : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 36 <= a < F + 40) ->
  aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) (ms_mem ms8) a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => F + 36 <= x < F + 40) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(rewrite ?U24' in Hx; lia). }
assert (GA9 : forall a, apresent (w_H W) (ms_mem ms8) a -> apresent (w_H W) (ms_mem ms9) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
sdh_region HS 0%nat HRhp.
unfold region_ok in HRhp.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRhp.
rewrite U24' in HRhp.
assert (VHP : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms9) (F + 32 + 4 + Z.of_nat j) =
  Some (YO0f.le_byte (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) 4 j)).
{ apply (sdh_chunk_rd4 E6 (w_H W) (ms_mem ms9) (F + 32) 4 (SOff 23 0)
    (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)
    (Forall_inv (proj2 (proj2 (proj2 HRhp))))).
  cbn [sv_denot]. rewrite (EE6 23%nat 23%bv eq_refl), N23b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
(* the two slots of the realigned frame, kept by everything since run 2 *)
assert (KSTK : forall a, sp1 + 16 <= a < sp1 + 32 ->
  aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) (ms_mem ms2) a).
{ intros a Ha.
  rewrite (KR5c a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])), (KR5b a ltac:(first [lia | split; lia]) ltac:(unfold SENDDATA_S, TA_g_s in *; lia)),
    (KR5a a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])), (HeffM a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])),
    (KR4 a ltac:(first [lia | split; lia]) ltac:(unfold SHADOW_OFF in *; lia)), (KR3 a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
  apply (K1a a); lia. }
assert (HSL9 : rdword (aview segs (w_H W) (ms_mem ms9)) (sp1 + 24) =
  Some (bv_unsigned (YK11.getr regs (12%bv : bv 5)))).
{ rewrite <- HSLlen. apply sdh_rdword_frame. intros i Hi. apply KSTK. lia. }
assert (HSN9 : rdword (aview segs (w_H W) (ms_mem ms9)) (sp1 + 16) = Some now).
{ rewrite <- HSLnow. apply sdh_rdword_frame. intros i Hi. apply KSTK. lia. }
(* the mode the code loads: the 4 bytes at s + 20, untouched since the entry *)
assert (Vmd7 : YI04.val_mem segs (mrestrict (w_H W) (ms_mem ms7)) (SENDDATA_S + 20) 4 (TW.u_at Bw 1668 4)).
{ pose proof (tw_read_val segs (mrestrict (w_H W) (ms_mem ms7)) TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 20 4
    TMAP_A_ok HTW7 TMAP_A_g_s ltac:(first [lia | split; lia]) ltac:(unfold TW.SZ_g_s; lia)) as V.
  rewrite EOmd in V. exact V. }
assert (KMD : forall a, SENDDATA_S + 20 <= a < SENDDATA_S + 24 ->
  aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) (ms_mem ms7) a).
{ intros a Ha.
  assert (HxG : W_journalG.inG TG.G_HARNESS a)
    by (apply sd_inG_gs; change TA_g_s with SENDDATA_S; unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia).
  pose proof (GLOW a HxG) as Hl. pose proof (GNF a HxG) as Hnf. unfold kLowMemEnd in Hl.
  rewrite (KR5c a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])). apply KR5b; lia. }
assert (Vmd : YI04.val_mem segs (mrestrict (w_H W) (ms_mem ms9)) (SENDDATA_S + 20) 4 (TW.u_at Bw 1668 4)).
{ intros j Hj.
  rewrite (can_mbyte_of_aview (w_H W) (ms_mem ms7) (ms_mem ms9) (SENDDATA_S + 20 + Z.of_nat j)
    (KMD (SENDDATA_S + 20 + Z.of_nat j) ltac:(first [lia | split; lia]))).
  exact (Vmd7 j Hj). }
(* the registers at +0x148 *)
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (EX6 := EF) in HS end.
assert (EEX6 : forall n, (n < 1024)%nat -> ew EX6 n = ew E6 n)
  by (intros n Hn; unfold EX6; reflexivity).
assert (O2 : YK11.getr (ms_regs ms9) 2 = Z_to_bv 64 sp1).
{ sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 2%nat ltac:(first [lia | split; lia])), (EE6 2%nat 2%bv eq_refl), N2b, Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O3 : YK11.getr (ms_regs ms9) 3 = w64 (as_gp B)).
{ sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 3%nat ltac:(first [lia | split; lia])), (EE6 3%nat 3%bv eq_refl), N3b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O4 : YK11.getr (ms_regs ms9) 4 = w64 (as_tp B)).
{ sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 4%nat ltac:(first [lia | split; lia])), (EE6 4%nat 4%bv eq_refl), N4b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O8 : YK11.getr (ms_regs ms9) 8 = w64 (spZ regs)).
{ sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 8%nat ltac:(first [lia | split; lia])), (EE6 8%nat 8%bv eq_refl), N8b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O9 : YK11.getr (ms_regs ms9) 9 = Z_to_bv 64 sp1).
{ sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 9%nat ltac:(first [lia | split; lia])), (EE6 9%nat 9%bv eq_refl), N9b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O18 : YK11.getr (ms_regs ms9) 18 = Z_to_bv 64 F).
{ sdh_reg HS (18%bv : bv 5) (Z_to_bv 64 F) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 18%nat ltac:(first [lia | split; lia])), (EE6 18%nat 18%bv eq_refl), N18b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O19 : YK11.getr (ms_regs ms9) 19 = w64 SENDDATA_S).
{ sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 19%nat ltac:(first [lia | split; lia])), (EE6 19%nat 19%bv eq_refl), N19b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O20 : YK11.getr (ms_regs ms9) 20 = w64 SHADOW_OFF).
{ sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 20%nat ltac:(first [lia | split; lia])), (EE6 20%nat 20%bv eq_refl), N20b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O21 : YK11.getr (ms_regs ms9) 21 = w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8)).
{ sdh_reg HS (21%bv : bv 5) (w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 21%nat ltac:(first [lia | split; lia])), (EE6 21%nat 21%bv eq_refl), N21b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O22 : YK11.getr (ms_regs ms9) 22 = w64 bodyp).
{ sdh_reg HS (22%bv : bv 5) (w64 bodyp) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 22%nat ltac:(first [lia | split; lia])), (EE6 22%nat 22%bv eq_refl), N22b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O23 : YK11.getr (ms_regs ms9) 23 = Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)).
{ sdh_reg HS (23%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 23%nat ltac:(first [lia | split; lia])), (EE6 23%nat 23%bv eq_refl), N23b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O24 : YK11.getr (ms_regs ms9) 24 = Z_to_bv 64 (F + 32)).
{ sdh_reg HS (24%bv : bv 5) (Z_to_bv 64 (F + 32)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 24%nat ltac:(first [lia | split; lia])), (EE6 24%nat 24%bv eq_refl), N24b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O25 : YK11.getr (ms_regs ms9) 25 = w64 (SENDDATA_S + 160)).
{ sdh_reg HS (25%bv : bv 5) (w64 (SENDDATA_S + 160)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 25%nat ltac:(first [lia | split; lia])), (EE6 25%nat 25%bv eq_refl), N25b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O26 : YK11.getr (ms_regs ms9) 26 = Z_to_bv 64 F).
{ sdh_reg HS (26%bv : bv 5) (Z_to_bv 64 F) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 26%nat ltac:(first [lia | split; lia])), (EE6 26%nat 26%bv eq_refl), N26b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O27 : YK11.getr (ms_regs ms9) 27 = Z_to_bv 64 (SHADOW_OFF + F / 8)).
{ sdh_reg HS (27%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 27%nat ltac:(first [lia | split; lia])), (EE6 27%nat 27%bv eq_refl), N27b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
assert (O10 : YK11.getr (ms_regs ms9) 10 = w64 (SENDDATA_S + 20)).
{ sdh_reg HS (10%bv : bv 5) (w64 (SENDDATA_S + 20)) Hq
    ltac:(cbn [sv_denot]; rewrite (EEX6 10%nat ltac:(first [lia | split; lia])), (EE6 10%nat 10%bv eq_refl), N10b,
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  exact Hq. }
(* run 5d, +0x148 .. +0x178: the checked load of S_cfg_sum_mode, the seven arguments and `jal
   diginet_frame_build`. *)
pmkst HS.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR9.
destruct (sdh_entry5d lyc S2 W (ms_regs ms9) (ms_mem ms9) md9 sp1 (TW.u_at Bw 1668 4)
  (bv_unsigned (YK11.getr regs (12%bv : bv 5))) HSDC HAR9 O2 O9 O19 O20 O10 ltac:(first [lia | split; lia]) Hsp1al Rmd Hb12
  Vmd HSL9) as [HS5d SHOK5d].
clear HS HEI6 SHOK6. rename HS5d into HS.
set (E7 := sdh_E (ms_regs ms9) [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw 1668 4);
  Z_to_bv 64 (bv_unsigned (YK11.getr regs (12%bv : bv 5)))]) in HS, SHOK5d.
assert (HEI7 : img_env VAL A_LIM E7) by (unfold E7; apply sdh_env_img).
assert (EE7 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E7 n = YK11.getr (ms_regs ms9) q)
  by (intros n q Hn; unfold E7; apply sdh_ew_reg; exact Hn).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx (ms_regs ms9) (Z_to_bv 64 (BASE + SDH_C7)) (ms_mem ms9)
    (YK11.seg_rom segs)) md9) Q) end.
paj_run_tok RUN HS HJ3 SHOK5d YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
set (md10 := with_vm_backing (m_vm_lazy md9) mat md9) in *. clearbody md10. clear mat.
rename ms into ms10.
(* run 5d wrote nothing *)
assert (KR5d : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W) (ms_mem ms10) a = aview segs (w_H W) (ms_mem ms9) a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. cbv beta. sdh_win Hin Hx ltac:(first [lia | split; lia]). }
assert (GA10 : forall a, apresent (w_H W) (ms_mem ms9) a -> apresent (w_H W) (ms_mem ms10) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the world the walk hands diginet_frame_build: the model's host-counter store *)
assert (EM1 : sd_M1 Bw ncmds =
  TW.upd Bw 1808 (TW.put 4 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds))).
{ unfold sd_M1, TW.set_S_host_counter, TW.S_host_counter. rewrite EAhc, sdh_hc_put. reflexivity. }
assert (HTW8 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms8)) (sd_M1 Bw ncmds)).
{ rewrite EM1. replace 1808 with (TW.OFF_g_s + 160) by reflexivity.
  apply (tw_write TMAP_A (aview segs (w_H W) (ms_mem ms7)) _ Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 160 4
    (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) TMAP_A_ok HTW7 TMAP_A_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. change (TA_g_s + 160) with (SENDDATA_S + 160). exact (VHC8 j Hj).
  - intros x Hx Hn. destruct Hx as (o & b & n & Hin3 & Hx).
    assert (HxG : W_journalG.inG TG.G_HARNESS x).
    { unfold W_journalG.inG. apply Exists_exists. exists (b, n).
      split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KR5b; [pose proof (GLOW x HxG); unfold kLowMemEnd in *; lia|].
    change TA_g_s with SENDDATA_S in Hn. unfold SENDDATA_S, TA_g_s in *. lia. }
assert (HTW10 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms10)) (sd_M1 Bw ncmds)).
{ apply (tw_kept_GA (aview segs (w_H W) (ms_mem ms8))); [exact HTW8|].
  intros b n i Hbn Hi.
  assert (HxG : W_journalG.inG TG.G_HARNESS (b + i))
    by (unfold W_journalG.inG; apply Exists_exists; exists (b, n);
        split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (GLOW (b + i) HxG) as Hl. pose proof (GNF (b + i) HxG) as Hnf. unfold kLowMemEnd in Hl.
  rewrite (KR5d (b + i) ltac:(first [lia | split; lia])). apply KR5c; lia. }
(* the registers at the call of diginet_frame_build *)
lazymatch type of HS with YP0l.st_ok _ ?EF _ _ => set (EX7 := EF) in HS end.
assert (EEX7 : forall n, (n < 1024)%nat -> ew EX7 n = ew E7 n)
  by (intros n Hn; unfold EX7; rewrite !ew_ewset_other by lia; reflexivity).
assert (E7_33 : ew E7 33 = Z_to_bv 64 (TW.u_at Bw 1668 4))
  by (unfold E7; exact (sdh_ew_x (ms_regs ms9) [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw 1668 4);
      Z_to_bv 64 (bv_unsigned (YK11.getr regs (12%bv : bv 5)))] 1 ltac:(cbn; lia))).
assert (E7_34 : ew E7 34 = Z_to_bv 64 (bv_unsigned (YK11.getr regs (12%bv : bv 5))))
  by (unfold E7; exact (sdh_ew_x (ms_regs ms9) [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw 1668 4);
      Z_to_bv 64 (bv_unsigned (YK11.getr regs (12%bv : bv 5)))] 2 ltac:(cbn; lia))).
assert (HEIX7 : img_env VAL A_LIM EX7)
  by (intros a Ha; rewrite (EEX7 a ltac:(unfold A_LIM in Ha; lia)); exact (HEI7 a Ha)).
sdh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + SD_FB)) C1 ltac:(apply codeptr_val; exact HEIX7).
sdh_reg HS (Z_to_bv 5 11) (w64 1514) C11 ltac:(reflexivity).
sdh_reg HS (Z_to_bv 5 16) (Z_to_bv 64 (bv_unsigned (YK11.getr regs (12%bv : bv 5)))) C16
  ltac:(cbn [sv_denot]; rewrite (EEX7 34%nat ltac:(first [lia | split; lia])), E7_34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (Z_to_bv 5 17) (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw 1668 4))) C17
  ltac:(apply (sdh_sext_den EX7 33 (TW.u_at Bw 1668 4));
        [rewrite (EEX7 33%nat ltac:(first [lia | split; lia])); exact E7_33 | exact Rmd]).
sdh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) C2
  ltac:(cbn [sv_denot]; rewrite (EEX7 2%nat ltac:(first [lia | split; lia])), (EE7 2%nat 2%bv eq_refl), O2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (3%bv : bv 5) (w64 (as_gp B)) C3
  ltac:(cbn [sv_denot]; rewrite (EEX7 3%nat ltac:(first [lia | split; lia])), (EE7 3%nat 3%bv eq_refl), O3, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (4%bv : bv 5) (w64 (as_tp B)) C4
  ltac:(cbn [sv_denot]; rewrite (EEX7 4%nat ltac:(first [lia | split; lia])), (EE7 4%nat 4%bv eq_refl), O4, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (8%bv : bv 5) (w64 (spZ regs)) C8
  ltac:(cbn [sv_denot]; rewrite (EEX7 8%nat ltac:(first [lia | split; lia])), (EE7 8%nat 8%bv eq_refl), O8, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) C9
  ltac:(cbn [sv_denot]; rewrite (EEX7 9%nat ltac:(first [lia | split; lia])), (EE7 9%nat 9%bv eq_refl), O9, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (18%bv : bv 5) (Z_to_bv 64 F) C18
  ltac:(cbn [sv_denot]; rewrite (EEX7 18%nat ltac:(first [lia | split; lia])), (EE7 18%nat 18%bv eq_refl), O18, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (19%bv : bv 5) (w64 SENDDATA_S) C19
  ltac:(cbn [sv_denot]; rewrite (EEX7 19%nat ltac:(first [lia | split; lia])), (EE7 19%nat 19%bv eq_refl), O19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (20%bv : bv 5) (w64 SHADOW_OFF) C20
  ltac:(cbn [sv_denot]; rewrite (EEX7 20%nat ltac:(first [lia | split; lia])), (EE7 20%nat 20%bv eq_refl), O20, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (21%bv : bv 5) (w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8)) C21
  ltac:(cbn [sv_denot]; rewrite (EEX7 21%nat ltac:(first [lia | split; lia])), (EE7 21%nat 21%bv eq_refl), O21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (25%bv : bv 5) (w64 (SENDDATA_S + 160)) C25
  ltac:(cbn [sv_denot]; rewrite (EEX7 25%nat ltac:(first [lia | split; lia])), (EE7 25%nat 25%bv eq_refl), O25, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (26%bv : bv 5) (Z_to_bv 64 F) C26
  ltac:(cbn [sv_denot]; rewrite (EEX7 26%nat ltac:(first [lia | split; lia])), (EE7 26%nat 26%bv eq_refl), O26, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (27%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) C27
  ltac:(cbn [sv_denot]; rewrite (EEX7 27%nat ltac:(first [lia | split; lia])), (EE7 27%nat 27%bv eq_refl), O27, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (Z_to_bv 5 10) (w64 (SENDDATA_S + 216)) C10
  ltac:(cbn [sv_denot]; rewrite (EEX7 19%nat ltac:(first [lia | split; lia])), (EE7 19%nat 19%bv eq_refl), O19;
        vm_compute; reflexivity).
sdh_reg HS (Z_to_bv 5 12) (w64 (SENDDATA_S + 120)) C12
  ltac:(cbn [sv_denot]; rewrite (EEX7 19%nat ltac:(first [lia | split; lia])), (EE7 19%nat 19%bv eq_refl), O19;
        vm_compute; reflexivity).
sdh_reg HS (Z_to_bv 5 13) (w64 SENDDATA_S) C13
  ltac:(cbn [sv_denot]; rewrite (EEX7 19%nat ltac:(first [lia | split; lia])), (EE7 19%nat 19%bv eq_refl), O19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (Z_to_bv 5 14) (Z_to_bv 64 (F + 32)) C14
  ltac:(cbn [sv_denot]; rewrite (EEX7 24%nat ltac:(first [lia | split; lia])), (EE7 24%nat 24%bv eq_refl), O24, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (Z_to_bv 5 15) (w64 bodyp) C15
  ltac:(cbn [sv_denot]; rewrite (EEX7 22%nat ltac:(first [lia | split; lia])), (EE7 22%nat 22%bv eq_refl), O22, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
sdh_reg HS (23%bv : bv 5) (w64 (SENDDATA_S + 216)) C23
  ltac:(cbn [sv_denot]; rewrite (EEX7 19%nat ltac:(first [lia | split; lia])), (EE7 19%nat 19%bv eq_refl), O19;
        vm_compute; reflexivity).
assert (Hsp10 : spZ (ms_regs ms10) = sp1)
  by (unfold spZ; rewrite C2; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR10.
(* what the walk kept of the caller's memory, from the entry to the call of diginet_frame_build *)
set (FL := flag_addr lyc SENDDATA_CID pos) in *.
assert (SHLT : forall cid pos' a, In (cid, pos') (frames Sc) ->
  in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8) -> 0 <= a < 2 ^ 46).
{ intros cid pos' a Hin Hr.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyc cid pos') (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos') 8 ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
  unfold in_zr in Hr. cbn [fst snd] in Hr. unfold shadow_addr, SHADOW_OFF in *.
  change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
assert (KEPT0 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memc
  (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr)
  by (apply dk_kept_refl_g; intros a Ha; apply Hwin; lia).
assert (KEPT2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms2)
  (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr).
{ apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W memc (ms_mem ms2)
    (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr
    (fun a => spZ regs - SENDDATA_STK <= a < spZ regs) HAR KEPT0).
  - intros a Ha Hn. rewrite (KR2 a Ha ltac:(first [lia | split; lia])). apply KR1; lia.
  - intros a Ha. apply GA2, GA1, Ha.
  - intros a HZ Hc. exact HZ.
  - intros b m i Hb Hi HZ. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _). lia.
  - intros a HZ Hi HnG Hno He. exfalso. pose proof (transport_segs_low a Hi). unfold kLowMemEnd in *. lia.
  - intros cid pos' a Hin Hr HZ. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HAR Hin) as (F4096 & Fce & _).
    destruct Hr as [Hr | Hr].
    + unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
    + pose proof (SHLT cid pos' a Hin Hr). lia. }
destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem3 md3 SENDDATA_CID pos F FL HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL)
  as (NB1 & NB2 & NB3 & NB4).
assert (KEPT3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem3
  (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr).
{ eapply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc Sc W memc W (ms_mem ms2) W mem3
    (spZ regs - SENDDATA_STK) (spZ regs) (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0)) senddata_wr
    (fun _ => False) (dkg_nf SENDDATA_CID F FL)).
  - lia.
  - lia.
  - reflexivity.
  - intros f Hf. exact Hf.
  - intros bm Hbm. exact Hbm.
  - exact NB1.
  - exact NB3.
  - exact KEPT2.
  - apply acall_kept_g_of. exact (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f))))).
  - lia.
  - lia.
  - intros a []. }
(* every byte the walk did not write between the stack malloc and the call of diginet_frame_build *)
assert (KCH : forall a, 0 <= a < 2 ^ 64 ->
  (a < spZ regs - SENDDATA_STK \/ spZ regs <= a) ->
  ~ dkg_nf SENDDATA_CID F FL a ->
  ~ (SENDDATA_S + 160 <= a < SENDDATA_S + 164) ->
  aview segs (w_H W) (ms_mem ms10) a = aview segs (w_H W) mem3 a).
{ intros a Ha Hw Hnf HG160.
  unfold dkg_nf in Hnf. change (fs_frame_bytes SENDDATA_CID) with 64 in Hnf.
  change (fs_frame_bytes SENDDATA_CID / 8) with 8 in Hnf.
  assert (HF1 : a < F \/ F + 64 <= a).
  { destruct (Z_lt_le_dec a F) as [Hx|Hx]; [left; exact Hx|].
    destruct (Z_lt_le_dec a (F + 64)) as [Hy|Hy]; [|right; exact Hy].
    exfalso. apply Hnf. left. split; [exact Hx | exact Hy]. }
  assert (HF2 : a < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 8 <= a).
  { destruct (Z_lt_le_dec a (SHADOW_OFF + F / 8)) as [Hx|Hx]; [left; exact Hx|].
    destruct (Z_lt_le_dec a (SHADOW_OFF + F / 8 + 8)) as [Hy|Hy]; [|right; exact Hy].
    exfalso. apply Hnf. right. left. split; [exact Hx | exact Hy]. }
  rewrite (KR5d a Ha), (KR5c a Ha ltac:(first [lia | split; lia])), (KR5b a Ha HG160), (KR5a a Ha ltac:(first [lia | split; lia])),
    (HeffM a Ha ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])), (KR4 a Ha ltac:(first [lia | split; lia])). apply KR3; lia. }
assert (KEPT10 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms10)
  (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr).
{ eapply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem3 md3
    mem3 (ms_mem ms10) (spZ regs - SENDDATA_STK) (spZ regs) SENDDATA_CID pos F FL senddata_wr
    (fun a => (spZ regs - SENDDATA_STK <= a < spZ regs) \/ dkg_nf SENDDATA_CID F FL a
              \/ W_journalG.inG TG.G_HARNESS a)).
  - exact (G_HARNESS_gx_ok B HGU).
  - exact HAR.
  - exact HAR2.
  - exact Hfrs2.
  - intros bm Hbm. rewrite Eab2. exact Hbm.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact FFL.
  - lia.
  - lia.
  - intros a Ha. exact Ha.
  - exact KEPT3.
  - intros a Ha Hn.
    assert (Hw : a < spZ regs - SENDDATA_STK \/ spZ regs <= a).
    { destruct (Z_lt_le_dec a (spZ regs - SENDDATA_STK)) as [Hx|Hx]; [left; exact Hx|].
      destruct (Z_lt_le_dec a (spZ regs)) as [Hy|Hy]; [|right; exact Hy].
      exfalso. apply Hn. left. split; [exact Hx | exact Hy]. }
    assert (HnG : ~ W_journalG.inG TG.G_HARNESS a)
      by (intros Hc; apply Hn; right; right; exact Hc).
    apply (KCH a Ha Hw ltac:(intros Hc; apply Hn; right; left; exact Hc)).
    intros Hc. apply HnG. apply sd_inG_gs. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia.
  - intros a Ha. apply GA10, GA9, GA8, GA7, HgrM, GA5, GA4, Ha. }
(* the body, as diginet_frame_build must see it at the call *)
assert (HOFFB : bodyp + Z.of_nat (length body) <= spZ regs - SENDDATA_STK \/ spZ regs <= bodyp)
  by (unfold decode_off_win in Hoffw; exact Hoffw).
assert (HNFB : forall a, bodyp <= a < bodyp + Z.of_nat (length body) ->
  ~ dkg_nf SENDDATA_CID F FL a).
{ intros a Ha Hc. destruct Hsrc as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    apply (NB1 bA nA (a - bA) Hin ltac:(first [lia | split; lia])). replace (bA + (a - bA)) with a by lia. exact Hc.
  - destruct HL as [(cid & pos' & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + exact (NB3 cid pos' a Hin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) Hc).
    + exact (NB2 a Hc (trans_g_img a (HG a Ha))).
    + pose proof (NB4 a Hc). destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [TK1 TK2]. lia.
    + exact (NB2 a Hc (trans_ro_img a (HR a Ha))). }
assert (KVB : forall a, bodyp <= a < bodyp + Z.of_nat (length body) ->
  aview segs (w_H W) (ms_mem ms10) a = aview segs (w_H W) memc a).
{ intros a Ha.
  assert (Hn0 : 0 < Z.of_nat (length body)) by lia.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc bodyp (Z.of_nat (length body)) HAR Hsrc Hn0)
    as (_ & _ & _ & _ & Hq0 & Hq63).
  assert (Hmid : aview segs (w_H W) mem3 a = aview segs (w_H W) (ms_mem ms2) a).
  { destruct Hsrc as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnn).
      pose proof (req_size_pos nA (proj1 Hnn)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K1b bA nA (a - bA) Hin ltac:(first [lia | split; lia])). intros [].
    - destruct HL as [(cid & pos' & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K1d cid pos' a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []].
      + pose proof (HG a Ha) as Ga. exact (K1c a (trans_g_img a Ga) (HGU a Ga) (HGE a Ga)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [TK1 TK2]. apply K1a; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        exact (K1c a (trans_ro_img a Ra) Ho He). }
  rewrite (KCH a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) (HNFB a Ha)
    ltac:(intros Hc; apply (HbodyG a Ha); apply sd_inG_gs;
          unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia)).
  rewrite Hmid, (KR2 a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])). apply KR1; lia. }
assert (KSB : forall cid pos' sdw, In (cid, pos') (frames Sc) ->
  in_zr sdw (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8) ->
  aview segs (w_H W) (ms_mem ms10) sdw = aview segs (w_H W) memc sdw).
{ intros cid pos' sdw Hin Hs'.
  pose proof (SHLT cid pos' sdw Hin Hs') as Hsb.
  assert (Hlow : SHADOW_OFF <= sdw).
  { destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HAR Hin) as (F4096 & _ & _).
    pose proof (Z.div_pos (frame_addr lyc cid pos') 8 ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
    unfold in_zr, shadow_addr in Hs'. cbn [fst snd] in Hs'. lia. }
  rewrite (KCH sdw ltac:(unfold SHADOW_OFF in *; lia) ltac:(left; unfold SHADOW_OFF in *; lia)
    ltac:(intros Hc; exact (NB3 cid pos' sdw Hin (or_intror Hs') Hc))
    ltac:(unfold SENDDATA_S, TA_g_s, SHADOW_OFF in *; lia)).
  rewrite (K1d cid pos' sdw Hin (or_intror Hs') ltac:(intros [])).
  rewrite (KR2 sdw ltac:(unfold SHADOW_OFF in *; lia) ltac:(unfold SHADOW_OFF in *; lia)).
  apply KR1; unfold SHADOW_OFF in *; lia. }
assert (TSB : trans_src_ok B lyc S2 W (ms_mem ms10) bodyp (Z.of_nat (length body))).
{ destruct (Z.eq_dec (Z.of_nat (length body)) 0) as [HB0 | HBpos].
  - rewrite HB0. rewrite HB0 in Hsrc.
    exact (sdh_src_kept0 LAWS lyc Sc W memc mdc lyc S2 W (ms_mem ms10) md10 bodyp HAR HAR10
      ltac:(rewrite Eab2; apply Permutation_refl) ltac:(intros f Hf; rewrite Hfrs2; right; exact Hf)
      ltac:(reflexivity) eq_refl eq_refl Hsrc).
  - exact (sdh_src_kept LAWS lyc Sc W memc mdc lyc S2 W (ms_mem ms10) md10 bodyp
      (Z.of_nat (length body)) HAR HAR10 ltac:(rewrite Eab2; apply Permutation_refl)
      ltac:(intros f Hf; rewrite Hfrs2; right; exact Hf) ltac:(reflexivity) eq_refl eq_refl
      KVB KSB Hsrc ltac:(first [lia | split; lia])). }
assert (GBODY : garr8 segs (mrestrict (w_H W) (ms_mem ms10)) bodyp (map DSpec.bz body)).
{ apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms10)) bodyp
    (map DSpec.bz body)).
  - exact Hgarr.
  - intros a Ha. rewrite length_map in Ha.
    exact (can_mbyte_of_aview (w_H W) memc (ms_mem ms10) a (KVB a Ha)). }
assert (DISJB : SENDDATA_S + 216 + 1514 <= bodyp \/ bodyp + Z.of_nat (length body) <= SENDDATA_S + 216).
{ destruct (Z_lt_le_dec bodyp (SENDDATA_S + 216 + 1514)) as [Hlt | Hge]; [|left; exact Hge].
  right.
  assert (Hle : bodyp <= SENDDATA_S + 216).
  { destruct (Z_lt_le_dec (SENDDATA_S + 216) bodyp) as [Hx | Hx]; [|exact Hx].
    exfalso. apply HBODYG. apply sd_inG_gs. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia. }
  destruct (Z_lt_le_dec (SENDDATA_S + 216) (bodyp + Z.of_nat (length body))) as [Hx | Hx]; [|exact Hx].
  exfalso. apply (HbodyG (SENDDATA_S + 216) ltac:(first [lia | split; lia])). apply sd_inG_gs.
  unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia. }
(* the own frame is apart from its own shadow bytes and from g_s *)
assert (FSEP : F + 64 <= SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 8 <= F).
{ assert (Hdp : 0 <= F / 8) by (apply Z.div_pos; lia).
  pose proof (Z.div_mod F 8 ltac:(first [lia | split; lia])) as DF8.
  pose proof (Z.mod_pos_bound F 8 ltac:(first [lia | split; lia])) as MF8.
  pose proof HFapp as HFapp2. unfold in_app, ASAN_CEIL in HFapp2.
  destruct HFapp2 as (_ & [HL | (HH1 & HH2)]);
    [left; unfold kLowShadowBeg, SHADOW_OFF in *; lia
    | right; unfold kHighMemBeg, SHADOW_OFF in *; lia]. }
assert (FGSEP : F + 64 <= SENDDATA_S \/ SENDDATA_S + TW.SZ_g_s <= F).
{ destruct (Z_lt_le_dec (F + 64) (SENDDATA_S + 1)) as [Hx|Hx]; [left; lia|].
  destruct (Z_lt_le_dec F (SENDDATA_S + TW.SZ_g_s)) as [Hy|Hy]; [|right; lia].
  exfalso.
  apply (frm_img segs B LAWS lyc S2 W mem3 md3 SENDDATA_CID pos (Z.max F SENDDATA_S) HAR2 Hin2).
  - change (fs_frame_bytes SENDDATA_CID) with 64. fold F.
    unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia.
  - apply trans_g_img. apply sd_inG_gs. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia. }
(* the frame's eight shadow bytes and its bytes, at the call *)
assert (KSH45 : forall sdw, SHADOW_OFF + F / 8 <= sdw < SHADOW_OFF + F / 8 + 8 ->
  aview segs (w_H W) (ms_mem ms10) sdw = aview segs (w_H W) (ms_mem ms5) sdw).
{ intros sdw Hs. assert (Hb : 0 <= sdw < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
  assert (Hnf1 : ~ (F + 32 <= sdw < F + 32 + 15)) by (destruct FSEP as [FS1|FS1]; lia).
  assert (Hnf2 : ~ (F + 36 <= sdw < F + 40)) by (destruct FSEP as [FS1|FS1]; lia).
  assert (Hnf3 : ~ (F + 47 <= sdw < F + 48)) by (destruct FSEP as [FS1|FS1]; lia).
  rewrite (KR5d sdw Hb), (KR5c sdw Hb Hnf2),
    (KR5b sdw Hb ltac:(unfold SENDDATA_S, TA_g_s, SHADOW_OFF in *; lia)), (KR5a sdw Hb Hnf3).
  apply (HeffM sdw Hb); [exact Hnf1 | unfold SHADOW_OFF in *; lia]. }
assert (HSH4F : aview segs (w_H W) (ms_mem ms10) (SHADOW_OFF + F / 8 + 4) = Some 0)
  by (rewrite (KSH45 (SHADOW_OFF + F / 8 + 4) ltac:(split; lia)); exact HSH4).
assert (HSH5F : aview segs (w_H W) (ms_mem ms10) (SHADOW_OFF + F / 8 + 5) = Some 0)
  by (rewrite (KSH45 (SHADOW_OFF + F / 8 + 5) ltac:(split; lia)); exact HSH5).
assert (HSHpF : forall i, 0 <= i < 8 -> apresent (w_H W) (ms_mem ms10) (SHADOW_OFF + F / 8 + i))
  by (intros i Hi; apply GA10, GA9, GA8, GA7, HgrM; apply HSHp; lia).
assert (HFpF : forall a, F <= a < F + 64 -> apresent (w_H W) (ms_mem ms10) a)
  by (intros a Ha; apply GA10, GA9, GA8, GA7, HgrM, GA5, GA4; apply Hfpres; lia).
(* the twelve header bytes diginet_frame_build reads at hp + 4 *)
assert (HDRRD : decode_rd_ok W (ms_mem ms10) (F + 32 + 4) 12).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply can_aview_vis. apply HFpF. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    rewrite (sdh_div8 F x HF8), Z.add_assoc.
    assert (H4 : 4 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (H5 : (x - F) / 8 < 6) by (apply Z.div_lt_upper_bound; lia).
    assert (Hc : (x - F) / 8 = 4 \/ (x - F) / 8 = 5) by lia.
    destruct Hc as [Hc|Hc]; rewrite Hc; [exact HSH4F | exact HSH5F].
  - intros sdw Hs.
    assert (HHlo : shadow_addr (F + 32 + 4) / 8 * 8 = SHADOW_OFF + F / 8).
    { unfold shadow_addr. rewrite (sdh_div8 F (F + 32 + 4) HF8).
      replace (F + 32 + 4 - F) with 36 by lia. change (36 / 8) with 4. rewrite EF8.
      replace (SHADOW_OFF + (8 * (F / 64) + 4)) with ((268431360 + F / 64) * 8 + 4)
        by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. change (4 / 8) with 0. rewrite Z.add_0_r. unfold SHADOW_OFF. lia. }
    assert (HHhi : shadow_addr (F + 32 + 4 + 12 - 1) / 8 * 8 + 8 = SHADOW_OFF + F / 8 + 8).
    { unfold shadow_addr. rewrite (sdh_div8 F (F + 32 + 4 + 12 - 1) HF8).
      replace (F + 32 + 4 + 12 - 1 - F) with 47 by lia. change (47 / 8) with 5. rewrite EF8.
      replace (SHADOW_OFF + (8 * (F / 64) + 5)) with ((268431360 + F / 64) * 8 + 5)
        by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. change (5 / 8) with 0. rewrite Z.add_0_r. unfold SHADOW_OFF. lia. }
    rewrite HHlo, HHhi in Hs. apply can_aview_vis.
    replace sdw with (SHADOW_OFF + F / 8 + (sdw - (SHADOW_OFF + F / 8))) by lia.
    apply HSHpF. lia.
  - pose proof HFapp as HFapp2. unfold in_app, ASAN_CEIL in HFapp2. unfold amem_range.
    destruct HFapp2 as (_ & [HL | (HH1 & HH2)]);
      [left; unfold kLowShadowBeg, kLowMemEnd in *; lia
      | right; unfold kHighMemBeg, kHighMemEnd, kLowMemEnd in *; lia].
  - lia.
  - lia. }
(* the three ranges of g_s diginet_frame_build reads and writes *)
assert (HWL : Z.of_nat (length (sd_M1 Bw ncmds)) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ HTW10); apply Z2Nat.id; unfold TW.W_LEN; lia).
assert (HOJL : length (TW.sub (sd_M1 Bw ncmds) 1864 1514) = 1514%nat)
  by (apply TWL.length_sub; [lia | rewrite HWL; unfold TW.W_LEN; lia]).
assert (HOJZ : Z.of_nat (length (TW.sub (sd_M1 Bw ncmds) 1864 1514)) = 1514)
  by (rewrite HOJL; reflexivity).
assert (HDML : length (TW.sub (sd_M1 Bw ncmds) 1768 6) = 6%nat)
  by (apply TWL.length_sub; [lia | rewrite HWL; unfold TW.W_LEN; lia]).
assert (HSML : length (TW.sub (sd_M1 Bw ncmds) 1648 6) = 6%nat)
  by (apply TWL.length_sub; [lia | rewrite HWL; unfold TW.W_LEN; lia]).
assert (HVISG : forall a, SENDDATA_S <= a < SENDDATA_S + TW.SZ_g_s ->
  aview segs (w_H W) (ms_mem ms10) a <> None).
{ intros a Ha. pose proof HTW10 as HTWt. destruct HTWt as [_ Hr].
  replace a with (TA_g_s + (a - TA_g_s)) by (unfold SENDDATA_S, TA_g_s in *; lia).
  rewrite (Hr TW.OFF_g_s TA_g_s TW.SZ_g_s (a - TA_g_s) TMAP_A_g_s
    ltac:(unfold SENDDATA_S, TA_g_s in *; lia)). discriminate. }
assert (SHANY : forall q n, 0 < n -> SENDDATA_S <= q -> q + n <= SENDDATA_S + 18200 ->
  trans_sh_any B q n).
{ intros q n Hn H1 H2. apply (trans_sh_any_zshadow B SENDDATA_S (SENDDATA_S + TW.SZ_g_s) q n HSDC Hn).
  - assert (96231 <= q / 64)
      by (apply Z.div_le_lower_bound; [lia | unfold SENDDATA_S, TA_g_s in *; lia]).
    unfold SENDDATA_S, TA_g_s in *. lia.
  - pose proof (Z.div_mod (q + n - 1) 64 ltac:(first [lia | split; lia])) as D.
    pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(first [lia | split; lia])) as M.
    unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia. }
assert (RDG : forall q n, 0 < n -> SENDDATA_S <= q -> q + n <= SENDDATA_S + 18200 ->
  decode_rd_ok W (ms_mem ms10) q n).
{ intros q n Hn H1 H2.
  destruct (sdh_gs_ra lyc S2 W (ms_mem ms10) md10 q n HSDC HAR10 Hn H1 H2) as [HA HH].
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply HVISG. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia.
  - exact HA.
  - exact HH.
  - left. unfold kLowMemEnd, SENDDATA_S, TA_g_s in *. lia.
  - unfold SENDDATA_S, TA_g_s in *. lia.
  - unfold SENDDATA_S, TA_g_s in *. lia. }
assert (HOUT : trans_out_ok B lyc S2 W (ms_mem ms10) (SENDDATA_S + 216) 1514).
{ split; [|apply RDG; unfold SENDDATA_S, TA_g_s; lia]. right. split.
  - intros a Ha. apply sd_inG_gs. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia.
  - apply SHANY; unfold SENDDATA_S, TA_g_s; lia. }
assert (HTWR : transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc S2
  ((SENDDATA_CID, pos) :: own) W (ms_mem ms10) (spZ (ms_regs ms10) - FRAME_FB_FRAME)
  (SENDDATA_S + 216) 1514).
{ eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|].
  intros a Ha. right. apply sd_inG_gs. unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *. lia. }
assert (GOJ : garr8 segs (mrestrict (w_H W) (ms_mem ms10)) (SENDDATA_S + 216)
  (map DSpec.bz (TW.sub (sd_M1 Bw ncmds) 1864 1514)))
  by (exact (tw_garr8 segs (mrestrict (w_H W) (ms_mem ms10)) TMAP_A (sd_M1 Bw ncmds) TW.OFF_g_s TA_g_s
      TW.SZ_g_s 216 1514 TMAP_A_ok HTW10 TMAP_A_g_s ltac:(first [lia | split; lia]) ltac:(unfold TW.SZ_g_s; lia))).
assert (GDM : garr8 segs (mrestrict (w_H W) (ms_mem ms10)) (SENDDATA_S + 120)
  (map DSpec.bz (TW.sub (sd_M1 Bw ncmds) 1768 6)))
  by (exact (tw_garr8 segs (mrestrict (w_H W) (ms_mem ms10)) TMAP_A (sd_M1 Bw ncmds) TW.OFF_g_s TA_g_s
      TW.SZ_g_s 120 6 TMAP_A_ok HTW10 TMAP_A_g_s ltac:(first [lia | split; lia]) ltac:(unfold TW.SZ_g_s; lia))).
assert (GSM : garr8 segs (mrestrict (w_H W) (ms_mem ms10)) SENDDATA_S
  (map DSpec.bz (TW.sub (sd_M1 Bw ncmds) 1648 6))).
{ replace SENDDATA_S with (TA_g_s + 0) by (unfold SENDDATA_S; lia).
  exact (tw_garr8 segs (mrestrict (w_H W) (ms_mem ms10)) TMAP_A (sd_M1 Bw ncmds) TW.OFF_g_s TA_g_s
    TW.SZ_g_s 0 6 TMAP_A_ok HTW10 TMAP_A_g_s ltac:(first [lia | split; lia]) ltac:(unfold TW.SZ_g_s; lia)). }
assert (TSD : trans_src_ok B lyc S2 W (ms_mem ms10) (SENDDATA_S + 120) 6)
  by (apply (trans_src_ok_G_range B lyc S2 W (ms_mem ms10) (SENDDATA_S + 120) 6 TA_g_s TW.SZ_g_s
        sd_gs_row); [unfold SENDDATA_S, TA_g_s; lia | unfold SENDDATA_S, TA_g_s, TW.SZ_g_s; lia
      | apply SHANY; unfold SENDDATA_S, TA_g_s; lia | apply RDG; unfold SENDDATA_S, TA_g_s; lia]).
assert (TSS : trans_src_ok B lyc S2 W (ms_mem ms10) SENDDATA_S 6)
  by (apply (trans_src_ok_G_range B lyc S2 W (ms_mem ms10) SENDDATA_S 6 TA_g_s TW.SZ_g_s
        sd_gs_row); [unfold SENDDATA_S, TA_g_s; lia | unfold SENDDATA_S, TA_g_s, TW.SZ_g_s; lia
      | apply SHANY; unfold SENDDATA_S, TA_g_s; lia | apply RDG; unfold SENDDATA_S, TA_g_s; lia]).
assert (HDRF : decode_in_fake lyc S2 (F + 32 + 4) 12).
{ exists SENDDATA_CID, pos. rewrite Hfrs2. split; [left; reflexivity|].
  change (fs_frame_bytes SENDDATA_CID) with 64. fold F. lia. }
assert (EBN : 4096 <= BASE /\ BASE + 2 ^ 20 <= 2 ^ 40).
{ let v := eval vm_compute in BASE in change BASE with v. split; lia. }
(* the twelve header bytes, as frame_fb_hdr_bytes spells them *)
assert (KFR : forall a, F <= a < F + 64 -> ~ (F + 36 <= a < F + 40) ->
  aview segs (w_H W) (ms_mem ms10) a = aview segs (w_H W) (ms_mem ms7) a).
{ intros a Ha Hn. assert (Hb : 0 <= a < 2 ^ 64) by lia.
  rewrite (KR5d a Hb), (KR5c a Hb Hn).
  apply KR5b; [exact Hb |]. destruct FGSEP as [FG1|FG1]; unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia. }
assert (KFM : forall a, F <= a < F + 64 -> ~ (F + 36 <= a < F + 40) -> a <> F + 47 ->
  aview segs (w_H W) (ms_mem ms10) a = aview segs (w_H W) mem6 a)
  by (intros a Ha H1 H2; rewrite (KFR a Ha H1); apply KR5a; lia).
assert (HWLB : Z.of_nat (length Bw) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw); apply Z2Nat.id; unfold TW.W_LEN; lia).
assert (ESEND : TW.u_at (sd_M1 Bw ncmds) 1808 4 =
  (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) mod 2 ^ 32).
{ rewrite EM1.
  rewrite (TWL.u_at_upd_put Bw 1808 4 _ ltac:(first [lia | split; lia]) ltac:(rewrite HWLB; unfold TW.W_LEN; lia)).
  change (8 * Z.of_nat 4) with 32. reflexivity. }
assert (Hsend32 : 0 <= TW.u_at (sd_M1 Bw ncmds) 1808 4 < 2 ^ 32)
  by (pose proof (TWL.u_at_range (sd_M1 Bw ncmds) 1808 4) as R;
      change (8 * Z.of_nat 4) with 32 in R; lia).
assert (BZR : forall x : bv 8, 0 <= DSpec.bz x < 256).
{ intros x. pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. unfold DSpec.bz. lia. }
assert (EB : forall j, (j < 4)%nat ->
  DSpec.bz (Z_to_bv 8 (Z.shiftr (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4)))
                                (8 * Z.of_nat j)))
  = YO0f.le_byte (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) 4 j)
  by (intros j Hj; rewrite (sdh_hdrb _ j Hj); unfold YO0f.le_byte; rewrite ESEND, Zmod_mod;
      reflexivity).
assert (EBn : forall j, (j < 4)%nat -> forall X,
  X = Z.shiftr (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) (8 * Z.of_nat j) ->
  DSpec.bz (Z_to_bv 8 X)
  = YO0f.le_byte (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) 4 j)
  by (intros j Hj X HX; rewrite HX; exact (EB j Hj)).
assert (VHP10 : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms10) (F + 32 + 4 + Z.of_nat j) =
  Some (YO0f.le_byte (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds) 4 j))
  by (intros j Hj; rewrite (KR5d (F + 32 + 4 + Z.of_nat j) ltac:(split; lia)); exact (VHP j Hj)).
assert (VNC10 : aview segs (w_H W) (ms_mem ms10) (F + 47) =
  Some (YO0f.le_byte (bv_swrap 32 ncmds) 1 0))
  by (rewrite (KFR (F + 47) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])); exact VNC).
assert (VZ10 : forall i, 8 <= i < 15 -> aview segs (w_H W) (ms_mem ms10) (F + 32 + i) = Some 0)
  by (intros i Hi; rewrite (KFM (F + 32 + i) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]));
      rewrite (HsetM i ltac:(first [lia | split; lia])); reflexivity).
assert (GHDR : garr8 segs (mrestrict (w_H W) (ms_mem ms10)) (F + 32 + 4)
  (frame_fb_hdr_bytes (TW.u_at (sd_M1 Bw ncmds) 1808 4) 0 0 TS0.DIGINET_CMD_DATA (DSpec.u8 ncmds))).
{ assert (EL : frame_fb_hdr_bytes (TW.u_at (sd_M1 Bw ncmds) 1808 4) 0 0 TS0.DIGINET_CMD_DATA
    (DSpec.u8 ncmds) =
    [DSpec.bz (Z_to_bv 8 (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) 8));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (Z.shiftr
        (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) 8) 8));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (Z.shiftr (Z.shiftr
        (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) 8) 8) 8));
     DSpec.bz (Z_to_bv 8 (bv_unsigned (w64 0)));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (bv_unsigned (w64 0)) 8));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (Z.shiftr (bv_unsigned (w64 0)) 8) 8));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (Z.shiftr (Z.shiftr (bv_unsigned (w64 0)) 8) 8) 8));
     DSpec.bz (Z_to_bv 8 (bv_unsigned (w64 0)));
     DSpec.bz (Z_to_bv 8 (Z.shiftr (bv_unsigned (w64 0)) 8));
     DSpec.bz (DSpec.b8 TS0.DIGINET_CMD_DATA);
     DSpec.bz (DSpec.b8 (DSpec.u8 ncmds))]) by (cbn; reflexivity).
  rewrite EL. intros j Hj. cbn [length] in Hj.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]; cbn [nth]; try (exfalso; cbn in Hj; lia).
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    rewrite (EBn 0%nat ltac:(first [lia | split; lia]) (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4)))
      ltac:(change (8 * Z.of_nat 0) with 0; rewrite Z.shiftr_0_r; reflexivity)).
    exact (VHP10 0%nat ltac:(first [lia | split; lia])).
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    rewrite (EBn 1%nat ltac:(first [lia | split; lia]) (Z.shiftr (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) 8)
      ltac:(change (8 * Z.of_nat 1) with 8; reflexivity)).
    exact (VHP10 1%nat ltac:(first [lia | split; lia])).
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    rewrite (EBn 2%nat ltac:(first [lia | split; lia]) (Z.shiftr (Z.shiftr (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) 8) 8)
      ltac:(rewrite Z.shiftr_shiftr by lia; f_equal; lia)).
    exact (VHP10 2%nat ltac:(first [lia | split; lia])).
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    rewrite (EBn 3%nat ltac:(first [lia | split; lia]) (Z.shiftr (Z.shiftr (Z.shiftr (bv_unsigned (w64 (TW.u_at (sd_M1 Bw ncmds) 1808 4))) 8) 8) 8)
      ltac:(rewrite !Z.shiftr_shiftr by lia; f_equal; lia)).
    exact (VHP10 3%nat ltac:(first [lia | split; lia])).
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 4) with (F + 32 + 8) by lia.
    rewrite (VZ10 8 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 5) with (F + 32 + 9) by lia.
    rewrite (VZ10 9 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 6) with (F + 32 + 10) by lia.
    rewrite (VZ10 10 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 7) with (F + 32 + 11) by lia.
    rewrite (VZ10 11 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 8) with (F + 32 + 12) by lia.
    rewrite (VZ10 12 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 9) with (F + 32 + 13) by lia.
    rewrite (VZ10 13 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 10) with (F + 32 + 14) by lia.
    rewrite (VZ10 14 ltac:(first [lia | split; lia])). reflexivity.
  - split; [|apply BZR]. apply sdh_val1; [apply BZR|].
    replace (F + 32 + 4 + Z.of_nat 11) with (F + 47) by lia.
    rewrite VNC10. f_equal. unfold YO0f.le_byte, DSpec.bz, DSpec.b8, DSpec.u8.
    change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    change (2 ^ 8) with 256. rewrite !Zmod_mod.
    assert (D : (256 | 2 ^ 32)) by (exists (2 ^ 24); reflexivity).
    assert (MM : forall z, z mod 2 ^ 32 mod 256 = z mod 256)
      by (intros z; apply Z.mod_mod_divide; exact D).
    rewrite <- (MM (bv_swrap 32 ncmds)), sdh_swrap32_mod, MM. reflexivity. }
(* +0x17c: diginet_frame_build (out = s + 216, dst = s + 120, src = s, hp, body, mode) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_diginet_frame_build)) mm rom)
    mdx) Q) end.
eapply SRr_bind.
{ eapply (FB0 fx STK sp0 FP ly S W0 mem0 md0 ((SENDDATA_CID, pos) :: own) lyc S2 W (ms_mem ms10) md10 k
    (ms_regs ms10) (SENDDATA_S + 216) (SENDDATA_S + 120) SENDDATA_S (F + 32) bodyp
    (bv_swrap 32 (TW.u_at Bw 1668 4)) (TW.u_at (sd_M1 Bw ncmds) 1808 4) 0 0 TS0.DIGINET_CMD_DATA
    (DSpec.u8 ncmds) (TW.sub (sd_M1 Bw ncmds) 1768 6) (TW.sub (sd_M1 Bw ncmds) 1648 6) body
    (TW.sub (sd_M1 Bw ncmds) 1864 1514)).
  - exact HJ3.
  - rewrite C1. apply (ret_ok_codeptr_v (PI := PI_transport));
    [unfold SD_FB, AF_send_data; lia | unfold SD_FB, AF_send_data; reflexivity].
  - unfold raZ. rewrite C1, unsigned_lit_small by (unfold SD_FB, AF_send_data in *; lia).
    unfold SD_FB, AF_send_data in *. lia.
  - exact C3.
  - exact C4.
  - exact C10.
  - rewrite HOJZ. exact C11.
  - exact C12.
  - exact C13.
  - exact C14.
  - exact C15.
  - transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr regs (12%bv : bv 5)))).
    + exact C16.
    + rewrite Z_to_bv_bv_unsigned. exact H12.
  - exact C17.
  - rewrite Hsp10. exact Hsp1al16.
  - rewrite Hsp10. lia.
  - rewrite Hsp10. lia.
  - unfold SENDDATA_S, TA_g_s. lia.
  - unfold SENDDATA_S, TA_g_s. lia.
  - unfold SENDDATA_S, TA_g_s. lia.
  - lia.
  - left. lia.
  - assert (SW : forall z, bv_swrap 32 z = (z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) by reflexivity.
    rewrite SW.
    pose proof (Z.mod_pos_bound (TW.u_at Bw 1668 4 + 2 ^ 31) (2 ^ 32) ltac:(reflexivity)) as MB.
    change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648 in *. lia.
  - lia.
  - lia.
  - lia.
  - unfold TS0.DIGINET_CMD_DATA. lia.
  - unfold DSpec.u8. pose proof (Z.mod_pos_bound ncmds 256 ltac:(first [lia | split; lia])). lia.
  - rewrite HOJZ. exact HOUT.
  - rewrite HOJZ. exact HTWR.
  - exact GOJ.
  - exact HDML.
  - exact TSD.
  - unfold decode_off_win. rewrite Hsp10. left. unfold SENDDATA_S, TA_g_s in *. lia.
  - exact GDM.
  - exact HSML.
  - exact TSS.
  - unfold decode_off_win. rewrite Hsp10. left. unfold SENDDATA_S, TA_g_s in *. lia.
  - exact GSM.
  - exact TSB.
  - unfold decode_off_win. rewrite Hsp10. destruct HOFFB as [Hx|Hx]; [left; lia | right; lia].
  - exact GBODY.
  - exact HDRF.
  - exact HDRRD.
  - unfold decode_off_win. rewrite Hsp10. left. lia.
  - exact GHDR.
  - rewrite HOJZ. right. unfold SENDDATA_S, TA_g_s. lia.
  - rewrite HOJZ. right. unfold SENDDATA_S, TA_g_s. lia.
  - rewrite HOJZ. destruct FGSEP as [Hx|Hx];
    [right; lia | left; unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia].
  - rewrite HOJZ. exact DISJB.
  - rewrite Hfrs2. cbn [count_cid]. exact Hcnt2.
  - change FRAME_FB_EV with 0. change SENDDATA_EV with 0 in Hev. lia. }
cbv beta. intros W5 c5 _ (ly3 & S3 & regs11 & mem11 & md11 & e3 & -> & He3 & HJ4 & HP4 & Hfr3 & Hperm3
  & HK3 & HMO3 & (HA0F & GOUTF & GKEPTF)).
(* the structural facts of the cut *)
assert (He30 : e3 = 0) by (change FRAME_FB_EV with 0 in He3; lia).
subst e3.
pose proof HJ4 as (_ & _ & (memS4 & HJi4 & _) & _).
pose proof HJi4 as (HAR4 & HLE4 & _).
pose proof HLE4 as (_ & _ & _ & _ & _ & ELF4 & _).
pose proof HLE0i as (_ & _ & _ & _ & _ & ELF0 & _).
assert (ELF : ly_F ly3 = ly_F lyc) by (rewrite ELF4, <- ELF0; reflexivity).
destruct Hset2 as (fsx & Hfsx).
assert (HMO : mo_le MT Sc S3 0).
{ apply (mo_le_set_fs_l MT MTF Sc S3 fsx 0). rewrite <- Hfsx. exact HMO3. }
assert (HFRS : frames S3 = (SENDDATA_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs2).
assert (HPERM : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc))
  by (rewrite <- Eab2; exact Hperm3).
(* what the call kept, over the walk's whole window *)
assert (KEPTF : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W5 mem11
  (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr).
{ eapply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms10) W5 mem11
    (spZ regs - SENDDATA_STK) (spZ regs) (spZ (ms_regs ms10) - FRAME_FB_STK) (spZ (ms_regs ms10))
    senddata_wr
    (fun a => SENDDATA_S + 216 <= a <
       SENDDATA_S + 216 + Z.of_nat (length (TW.sub (sd_M1 Bw ncmds) 1864 1514)))
    (dkg_nf SENDDATA_CID F FL)).
  - lia.
  - lia.
  - reflexivity.
  - intros f Hf. rewrite Hfrs2. right. exact Hf.
  - intros bm Hbm. rewrite Eab2. exact Hbm.
  - exact NB1.
  - exact NB3.
  - exact KEPT10.
  - exact HK3.
  - rewrite Hsp10. lia.
  - rewrite Hsp10. lia.
  - intros a Ha. rewrite HOJZ in Ha. left. right. left. unfold twa_fld.
    unfold SENDDATA_S, TA_g_s, TW.A_S_inflight_frame, TW.OFF_g_s, SENDDATA_CAP in *. lia. }
(* the thirteen saved words, and the frame's flag word, at the cut *)
pose proof HK3 as (L1 & L2 & L3 & L4 & L5 & L6).
assert (KSAV : forall a, spZ regs - 104 <= a < spZ regs ->
  aview segs (w_H W5) mem11 a = aview segs (w_H W) (ms_mem ms1) a).
{ intros a Ha. assert (Hb : 0 <= a < 2 ^ 64) by lia.
  transitivity (aview segs (w_H W) (ms_mem ms10) a);
    [apply (L1 a); [split; lia | rewrite Hsp10; lia] |].
  rewrite (KR5d a Hb), (KR5c a Hb ltac:(first [lia | split; lia])),
    (KR5b a Hb ltac:(unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia)), (KR5a a Hb ltac:(first [lia | split; lia])),
    (HeffM a Hb ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])), (KR4 a Hb ltac:(unfold SHADOW_OFF in *; lia)),
    (KR3 a Hb ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])).
  rewrite (K1a a ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])). apply KR2; lia. }
assert (HSVF : forall (o : Z) (q : bv 5), In (o, q) sdh_saved ->
  rdword (aview segs (w_H W5) mem11) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs q))).
{ intros o q Hin. rewrite <- (HSV o q Hin). apply sdh_rdword_frame.
  intros i Hi. apply KSAV. pose proof (HSVo o q Hin). lia. }
assert (KFLG : aview segs (w_H W5) mem11 = aview segs (w_H W5) mem11) by reflexivity.
assert (HFLW : rdword (aview segs (w_H W5) mem11) (F + 64 - 8) = Some FL).
{ rewrite <- Hflag. apply sdh_rdword_frame. intros i Hi.
  assert (Hb : 0 <= F + 64 - 8 + i < 2 ^ 64) by lia.
  transitivity (aview segs (w_H W) (ms_mem ms10) (F + 64 - 8 + i));
  [apply (L4 SENDDATA_CID pos (F + 64 - 8 + i) ltac:(rewrite Hfrs2; left; reflexivity)
    ltac:(left; unfold in_zr, frame_rng; cbn [fst snd];
          change (fs_frame_bytes SENDDATA_CID) with 64; fold F; lia)
    ltac:(rewrite HOJZ; destruct FGSEP as [FG1|FG1];
          unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia)) |].
  rewrite (KR5d _ Hb), (KR5c _ Hb ltac:(first [lia | split; lia])),
    (KR5b _ Hb ltac:(destruct FGSEP as [FG1|FG1]; unfold SENDDATA_S, TA_g_s, TW.SZ_g_s in *; lia)),
    (KR5a _ Hb ltac:(first [lia | split; lia])), (HeffM _ Hb ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia])),
    (KR4 _ Hb ltac:(destruct FSEP as [FS1|FS1]; unfold SHADOW_OFF in *; lia)).
  apply KR3; lia. }
(* the model's world at the cut *)
assert (LPUT : length (TW.put 4 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds)) = 4%nat)
  by (apply TWL.length_put).
assert (EMODE : bv_swrap 32 (TW.u_at Bw 1668 4) = TW.S_cfg_sum_mode (sd_M1 Bw ncmds)).
{ unfold TW.S_cfg_sum_mode, TW.s32_at. rewrite EAmd, EM1.
  rewrite (TWL.u_at_upd_out Bw (TW.put 4 (bv_swrap 32 (TW.u_at Bw 1808 4) + bv_swrap 32 ncmds))
    1808 1668 4 ltac:(first [lia | split; lia]) ltac:(first [lia | split; lia]) ltac:(rewrite LPUT; left; cbn [Z.of_nat]; lia)
    ltac:(rewrite LPUT, HWLB; unfold TW.W_LEN; cbn [Z.of_nat]; lia)).
  reflexivity. }
assert (EHC : TW.u_at (sd_M1 Bw ncmds) 1808 4 = TW.S_host_counter (sd_M1 Bw ncmds))
  by (unfold TW.S_host_counter; rewrite EAhc; reflexivity).
assert (EDM : TW.sub (sd_M1 Bw ncmds) 1768 6 = TW.S_desk_mac (sd_M1 Bw ncmds)) by reflexivity.
assert (ESM : TW.sub (sd_M1 Bw ncmds) 1648 6 = TW.S_cfg_host_mac (sd_M1 Bw ncmds)) by reflexivity.
assert (ECODE : TNd.diginet_frame_build_code body 1514 (bv_swrap 32 (TW.u_at Bw 1668 4))
  = sd_n Bw ncmds body) by (unfold sd_n; rewrite EMODE; reflexivity).
set (LOUT := PBuildW.build_out_w (TW.sub (sd_M1 Bw ncmds) 1768 6) (TW.sub (sd_M1 Bw ncmds) 1648 6)
  (TW.u_at (sd_M1 Bw ncmds) 1808 4) 0 0 TS0.DIGINET_CMD_DATA (DSpec.u8 ncmds) body
  (bv_swrap 32 (TW.u_at Bw 1668 4)) (TW.sub (sd_M1 Bw ncmds) 1864 1514)) in *.
set (LFv := DLib.lib_frame (TW.sub (sd_M1 Bw ncmds) 1768 6) (TW.sub (sd_M1 Bw ncmds) 1648 6)
  (TW.u_at (sd_M1 Bw ncmds) 1808 4) 0 0 TS0.DIGINET_CMD_DATA (DSpec.u8 ncmds) body
  (bv_swrap 32 (TW.u_at Bw 1668 4))) in *.
assert (ELOUT : LOUT = (if 0 <=? sd_n Bw ncmds body
   then LFv ++ skipn (Z.to_nat (sd_n Bw ncmds body)) (TW.sub (sd_M1 Bw ncmds) 1864 1514)
   else TW.sub (sd_M1 Bw ncmds) 1864 1514)).
{ unfold LOUT, LFv. rewrite sdh_bout_eq, HOJZ, ECODE. reflexivity. }
assert (LFACT : 0 <= sd_n Bw ncmds body ->
  Z.of_nat (length LFv) = sd_n Bw ncmds body /\ (length body <= 1484)%nat /\
  sd_n Bw ncmds body = DSpec.frame_len (length body)).
{ intros HP.
  assert (HC : 0 <= TNd.diginet_frame_build_code body 1514 (bv_swrap 32 (TW.u_at Bw 1668 4)))
    by (rewrite ECODE; exact HP).
  destruct (sdh_bc_val body 1514 (bv_swrap 32 (TW.u_at Bw 1668 4)) HC) as (LN & LB).
  split; [|split; [exact LB | rewrite <- ECODE; exact LN]].
  unfold LFv.
  rewrite (sdh_length_lib_frame (TW.sub (sd_M1 Bw ncmds) 1768 6) (TW.sub (sd_M1 Bw ncmds) 1648 6)
    (TW.u_at (sd_M1 Bw ncmds) 1808 4) 0 0 TS0.DIGINET_CMD_DATA (DSpec.u8 ncmds) body
    (bv_swrap 32 (TW.u_at Bw 1668 4)) HDML HSML
    (sdh_bc_mode body 1514 (bv_swrap 32 (TW.u_at Bw 1668 4)) HC)).
  rewrite <- LN. exact ECODE. }
assert (LLOUT : length LOUT = 1514%nat).
{ rewrite ELOUT. destruct (Z.leb_spec 0 (sd_n Bw ncmds body)) as [HP|HP]; [|exact HOJL].
  destruct (LFACT HP) as (LF & LB & LFL).
  rewrite length_app, length_skipn, HOJL.
  unfold DSpec.frame_len in *. lia. }
assert (EB2 : TW.upd (sd_M1 Bw ncmds) 1864 LOUT = sd_Bfb Bw ncmds body).
{ rewrite ELOUT. unfold sd_Bfb.
  destruct (Z.leb_spec 0 (sd_n Bw ncmds body)) as [HP|HP].
  - destruct (LFACT HP) as (LF & LB & LFL).
    assert (LFN : length LFv = Z.to_nat (sd_n Bw ncmds body)) by lia.
    rewrite <- LFN.
    rewrite (sdh_upd_app_tail (sd_M1 Bw ncmds) LFv 1864 1514 ltac:(first [lia | split; lia])
      ltac:(assert (HL : Z.of_nat (length (sd_M1 Bw ncmds)) = TW.W_LEN) by exact HWL;
            unfold TW.W_LEN in HL; lia) ltac:(unfold DSpec.frame_len in *; lia)).
    unfold sd_B2, TW.set_S_inflight_frame, sd_LF, LFv.
    rewrite EDM, ESM, EHC, EMODE. reflexivity.
  - apply TWL.upd_sub_id; [lia | rewrite HWL; unfold TW.W_LEN; cbn [Z.of_nat]; lia]. }
assert (HTWF : tw_at TMAP_A (aview segs (w_H W5) mem11) (sd_Bfb Bw ncmds body)).
{ rewrite <- EB2. replace 1864 with (TW.OFF_g_s + 216) by reflexivity.
  apply (tw_upd TMAP_A (aview segs (w_H W) (ms_mem ms10)) (aview segs (w_H W5) mem11)
    (sd_M1 Bw ncmds) TW.OFF_g_s TA_g_s TW.SZ_g_s 216 LOUT TMAP_A_ok HTW10 TMAP_A_g_s
    ltac:(first [lia | split; lia]) ltac:(rewrite LLOUT; unfold TW.SZ_g_s; cbn [Z.of_nat]; lia)).
  - intros j Hj.
    pose proof (garr8_mbyte segs (mrestrict (w_H W5) mem11) (SENDDATA_S + 216)
      (map DSpec.bz LOUT) j GOUTF ltac:(rewrite length_map; lia)) as Hm.
    change (aview segs (w_H W5) mem11 (TA_g_s + 216 + Z.of_nat j))
      with (option_map (fun b : byte => bv_unsigned b)
            (YP09.mbyte segs (mrestrict (w_H W5) mem11) (TA_g_s + 216 + Z.of_nat j))).
    replace (TA_g_s + 216 + Z.of_nat j) with (SENDDATA_S + 216 + Z.of_nat j)
      by (unfold SENDDATA_S; lia).
    rewrite Hm. cbn [option_map]. f_equal.
    rewrite (nth_indep (map DSpec.bz LOUT) 0 (DSpec.bz (Z_to_bv 8 0)) ltac:(rewrite length_map; exact Hj)).
    rewrite (map_nth DSpec.bz LOUT (Z_to_bv 8 0) j).
    pose proof (BZR (nth j LOUT (Z_to_bv 8 0))) as Hb.
    unfold DSpec.bz in *. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
  - intros x Hx Hout. destruct Hx as (o & b & n & Hin3 & Hxr).
    assert (HxG : W_journalG.inG TG.G_HARNESS x)
      by (unfold W_journalG.inG; apply Exists_exists; exists (b, n);
          split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]).
    apply (GKEPTF x HxG). rewrite LLOUT in Hout. rewrite HOJZ.
    unfold SENDDATA_S, TA_g_s in *. lia. }
(* the slot the mid piece reads, and the read-only view *)
assert (HSNF : rdword (aview segs (w_H W5) mem11) (sp1 + 16) = Some now).
{ rewrite <- HSN9. apply sdh_rdword_frame. intros i Hi.
  transitivity (aview segs (w_H W) (ms_mem ms10) (sp1 + 16 + i));
    [apply (L1 (sp1 + 16 + i)); [split; lia | rewrite Hsp10; lia] |].
  apply KR5d. split; lia. }
assert (HROMF : trans_rom_view_rd W5 mem11).
{ intros a Ha.
  destruct (trans_ro_rd_bounds a Ha) as (HR1 & HR2).
  assert (HnG : ~ W_journalG.inG TG.G_HARNESS a).
  { intros Hc. pose proof (inG_G_HARNESS_hull a Hc) as Hh. unfold TG.G_HARNESS_LO in Hh. lia. }
  transitivity (aview segs (w_H W) (ms_mem ms10) a);
  [apply (L3 a (trans_ro_img a Ha) HnG (proj1 (trans_ro_rd_scoped B HRU HRE a Ha))
    (proj2 (trans_ro_rd_scoped B HRU HRE a Ha))) |].
  assert (Hb : 0 <= a < 2 ^ 64) by lia.
  rewrite (KCH a Hb ltac:(left; lia)
    ltac:(intros Hc; apply (NB2 a Hc); exact (trans_ro_img a Ha))
    ltac:(unfold SENDDATA_S, TA_g_s in *; lia)).
  rewrite (K1c a (trans_ro_img a Ha) (proj1 (trans_ro_rd_scoped B HRU HRE a Ha))
    (proj2 (trans_ro_rd_scoped B HRU HRE a Ha))).
  rewrite (KR2 a Hb ltac:(first [lia | split; lia])), (KR1 a Hb ltac:(first [lia | split; lia])).
  exact (Hrom a Ha). }
(* the registers at the cut *)
assert (RK3 : YK11.getr regs11 3 = YK11.getr regs 3).
{ transitivity (YK11.getr (ms_regs ms10) 3); [exact (HP4 3 ltac:(unfold acallee_saved; lia)) |].
  rewrite C3, Hgp. reflexivity. }
assert (RK4 : YK11.getr regs11 4 = YK11.getr regs 4).
{ transitivity (YK11.getr (ms_regs ms10) 4); [exact (HP4 4 ltac:(unfold acallee_saved; lia)) |].
  rewrite C4, Htp. reflexivity. }
assert (RK8 : YK11.getr regs11 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms10) 8);
      [exact (HP4 8 ltac:(unfold acallee_saved; lia)) | exact C8]).
assert (RK18 : YK11.getr regs11 18 = w64 F)
  by (transitivity (YK11.getr (ms_regs ms10) 18);
      [exact (HP4 18 ltac:(unfold acallee_saved; lia)) | exact C18]).
assert (RK26 : YK11.getr regs11 26 = w64 F)
  by (transitivity (YK11.getr (ms_regs ms10) 26);
      [exact (HP4 26 ltac:(unfold acallee_saved; lia)) | exact C26]).
assert (RK27 : YK11.getr regs11 27 = w64 (SHADOW_OFF + F / 8))
  by (transitivity (YK11.getr (ms_regs ms10) 27);
      [exact (HP4 27 ltac:(unfold acallee_saved; lia)) | exact C27]).
assert (RK2 : YK11.getr regs11 2 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs ms10) 2);
      [exact (HP4 2 ltac:(unfold acallee_saved; lia)) | exact C2]).
assert (RK9 : YK11.getr regs11 9 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs ms10) 9);
      [exact (HP4 9 ltac:(unfold acallee_saved; lia)) | exact C9]).
assert (RK19 : YK11.getr regs11 19 = w64 SENDDATA_S)
  by (transitivity (YK11.getr (ms_regs ms10) 19);
      [exact (HP4 19 ltac:(unfold acallee_saved; lia)) | exact C19]).
assert (RK20 : YK11.getr regs11 20 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms10) 20);
      [exact (HP4 20 ltac:(unfold acallee_saved; lia)) | exact C20]).
assert (RK21 : YK11.getr regs11 21 = w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8))
  by (transitivity (YK11.getr (ms_regs ms10) 21);
      [exact (HP4 21 ltac:(unfold acallee_saved; lia)) | exact C21]).
assert (RK23 : YK11.getr regs11 23 = w64 (SENDDATA_S + 216))
  by (transitivity (YK11.getr (ms_regs ms10) 23);
      [exact (HP4 23 ltac:(unfold acallee_saved; lia)) | exact C23]).
assert (RK25 : YK11.getr regs11 25 = w64 (SENDDATA_S + 160))
  by (transitivity (YK11.getr (ms_regs ms10) 25);
      [exact (HP4 25 ltac:(unfold acallee_saved; lia)) | exact C25]).
assert (RA0 : YK11.getr regs11 10 = w64 (sd_n Bw ncmds body))
  by (rewrite HA0F, HOJZ, sdh_bcw_eq, ECODE; reflexivity).
(* the three records the cut file names *)
assert (ESP1 : sp1 = 32 * ((spZ regs - SENDDATA_FRAME) / 32))
  by (unfold SENDDATA_FRAME; replace (spZ regs - 160) with (spZ regs + -160) by lia; reflexivity).
assert (HFIX : sd_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body
  TF Bw Bwf pos sp1 F).
{ unfold sd_fix. exact (conj HJENT (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj Hsp16 (conj Hlo (conj Hhi (conj Hnc (conj Hnow (conj Hbodyp (conj Hgarr (conj Hsrc (conj Hoffw (conj HbodyG (conj Htw (conj Hgf (conj Hmodel (conj Hrom (conj Hinv1 (conj Hinv4 (conj Hcnt0 (conj Hcnt2 (conj Hev (conj ESP1 (conj eq_refl (conj HF0 (conj HF64 (conj HFc (HFapp))))))))))))))))))))))))))))))))))). }
assert (HCUR : sd_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pos F ly3 S3 W5 mem11 md11 0).
{ unfold sd_cur.
  assert (HE0 : 0 <= 0 <= SENDDATA_EV) by (change SENDDATA_EV with 0; lia).
  assert (HSAVF : Forall (fun o : Z * Z =>
      rdword (aview segs (w_H W5) mem11) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SD_SAVED).
  { unfold SD_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    match goal with
    | |- rdword _ (spZ regs - ?o) = _ => replace (spZ regs - o) with (spZ regs + - o) by lia
    end;
    first [ exact (HSVF (-8) (1%bv) ltac:(sdh_in)) | exact (HSVF (-16) (8%bv) ltac:(sdh_in)) | exact (HSVF (-24) (9%bv) ltac:(sdh_in)) | exact (HSVF (-32) (18%bv) ltac:(sdh_in)) | exact (HSVF (-40) (19%bv) ltac:(sdh_in)) | exact (HSVF (-48) (20%bv) ltac:(sdh_in)) | exact (HSVF (-56) (21%bv) ltac:(sdh_in)) | exact (HSVF (-64) (22%bv) ltac:(sdh_in)) | exact (HSVF (-72) (23%bv) ltac:(sdh_in)) | exact (HSVF (-80) (24%bv) ltac:(sdh_in)) | exact (HSVF (-88) (25%bv) ltac:(sdh_in)) | exact (HSVF (-96) (26%bv) ltac:(sdh_in)) | exact (HSVF (-104) (27%bv) ltac:(sdh_in)) ]. }
  exact (conj HJ4 (conj HE0 (conj HFRS (conj HPERM (conj ELF (conj HMO
    (conj KEPTF (conj HSAVF HFLW)))))))). }
assert (HREGS : sd_regs_fb regs regs11 sp1 F (sd_n Bw ncmds body)).
{ unfold sd_regs_fb, sd_regs_keep. repeat apply conj; assumption. }
rewrite C1.
exact (FB (conj HPCS (conj HCELLS (conj HSDC (conj HGU (conj HGE (conj HRU (conj HRE (conj LAWS
    (conj MTL (conj MTF (conj SMP (conj ASF (conj FFL (conj (G_HARNESS_gx_ok B HGU)
    (G_HARNESS_gx_noerrno B HGE))))))))))))))) IOS0
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body TF Bw
  Bwf pos sp1 F ly3 S3 W5 mem11 md11 0 regs11
  HFIX (conj HCUR (conj HTWF (conj HROMF HSNF))) HREGS).
Qed.

End head.

Print Assumptions sd_head.
