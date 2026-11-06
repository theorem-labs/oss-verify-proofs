(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bBase.v and RPgEntBKit.v at f3898085bda
   (the block statements of ent_build's cases 1, 4, 5 and 9 and the engine kit of their walk) for
   reac-pw/fuzz_headamp's image B: image B's pcs, registers (the cursor in s2, what is left in s4 and t1, the
   shadow offset in s11), real-frame cells (R+0x40, R+0xe8, R+0x118, R+0x130, R+0x138, R+0x148 read; R+0x58,
   R+0x110 written by case 1), the e62 pod object at F+0x210, the class-4 frame, the join's post through
   HPgSteps.hdu_blk_postE and HPgCaseBJ.cj_J_R, image B's ent_build.s and ent_build.vocab, and image B's code
   table. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the BLOCK STATEMENTS of the
   walk piece W6b of LLVMFuzzerTestOneInput (0x80c40): the cases 1, 4, 5 and 9 of ent_build's `switch (kind % 10)`
   (pod.h:285-296, 326-339, 367-377), each from its entry to the join J 0x82618, and the engine kit their walks
   share. Statement text only: no function is proved here (kind: segment lemma).

   ONE BLOCK PER CASE, so that a case is proved without the cut records of lib/AU/HPgSeg.v and the piece is the
   case's block between the two cut bridges of lib/AU/HPgCaseBJ.v (cj_D_facts / cj_D_input / cj_D_img at the entry,
   cj_J_post at the join).
     hw6b_c4  0x81c68 .. J: v = fuzz_u8 % 3 (pod.h:327-330); no byte left: 0x82078.
     hw6b_c5  0x81e6c .. J: n = min(fuzz_u8 % 32, left), __asan_memcpy(e62.body, cursor, n) at 0x81ec4, the NUL
              unless kind & 0x80 (pod.h:336-337, 209-219); no byte left: 0x82214.
     hw6b_c9  0x82004 .. J: e62.type = 14, body[0..8) = 14, 8, __asan_memcpy(e62.body + 8, s, 14) at 0x82054,
              e62.size = 24 (pod.h:369-375); no input read.
     hw6b_c1  0x81e04 .. J: i = fuzz_u8 % 9, the 8-byte load of vocab[i] (0x8212c), the strlen wrapper at 0x82134,
              __asan_memcpy at 0x82158, the NUL, and with kind & 0x80 (and len <= 93) the two checked byte stores
              'x', 0 (pod.h:286-294); no byte left: 0x820f8.
   THE STATE AT A CASE ENTRY (HPgSeg.hsu_L_D, checked against the code): s1 = R (x9) the real frame's base,
   sp = R, s11 = SHADOW_OFF (x27), s2 = c (x18) the cursor after the kind byte, a7 = c - 1 (x17), t1 = |r| + 1 (x6),
   s4 = |r| (x20) what is left after it, a6 = 1 (x16), a3 = the kind byte sign-extended (x13, not on case 9: `bltu`
   0x81924 jumps before the table's 0x81928); [R+0x40] = F + 0x220 (&e62.body[8]), [R+0xe8] = -(F + 0x219) mod 2^64
   (the complement the pointer-overflow tests of pod.h:215 compare against), [R+0x118] = F + 0x218 (&e62.body),
   [R+0x130] = F + 0x210 (&e62), [R+0x138] = pp + 0x4000 (&pp->len), [R+0x148] = pp; e62 = 104 zero bytes with its
   13 shadow granules 0 (in scope).
   THE STATE AT J (HPgSeg.hsu_cut_J, HPgCaseBJ.cj_J_R): a3 = the cursor after the pod (x13), t1 = what is left (x6),
   s2 = pp + 0x4000 (x18, `ld s2,0x138(s1)` 0x82614), s4 = F + 0x210 (x20), s7 = pp (x23); e62 = Layout.ent_mem of
   the pod; the registers outside hw6b_clob as at the entry; every byte outside HPgCaseBJ.cj_wr R F hw6b_ws (the
   callees' stack below R, R+0x58 and R+0x110 (case 1's spills of the kind byte and the cursor), e62) as at the
   entry. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSteps HPgCaseB HPgCaseBJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition HB_D1 : Z := 0x81e04.     (* jt_tgt 1 *)
Definition HB_D4 : Z := 0x81c68.     (* jt_tgt 4 *)
Definition HB_D5 : Z := 0x81e6c.     (* jt_tgt 5 *)
Definition HB_D9 : Z := 0x82004.     (* `bltu a2,a1` 0x81924 taken *)
Definition HB_J : Z := 0x82618.      (* the join: the reload of &pp->len's shadow address before pod_write_ent *)
Definition HB_MEMCPY : Z := 0x51d8c. (* __asan_memcpy, the `jal` target at 0x81ec4, 0x82054, 0x82158 *)
Lemma hb_pcs : hsu_pc_D headamp_bld_B 1 = HB_D1 /\ hsu_pc_D headamp_bld_B 4 = HB_D4 /\
  hsu_pc_D headamp_bld_B 5 = HB_D5 /\ hsu_pc_D headamp_bld_B 9 = HB_D9 /\ bi_J headamp_bld_B = HB_J.
Proof. repeat split. Qed.
(* the image's data the cases read: ent_build.s (case 9's memcpy source, 14 bytes) and ent_build.vocab (nine
   8-byte pointer cells in .data.rel.ro, each the address of one vocab string in .rodata) *)
Definition HB_S : Z := 0x21160.
Definition HB_VOCAB : Z := 0x9c4e0.
Definition hb_vptr (i : Z) : Z :=
  nth (Z.to_nat i) [0x20f00; 0x20f20; 0x20f40; 0x20f60; 0x20f80; 0x20fa0; 0x20fe0; 0x21000; 0x21020] 0.
(* the nine pointer cells and their strings are image B's record's (HPgImgB headamp_B_cells, headamp_B_strs) *)
Lemma hb_vocab_cells : forall i, 0 <= i < 9 -> In (HB_VOCAB + 8 * i, hb_vptr i) headamp_B_cells.
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct E as [E|E]; [subst i; vm_compute; tauto|]). subst i. vm_compute. tauto.
Qed.
Lemma hb_vocab_strs : forall i, 0 <= i < 9 -> In (hb_vptr i, hd_zbytes (nth (Z.to_nat i) vocab [])) headamp_B_strs.
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct E as [E|E]; [subst i; vm_compute; tauto|]). subst i. vm_compute. tauto.
Qed.
Lemma hb_s_str : In (HB_S, hd_zbytes S9) headamp_B_strs.
Proof. vm_compute. tauto. Qed.
Lemma hb_vocab_glob : In (HB_VOCAB, 72) headamp_B_globs.
Proof. vm_compute. tauto. Qed.

(* ======================================== the code table ========================================
   Every instruction word of [0x81c68, 0x8261c): the four cases' fast paths, their tails and the join's
   first instruction; the second tests of their input checks [0x827ec, 0x82858); the error-path entry 0x83c44 of
   the vocab cell's check and the two `unimp` words 0x83a10 / 0x83a14 the pointer-overflow tests branch to (never
   stepped: each such branch is shown not taken). Precomputed once. *)
Definition hb_tbl : ctable :=
  Eval vm_compute in
    build_table rsegs 0x83a10 2 (build_table rsegs 0x83c44 1
      (build_table rsegs 0x827ec 27 (build_table rsegs 0x81c68 621 TEmpty))).
Lemma hb_tbl_ok : table_ok rsegs hb_tbl.
Proof.
  change hb_tbl with (build_table rsegs 0x83a10 2 (build_table rsegs 0x83c44 1
      (build_table rsegs 0x827ec 27 (build_table rsegs 0x81c68 621 TEmpty)))).
  apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
  apply build_table_ok0. lia.
Qed.

(* ======================================== the shadow machinery ========================================
   s11 holds the runtime's shadow offset (atom 27); e62 is covered by one shadow entry over atom 32 = F. *)
Definition HBx : sv := SOff 27 0.
Definition HBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition hb_SH : list shent := [mkSHE 32 0x210 0x278].

(* the registers a case may change (cj_clob_ok: none of hsu_Rc0's, sp, gp, tp) and the real-frame cells it writes
   (cj_ws_ok: R+0x58 and R+0x110, cells of no cut list) *)
Definition hw6b_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 23; 26; 28; 29; 30; 31]%bv.
Definition hw6b_ws : list Z := [0x58; 0x110].
Lemma hw6b_clob_ok : cj_clob_ok hw6b_clob = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hw6b_ws_ok : cj_ws_ok hw6b_ws = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the context every block runs in =====================
   The image-B case kit's block context (lib/AU/HPgCaseB.v cb_ctx): the harness's journal from the segment's start
   (hd_seg_pre's first conjunct), the real frame [R, R + 0x220) inside the journal's stack window with the callees'
   stack below it, the frame for locals F = the side-stack frame (4, pos) the harness holds, and the read-only
   segments as in the image (hd_seg_pre's rom_view). *)
Definition hw6b_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos.

(* the input bytes r at cursor c: bytes, shadow, ranges, and apart from the callees' stack and M01's real-frame
   range *)
Definition hw6b_inp (W : world rsegs) (memc : word -> option byte) (R c : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) c (hd_zbytes r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c (Z.of_nat (length r)) /\
0 < c /\ c + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range c (Z.of_nat (length r)) /\
(forall a, c <= a < c + Z.of_nat (length r) -> ~ (R - T_SEG_STK <= a < R + 0x198)).

(* ===================== the state at a case entry =====================
   kd is the kind byte, c the cursor after it, r the input after it. *)
Definition hw6b_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F c pp kd : Z)
(r : list byte) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 27 = w64 SHADOW_OFF /\
getr regs 18 = w64 c /\ getr regs 17 = w64 (c - 1) /\
getr regs 6 = w64 (Z.of_nat (length r) + 1) /\ getr regs 20 = w64 (Z.of_nat (length r)) /\
getr regs 16 = w64 1 /\
(kd mod 10 <> 9 -> getr regs 13 = w64 (kd - 256 * (kd / 128))) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x40) 8 (F + 0x220) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((- (F + 0x219)) mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp /\
0 <= kd < 256 /\ 4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling /\
4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 32 = 0 /\ alloc_ceiling + T_SEG_STK <= R /\
(forall o, 0 <= o < 1024 -> apresent (w_H W) memc (F + o)) /\
(forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x210 + i) = Some (Z_to_bv 8 0)) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 /\
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 /\
0 < c - 1 /\ hw6b_inp W memc R c r /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) c (Z.of_nat (length r))) /\
(forall a, c <= a < c + Z.of_nat (length r) -> ~ (F + 0x20 <= a < F + 0x278)).

(* ===================== the case block =====================
   P picks the case by kind % 10; X is what the case reads of the image besides the code. The post is the
   journal-form block post at J (HPgSteps.hdu_blk_postE) with the registers hw6b_clob, the bytes
   cj_wr R F hw6b_ws, and the join's values cj_J_R of the turn's input b :: r. *)
Definition hw6b_case_stmt (pc : Z) (P : Z -> Prop) (X : world rsegs -> (word -> option byte) -> Prop) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c pp : Z)
  (b : byte) (r : list byte),
hw6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
P (bv_unsigned b) ->
hw6b_in W memc regs R F c pp (bv_unsigned b) r ->
X W memc ->
SRr rsegs W (cfg_at rsegs pc regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HB_J hw6b_clob (cj_wr R F hw6b_ws)
  (cj_J_R R F pp c r (b :: r))).

(* case 9 reads ent_build.s (a registered global of 14 bytes, the text "reac.cfg.rate" and its NUL) *)
Definition hw6b_s_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
hd_cstr rsegs (w_H W) memc HB_S (hd_zbytes S9).
(* case 1 reads vocab[i] (the registered table of 72 bytes) and the string it points to *)
Definition hw6b_vocab_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF HB_VOCAB 72 /\
(forall i, 0 <= i < 9 ->
  val_mem rsegs (mrestrict (w_H W) memc) (HB_VOCAB + 8 * i) 8 (hb_vptr i) /\
  hd_cstr rsegs (w_H W) memc (hb_vptr i) (hd_zbytes (nth (Z.to_nat i) vocab []))).

Definition hw6b_c4_stmt : Prop := hw6b_case_stmt HB_D4 (fun kd => kd mod 10 = 4) (fun _ _ => True).
Definition hw6b_c5_stmt : Prop := hw6b_case_stmt HB_D5 (fun kd => kd mod 10 = 5) (fun _ _ => True).
Definition hw6b_c9_stmt : Prop := hw6b_case_stmt HB_D9 (fun kd => kd mod 10 = 9) hw6b_s_ok.
Definition hw6b_c1_stmt : Prop := hw6b_case_stmt HB_D1 (fun kd => kd mod 10 = 1) hw6b_vocab_ok.

End d.

(* ======================================== the engine kit ========================================
   THE SYMBOLIC STATE AT A CASE ENTRY. The registers are their own atoms (sr_atoms). The extra atoms are
     32 = F (the frame for locals), 33 = pp, 34 = [R+0xe8] = -(F + 0x219) mod 2^64, 35 = the next input byte (0 when
     none is left).
   The regions are R-based (atom 9 = s1 = R) and F-based (atom 32):
     A  [R+0x40, R+0x58)   read only: R+0x40 = F+0x220
     B  [R+0x58, R+0x60)   written (case 1's spill of the kind byte, 0x8210c)
     C  [R+0x60, R+0x110)  read only: R+0xe8 = atom 34
     D  [R+0x110, R+0x118) written (case 1's spill of the cursor, 0x82110)
     E  [R+0x118, R+0x150) read only: R+0x118 = F+0x218, R+0x130 = F+0x210, R+0x138 = pp+0x4000, R+0x148 = pp
     F  [F+0x210, F+0x278) written: e62, all zero (ent_build's memset)
     I  [s2, s2+1)         read only: the next input byte, atom 35 (only when one is left)
   The other R-relative cells lie outside every region, so a run keeps them (frame_of).
   THE FACTS. R in [alloc_ceiling's floor, 2^47], 16-aligned; s11 = K; the cursor in [1, 2^47 - 1]; F in
   [4096, alloc_ceiling's ceiling]; atom 34 in [2^64 - 0x7fffff800000 - 0x219, 2^64 - 4096 - 0x219]. *)
Definition hb_extra (F pp e8 b : Z) : list word := [Z_to_bv 64 F; Z_to_bv 64 pp; Z_to_bv 64 e8; Z_to_bv 64 b].
Definition hb_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x58 0 0 [YP09.mkChunk 0x40 (CVal 8 (SOff 32 0x220))].
Definition hb_rB : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0x58 0x60 [].
Definition hb_rC : YP09.region := YP09.mkRegion (Some 9%nat) 0x60 0x110 0 0 [YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0))].
Definition hb_rD : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x118 0x110 0x118 [].
Definition hb_rE : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x150 0 0
  [ YP09.mkChunk 0x118 (CVal 8 (SOff 32 0x218)); YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210));
    YP09.mkChunk 0x138 (CVal 8 (SOff 33 0x4000)); YP09.mkChunk 0x148 (CVal 8 (SOff 33 0)) ].
Definition hb_rF : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x278 0x210 0x278 [YP09.mkChunk 0x210 (CZero 104)].
Definition hb_rI : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition hb_regions (byte : bool) : smem :=
  if byte then [hb_rA; hb_rB; hb_rC; hb_rD; hb_rE; hb_rF; hb_rI] else [hb_rA; hb_rB; hb_rC; hb_rD; hb_rE; hb_rF].
Definition HB_E8LO : Z := 2 ^ 64 - 0x7fffff800000 - 0x219.
Definition HB_E8HI : Z := 2 ^ 64 - 4096 - 0x219.
Definition hb_atoms : list (nat * afact) :=
  [ (9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (18%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF 4096 0x7fffff800000 0);
    (34%nat, mkAF HB_E8LO HB_E8HI 0) ].
Definition ss_hb (pc : Z) (byte : bool) : sstate :=
  mkSS pc sr_atoms (hb_regions byte) None (mkFacts hb_atoms [] []).

Lemma hb_wx : wx_segs_nowrap rsegs.
Proof. exact img_wx. Qed.
Lemma hb_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact img_segs_low. Qed.

(* the value of an extra atom *)
Lemma hb_U_reg : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.

(* -(F + 0x219) mod 2^64 lies in atom 34's interval *)
Lemma hb_e8_range : forall {rc' : YM05.RunCeil} F, 4096 <= F -> F + 1024 <= alloc_ceiling ->
  HB_E8LO <= (- (F + 0x219)) mod 2 ^ 64 <= HB_E8HI.
Proof.
  intros rc' F H1 H2. pose proof (@asan_consts rc') as (Hc & _).
  replace ((- (F + 0x219)) mod 2 ^ 64) with (2 ^ 64 - (F + 0x219)).
  - unfold HB_E8LO, HB_E8HI. lia.
  - apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(* ---- the entry state ---- *)
Lemma hb_entry : forall pc (byte : bool) (W : world rsegs) (regs : bvmap 5 word) memc (R F cur pp b : Z),
  0 <= pc ->
  getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 cur ->
  alloc_ceiling <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
  4096 <= F -> F + 1024 <= alloc_ceiling ->
  1 <= cur <= 2 ^ 47 - 1 -> 0 <= b < 256 ->
  0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x40) 8 (F + 0x220) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((- (F + 0x219)) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  (forall o, (0x58 <= o < 0x60 \/ 0x110 <= o < 0x118) -> apresent (w_H W) memc (R + o)) ->
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x210 + i) = Some (Z_to_bv 8 0)) ->
  (forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0x210 + o)) ->
  (byte = true -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b /\ (cur + 1 <= R + 0x40 \/ R + 0x150 <= cur) /\
                  (cur + 1 <= F + 0x210 \/ F + 0x278 <= cur)) ->
  st_ok rsegs (Ereg regs (hb_extra F pp ((- (F + 0x219)) mod 2 ^ 64) b)) (ss_hb pc byte)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
  intros pc byte W regs memc R F cur pp b Hpc H9 H27 H18 HR1 HR2 HR3 HF1 HF2 Hc Hb Hpp1 Hpp2
    V40 Ve8 V118 V130 V138 V148 Pw Ez Pe Hbyte.
  pose proof (@asan_consts rc) as (Hceil & _).
  pose proof (hb_e8_range F HF1 HF2) as He8.
  set (e8 := (- (F + 0x219)) mod 2 ^ 64) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs (hb_extra F pp e8 b)).
  assert (U9 : bv_unsigned (ew E 9) = R) by (exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
    by (exact (hb_U_reg regs _ 27 27%bv _ eq_refl H27 ltac:(unfold SHADOW_OFF; lia))).
  assert (U18 : bv_unsigned (ew E 18) = cur) by (exact (hb_U_reg regs _ 18 18%bv cur eq_refl H18 ltac:(lia))).
  assert (U32 : bv_unsigned (ew E 32) = F).
  { subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth hb_extra]. apply unsigned_lit_small. lia. }
  assert (U33 : bv_unsigned (ew E 33) = pp).
  { subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth hb_extra]. apply unsigned_lit_small. lia. }
  assert (U34 : bv_unsigned (ew E 34) = e8).
  { subst E. rewrite (ew_Ereg_extra regs _ 2). cbn [nth hb_extra]. apply unsigned_lit_small.
    unfold HB_E8LO, HB_E8HI in He8. lia. }
  assert (U35 : bv_unsigned (ew E 35) = b).
  { subst E. rewrite (ew_Ereg_extra regs _ 3). cbn [nth hb_extra]. apply unsigned_lit_small. lia. }
  assert (RA : region_ok rsegs E (mrestrict (w_H W) memc) hb_rA).
  { unfold region_ok, hb_rA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val rsegs E _ R 0x40 8 (SOff 32 0x220) (F + 0x220));
      [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V40]. }
  assert (RB : region_ok rsegs E (mrestrict (w_H W) memc) hb_rB).
  { unfold region_ok, hb_rB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Pw. lia. }
  assert (RC : region_ok rsegs E (mrestrict (w_H W) memc) hb_rC).
  { unfold region_ok, hb_rC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val rsegs E _ R 0xe8 8 (SOff 34 0) e8);
      [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64;
       unfold HB_E8LO, HB_E8HI in He8; lia | lia | exact Ve8]. }
  assert (RD : region_ok rsegs E (mrestrict (w_H W) memc) hb_rD).
  { unfold region_ok, hb_rD. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Pw. lia. }
  assert (RE : region_ok rsegs E (mrestrict (w_H W) memc) hb_rE).
  { unfold region_ok, hb_rE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val rsegs E _ R 0x118 8 (SOff 32 0x218) (F + 0x218));
        [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V118].
    - apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 32 0x210) (F + 0x210));
        [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V130].
    - apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 33 0x4000) (pp + 0x4000));
        [cbn [sv_denot]; rewrite U33; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V138].
    - apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 33 0) pp);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V148]. }
  assert (RF : region_ok rsegs E (mrestrict (w_H W) memc) hb_rF).
  { unfold region_ok, hb_rF. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); replace (F + o) with (F + 0x210 + (o - 0x210)) by lia; apply Pe; lia|].
    apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
    apply Ez. exact Hi. }
  unfold ss_hb. apply (entry_st_ok_full rsegs); try change (Ereg regs (hb_extra F pp e8 b)) with E.
  - apply regs_ok_Ereg.
  - destruct byte; vm_compute; reflexivity.
  - destruct byte; unfold hb_regions; repeat apply Forall_cons; try apply Forall_nil; try assumption.
    destruct (Hbyte eq_refl) as (Vb & _ & _).
    unfold region_ok, hb_rI. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs E _ cur 0 1 (SOff 35 0) b);
      [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | change (8 * Z.of_N 1) with 8; lia | lia |].
    rewrite Z.add_0_r. exact Vb.
  - destruct byte; unfold hb_regions; apply pairwise_disjoint_of_extents;
      unfold hb_rA, hb_rB, hb_rC, hb_rD, hb_rE, hb_rF, hb_rI; cbn [map]; unfold extent_of_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
      try change (Ereg regs (hb_extra F pp e8 b)) with E; rewrite ?U9, ?U32, ?U18.
    + destruct (Hbyte eq_refl) as (_ & D1 & D2). repeat split; first [exact I | lia].
    + repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [hb_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U27, U18, U32, U34. repeat split; try lia;
      first [change (2 ^ 4) with 16; exact HR3 | change (2 ^ 0) with 1; apply Z.mod_1_r].
Qed.

(* ---- the shadow entry over e62: e62 is in scope (granules 0x42 .. 0x4e are 0) and lies outside the shadow band ---- *)
Lemma hb_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem F pp e8 b,
  getr regs 27 = w64 SHADOW_OFF -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0x210) 104 ->
  (forall a, F + 0x210 <= a < F + 0x278 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) ->
  sh_ok rsegs HBx hb_SH (Ereg regs (hb_extra F pp e8 b)) (mrestrict H mem).
Proof.
  intros regs H mem F pp e8 b H27 HF1 HF2 Hra Hap. pose proof (@asan_consts rc) as (Hceil & _).
  set (E := Ereg regs (hb_extra F pp e8 b)).
  assert (U27 : U E (SOff 27 0) = SHADOW_OFF).
  { apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity | unfold SHADOW_OFF; lia]. }
  assert (U32 : U E (SOff 32 0) = F).
  { apply U_atom; [subst E; rewrite (ew_Ereg_extra regs _ 0); reflexivity | lia]. }
  apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
  unfold HBx. rewrite U27, U32. split.
  - rewrite <- (aview_rd_of rsegs). exact Hra.
  - unfold app_apart. cbn [she_m she_lo she_hi]. unfold HBx. rewrite U27, U32. intros a Ha. apply Hap. lia.
Qed.

(* ---- reading the final state ---- *)
Lemma hb_region : forall E ss ms r, st_ok rsegs E ss ms -> In r (ss_mem ss) -> region_ok rsegs E (ms_mem ms) r.
Proof. intros E ss ms r HS Hin. exact (mem_ok_region rsegs E _ _ r (st_ok_mem_ok rsegs E ss ms HS) Hin). Qed.
Lemma hb_chunk_val : forall E m r off (n : N) e v,
  region_ok rsegs E m r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem rsegs m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
  intros E m r off n e v HR Hin He Hv Hn.
  exact (val_of_chunk_ok rsegs E m _ off n e v (region_ok_chunk rsegs E m r _ HR Hin) He Hv Hn).
Qed.
Lemma hb_chunk_zero : forall E m r off len,
  region_ok rsegs E m r -> In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) ->
  forall i, 0 <= i < len -> mbyte rsegs m (base_val E (YP09.r_base r) + off + i) = Some (Z_to_bv 8 0).
Proof.
  intros E m r off len HR Hin i Hi.
  destruct (region_ok_chunk rsegs E m r _ HR Hin i ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-. exact Hb2.
Qed.
End b.

Print Assumptions hb_pcs.
Print Assumptions hb_vocab_cells.
Print Assumptions hb_vocab_strs.
Print Assumptions hb_s_str.
Print Assumptions hb_vocab_glob.
Print Assumptions hb_tbl_ok.
Print Assumptions hw6b_clob_ok.
Print Assumptions hw6b_ws_ok.
Print Assumptions hb_e8_range.
Print Assumptions hb_entry.
Print Assumptions hb_shok.
Print Assumptions hb_region.
Print Assumptions hb_chunk_val.
Print Assumptions hb_chunk_zero.
