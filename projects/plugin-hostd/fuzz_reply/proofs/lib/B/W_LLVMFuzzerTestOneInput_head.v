(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEG_HEAD of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput (fuzz_reply.asan
   0x842a0 .. 0x843fc and the two exits), in the form of the cgif entry walk's run segments (proofs/cgif/cgif_file_fuzzer/
   lib/A/ACf5.v rt_from) and of lf_seg_jt in lib/A/W_LLVMFuzzerTestOneInput_cut.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_head.v, with its module paths, module names and numbers changed; 617 of its 1426 lines of code are new or changed and 668 lines of the source are left out. *)
(* proves function LLVMFuzzerTestOneInput, segment SEG_HEAD (image B), as lf_seg_head_b against the frozen cut 7d4f6d8955b; reuse search and CONFIRM: seghead-r24.md (sha256 d185c49d4dec; internal record) *)
(* SEG_HEAD of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput (image B, fuzz_reply.asan-ubsan,
   sha256 10ffb5f9202ae2bd...): lf_seg_head_b below is exactly the Section hypothesis SEG_HEAD of
   lib/B/W_LLVMFuzzerTestOneInput_cut.v (:744).  A port of image A's lf_seg_head (lib/A/W_LLVMFuzzerTestOneInput_head.v
   on a working branch ec4dd616ed1): A's structure, B's code.  Every pc, register, frame slot and object below is read
   from B's own objdump (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) of the pinned image fuzz_reply.asan-ubsan, sha256 10ffb5f9202ae2bd...), none by offset
   arithmetic from A.
     0x845e0  beqz s5,84e64          in.n = 0: to the shutdown block X (B tests in.n AT the head, _cut.v difference (2))
     0x845e4  addi s4,s6,1; bgeu s7,s4,unimp          PTR_INC trap (s7 = 1): refuted by the runner from the atom facts
     0x845ec  <shadow check of s6 through s11>; lbu a0,0(s6)     the op byte in.p[0]
     0x84600  addi t1,s5,-1; ld a1,136(s1); mulhu; li a2,10; mul; sub     a1 = op = in.p[0] % 10 (DIV10 at F+136)
     0x8461c  sd zero,-1892(s10)     g_nout := 0 (s10 = HI_G_NOUT)
     0x84620  li a2,4; bltu op-1,a2 -> P; li a0,6; bne a1,a0 -> 0x84758 (li s5,0; the dispatch D 0x8475c)
     0x84630  P: beqz t1 -> 0x8465c (a2 = 0); else `addi a0,s4,1; bgeu s7,a0,unimp` (PTR_INC, runner), <shadow check of
              s4>, lbu a2,0(s4) (the k byte), s4 = s6 + 2, t1 = s5 - 2
     0x84660  the open count (a6 = F+152's shadow pointer, a5 = F+128's &g_s[0].open): per slot `lb` of its shadow
              (g_s's shadow is zero: HZS), `lw` of the open flag, and the ADDW trap `bne a7,a3,unimp` (0x8468c) on the
              32-bit sum (refuted by the runner: the flags are literals, so the count is a literal 0..4)
     0x846b8  sext.w a0,a3; beqz a0 -> 0x8471c; remw a2,a2,a3; s5 = &g_s[0]; the k-th open slot (0x846d8): at
              `zext.b a5,a2; beqz a5` to D with s5 = &g_s[pick]
     0x8471c  bne a1,s7 -> 0x8480c (`continue`: no open source, op <> 1); li s5,0 -> arm 1 0x84724 (op = 1)
     0x8480c  addiw s9,s9,1; mv s5,t1; mv s6,s4; li a0,512; bne s9,a0 -> H (operation t + 1); j X
   B against A: the head test (so walk 1 below also ends at X, when in.n = 0); s9 = t (A: s11), s10 = HI_G_NOUT
   (A: s9), s11 = SB (A: s10), s7 = 1 (A: t2), s4 = the cursor and t1 = the bytes left (A: t3 / t4); no modulus or
   count registers (B materialises 10 and 4 inline); g_s is B's object A_OBJ 19 (A: A_OBJ 22) at 0x5d8e60; the three
   UBSan trap edges; `continue` lands on B's latch tail 0x8480c, which tests only t + 1 = 512 (the next head tests
   in.n); no `full` flag in aframe_at (_cut.v difference (3)).
   THE THREE UBSan TRAP EDGES (_cut.v :81-83, all to `unimp` 0x850fc), each decided by the runner from the seat's atom
   facts (lib/B/W_traps.v, the rows "R = runner decides after the recipe"), so no trap lemma is cited and no branch
   case is opened:
     0x845e8 `bgeu s7,s4` (s4 = s6 + 1)  WRAP p+1 (W_traps.v :77, R1; trap_ptr_inc)  s7 pinned to 1, atom 22 (s6) in
                                         [4096, 2^47 - 16] (hb_f1);
     0x84638 `bgeu s7,a0` (a0 = s4 + 1)  WRAP p+1 (same row)                          atom 20 (s4) in [4096, 2^47 - 16]
                                         (hb_f2);
     0x8468c `bne a7,a3` (addw / add)    INT32 + add (W_traps.v :87-88, R4)            the four open flags are literals
                                         (32 cases), so the count is a literal 0..4 and both sums fold.
   The seven premises beyond _cut's Section w, A's names and texts (each with where integration discharges it) are
   stated together at the head of Section hb. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ walk 1's symbolic state *)
Definition AF_LLVM_pick : Z := AF_fr_LLVMFuzzerTestOneInput + 0x228.   (* 0x84630 `beqz t1` *)
Definition hb_Bx : sv := SOff 27 0.                                      (* s11 = SB *)
Definition hb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition hb_opsv : sv :=
  SAlu ALU_SUB (SOff 32 0) (SMd M_MUL (SMd M_MULHU (SOff 32 0) (SLit 1844674407370955162)) (SLit 10)).
Definition hb_rin0 : YP09.region := YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition hb_rdiv : YP09.region := YP09.mkRegion (Some 9%nat) 136 144 0 0 [YP09.mkChunk 136 (CVal 8 (SLit DIV10))].
Definition hb_rnout : YP09.region := YP09.mkRegion (Some 26%nat) (-1892) (-1884) (-1892) (-1884) [].
(* the atom facts the runner decides the head test and the PTR_INC trap with: in.n left (s5) in [1, 2^26], the
   cursor (s6) in the user range, and s7 pinned to 1 *)
Definition hb_f1 : facts := mkFacts [ (21%nat, mkAF 1 (2 ^ 26) 0); (22%nat, mkAF 4096 (2 ^ 47 - 16) 0);
  (26%nat, mkAF HI_G_NOUT HI_G_NOUT 0); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition hb_sr : list sv := sr_set sr_atoms 23%bv (SLit 1).
Definition hb_ss1 : sstate := mkSS AF_LLVM_head hb_sr [hb_rin0; hb_rdiv; hb_rnout] None hb_f1.
Definition hb_SH1 : list shent := [mkSHE 22 0 1].
Definition hb_x1 (b0 : Z) : list word := map (Z_to_bv 64) [b0].
(* in.n = 0 at the head: nothing is read, s5 is pinned to 0 *)
Definition hb_f0 : facts := mkFacts [ (27%nat, mkAF SB SB 0) ] [] [].
Definition hb_ss0 : sstate := mkSS AF_LLVM_head (sr_set hb_sr 21%bv (SLit 0)) [] None hb_f0.

Lemma hb_in_byte : forall {rc : YM05.RunCeil} (cx : lfcx) (m : word -> option byte) i,
  garr8 (@pa_segs _ fr_prog_listing PB_fr) m (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  0 <= i < Z.of_nat (length (c_pl cx)) ->
  val_mem (@pa_segs _ fr_prog_listing PB_fr) m (c_p cx + i) 1 (in_byte cx i) /\ 0 <= in_byte cx i < 256.
Proof.
  intros rc cx m i Hg Hi. unfold in_byte.
  destruct (Hg (Z.to_nat i) ltac:(rewrite length_map; lia)) as [Hv Hr].
  rewrite Z2Nat.id in Hv by lia.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by (rewrite length_map; lia).
  rewrite map_nth in Hv, Hr. split; [exact Hv | exact Hr].
Qed.
Lemma hb_exh : forall f : Z -> Z, forallb (fun b => f b =? b mod 10) (map Z.of_nat (seq 0 256)) = true ->
  forall b, 0 <= b < 256 -> f b = b mod 10.
Proof.
  intros f Hf b Hb. rewrite forallb_forall in Hf. apply Z.eqb_eq. apply Hf.
  apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.
Lemma hb_cases10 : forall (P : Z -> Prop) op, 0 <= op <= 9 ->
  P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> P 9 -> P op.
Proof.
  intros P op Hop H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  assert (op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/ op = 9) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; assumption.
Qed.
Lemma hb_cls_ltu : forall E op, 0 <= op <= 9 ->
  (zcanon (zalu_raw 63 64 ALU_ADD op (U E (SLit (-1)))) <? U E (SLit 4)) = (1 <=? op) && (op <=? 4).
Proof.
  intros E op Hop. rewrite !U_SLit.
  apply (hb_cases10 (fun op => (zcanon (zalu_raw 63 64 ALU_ADD op (zcanon (-1))) <? zcanon 4) = (1 <=? op) && (op <=? 4)));
    [exact Hop | vm_compute; reflexivity ..].
Qed.
Lemma hb_op_U : forall E b0, ew E 32 = Z_to_bv 64 b0 -> 0 <= b0 < 256 -> U E hb_opsv = b0 mod 10.
Proof.
  intros E b0 H32 Hb. unfold hb_opsv.
  rewrite !U_SAlu, !U_SMd, (U_atom E 32 b0 H32), !U_lit by lia.
  apply (hb_exh (fun b => zcanon (zalu_raw 63 64 ALU_SUB b
    (zcanon (zmd_raw 64 M_MUL (zcanon (zmd_raw 64 M_MULHU b 1844674407370955162)) 10)))));
    [vm_compute; reflexivity | exact Hb].
Qed.

Section hb.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

Lemma hb_entry1 : forall (W : world segs) regs mem N P F b0,
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 21 = w64 N -> getr regs 22 = w64 P ->
  getr regs 26 = w64 HI_G_NOUT -> getr regs 27 = w64 SB ->
  1 <= N <= 2 ^ 26 -> 4096 <= P <= 2 ^ 47 - 16 -> 0 <= b0 < 256 -> 0 <= F -> F + 144 <= 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mem) P 1 b0 ->
  sv8 W mem (F + 136) DIV10 ->
  awr W mem (rg_nout fr_RG) 8 ->
  (P + 1 <= F + 136 \/ F + 144 <= P) -> (P + 1 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= P) ->
  (F + 144 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= F + 136) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF P 1 ->
  ~ (SHADOW_OFF <= P < SHADOW_OFF + 17592186044416) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (hb_x1 b0))) hb_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_head)) mem (seg_rom segs)))
  /\ sh_ok segs hb_Bx hb_SH1 (Eimg (Ereg regs (hb_x1 b0))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem N P F b0 R23 R9 R21 R22 R26 R27 HN HP Hb HF0 HF1 MB MD AWN D1 D2 D3 RA HAP.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (hb_x1 b0))) as E eqn:HE.
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E21 : ew E 21 = Z_to_bv 64 N) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 P) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 b0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold hb_ss1, hb_sr. apply pa_entry_st_ok_full.
    + apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | discriminate | rewrite R23; reflexivity].
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks hb_rin0 hb_rdiv hb_rnout].
      * cbn [YP09.base_val]. rewrite E22, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ P 0 1 (SOff 32 0) b0);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact MB.
      * cbn [YP09.base_val]. rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 136 8 (SLit DIV10) DIV10); [reflexivity | unfold DIV10; zside | zside |].
        exact MD.
      * cbn [YP09.base_val]. rewrite E26, unsigned_lit_small by (unfold HI_G_NOUT; lia). split; [unfold HI_G_NOUT; lia|].
        split; [unfold HI_G_NOUT; lia|]. split; [|constructor].
        intros o Ho. replace (HI_G_NOUT + o) with (rg_nout fr_RG + (o + 1892)) by (cbn; unfold HI_G_NOUT; lia).
        apply AWN. lia.
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, hb_rin0, hb_rdiv, hb_rnout.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite E22, E9, E26, !unsigned_lit_small by (unfold HI_G_NOUT; lia).
      cbn in D2, D3. unfold HI_G_NOUT. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [hb_f1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E22, E26, E27, E32, !unsigned_lit_small by (unfold HI_G_NOUT, SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HI_G_NOUT, SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, hb_SH1. constructor; [|constructor].
    eapply shent_ok_of_range.
    + exact RA.
    + unfold U, hb_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. lia.
Qed.
Lemma hb_entry0 : forall (W : world segs) regs mem,
  getr regs 23 = w64 1 -> getr regs 21 = w64 0 -> getr regs 27 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) hb_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_head)) mem (seg_rom segs)))
  /\ sh_ok segs hb_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem R23 R21 R27. rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  split.
  - unfold hb_ss0, hb_sr. apply pa_entry_st_ok_full.
    + apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | discriminate | rewrite R23; reflexivity]
        | discriminate | rewrite R21; reflexivity].
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [hb_f0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E27, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* ------------------------------------------------------------------ the cut file's Section w, variable for variable *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* the model steps the premises below name (A's definitions, A's names): g_nout := 0 forgets what the controller
   read in the previous operation; `continue` moves the cursor past the op byte and, when one is left, the k byte *)
Definition lm_clear_O (m : lmod) : lmod :=
  LM (lm_k m) (lm_hs m) (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition lm_set_k (m : lmod) (k : Z) : lmod :=
  LM k (lm_hs m) (lm_G m) (lm_es m) (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition hd_kb (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0.
Definition hd_k' (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1.

(* ------------------------------------------------------------------ what this file takes beyond _cut's Section w
   The seven premises of image A's lf_seg_head (lib/A/W_LLVMFuzzerTestOneInput_head.v :382-391, :949, :1003-1009 on
   ec4dd616ed1), A's names and texts.  B's cut state does not give them: G_fr, B, RINV and LS are Section variables no
   premise of _cut's Section w constrains (HG = gx_ok says only "in the image, not owned"; fr_gi only "inG ->
   writable"; AR_laws says nothing of errno or of which ranges have zero shadow; RINV and LS have no laws). *)
(* g_nout's 8 bytes are in G_fr (the store at 0x8461c).  At the pin, G_fr := G_fr_c:
   lib/B/W_LLVMFuzzerTestOneInput_G.v c_HGnout (:167-169). *)
Hypothesis HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
(* errno's cell (tp - 164, in musl's static TLS) is apart from g_nout: aout_at holds errno's cell, and the store to
   g_nout must keep it.  At the pin: lib/B/W_LLVMFuzzerTestOneInput_G.v c_HERRNO (:250-253). *)
Hypothesis HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
(* g_s's shadow is zero: the instance lists g_s's 384 bytes among its zero-shadow ranges (W_contract.v azs B
   (rg_s fr_RG) (4 * ASRC), unfolded as A states it); both pick loops (0x84674, 0x846d8) read g_s's shadow.  At the
   pin: YF0m's Tfib_zero_shadow holds (0x5d8e60, 384), lib/B/W_LLVMFuzzerTestOneInput_G.v header (:30-31). *)
Hypothesis HZS : exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= rg_s fr_RG /\
  rg_s fr_RG + 4 * ASRC <= fst r + snd r / 8 * 8.
(* The model obligations on _cut's Section variables RINV / LS.  W_LLVMFuzzerTestOneInput_G.v has nothing for them:
   they are discharged at integration from the instance's RINV / LS.
   RI_head_nout / LS_head_nout: g_nout := 0 forgets what the controller read in the previous operation (no allocation,
   no block changes). *)
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Hypothesis LS_head_nout : forall cx t m ly S, LS cx t m ly S -> LS cx t (lm_clear_O m) ly S.
(* RI_head_skip / LS_head_skip: `continue` (an op that picks, no open source, op <> 1) ends the operation with the
   input consumed *)
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LS cx t m ly S -> LS cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.

(* ---- the frame of a store to a program global (generic over the stored range [lo, hi); A's, unchanged).
   A run that stores only to [lo, hi) leaves every other byte's ASan view and writability as it was; the bytes the
   cut facts read are either concrete global cells (checked against [lo, hi) by lia), stack and fake-frame bytes, or
   heap bytes within 8 of a live block (a key's slack, W_rep.v aentry_ok), which are off the image when [lo, hi) is an
   image range at least 8 bytes above the image's start (B's off_img: below 0x10000 or from 0x5fb000). *)
Definition hb_offw (lo hi a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi).
Definition hb_rng_off (lo hi : Z) (r : Z * Z) : Prop := forall a, fst r <= a < snd r -> hb_offw lo hi a.

Lemma hb_writable_kept : forall (W : world segs) mem mem',
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a.
Proof.
  intros W mem mem' HGR a. unfold arm. apply writable_kept. intros [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGR (Z_to_bv 64 a)). unfold mrestrict in HGR. rewrite Hh, Hb in HGR.
  destruct (mem' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso. apply HGR; first [discriminate | reflexivity].
Qed.
Lemma hb_kept_off : forall (W : world segs) mem mem' lo hi,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  forall a, hb_offw lo hi a -> abyte_kept W mem W mem' a.
Proof.
  intros W mem mem' lo hi HKX HGR a [Ha Hn]. split.
  - apply aview_eq_of. apply HKX. rewrite unsigned_lit_small by lia. exact Hn.
  - exact (hb_writable_kept W mem mem' HGR a).
Qed.
Lemma hb_akept : forall (W : world segs) mem mem' lo hi fp,
  (forall a, hb_offw lo hi a -> abyte_kept W mem W mem' a) ->
  (forall r, In r fp -> hb_rng_off lo hi r) -> akept W mem W mem' fp.
Proof. intros W mem mem' lo hi fp KB Hfp r Hr a Ha. apply KB. exact (Hfp r Hr a Ha). Qed.
Lemma hb_rng_off_sub : forall lo hi a n a' n', hb_rng_off lo hi (a, a + n) -> a <= a' -> a' + n' <= a + n ->
  hb_rng_off lo hi (a', a' + n').
Proof. intros lo hi a n a' n' H H1 H2 x Hx. apply H. cbn in *. lia. Qed.

Lemma hb_len_text : forall recs, length (concat (map text_rec recs)) = (16 * length recs)%nat.
Proof.
  induction recs as [|r recs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
  assert (Hx : length (text_rec r) = 16%nat) by reflexivity. rewrite Hx. cbn [length]. lia.
Qed.
Lemma hb_len_kptrs : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
  match goal with |- (length ?x + _)%nat = _ => assert (Hx : length x = 8%nat) by reflexivity; rewrite Hx end.
  cbn [length]. lia.
Qed.

Section fo.
Variables lo hi : Z.
Hypothesis Hlo : 0x10008 <= lo.
Hypothesis Hhi : hi <= 0x5fb000.
(* a byte of a live block, or within 8 bytes after it *)
Lemma hb_blk_off : forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n + 8 -> hb_offw lo hi a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Himg. unfold YCbq.off_img in Himg.
  pose proof asan_consts as (C1 & _). unfold hb_offw. split; lia.
Qed.
Lemma hb_alist_fp_off : forall ly S W mem md LA l lines, AR segs B ly S W mem md ->
  alist_at B ly S W mem LA l lines -> hb_rng_off lo hi (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> hb_rng_off lo hi r.
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, hb_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (hb_blk_off ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (hb_blk_off ly S W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma hb_alist_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (rr & <- & Hrr). rewrite Forall_forall in H9. exact (proj1 (H9 rr Hrr)).
Qed.
Lemma hb_asrc_fp_off : forall ly S W mem md HA h, AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  hb_rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> hb_rng_off lo hi r.
Proof.
  intros ly S W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (hb_blk_off ly S W mem md (hs_partial h) APARTIAL a HAR H18).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (hb_alist_fp_off ly S W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (hb_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (hb_alist_fp_off ly S W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (hb_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (hb_alist_fp_off ly S W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (hb_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma hb_asrc_blks_in : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h Hs b Hb.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - exact (hb_alist_blks_in ly S W mem _ _ _ H10 b Hb).
  - exact (hb_alist_blks_in ly S W mem _ _ _ H22 b Hb).
  - exact (hb_alist_blks_in ly S W mem _ _ _ H23 b Hb).
Qed.
Lemma hb_aentry_fp_off : forall ly S W mem md e, AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> hb_rng_off lo hi r.
Proof.
  intros ly S W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (hb_blk_off ly S W mem md (re_buf e) (re_cap e) a HAR Hin).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, hb_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (hb_blk_off ly S W mem md (re_hp e) (re_kh e) a HAR Hin).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & _).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (hb_blk_off ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR K1).
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma hb_aentry_blks_in : forall ly S W mem e, aentry_ok B ly S W mem e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - destruct (re_hp e =? 0) eqn:Ez; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ez.
    destruct H12 as [(Hz & _) | (Hz & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma hb_arelay_fp_off : forall RG ly S W mem md G es, AR segs B ly S W mem md -> arelay_at B RG ly S W mem G es ->
  hb_rng_off lo hi (rg_src RG, rg_src RG + 8) -> hb_rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  hb_rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> hb_rng_off lo hi r.
Proof.
  intros RG ly S W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (hb_blk_off ly S W mem md G ATABLE a HAR H8).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (hb_aentry_fp_off ly S W mem md e HAR (H10 e He) r Hr).
Qed.
Lemma hb_arelay_blks_in : forall RG ly S W mem G es, arelay_at B RG ly S W mem G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (hb_aentry_blks_in ly S W mem e (H10 e He) b Hb).
Qed.
End fo.

Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ---- the pick P (0x84630 `beqz t1`), walk 1's second end: an op that picks, the model after g_nout := 0; s4 / t1
   the cursor and the bytes left after the op byte, s5 / s6 still in.n left and in.p *)
Definition hb_lregs_P (cx : lfcx) (t : Z) (m : lmod) (FF : Z) (regs : bvmap 5 word) (W : world segs)
    (mem : word -> option byte) : Prop :=
  lregs_common B cx FF regs /\ getr regs 25 = w64 t /\
  0 <= t < OPS_MAX /\ 0 <= lm_k m < c_n cx /\ lm_O m = [] /\
  getr regs 21 = w64 (c_n cx - lm_k m) /\ getr regs 22 = w64 (c_p cx + lm_k m) /\
  getr regs 11 = w64 (in_byte cx (lm_k m) mod 10) /\ picks (in_byte cx (lm_k m) mod 10) = true /\
  getr regs 20 = w64 (c_p cx + lm_k m + 1) /\ getr regs 6 = w64 (c_n cx - lm_k m - 1).
Definition hb_INV_P (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_pick) regs mem md /\
    jt_rom W mem /\ lcut B G_fr fr_FP LS RINV cx t (hb_lregs_P cx t) regs mem md W.

(* g_nout's 8 bytes are image data, not .rodata (computed on the pinned segments) *)
Definition hb_seg_rom_hit (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <? hi) && (lo <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
    segs.
Lemma hb_not_rom : forall lo hi a, hb_seg_rom_hit lo hi = false -> lo <= a < hi -> ~ in_rom segs a.
Proof.
  intros lo hi a Hh Ha (sg & Hin & Hw & Hr). unfold hb_seg_rom_hit in Hh.
  assert (Hx : existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <? hi) &&
    (lo <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true).
  { apply existsb_exists. exists sg. split; [exact Hin|]. rewrite Hw. cbn [negb andb].
    apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  rewrite Hh in Hx. discriminate.
Qed.
Lemma hb_rom_low : forall a, in_rom segs a -> 0 <= a < 2 ^ 64.
Proof.
  intros a (sg & Hin & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hin Hr))) as H.
  unfold kLowMemEnd in H. lia.
Qed.
(* B's g_nout: 0x5d8e40 = 6131264 *)
Lemma hb_nout_val : rg_nout fr_RG = 6131264.
Proof. reflexivity. Qed.
Lemma hb_nout_not_rom : hb_seg_rom_hit 6131264 6131272 = false.
Proof. vm_compute. reflexivity. Qed.

(* the controller's stream after g_nout := 0: what it read in this operation is forgotten (O = []), its bytes become
   part of the buffer's junk *)
Lemma hb_aout_clear : forall ly S W mem md mem' c O mx no cap out,
  AR segs B ly S W mem md ->
  (forall a, hb_offw 6131264 6131272 a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 -> hb_rng_off 6131264 6131272 (as_errno B, as_errno B + 4) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c [] mx 0 cap out.
Proof.
  intros ly S W mem md mem' c O mx no cap out HAR KB KW HN0 HER
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  assert (KK : forall x, 0 <= x < 6131264 \/ 6131272 <= x < 2 ^ 64 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KB; split; lia).
  unfold aout_at. cbn [rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr fr_RG
    fr_globals_b] in *.
  pose proof HER as HER'. unfold hb_rng_off, hb_offw in HER'. cbn [fst snd] in HER'.
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H2]|].
  split; [exact HN0|].
  split; [intros i Hi; apply KW; exact (H4 i Hi)|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H16]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KB; apply HER'; cbn in Hx; lia | exact H17]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KB; apply HER'; lia | exact H18]|].
  do 6 (split; [assumption|]).
  split; [reflexivity|].
  destruct H26 as [(Hc & Ho & Hn) | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; lia|right].
  split; [exact Hc|]. split; [lia|]. split; [exact Hin|].
  exists (O ++ junk). split; [rewrite length_app, Nat2Z.inj_add; lia|].
  cbn [app]. apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx. apply KB.
  apply (hb_blk_off 6131264 6131272 ltac:(lia) ltac:(lia) ly S W mem md out cap x HAR Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

(* every cut fact but the journal and the model's stream, across a store to g_nout only (B's frame: no `full` flag,
   the slots F+32 .. F+184) *)
Lemma hb_store_kept : forall cx ly3 S3 W mem md mem' fpos m,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' (lm_clear_O m) /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT.
  rewrite hb_nout_val in HKX, HN0.
  pose proof (hb_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof (hb_writable_kept W mem mem' HGR) as KW.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold YCfn.LLVMF_STK in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HF : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  assert (KX : forall a n, 0 <= a -> a + n <= 6131264 \/ 6131272 <= a -> a + n <= 2 ^ 64 ->
    forall x, a <= x < a + n -> abyte_kept W mem W mem' x)
    by (intros a n Ha Hn Hb x Hx; apply KB; split; lia).
  split; [|split; [|split; [|split]]].
  - (* the frame and the fake frame *)
    unfold aframe_at in *. cbv zeta in *.
    destruct HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
      F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (lf_F cx) (spZ (c_regs cx) - lf_F cx)); lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F40]|].
    split; [apply KV; [lia | lia | exact F48]|]. split; [apply KV; [lia | lia | exact F56]|].
    split; [apply KV; [lia | lia | exact F64]|]. split; [apply KV; [lia | lia | exact F72]|].
    split; [apply KV; [lia | lia | exact F80]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F104]|]. split; [apply KV; [lia | lia | exact F120]|].
    split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
    split; [apply KV; [lia | lia | exact F152]|]. split; [apply KV; [lia | lia | exact F184]|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (frame_addr ly3 1 fpos) 128); lia | exact FFw]|].
    assert (HSB : 0 <= SB + frame_addr ly3 1 fpos / 8 /\ SB + frame_addr ly3 1 fpos / 8 + 16 <= 2 ^ 64 /\
      6131272 <= SB + frame_addr ly3 1 fpos / 8).
    { unfold SB. pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
    split.
    { apply (akept_garr8 W mem); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia. }
    apply (akept_awr W mem); [intros x Hx; apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia | exact FFshw].
  - (* the model, with what the controller read in this operation forgotten *)
    destruct HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr & Htu & Hlst & Hlstw).
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_clear_O].
    split; [exact Hhs4|].
    split.
    { intros i Hi. specialize (Hslots i Hi). unfold aslot in *.
      assert (HHA : hb_rng_off 6131264 6131272 (rg_s fr_RG + ASRC * Z.of_nat i, rg_s fr_RG + ASRC * Z.of_nat i + ASRC)).
      { intros x Hx. cbn [fst snd rg_s fr_RG fr_globals_b] in Hx. unfold ASRC in Hx. split; lia. }
      destruct (nth i (lm_hs m) None) as [h|].
      - apply (asrc_at_kept B ly3 S3 W mem ly3 S3 W mem' _ h Hslots).
        + apply (hb_akept W mem mem' 6131264 6131272); [exact KB|].
          exact (hb_asrc_fp_off 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 W mem md _ h HAR Hslots HHA).
        + exact (hb_asrc_blks_in ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (hb_akept W mem mem' 6131264 6131272); [exact KB|].
        apply (hb_arelay_fp_off 6131264 6131272 ltac:(lia) ltac:(lia) fr_RG ly3 S3 W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals_b] in Hx; split; lia.
      + exact (hb_arelay_blks_in fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (hb_aout_clear ly3 S3 W mem md mem' _ _ _ _ _ _ HAR KB KW); [rewrite hb_nout_val; exact HN0 | | exact Hout].
      intros x Hx. cbn [fst snd] in Hx. pose proof HERRNO as (He0 & He1 & He2).
      rewrite hb_nout_val in He2. split; lia. }
    split.
    { apply (agone_at_kept fr_RG W mem W mem' _ Hgone). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (alock_at_kept fr_RG W mem W mem' _ Hlock). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (awake_at_kept fr_RG W mem W mem' Hwake). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_NFD in *; cbn in Hx; split; lia | exact Hnfd]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_NFD in *; split; lia | exact Hnfdw]|].
    split; [exact Hnfdr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_THREAD_UP in *; cbn in Hx; split; lia | exact Htu]|].
    split; [destruct Hlst as [lst Hlst]; exists lst;
      apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; cbn in Hx; split; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; split; lia | exact Hlstw].
  - (* the input block *)
    destruct HIN as [Hblk Hg]. split; [exact Hblk|]. apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. rewrite length_map, <- Hlen in Hx. apply KB.
    destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
    apply (hb_blk_off 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 W mem md (c_p cx) (c_n cx) x HAR Hin).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
  - (* .rodata *)
    intros a Ha. pose proof (hb_rom_low a Ha) as Hrl.
    destruct (Z_lt_le_dec a 6131264) as [Hlt | Hge].
    + rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
    + destruct (Z_lt_le_dec a 6131272) as [Hlt2 | Hge2].
      * exfalso. exact (hb_not_rom 6131264 6131272 a hb_nout_not_rom ltac:(lia) Ha).
      * rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
  - (* the jump table *)
    intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
    intros x Hx. apply KB. unfold fr_jtab in Hx. cbn in Hx. split; lia.
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at) across a store to g_nout only *)
Lemma hb_flag_kept : forall ly3 S3 W mem md mem' fpos,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR Hv.
  rewrite hb_nout_val in HKX.
  pose proof (hb_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. cbn in Hx. apply KB. split; lia.
Qed.

(* the cut facts after walk 1's store to g_nout, at the run's final memory and registers *)
Lemma hb_w1_lcut : forall cx t W mem md mem' md' ly3 S3 k m fpos
    (R : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop) regs',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  ajournal_gx segs B G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> jt_rom W mem ->
  R (lm_clear_O m) (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut B G_fr fr_FP LS RINV cx t R regs' mem' md' W.
Proof.
  intros cx t W mem md mem' md' ly3 S3 k m fpos R regs' HB HJ HJ' HKX HGR HN0 HFR HFL HMOD HIN HRV HSEP HLS HRI HJT HR.
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hfp : In (1, fpos) (frames S3)).
  { destruct (ajournal_gx_inner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (hb_store_kept cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT)
    as (F' & M' & I' & RV' & JT').
  split; [exact JT'|].
  exists [(1, fpos)], ly3, S3, k, (lm_clear_O m), fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact F'|].
  split; [exact (hb_flag_kept ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL)|].
  split; [exact M'|]. split; [exact I'|].
  split; [exact RV'|]. split; [exact HSEP|]. split; [apply LS_head_nout; exact HLS|].
  split; [apply RI_head_nout; exact HRI|]. exact HR.
Qed.
(* the region list of a run whose only writable window is g_nout's *)
Lemma hb_frame_nout : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> rg_nout fr_RG <= a < rg_nout fr_RG + 8) ->
  forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> m' x = m x.
Proof. intros E rs m m' HF Hw x Hx. apply HF. intros Hin. apply Hx. apply Hw. exact Hin. Qed.
Lemma hb_mem_grows_trans : forall m1 m2 m3 : word -> option byte, mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.

Lemma hb_picks14 : forall op, 1 <= op <= 4 -> picks op = true.
Proof.
  intros op Hop. assert (op = 1 \/ op = 2 \/ op = 3 \/ op = 4) as Hc by lia.
  destruct Hc as [->|[->|[->| ->]]]; reflexivity.
Qed.
Lemma hb_picks_no : forall op, 0 <= op <= 9 -> ((1 <=? op) && (op <=? 4)) = false -> op <> 6 -> picks op = false.
Proof.
  intros op Hop. apply (hb_cases10 (fun op => ((1 <=? op) && (op <=? 4)) = false -> op <> 6 -> picks op = false));
    [exact Hop | ..]; intros H1 H2; first [reflexivity | discriminate H1 | exfalso; exact (H2 eq_refl)].
Qed.
(* writes of walk 1's runs: g_nout's 8 bytes only (the region on s10 = HI_G_NOUT at -1892) *)
Ltac hb_wr E26 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
    first [ lia
          | rewrite ?ew_ewset_other in Hr by lia; rewrite E26, unsigned_lit_small in Hr by (unfold HI_G_NOUT; lia);
            rewrite hb_nout_val; unfold HI_G_NOUT in Hr; lia ] |]);
  destruct Hin.
Ltac hb_awr E26 HGn :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       first [ lia
             | right; left; apply HGn; rewrite ?ew_ewset_other in Ha by lia;
               rewrite E26, unsigned_lit_small in Ha by (unfold HI_G_NOUT; lia); rewrite hb_nout_val;
               unfold HI_G_NOUT in Ha; lia ] |] ].
(* g_nout = 0 after the store, read off the run's g_nout region (the third region) *)
Ltac hb_nout0 HS E26 HN0 :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 2 (ss_mem ss) hb_rnout) in
    let HRN := fresh "HRN" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 2 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 26 HI_G_NOUT _ _ _ _ _ (-1892) 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E26; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + -1892) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end.
Ltac hb_upd E26 MEQ MG :=
  lazymatch goal with HFx : frame_of ?Ev ?rs (mrestrict ?H (ms_mem ?ms0)) (mrestrict ?H (ms_mem ?ms1)) |- _ =>
  lazymatch goal with HGx : mem_grows (mrestrict H (ms_mem ms0)) (mrestrict H (ms_mem ms1)) |- _ =>
    let MEQn := fresh "MEQn" in let MGn := fresh "MGn" in
    lazymatch type of MEQ with forall x, _ -> mrestrict _ _ x = mrestrict _ ?m0 x =>
    assert (MEQn : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict H (ms_mem ms1) x = mrestrict H m0 x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          rewrite (hb_frame_nout Ev rs _ _ HFx ltac:(hb_wr E26) x Hx); exact (MEQ x Hx)) end;
    pose proof (hb_mem_grows_trans _ _ _ MG HGx) as MGn;
    clear MEQ MG HFx HGx; rename MEQn into MEQ; rename MGn into MG end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
Ltac hb_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.
Lemma hb_sv_of_U : forall E v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H Hz. apply bv_eq. rewrite unsigned_lit_small by exact Hz. exact H. Qed.
(* a run over read-only regions leaves the memory as it was (_cut's jt_mem) *)
Ltac hb_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac hb_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the registers walk 1 does not write (s7 is pinned to 1; s4, t1, a0-a2 and, on the dispatch side, s5 are written) *)
Definition HB_KEPT1 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26; 27]%bv.
(* the registers the in.n = 0 exit does not write: all *)
Definition HB_KEPTX : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27]%bv.

(* ------------------------------------------------------------------ walk 1: the head (0x845e0) to D or P
   in.n = 0: `beqz s5` to X, nothing read or written.  Else the PTR_INC trap at 0x845e8 (runner, from the atom facts),
   the op byte, g_nout := 0, the class test: D for an op that picks no source (s5 := 0), P for op in 1-4 or 6. *)
Lemma hb_w1 : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_H B G_fr fr_FP LS RINV cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D B G_fr fr_FP LS RINV cx t op W' c') \/
    hb_INV_P cx t W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R26 & R27 & R3 & R4) & R25 & R21 & R22 & Ht & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_head)) with (Z_to_bv 64 (BASE + AF_LLVM_head)).
  destruct (Z.eq_dec (lm_k m) (c_n cx)) as [Hkn | Hkn].
  { (* in.n = 0: `beqz s5` to the shutdown block *)
    assert (R21' : getr regs 21 = w64 0) by (rewrite R21, Hkn, Z.sub_diag; reflexivity).
    destruct (hb_entry0 W regs mem R23 R21' R27) as [HS SHOK].
    remember (Eimg (Ereg regs [])) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs []) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HE.
    paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_exit.
    { apply awr_ok_x_nil. }
    hb_mem HF Em.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] HB_KEPTX HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em in *. clear HF HFr HG0.
    apply SRr_ret. right; right.
    lazymatch goal with |- INV_X _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} => exists r, mem, d, t end.
    split; [reflexivity|]. split; [exact HROM|].
    exists [(1, fpos)], ly3, S3, k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
    split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HRI|].
    unfold lregs_X.
    repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ]. }
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hblk) as Hpimg. unfold YCbq.off_img in Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold YCfn.LLVMF_STK in *.
  destruct (hb_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB Rb0].
  pose proof HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
    F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
  pose proof HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  destruct (hb_entry1 W regs mem (c_n cx - lm_k m) (c_p cx + lm_k m) (lf_F cx) (in_byte cx (lm_k m)) R23 R9 R21 R22 R26 R27
    ltac:(lia) ltac:(lia) Rb0 ltac:(lia) ltac:(lia) MB F136 O4 ltac:(lia)
    ltac:(rewrite hb_nout_val; lia) ltac:(rewrite hb_nout_val; lia)
    ltac:(apply (range_addressable_of_block segs B LAWS ly3 S3 W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia])
    ltac:(unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (hb_x1 (in_byte cx (lm_k m))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (lm_k m)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof HJ as HJ0.
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  assert (UOP : forall Ev, ew Ev 32 = ew E 32 -> U Ev hb_opsv = in_byte cx (lm_k m) mod 10)
    by (intros Ev HEv; apply hb_op_U; [rewrite HEv; exact E32 | exact Rb0]).
  (* the head test, the PTR_INC trap, the shadow check and read of in.p[0], op = in.p[0] % 10, g_nout = 0, to the
     class test *)
  paj_run_tok RUN HS HJ SHOK hb_Bspan.
  { hb_awr E26 HGnout. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    assert (MEQ1 : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x)
      by (apply (hb_frame_nout E (ss_mem hb_ss1)); [exact HFx | hb_wr E26]) end.
  lazymatch goal with H : mem_grows (mrestrict _ mem) _ |- _ => rename H into MG1 end.
  rename MEQ1 into MEQ. rename MG1 into MG.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (UO : U Ev hb_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite !ew_ewset_other by lia; reflexivity);
    assert (HAE1 : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) Ev)
      by (split; [intros m0 Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite !ed_ewset; exact (proj2 HAE)])
  end.
  psrr_branch_tok RUN BR HS SHOK hb_Bspan.
  - (* op in 1..4: on to the pick *)
    unfold hb_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hb_cls_ltu in Hc by lia.
    apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2. fold hb_opsv in UO.
    paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_pick.
    { hb_awr E26 HGnout. }
    hb_upd E26 MEQ MG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
    hb_prreg_raw HS (11%bv : bv 5) Q11.
    prreg HS (21%bv : bv 5) Q21.
    hb_nout0 HS E26 HN0.
    pmkst HS.
    apply SRr_ret. right; left.
    lazymatch goal with |- hb_INV_P _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
    split; [reflexivity|].
    apply (hb_w1_lcut cx t W mem md _ _ ly3 S3 k m fpos (hb_lregs_P cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
    unfold hb_lregs_P. cbn [lm_k lm_O lm_clear_O].
    rewrite E21 in Q21, Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
    split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
      | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
    split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
    split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
    split; [exact Q21|].
    split; [rewrite (KR 22%bv ltac:(hb_in)); exact R22|].
    split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
    split; [apply hb_picks14; exact (conj Hc1 Hc2)|].
    split; [rewrite Q20; unfold w64; f_equal; lia|].
    rewrite Q6; unfold w64; f_equal; lia.
  - unfold hb_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hb_cls_ltu in Hc by lia. fold hb_opsv in UO.
    rename Hc into Hcls.
    paj_run_tok RUN HS HJ SHOK hb_Bspan.
    { hb_awr E26 HGnout. }
    hb_upd E26 MEQ MG.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (UO2 : U Ev hb_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite ?ew_ewset_other by lia; reflexivity);
      assert (HAE2 : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)])
    end.
    clear UO HAE1. rename UO2 into UO. rename HAE2 into HAE1.
    psrr_branch_tok RUN BR HS SHOK hb_Bspan.
    + (* op not in 1..4, op <> 6: no source (0x84758 li s5,0); to the dispatch *)
      unfold hb_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hb_opsv in UO.
      apply negb_true_iff, Z.eqb_neq in Hc.
      pose proof (hb_picks_no (in_byte cx (lm_k m) mod 10) ltac:(lia) Hcls Hc) as Hpk.
      paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_dispatch.
      { hb_awr E26 HGnout. }
      hb_upd E26 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      hb_prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21.
      hb_nout0 HS E26 HN0.
      pmkst HS.
      apply SRr_ret. left. exists (in_byte cx (lm_k m) mod 10). split; [lia|].
      lazymatch goal with |- INV_D _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      rewrite ?wvb_collapse in HJ.
      split; [exists [(1, fpos)], ly3, S3, k; exact HJ|].
      apply (hb_w1_lcut cx t W mem md _ _ ly3 S3 k m fpos (lregs_D B cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
      unfold lregs_D. cbv zeta. cbn [lm_k lm_O lm_clear_O]. rewrite Hpk. cbv iota.
      rewrite E21 in Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      rewrite Q21. reflexivity.
    + (* op = 6: on to the pick *)
      unfold hb_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hb_opsv in UO.
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_pick.
      { hb_awr E26 HGnout. }
      hb_upd E26 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      hb_prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21.
      hb_nout0 HS E26 HN0.
      pmkst HS.
      apply SRr_ret. right; left.
      lazymatch goal with |- hb_INV_P _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      apply (hb_w1_lcut cx t W mem md _ _ ly3 S3 k m fpos (hb_lregs_P cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
      unfold hb_lregs_P. cbn [lm_k lm_O lm_clear_O].
      rewrite E21 in Q21, Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
      split; [exact Q21|].
      split; [rewrite (KR 22%bv ltac:(hb_in)); exact R22|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      split; [rewrite Hc; reflexivity|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      rewrite Q6; unfold w64; f_equal; lia.
Qed.

(* ------------------------------------------------------------------ walk 2: the pick (0x84630 .. D, arm 1, H, X)
   Split on whether a second byte is left and on which of g_s[0..3] are open (32 cases), so the open count and the
   k-th-open loop run with literal flags: the PTR_INC trap at 0x84638 (runner), the shadow-checked read of the k byte,
   the open count (0x84674: g_s's shadow read through the pointer at F+152, the open flags through F+128's
   &g_s[0].open, the ADDW trap at 0x8468c on literals), the remainder kb % n (pinned to its value), the k-th-open loop
   (0x846d8), ending at D with s5 = &g_s[pick]; with no open source, at arm 1 (0x84724, s5 = 0) for op = 1, else
   `continue` through B's latch tail 0x8480c to H (operation t + 1) or, at t + 1 = 512, X. *)
Definition hb_ob (b : bool) : Z := if b then 1 else 0.
Definition hb_isS (o : option hsrc) : bool := match o with Some _ => true | None => false end.
(* g_s is B's image object A_OBJ 19 (0x5d8e60); F+152 holds the shadow address of &g_s[0].open *)
Definition hb_shgs : Z := SB + (rg_s fr_RG + 4) / 8.
Definition hb_rb1 : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition hb_rfr2 : YP09.region := YP09.mkRegion (Some 9%nat) 128 160 0 0
  [YP09.mkChunk 128 (CVal 8 (SOff (A_OBJ 19) 4)); YP09.mkChunk 152 (CVal 8 (SLit hb_shgs))].
Definition hb_rgs (b0 b1 b2 b3 : bool) : YP09.region := YP09.mkRegion (Some (A_OBJ 19)) 4 296 0 0
  [YP09.mkChunk 4 (CVal 4 (SLit (hb_ob b0))); YP09.mkChunk 100 (CVal 4 (SLit (hb_ob b1)));
   YP09.mkChunk 196 (CVal 4 (SLit (hb_ob b2))); YP09.mkChunk 292 (CVal 4 (SLit (hb_ob b3)))].
Definition hb_rsh : YP09.region := YP09.mkRegion None hb_shgs (hb_shgs + 37) 0 0
  [YP09.mkChunk hb_shgs (CVal 1 (SLit 0)); YP09.mkChunk (hb_shgs + 12) (CVal 1 (SLit 0));
   YP09.mkChunk (hb_shgs + 24) (CVal 1 (SLit 0)); YP09.mkChunk (hb_shgs + 36) (CVal 1 (SLit 0))].
(* the cursor s4 in the user range (it decides the PTR_INC trap `bgeu s7,s4+1`) *)
Definition hb_f2 : facts :=
  mkFacts [ (20%nat, mkAF 4096 (2 ^ 47 - 16) 0); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition hb_ss2 (more b0 b1 b2 b3 : bool) : sstate :=
  mkSS AF_LLVM_pick hb_sr ((if more then [hb_rb1] else []) ++ [hb_rfr2; hb_rgs b0 b1 b2 b3; hb_rsh]) None hb_f2.
Definition hb_SH2 (more : bool) : list shent := if more then [mkSHE 20 0 1] else [].
Lemma hb_shgs_val : hb_shgs = 2148217292.
Proof. reflexivity. Qed.

(* the open flag of g_s[i] as the program reads it: 1 for an open source, 0 for a reset one *)
Lemma hb_le_byte0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma hb_open_val : forall ly S W mem i o, aslot B ly S W mem i o ->
  val_mem segs (arm W mem) (rg_s fr_RG + ASRC * Z.of_nat i + 4) 4 (hb_ob (hb_isS o)).
Proof.
  intros ly S W mem i [h|] Hs; cbn [aslot hb_isS hb_ob] in *.
  - pose proof Hs as (_ & H2 & _ & _ & _ & _ & _ & H8 & _). rewrite H8 in H2. exact H2.
  - destruct Hs as [Hz _]. intros kk Hkk.
    destruct (Hz (Z.to_nat (4 + Z.of_nat kk)) ltac:(rewrite repeat_length; unfold ASRC; cbn; lia)) as [Hv _].
    specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
    replace (rg_s fr_RG + ASRC * Z.of_nat i + 4 + Z.of_nat kk)
      with (rg_s fr_RG + ASRC * Z.of_nat i + Z.of_nat (Z.to_nat (4 + Z.of_nat kk)) + Z.of_nat 0) by lia.
    rewrite Hv, !hb_le_byte0. reflexivity.
Qed.
Lemma hb_vm0_of_aview : forall H (mem : word -> option byte) a, aview segs H mem a = Some 0 -> val_mem segs (mrestrict H mem) a 1 0.
Proof.
  intros H mem a Hv kk Hk. assert (kk = 0%nat) as -> by lia.
  destruct (aview_byte segs H mem a 0 Hv) as (b & Hb & Hv0 & _). rewrite Z.add_0_r, Hb.
  rewrite <- (Z_to_bv_bv_unsigned _ b), <- Hv0, hb_le_byte0. reflexivity.
Qed.
(* g_s's shadow is zero (HZS): the four shadow bytes of &g_s[i].open, 12 apart *)
Lemma hb_gs_shadow : forall ly S W mem md, AR segs B ly S W mem md ->
  forall j, 0 <= j < 4 -> val_mem segs (mrestrict (w_H W) mem) (hb_shgs + 12 * j) 1 0.
Proof.
  intros ly S W mem md HAR j Hj. destruct HZS as ([lo len] & Hin & H8 & Hlo & Hhi). cbn [fst snd] in *.
  assert (Hz : zero_shadow (aview segs (w_H W) mem) SHADOW_OFF lo len).
  { apply (al_zshadow _ _ LAWS ly S W mem md (lo, len) HAR). unfold zero_shadow_ranges. right. exact Hin. }
  change (rg_s fr_RG) with 6131296 in *. unfold ASRC in Hhi.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. rewrite H8, Z.add_0_r in Dl.
  pose proof (Z.mul_div_le len 8 ltac:(lia)) as Dn.
  specialize (Hz (766412 - lo / 8 + 12 * j) ltac:(split; [lia | lia])).
  apply hb_vm0_of_aview. rewrite hb_shgs_val.
  replace (2148217292 + 12 * j) with (shadow_of_addr SHADOW_OFF lo + (766412 - lo / 8 + 12 * j))
    by (unfold shadow_of_addr, SHADOW_OFF; lia).
  exact Hz.
Qed.
(* the 32-bit remainder kb % n of the pick, and B's 32-bit `addiw s9,s9,1` at the latch tail (t <= 511) *)
Definition hb_envb (E : env) (b : Z) : env := {| ew := fun _ => Z_to_bv 64 b; ed := ed E |}.
Lemma hb_rem_U : forall E b c, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> 1 <= c <= 4 ->
  U E (SMdw M_REM (SOff 32 0) (SLit c)) = b mod c.
Proof.
  intros E b c H32 Hb Hc.
  assert (Hd : U E (SMdw M_REM (SOff 32 0) (SLit c)) = U (hb_envb E b) (SMdw M_REM (SOff 32 0) (SLit c)))
    by (unfold U; cbn [sv_denot]; rewrite H32; reflexivity).
  rewrite Hd. clear Hd H32.
  assert (K : forallb (fun c => forallb (fun b => U (hb_envb E b) (SMdw M_REM (SOff 32 0) (SLit c)) =? b mod c)
      (map Z.of_nat (seq 0 256))) [1; 2; 3; 4] = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. specialize (K c ltac:(cbn; lia)). rewrite forallb_forall in K.
  apply Z.eqb_eq. apply K. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.
Lemma hb_addiw_U : forall E t, ew E 25 = Z_to_bv 64 t -> 0 <= t <= 511 ->
  U E (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1.
Proof.
  intros E t H25 Ht.
  assert (Hd : U E (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = U (hb_envb E t) (SAluw ALU_ADD (SOff 25 0) (SLit 1)))
    by (unfold U; cbn [sv_denot]; rewrite H25; reflexivity).
  rewrite Hd. clear Hd H25.
  assert (K : forallb (fun t => U (hb_envb E t) (SAluw ALU_ADD (SOff 25 0) (SLit 1)) =? t + 1)
      (map Z.of_nat (seq 0 512)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. apply Z.eqb_eq. apply K. apply in_map_iff. exists (Z.to_nat t). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma hb_VAL_gs : VAL (A_OBJ 19) = rg_s fr_RG.
Proof. vm_compute. reflexivity. Qed.
Lemma hb_entry2 : forall (W : world segs) regs mem (more b0 b1 b2 b3 : bool) P1 F kb,
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 27 = w64 SB -> getr regs 20 = w64 P1 ->
  4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 -> alloc_ceiling <= F -> F + 160 <= 2 ^ 47 ->
  (more = true -> P1 + 1 <= 0x10000 \/ 0x5fb000 <= P1) -> (more = true -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (more = true -> P1 + 1 <= alloc_ceiling) ->
  (more = true -> val_mem segs (mrestrict (w_H W) mem) P1 1 kb) ->
  (more = true -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 128) (rg_s fr_RG + 4) -> sv8 W mem (F + 152) hb_shgs ->
  val_mem segs (mrestrict (w_H W) mem) (rg_s fr_RG + 4) 4 (hb_ob b0) ->
  val_mem segs (mrestrict (w_H W) mem) (rg_s fr_RG + 100) 4 (hb_ob b1) ->
  val_mem segs (mrestrict (w_H W) mem) (rg_s fr_RG + 196) 4 (hb_ob b2) ->
  val_mem segs (mrestrict (w_H W) mem) (rg_s fr_RG + 292) 4 (hb_ob b3) ->
  (forall j, 0 <= j < 4 -> val_mem segs (mrestrict (w_H W) mem) (hb_shgs + 12 * j) 1 0) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (hb_x1 kb))) (hb_ss2 more b0 b1 b2 b3)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_pick)) mem (seg_rom segs)))
  /\ sh_ok segs hb_Bx (hb_SH2 more) (Eimg (Ereg regs (hb_x1 kb))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem more b0 b1 b2 b3 P1 F kb R23 R9 R27 R20 HP Hkb HF0 HF1 HPi HPa HPc MB RA M128 M152 G0 G1 G2 G3 SH0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (hb_x1 kb))) as E eqn:HE.
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E20 : ew E 20 = Z_to_bv 64 P1) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 kb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EG : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite hb_VAL_gs; reflexivity).
  assert (UG : bv_unsigned (ew E (A_OBJ 19)) = rg_s fr_RG) by (rewrite EG; apply unsigned_lit_small; cbn; lia).
  rewrite hb_shgs_val in *.
  split.
  - unfold hb_ss2, hb_sr. apply pa_entry_st_ok_full.
    + apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | discriminate | rewrite R23; reflexivity].
    + destruct more, b0, b1, b2, b3; vm_compute; reflexivity.
    + assert (RF : region_ok segs E (mrestrict (w_H W) mem) hb_rfr2).
      { unfold region_ok, hb_rfr2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
        rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        - apply (chunk_ok_val segs E _ F 128 8 (SOff (A_OBJ 19) 4) (rg_s fr_RG + 4));
            [cbn [sv_denot]; rewrite UG; reflexivity | cbn; zside | zside |]. exact M128.
        - apply (chunk_ok_val segs E _ F 152 8 (SLit 2148217292) 2148217292); [reflexivity | zside | zside |].
          exact M152. }
      assert (RG : region_ok segs E (mrestrict (w_H W) mem) (hb_rgs b0 b1 b2 b3)).
      { unfold region_ok, hb_rgs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
        rewrite UG. cbn [rg_s fr_RG fr_globals_b] in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        assert (OB : forall b, 0 <= hb_ob b < 2 ^ (8 * Z.of_N 4)) by (intros []; cbn; lia).
        repeat apply Forall_cons; try apply Forall_nil.
        - apply (chunk_ok_val segs E _ _ 4 4 (SLit (hb_ob b0)) (hb_ob b0)); [reflexivity | apply OB | zside | exact G0].
        - apply (chunk_ok_val segs E _ _ 100 4 (SLit (hb_ob b1)) (hb_ob b1)); [reflexivity | apply OB | zside | exact G1].
        - apply (chunk_ok_val segs E _ _ 196 4 (SLit (hb_ob b2)) (hb_ob b2)); [reflexivity | apply OB | zside | exact G2].
        - apply (chunk_ok_val segs E _ _ 292 4 (SLit (hb_ob b3)) (hb_ob b3)); [reflexivity | apply OB | zside | exact G3]. }
      assert (RS : region_ok segs E (mrestrict (w_H W) mem) hb_rsh).
      { unfold region_ok, hb_rsh. rewrite hb_shgs_val.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        - apply (chunk_ok_val segs E _ 0 2148217292 1 (SLit 0) 0); [reflexivity | zside | zside |].
          exact (SH0 0 ltac:(lia)).
        - apply (chunk_ok_val segs E _ 0 (2148217292 + 12) 1 (SLit 0) 0); [reflexivity | zside | zside |].
          exact (SH0 1 ltac:(lia)).
        - apply (chunk_ok_val segs E _ 0 (2148217292 + 24) 1 (SLit 0) 0); [reflexivity | zside | zside |].
          exact (SH0 2 ltac:(lia)).
        - apply (chunk_ok_val segs E _ 0 (2148217292 + 36) 1 (SLit 0) 0); [reflexivity | zside | zside |].
          exact (SH0 3 ltac:(lia)). }
      destruct more; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; try assumption.
      unfold region_ok, hb_rb1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E20, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ P1 0 1 (SOff 32 0) kb);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (MB eq_refl).
    + destruct more; cbn [app pairwise_disjoint all_disjoint];
        [pose proof (HPi eq_refl); pose proof (HPa eq_refl); pose proof (HPc eq_refl) |];
        unfold extent_disjoint, hb_rb1, hb_rfr2, hb_rgs, hb_rsh; rewrite ?hb_shgs_val;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
        rewrite ?E20, ?E9, ?UG, ?unsigned_lit_small by lia; cbn [rg_s fr_RG fr_globals_b];
        unfold kLowShadowBeg, kHighMemBeg in *; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [hb_f2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E20, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, hb_SH2; [constructor; [|constructor] | constructor].
    eapply shent_ok_of_range.
    + exact (RA eq_refl).
    + unfold U, hb_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* the registers walk 2 does not write, to D / arm 1 (it writes s4, t1, s5, a0, a2-a7, t0) and to H / X (also s5,
   s6, s9); s7 is pinned to 1 *)
Definition HB_KEPT2 : list (bv 5) := [2; 3; 4; 8; 9; 11; 18; 19; 22; 24; 25; 26; 27]%bv.
Definition HB_KEPT3 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 24; 26; 27]%bv.
(* after a run with no writable window: the memory is the one walk 2 began with *)
Ltac hb_meq mem0 :=
  lazymatch goal with HFx : frame_of _ ?rs ?m0 (ms_mem ?ms1) |- _ =>
    let Hm := fresh "HMm" in
    assert (Hm : ms_mem ms1 = mem0) by
      (apply functional_extensionality; let x := fresh "x" in intros x; rewrite HFx;
       [ first [ reflexivity | match goal with Hp : ms_mem _ = mem0 |- _ => rewrite Hp; reflexivity end ]
       | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
         intros (r & Hin & Hr); vm_compute in Hin;
         repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hin ]);
    clear HFx;
    repeat match goal with Ho : ms_mem _ = mem0 |- _ => lazymatch Ho with Hm => fail | _ => clear Ho end end;
    try rename Hm into HMm end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hb_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha; lia |] ].

Lemma hb_w2 : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> hb_INV_P cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D B G_fr fr_FP LS RINV cx t op W' c') \/
    INV_A B G_fr fr_FP LS RINV 1 cx t W' c' \/ INV_H B G_fr fr_FP LS RINV cx (t + 1) W' c' \/
    INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R26 & R27 & R3 & R4) & R25 & Ht & Hk & HO &
    R21 & R22 & R11 & Hpk & R20 & R6).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hblk) as Hpimg. unfold YCbq.off_img in Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold YCfn.LLVMF_STK in *.
  pose proof HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 & _).
  pose proof HMOD as (Hhs4 & Hslots & _).
  destruct (hb_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB0 Rb0].
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  pose proof Ht as Ht'. unfold OPS_MAX in Ht'.
  assert (Hkb : 0 <= hd_kb cx m < 256).
  { unfold hd_kb. destruct (lm_k m + 1 <? c_n cx) eqn:Hm1; [|lia].
    apply Z.ltb_lt in Hm1. exact (proj2 (hb_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (MB1 : (lm_k m + 1 <? c_n cx) = true ->
      val_mem segs (mrestrict (w_H W) mem) (c_p cx + lm_k m + 1) 1 (hd_kb cx m)).
  { intros Hm1. unfold hd_kb. rewrite Hm1. apply Z.ltb_lt in Hm1. rewrite <- Z.add_assoc.
    exact (proj1 (hb_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (RA1 : (lm_k m + 1 <? c_n cx) = true ->
      range_addressable (aview segs (w_H W) mem) SHADOW_OFF (c_p cx + lm_k m + 1) 1).
  { intros Hm1. apply Z.ltb_lt in Hm1.
    apply (range_addressable_of_block segs B LAWS ly3 S3 W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia]. }
  pose proof (hb_gs_shadow ly3 S3 W mem md HAR) as SH0.
  pose proof (hb_open_val ly3 S3 W mem 0 _ (Hslots 0%nat ltac:(lia))) as G0.
  pose proof (hb_open_val ly3 S3 W mem 1 _ (Hslots 1%nat ltac:(lia))) as G1.
  pose proof (hb_open_val ly3 S3 W mem 2 _ (Hslots 2%nat ltac:(lia))) as G2.
  pose proof (hb_open_val ly3 S3 W mem 3 _ (Hslots 3%nat ltac:(lia))) as G3.
  pose proof Hhs4 as Hl4.
  destruct (lm_hs m) as [|o0 [|o1 [|o2 [|o3 [|o4 rest]]]]] eqn:Hhs; cbn [length] in Hl4; try discriminate Hl4.
  rewrite ?Hhs in G0, G1, G2, G3. cbn [nth] in G0, G1, G2, G3.
  destruct (hb_entry2 W regs mem (lm_k m + 1 <? c_n cx) (hb_isS o0) (hb_isS o1) (hb_isS o2) (hb_isS o3) (c_p cx + lm_k m + 1)
    (lf_F cx) (hd_kb cx m) R23 R9 R27 R20 ltac:(lia) Hkb ltac:(lia) ltac:(lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    MB1 RA1 F128 F152 G0 G1 G2 G3 SH0) as [HS SHOK].
  remember (Eimg (Ereg regs (hb_x1 (hd_kb cx m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E11 : ew E 11 = Z_to_bv 64 (in_byte cx (lm_k m) mod 10)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E20 : ew E 20 = Z_to_bv 64 (c_p cx + lm_k m + 1)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E32 : ew E 32 = Z_to_bv 64 (hd_kb cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (UG : bv_unsigned (ew E 260) = rg_s fr_RG).
  { subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 260%nat with (A_OBJ 19). rewrite hb_VAL_gs.
    apply unsigned_lit_small. cbn; lia. }
  assert (HAE : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  assert (EG' : ew E 260 = Z_to_bv 64 (rg_s fr_RG)) by (rewrite <- UG; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hnone : (lm_hs m = [None; None; None; None]) -> pick (lm_hs m) (hd_kb cx m) = None)
    by (intros Hn; unfold pick, nopen; rewrite Hn; reflexivity).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_pick)) with (Z_to_bv 64 (BASE + AF_LLVM_pick)).
  revert HS SHOK. destruct (lm_k m + 1 <? c_n cx) eqn:Hmore; intros HS SHOK.
  all: destruct o0 as [h0|]; destruct o1 as [h1|]; destruct o2 as [h2|]; destruct o3 as [h3|].
  all: cbn [hb_isS] in HS; norm_ss HS; cbn [hb_SH2] in SHOK.
  (* the test of in.n - 1 (t1): the side that contradicts `more` is refuted *)
  all: psrr_branch_tok RUN BR HS SHOK hb_Bspan.
  all: rewrite branch_eq_U, (U_atom E 6 (c_n cx - lm_k m - 1) E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc];
    first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore]; lia).
  all: clear Hc.
  (* the second byte (when in.n > 1) with its PTR_INC trap, the open count with its ADDW trap, to the remainder
     (0x846c4), or, with no open source, to `bne a1,s7` (0x8471c) *)
  all: paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan 9088.
  all: try hb_awr0.
  all: hb_meq mem.
  32:
  { psrr_branch_tok RUN BR HS SHOK hb_Bspan.
    - (* op <> 1: `continue`, to B's latch tail 0x8480c *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok RUN HS HJ SHOK hb_Bspan. { hb_awr0. } hb_meq mem.
      psrr_branch_tok RUN BR HS SHOK hb_Bspan.
      + (* t + 1 <> 512: the head of operation t + 1 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ne_U, (hb_addiw_U Ev t ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(lia)), U_lit in Hc by lia end.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Ht1.
        paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_head. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]);
        assert (U25 : U Ev (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1)
          by (apply hb_addiw_U; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
        hb_prreg_raw HS (25%bv : bv 5) Q25.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; left.
        lazymatch goal with |- INV_H _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        rewrite ?ew_ewset_other in Q21, Q22 by lia.
        rewrite ?E21 in Q21. rewrite ?E6 in Q21. rewrite ?E22 in Q22. rewrite ?E20 in Q22.
        rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
          | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
        split; [rewrite Q25; apply hb_sv_of_U; [exact U25 | lia]|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite Q22; unfold w64; f_equal; lia|].
        unfold OPS_MAX in *. lia.
      + (* t + 1 = 512: the shutdown block *)
        paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_exit. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ].
    - (* op = 1 with no open source: arm 1 (0x84724) with s5 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_arm_write. { hb_awr0. } hb_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(hb_in)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q20, Q6 by lia.
      rewrite ?E22 in Q20. rewrite ?E20 in Q20. rewrite ?E21 in Q6. rewrite ?E6 in Q6.
      rewrite ?unsigned_lit_small in Q20 by lia. rewrite ?unsigned_lit_small in Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  16:
  { psrr_branch_tok RUN BR HS SHOK hb_Bspan.
    - (* op <> 1: `continue`, to B's latch tail 0x8480c *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok RUN HS HJ SHOK hb_Bspan. { hb_awr0. } hb_meq mem.
      psrr_branch_tok RUN BR HS SHOK hb_Bspan.
      + (* t + 1 <> 512: the head of operation t + 1 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ne_U, (hb_addiw_U Ev t ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(lia)), U_lit in Hc by lia end.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Ht1.
        paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_head. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]);
        assert (U25 : U Ev (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1)
          by (apply hb_addiw_U; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
        hb_prreg_raw HS (25%bv : bv 5) Q25.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; left.
        lazymatch goal with |- INV_H _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        rewrite ?ew_ewset_other in Q21, Q22 by lia.
        rewrite ?E21 in Q21. rewrite ?E6 in Q21. rewrite ?E22 in Q22. rewrite ?E20 in Q22.
        rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
          | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
        split; [rewrite Q25; apply hb_sv_of_U; [exact U25 | lia]|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite Q22; unfold w64; f_equal; lia|].
        unfold OPS_MAX in *. lia.
      + (* t + 1 = 512: the shutdown block *)
        paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_exit. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ].
    - (* op = 1 with no open source: arm 1 (0x84724) with s5 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_arm_write. { hb_awr0. } hb_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(hb_in)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q20, Q6 by lia.
      rewrite ?E22 in Q20. rewrite ?E20 in Q20. rewrite ?E21 in Q6. rewrite ?E6 in Q6.
      rewrite ?unsigned_lit_small in Q20 by lia. rewrite ?unsigned_lit_small in Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  (* an open source: the remainder kb % n (pinned to its value), the k-th open source, to the dispatch *)
  all: lazymatch goal with HS : st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) |- _ =>
    let a2 := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in
    lazymatch a2 with
    | SMdw M_REM (SOff 32 0) (SLit ?c) =>
        assert (UR : U Ev (SMdw M_REM (SOff 32 0) (SLit c)) = hd_kb cx m mod c)
          by (apply hb_rem_U; [rewrite ?ew_ewset_other by lia; exact E32 | exact Hkb | lia]);
        pose proof (st_ok_pi_restrict_reg H Ev ss ms 12%bv HS) as Q12;
        change (sr_get (ss_regs ss) 12%bv) with a2 in Q12; cbn [ms_regs restrict] in Q12;
        pose proof (Z.mod_pos_bound (hd_kb cx m) c ltac:(lia)) as Rr;
        assert (Hr4 : hd_kb cx m mod c = 0 \/ hd_kb cx m mod c = 1 \/ hd_kb cx m mod c = 2 \/ hd_kb cx m mod c = 3)
          by lia
    | _ => idtac
    end end.
  all: try (destruct Hr4 as [HR | [HR | [HR | HR]]]).
  all: try (match goal with HR : hd_kb _ _ mod ?c = ?r, Rr : 0 <= _ < ?c |- _ => exfalso; clear - HR Rr; lia end).
  all: try (lazymatch goal with HR : hd_kb _ _ mod _ = ?r, Q12 : getr _ 12%bv = _, UR : U _ _ = _ |- _ =>
       lazymatch goal with HS : st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) |- _ =>
         pose proof (st_ok_pi_pin_reg' Ev ss (restrict H ms) 12%bv r HS
            ltac:(cbn [ms_regs restrict]; rewrite Q12; apply hb_sv_of_U; [rewrite UR; exact HR | lia]) eq_refl) as HS2;
         clear HS; rename HS2 into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; norm_ss HS end end).
  all: try (unfold hd_kb in HR; rewrite Hmore in HR; cbv iota in HR).
  all: paj_run_to_tok RUNTO HS HJ SHOK hb_Bspan AF_LLVM_dispatch.
  all: try hb_awr0.
  all: hb_meq mem.
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (23%bv : bv 5) Q23; prreg HS (20%bv : bv 5) Q20; prreg HS (6%bv : bv 5) Q6.
  all: prreg HS (21%bv : bv 5) Q21.
  all: pmkst HS.
  all: rewrite HMm; rewrite HMm in HJ.
  all: apply SRr_ret; left; exists (in_byte cx (lm_k m) mod 10); split; [lia|].
  all: lazymatch goal with |- INV_D _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
  all: split; [reflexivity|].
  all: split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
  all: split; [exists [(1, fpos)], ly3, S3, k; exact HJ|].
  all: split; [exact HROM|].
  all: exists [(1, fpos)], ly3, S3, k, m, fpos.
  all: split; [exact HJ|]; split; [reflexivity|]; split; [exact HFR|]; split; [exact HFL|]; split; [exact HMOD|]; split; [exact HIN|].
  all: split; [exact HRV|]; split; [exact HSEP|]; split; [exact HLS|]; split; [exact HRI|].
  all: unfold lregs_D; cbv zeta; rewrite Hpk; cbv iota; rewrite Hmore; cbv iota.
  all: rewrite ?ew_ewset_other in Q21, Q20, Q6 by lia.
  all: rewrite ?E22 in Q20; rewrite ?E20 in Q20; rewrite ?E21 in Q6; rewrite ?E6 in Q6; rewrite ?EG' in Q21.
  all: rewrite ?unsigned_lit_small in Q21 by (cbn; lia); rewrite ?unsigned_lit_small in Q20 by lia;
    rewrite ?unsigned_lit_small in Q6 by lia.
  all: split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
      | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
  all: split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
  all: split; [exact Ht|]; split; [exact Hk|]; split; [exact HO|].
  all: split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
  all: split; [rewrite Q20; unfold w64; f_equal; lia|].
  all: split; [rewrite Q6; unfold w64; f_equal; lia|].
  all: left; eexists; split.
  all: try (unfold pick; rewrite Hhs;
    lazymatch goal with |- context [nopen ?l] => let v := eval vm_compute in (nopen l) in change (nopen l) with v end;
    try rewrite HR; reflexivity).
  all: rewrite Q21; unfold w64, ASRC; f_equal; cbn [Z.of_nat Pos.of_succ_nat]; cbn; lia.
Qed.

(* ------------------------------------------------------------------ SEG_HEAD (_cut.v :744) *)
Theorem lf_seg_head_b : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_H B G_fr fr_FP LS RINV cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D B G_fr fr_FP LS RINV cx t op W' c') \/
    INV_A B G_fr fr_FP LS RINV 1 cx t W' c' \/
    INV_H B G_fr fr_FP LS RINV cx (t + 1) W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx t W c HB HH.
  eapply SRr_bind; [exact (hb_w1 cx t W c HB HH)|].
  intros W1 c1 _ [HD | [HP | HX]].
  - apply SRr_ret. left. exact HD.
  - exact (hb_w2 cx t W1 c1 HB HP).
  - apply SRr_ret. right; right; right. exact HX.
Qed.

End hb.
