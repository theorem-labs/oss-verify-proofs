(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the engine run from a fresh entry state and
   its re-seat at a fixed pc) for the value dispatch and the Int arm of reac-pw/fuzz_role's image-A segment M02
   (0x82318 .. 0x823e0). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyI.v at 7e8cf15c304 (the run / branch
   / exit pattern of a value dispatch, the entry state re-seated once the value entry's address is formed) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v at 7e8cf15c304 (m2k_ent_type_slice, m2k_ent_size_slice,
   m2k_ent_word_slice) for reac-pw/fuzz_headamp image A: the m2i_ / m2k_ prefixes are renamed hvd_, every address
   is headamp's own, role's two arms and its MAL exit are replaced by headamp's Bool and Int arms with their five
   exits, and the cuts are lib/A/HPgSegM.v's and lib/A/HPgM3dBase.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dDisp.v, with its module names and addresses changed; 1442 of its 1596 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgM3dDispU.v, with its module paths and module names changed; 1491 of its 1785 lines of code are new or changed and 1302 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the float step from cut FA of the
   piece value of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgM3dBaseU.v hvu_piece_flt_stmt
   (FA 0x83578 -> CV 0x83608 / RF 0x836a0). Proves no function (kind: segment lemma).

   THE CODE (the Float arm of the inlined cell_value up to `fcvt.l.s`, pod.h:116-160)
     0x83578  add a1,a3,s8                    a1 := &ent[v].size
     0x8357c  .. 0x83588  the instrumented check of &ent[v].size (slow block 0x837dc, which writes a3)
     0x8358c  lw a0,4(a0); li a2,4; bltu      size < 4 -> RF 0x836a0
     0x83598  sd a6,0x90(s1)                  R+0x90 := the param
     0x8359c  ld a0,0xe0(s1); add a0,a0,s8    a0 := &ent[v].body
     0x835a4  .. 0x835b0  the instrumented check of &ent[v].body (slow block 0x8383c, which writes a0)
     0x835b4  ld a0,0xe8(s1); add s8,a0,s8    s8 := &ent[v].body
     0x835bc  flw fs0,0(s8); feq.s; beqz      NaN -> the Float refusal 0x83664
     0x835c8  fmv.s fa0,fs0; jal __extendsftf2 (ra 0x835d0); mv s8,a0
     0x835d4  flt.s a0,fs0,fs1; sd a1,0x88(s1); bnez     b < -1.0f -> 0x83664
     0x835e0  flt.s a0,fs2,fs0; bnez                     256.0f < b -> 0x83664
     0x835e8  flt.s a0,fs0,fs3; beqz -> unimp            the float-cast check, never taken
     0x835f0  mv a0,s8; ld a1,0x88(s1); ld a2,0xb8(s1); ld a3,0xb0(s1); jal __gttf2 (ra 0x83604)
     0x83604  blez a0 -> unimp                           the float-cast check, never taken; then CV 0x83608
     0x83664  ld t5,0x110(s1); ld t6,0x108(s1); li a5,5; j RF     the Float refusal
   Registers read: a0 a3 a5 a6 s1 s5 s7 s8 s11 t5 t6 (FA's); float registers fs0 fs1 fs2 fs3. Real-frame cells read:
   R+0x88, R+0xb0, R+0xb8, R+0xe0, R+0xe8, R+0x108, R+0x110; written: R+0x88 (high word of d), R+0x90 (the param).

   HOW. The kit's engine (lib/Reusable/YCbq.v aj_run_tok) decides an instrumented check only when the checked address
   is a register of its entry state, and it has no rule for a float instruction, so the lane is a chain of block
   lemmas (hvf_b1 .. hvf_b17, hvf_rfl), each entered at a pc where the next check's address is a register, the float
   steps of lib/AU/HPgM3dFpU.v and the two soft-float calls of lib/AU/HPgCallsSFIU.v (hsfu_ext_stmt,
   hsfu_ge_stmt). hvf_I is what the lane carries from block to block (the cut base, the segment's fixed registers
   and real-frame cells, the float constants, the pair's facts and x); hvf_move carries it across a block, a float
   step or a call (a byte of the errno cell is either kept or one of the two stored real-frame cells, which the
   journal's stack window has present, so no hypothesis on errno's address is needed). The two float-cast checks
   (`flt.s fs0,fs3` and __gttf2 against -(2^63 + 1)) are never taken (hvf_traps, Near.v's hn_traps restated); a
   refused value (NaN, below -1.0f, above 256.0f, size below 4) gives expect_cell's OUT_OF_RANGE by
   lib/A/HPgM3dVal.v. hvu_flt_B composes them under one Section hypothesis, MTL : ameter_laws MT (the soft-float
   adapters of lib/AU/HPgCallsSFIU.v take it). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require NearVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors Nearest.
From Stdlib Require SpecFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgM3dVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSiteA HPgM3dFp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgM3dBaseU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgM3dDispU HPgM3dFpU HPgM3dSFU HPgCallsSFIU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the kit's modules whose short names lib/U/Reusable also uses, by full path (a file that loads lib/U/Reusable
   next to this one then still reads them as the kit's) *)
Module FP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.HPgM3dFp.
Module KI16 := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YI16.
Module KO0c := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YO0c.
Module KN0d := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YN0d.

(* ================================ the pcs and the kept registers ================================ *)
Definition HVF_B2 : Z := 0x8357c.     (* the size check, a1 = &ent[v].size *)
Definition HVF_B3 : Z := 0x83598.     (* `sd a6,0x90(s1)` *)
Definition HVF_B4 : Z := 0x835a4.     (* the body check, a0 = &ent[v].body *)
Definition HVF_B7 : Z := 0x835c4.     (* `beqz a0` after feq.s *)
Definition HVF_B9 : Z := 0x835cc.     (* `jal __extendsftf2` *)
Definition HVF_B10 : Z := 0x835d0.    (* `mv s8,a0` *)
Definition HVF_B12 : Z := 0x835d8.    (* `sd a1,0x88(s1); bnez a0` *)
Definition HVF_B14 : Z := 0x835e4.    (* `bnez a0` after the second flt.s *)
Definition HVF_B16 : Z := 0x835ec.    (* `beqz a0 -> unimp`, then the __gttf2 arguments and `jal` *)
Definition HVF_B17 : Z := 0x83604.    (* `blez a0 -> unimp` *)

Definition hvf_all : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvf_b1_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvf_b3_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvf_rfl_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29].
Definition hvf_b9_kept : list (bv 5) :=
map (Z_to_bv 5) [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvf_b10_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27;
  28; 29; 30; 31].
Definition hvf_b16_kept : list (bv 5) :=
map (Z_to_bv 5) [2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* ================================ the entry states ================================ *)
Definition hvf_ss_nr (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* R+0x90 written, R+0xe0 read; a region with a write window needs R's bounds among the facts (hvu_facts []: atom 9
   in [2 ^ 46, 2 ^ 47]), so that the engine sees the window apart from the shadow band *)
Definition hvf_b3_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x90 0xe8 0x90 0x98 [YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0))].
Definition hvf_b3_ss0 : sstate := mkSS HVF_B3 sr_atoms [hvf_b3_R] None (hvu_facts []).
(* R+0x108 and R+0x110 read *)
Definition hvf_rfl_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x108 0x118 0 0
    [YP09.mkChunk 0x108 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 34 0))].
Definition hvf_rfl_ss0 : sstate := mkSS HVU_RFL sr_atoms [hvf_rfl_R] None (mkFacts [] [] []).
Definition hvf_extra2 (v5 v6 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 v5; Z_to_bv 64 v6].
(* R+0x88 written *)
Definition hvf_b12_R : YP09.region := YP09.mkRegion (Some 9%nat) 0x88 0x90 0x88 0x90 [].
Definition hvf_b12_ss0 : sstate := mkSS HVF_B12 sr_atoms [hvf_b12_R] None (hvu_facts []).
(* R+0x88, R+0xb0 and R+0xb8 read *)
Definition hvf_b16_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0xc0 0 0
    [YP09.mkChunk 0x88 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xb0 (CVal 8 (SOff 34 0));
     YP09.mkChunk 0xb8 (CVal 8 (SOff 35 0))].
Definition hvf_b16_ss0 : sstate := mkSS HVF_B16 sr_atoms [hvf_b16_R] None (mkFacts [] [] []).
Definition hvf_extra3 (v1 v2 v3 : Z) : list word :=
  [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 v1; Z_to_bv 64 v2; Z_to_bv 64 v3].

(* the bytes a run changed lie in the write windows of its entry regions *)
Ltac hvf_memw Wr E9u :=
lazymatch goal with HFr : frame_of ?E0 ?rs0 (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
  let HK := fresh "HKw" in
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs H m1 a = aview rsegs H m0 a)
    by (intros a Ha Hw;
        apply (hvu_kept_run Wr E0 rs0 H m0 m0 m1); [intros; reflexivity | exact HFr | | exact Ha | exact Hw];
        let a' := fresh "a" in let r' := fresh "r" in let Hin := fresh "Hin" in let Ha' := fresh "Ha" in
        intros a' (r' & Hin & Ha');
        repeat match type of Hin with
        | In _ (ss_mem ?s) => unfold s in Hin
        end;
        cbn [ss_mem In] in Hin;
        repeat (destruct Hin as [<-|Hin];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hvf_b3_R hvf_b12_R] in Ha'; rewrite ?E9u in Ha';
                 cbv beta; lia|]);
        destruct Hin);
  clear HFr;
  repeat match goal with H' : frame_of _ _ _ _ |- _ => clear H' | H' : mem_grows _ _ |- _ => clear H' end
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : KI16.sink_head}.
Section d.
Variable B : asyms.

(* ================================ b1: 0x83578 -> 0x8357c, `add a1,a3,s8` ================================ *)
Lemma hvf_b1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (av o : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 13) = w64 av -> getr regs (Z_to_bv 5 24) = w64 o ->
0 <= av -> 0 <= o -> av + o < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs HVU_FA regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVF_B2 hvf_b1_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 11) = w64 (av + o))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs av o HJ H13 H24 Ha Ho Hs.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 av) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (HS : st_ok rsegs (Ereg regs ex) (hvf_ss_nr HVU_FA)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_FA) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_ss_nr. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVU_FA) with (Z_to_bv 64 HVU_FA).
hvu_run_to HPgSteps.RTBspan awr_ok_tac HVF_B2. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvf_b1_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 13 av E13 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* ================================ b2: 0x8357c -> RF 0x836a0 / 0x83598 ================================
   the size check (slow block 0x837dc, which writes a3), `lw a0,4(a0)`, `li a2,4` and the size test *)
Definition hvf_b2_ss0 : sstate := mkSS HVF_B2 sr_atoms [hvu_q3a_ent] None (hvu_facts [11%nat]).

Lemma hvf_b2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R A sz : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 A ->
getr regs (Z_to_bv 5 11) = w64 (A + 4) -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= A -> A + 16 <= 0x7fffff800000 -> 0 <= sz <= 45 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (A + 4) 4 ->
(A + 16 <= kLowShadowBeg \/ kHighMemBeg <= A) ->
val_mem rsegs (mrestrict (w_H W) memc) (A + 4) 4 sz ->
SRr rsegs W (cfg_at rsegs HVF_B2 regs memc mdc)
(fun W2 c2 =>
 (sz < 4 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvu_q6a_kept
    (fun _ => True) W2 c2) \/
 (4 <= sz /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVF_B3 hvu_q6a_kept
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R A sz HJ H9 H10 H11 H27
  HR Hal HA0 HA1 Hsz Hra Happ VA.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvu_q3a_extra sz) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 A) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 (A + 4))
  by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 sz) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvf_b2_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B2) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_b2_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 10 A);
      [rewrite E10; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    eapply (chunk_ok_val rsegs _ _ A 4 4 (SOff 33 0) sz);
      [rewrite hvu_denot0, E33; reflexivity | lia | cbn; lia | exact VA].
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 11 (A + 4) ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E11; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 11 0 4] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 11 (A + 4) 4);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 11 (A + 4) E11 ltac:(lia)); reflexivity | exact Hra | lia
  | destruct Happ as [Hp|Hp]; [left; lia | right; lia] | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (Usz : U E (SExt true 32 (SOff 33 0)) = sz)
  by (rewrite (hvu_U_sext32 E 33 sz E33 ltac:(lia)); apply hvm_sx_id; lia).
unfold cfg_at. change (w64 HVF_B2) with (Z_to_bv 64 HVF_B2).
hvu_run HVU_Bspan awr_ok_tac. hvu_mem.
hvu_branch HVU_Bspan Hc.
all: hvu_unext Hc.
all: rewrite Usz, U_SLit in Hc.
all: change (zcanon 4) with 4 in Hc.
all: rewrite KO0c.branch_ltu, !unsigned_lit_small in Hc by lia.
- hvu_run_to HVU_Bspan awr_ok_tac HQU_RF. hvu_mem.
  apply SRr_ret; left. split; [apply Z.ltb_lt in Hc; exact Hc|].
  hvu_post0x B hvu_q6a_kept. exact I.
- hvu_run_to HVU_Bspan awr_ok_tac HVF_B3. hvu_mem.
  apply SRr_ret; right. split; [apply Z.ltb_ge in Hc; exact Hc|].
  hvu_post0x B hvu_q6a_kept. exact I.
Qed.

(* ================================ b3: 0x83598 -> 0x835a4 ================================
   `sd a6,0x90(s1)` (R+0x90 := the param), `ld a0,0xe0(s1); add a0,a0,s8` *)
Lemma hvf_b3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R p o vb8 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 16) = w64 p -> getr regs (Z_to_bv 5 24) = w64 o ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> sp0 - STK <= R + 0x90 -> R + 0x98 <= sp0 ->
0 <= p < 2 ^ 64 -> 0 <= o -> 0 <= vb8 -> vb8 + o < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (vb8 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HVF_B3 regs memc mdc)
(hvu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVF_B4 hvf_b3_kept
  (fun a => R + 0x90 <= a < R + 0x98)
  (fun regs2 mem2 => getr regs2 (Z_to_bv 5 10) = w64 (vb8 + o) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x90) 8 p)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R p o vb8 HJ H9 H16 H24 H27
  HR Hal HSlo HShi Hp Ho Hvb8 Hsum V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite (Z.mod_small vb8 (2 ^ 64)) in V by lia.
remember (hvu_q3b_extra vb8) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 p) by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb8) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (HS : st_ok rsegs (Ereg regs ex) hvf_b3_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B3) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_b3_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia | intros o' Ho'; apply Hpres; lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0xe0 vb8 33 E33 ltac:(rewrite Z.mod_small by lia; exact V)).
  - cbn. tauto.
  - exact (hvu_facts_ok0 _ R ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)). }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (E9u : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 HVF_B3) with (Z_to_bv 64 HVF_B3).
hvu_run_to HPgSteps.RTBspan hvu_awr HVF_B4.
hvf_memw (fun a => R + 0x90 <= a < R + 0x98) E9u.
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  let rr := eval vm_compute in (nth_error (ss_mem ss') 0) in
  lazymatch rr with Some ?r0 =>
    pose proof (KN0d.st_ok_chunk rsegs E' ss' (restrict (w_H W) ms) 0%nat r0
      (YP09.mkChunk 0x90 (CVal 8 (SOff 16 0))) HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as HC90 end end.
cbn [base_val YP09.r_base] in HC90. rewrite E9u in HC90.
eapply (hvu_post_intro B); [eassumption | reflexivity | reflexivity | eassumption | hvu_io | hvu_kept hvf_b3_kept
  | eassumption | ].
split.
- lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 33 vb8 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
- exact (hvu_chunk8_val E _ R 0x90 (SOff 16 0) p ltac:(rewrite hvu_denot0, E16; reflexivity) Hp HC90).
Qed.

(* ================================ b4: 0x835a4 -> 0x835bc ================================
   the body check (slow block 0x8383c, which writes a0), `ld a0,0xe8(s1); add s8,a0,s8` *)
Definition hvf_b4_ss0 : sstate := mkSS HVF_B4 sr_atoms [hvu_q4_R] None (hvu_facts [10%nat]).

Lemma hvf_b4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R Ab o vb8 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 Ab ->
getr regs (Z_to_bv 5 24) = w64 o -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> R + 0xf0 <= 2 ^ 64 ->
4096 <= Ab -> Ab + 4 <= 0x7fffff800000 -> 0 <= o -> 0 <= vb8 -> vb8 + o < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF Ab 4 ->
(Ab + 4 <= kLowShadowBeg \/ kHighMemBeg <= Ab) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (vb8 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HVF_B4 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVFU_FLW hvu_q4_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 24) = w64 (vb8 + o))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R Ab o vb8 HJ H9 H10 H24 H27
  HR Hal HR1 HA0 HA1 Ho Hvb8 Hsum Hra Happ V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (Z.mod_small vb8 (2 ^ 64)) in V by lia.
remember (hvu_q4_extra vb8) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 Ab) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb8) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvf_b4_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B4) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_b4_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0xe8 vb8 33 E33 ltac:(rewrite Z.mod_small by lia; exact V)).
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 10 Ab ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 10 0 4] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 10 Ab 4);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 10 Ab E10 ltac:(lia)); reflexivity | exact Hra | lia | exact Happ | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVF_B4) with (Z_to_bv 64 HVF_B4).
hvu_run_to HVU_Bspan awr_ok_tac HVFU_FLW. hvu_mem.
apply SRr_ret. hvu_post0x B hvu_q4_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !hvu_U_ewset by (first [lia | (vm_compute; reflexivity)]).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 33 vb8 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* ================================ b7: 0x835c4 `beqz a0` -> 0x83664 / 0x835c8 ================================ *)
Lemma hvf_b7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 (if c then 1 else 0) ->
SRr rsegs W (cfg_at rsegs HVF_B7 regs memc mdc)
(fun W2 c2 =>
 (c = false /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_RFL hvf_all
    (fun _ => True) W2 c2) \/
 (c = true /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVFU_FMV hvf_all
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ H10.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 (if c then 1 else 0))
  by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs ex) (hvf_ss_nr HVF_B7)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_ss_nr. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVF_B7) with (Z_to_bv 64 HVF_B7).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite !hvu_denot0, E10 in Hc.
all: cbn [sv_denot] in Hc.
- (* taken: a0 = 0 *)
  destruct c; [exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc|].
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_RFL. hvu_mem.
  apply SRr_ret; left. split; [reflexivity|].
  hvu_post0_tac B hvf_all. exact I.
- (* not taken: a0 = 1 *)
  destruct c; [|exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc].
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVFU_FMV. hvu_mem.
  apply SRr_ret; right. split; [reflexivity|].
  hvu_post0_tac B hvf_all. exact I.
Qed.

(* ================================ rfl: 0x83664 -> RF 0x836a0 ================================
   `ld t5,0x110(s1); ld t6,0x108(s1); li a5,5; j` *)
Lemma hvf_rfl : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R v5 v6 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x118 <= 2 ^ 64 -> 0 <= v5 < 2 ^ 64 -> 0 <= v6 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (v5 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (v6 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HVU_RFL regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvf_rfl_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 30) = w64 v5 /\ getr regs2 (Z_to_bv 5 31) = w64 v6 /\
     getr regs2 (Z_to_bv 5 15) = w64 Headamp.REFUSE_OUT_OF_RANGE)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R v5 v6 HJ H9 HR0 HR1 Hv5 Hv6 V5 V6.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvf_extra2 v6 v5) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 v6) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 v5) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hvf_rfl_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_RFL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_rfl_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + exact (hvu_slot_chunk _ _ _ R 0x108 v6 33 E33 V6).
    + exact (hvu_slot_chunk _ _ _ R 0x110 v5 34 E34 V5).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVU_RFL) with (Z_to_bv 64 HVU_RFL).
hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_RF. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvf_rfl_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split; [|split].
- hvu_sv. rewrite hvu_denot0, E34. reflexivity.
- hvu_sv. rewrite hvu_denot0, E33. reflexivity.
- hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

(* ================================ b9: 0x835cc `jal __extendsftf2` ================================ *)
Lemma hvf_b9 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
SRr rsegs W (cfg_at rsegs HVF_B9 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_SF_EXT hvf_b9_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 1) = w64 HVU_RA_EXT)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (HS : st_ok rsegs (Ereg regs ex) (hvf_ss_nr HVF_B9)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B9) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_ss_nr. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HVF_B9) with (Z_to_bv 64 HVF_B9).
hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_SF_EXT. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvf_b9_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

(* ================================ b10: 0x835d0 `mv s8,a0` ================================ *)
Lemma hvf_b10 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (lo : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 lo -> 0 <= lo < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs HVF_B10 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVFU_LT1 hvf_b10_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 24) = w64 lo)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs lo HJ H10 Hlo.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 lo) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs ex) (hvf_ss_nr HVF_B10)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B10) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_ss_nr. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVF_B10) with (Z_to_bv 64 HVF_B10).
hvu_run_to HPgSteps.RTBspan awr_ok_tac HVFU_LT1. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvf_b10_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
first [ exact (U_atom E 10 lo E10 ltac:(lia))
      | rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 10 lo E10 ltac:(lia)), U_SLit;
        unfold zcanon, M64; rewrite Z.add_0_r, Z.mod_small by lia; reflexivity ].
Qed.

(* ================================ b12: 0x835d8 `sd a1,0x88(s1); bnez a0` -> 0x83664 / 0x835e0 ================ *)
Lemma hvf_b12 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R h : Z) (c : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 (if c then 1 else 0) ->
getr regs (Z_to_bv 5 11) = w64 h -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> sp0 - STK <= R + 0x88 -> R + 0x90 <= sp0 -> 0 <= h < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs HVF_B12 regs memc mdc)
(fun W2 c2 =>
 (c = true /\ hvu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_RFL hvf_all
    (fun a => R + 0x88 <= a < R + 0x90)
    (fun _ mem2 => val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x88) 8 h) W2 c2) \/
 (c = false /\ hvu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVFU_LT2 hvf_all
    (fun a => R + 0x88 <= a < R + 0x90)
    (fun _ mem2 => val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x88) 8 h) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R h c HJ H9 H10 H11 H27 HR Hal HSlo HShi Hh.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 (if c then 1 else 0))
  by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 h) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (HS : st_ok rsegs (Ereg regs ex) hvf_b12_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B12) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_b12_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia | intros o' Ho'; apply Hpres; lia | constructor].
  - cbn. tauto.
  - exact (hvu_facts_ok0 _ R ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)). }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (E9u : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 HVF_B12) with (Z_to_bv 64 HVF_B12).
hvu_run HPgSteps.RTBspan hvu_awr.
hvf_memw (fun a => R + 0x88 <= a < R + 0x90) E9u.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite !hvu_denot0, E10 in Hc.
all: cbn [sv_denot] in Hc.
- (* taken: a0 <> 0 *)
  destruct c; [|exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc].
  hvu_run_to HPgSteps.RTBspan hvu_awr HVU_RFL.
  hvf_memw (fun a => R + 0x88 <= a < R + 0x90) E9u.
  apply SRr_ret; left. split; [reflexivity|].
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss') 0) in
    lazymatch rr with Some ?r0 =>
      pose proof (KN0d.st_ok_chunk rsegs E' ss' (restrict (w_H W) ms) 0%nat r0
        (YP09.mkChunk 0x88 (CVal 8 (SOff 11 0))) HS ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as HC88 end end.
  cbn [base_val YP09.r_base] in HC88. rewrite E9u in HC88.
  eapply (hvu_post_intro B); [eassumption | reflexivity | reflexivity | eassumption | hvu_io | hvu_kept hvf_all
    | | exact (hvu_chunk8_val E _ R 0x88 (SOff 11 0) h ltac:(rewrite hvu_denot0, E11; reflexivity) Hh HC88)].
  intros a Ha Hw.
  match goal with H1 : forall a, _ -> ~ _ -> aview _ _ ?m2 a = aview _ _ ?m1 a,
                  H2 : forall a, _ -> ~ _ -> aview _ _ ?m1 a = aview _ _ memc a |- _ =>
    rewrite (H1 a Ha Hw); exact (H2 a Ha Hw) end.
- (* not taken: a0 = 0 *)
  destruct c; [exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc|].
  hvu_run_to HPgSteps.RTBspan hvu_awr HVFU_LT2.
  hvf_memw (fun a => R + 0x88 <= a < R + 0x90) E9u.
  apply SRr_ret; right. split; [reflexivity|].
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss') 0) in
    lazymatch rr with Some ?r0 =>
      pose proof (KN0d.st_ok_chunk rsegs E' ss' (restrict (w_H W) ms) 0%nat r0
        (YP09.mkChunk 0x88 (CVal 8 (SOff 11 0))) HS ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as HC88 end end.
  cbn [base_val YP09.r_base] in HC88. rewrite E9u in HC88.
  eapply (hvu_post_intro B); [eassumption | reflexivity | reflexivity | eassumption | hvu_io | hvu_kept hvf_all
    | | exact (hvu_chunk8_val E _ R 0x88 (SOff 11 0) h ltac:(rewrite hvu_denot0, E11; reflexivity) Hh HC88)].
  intros a Ha Hw.
  match goal with H1 : forall a, _ -> ~ _ -> aview _ _ ?m2 a = aview _ _ ?m1 a,
                  H2 : forall a, _ -> ~ _ -> aview _ _ ?m1 a = aview _ _ memc a |- _ =>
    rewrite (H1 a Ha Hw); exact (H2 a Ha Hw) end.
Qed.

(* ================================ b14: 0x835e4 `bnez a0` -> 0x83664 / 0x835e8 ================================ *)
Lemma hvf_b14 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 (if c then 1 else 0) ->
SRr rsegs W (cfg_at rsegs HVF_B14 regs memc mdc)
(fun W2 c2 =>
 (c = true /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_RFL hvf_all
    (fun _ => True) W2 c2) \/
 (c = false /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVFU_LT3 hvf_all
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ H10.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 (if c then 1 else 0))
  by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs ex) (hvf_ss_nr HVF_B14)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B14) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_ss_nr. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVF_B14) with (Z_to_bv 64 HVF_B14).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite !hvu_denot0, E10 in Hc.
all: cbn [sv_denot] in Hc.
- (* taken: a0 <> 0 *)
  destruct c; [|exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc].
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_RFL. hvu_mem.
  apply SRr_ret; left. split; [reflexivity|].
  hvu_post0_tac B hvf_all. exact I.
- (* not taken: a0 = 0 *)
  destruct c; [exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc|].
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVFU_LT3. hvu_mem.
  apply SRr_ret; right. split; [reflexivity|].
  hvu_post0_tac B hvf_all. exact I.
Qed.

(* ================================ b16: 0x835ec -> `jal __gttf2` ================================
   `beqz a0 -> unimp` (a0 = 1: never taken), `mv a0,s8; ld a1,0x88(s1); ld a2,0xb8(s1); ld a3,0xb0(s1)` *)
Lemma hvf_b16 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R lo hi c2hi c2lo : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 1 -> getr regs (Z_to_bv 5 24) = w64 lo ->
0 <= R -> R + 0xc0 <= 2 ^ 64 -> 0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> 0 <= c2hi < 2 ^ 64 ->
0 <= c2lo < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x88) 8 (hi mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 (c2hi mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (c2lo mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HVF_B16 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_SF_GE hvf_b16_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 1) = w64 HVU_RA_GT /\ getr regs2 (Z_to_bv 5 10) = w64 lo /\
     getr regs2 (Z_to_bv 5 11) = w64 hi /\ getr regs2 (Z_to_bv 5 12) = w64 c2lo /\
     getr regs2 (Z_to_bv 5 13) = w64 c2hi)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R lo hi c2hi c2lo HJ H9 H10 H24
  HR0 HR1 Hlo Hhi Hc2h Hc2l V88 Vb0 Vb8.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvf_extra3 hi c2hi c2lo) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 1) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 lo) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 hi) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 c2hi) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 c2lo) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (HS : st_ok rsegs (Ereg regs ex) hvf_b16_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B16) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_b16_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor; [|constructor]]].
    + exact (hvu_slot_chunk _ _ _ R 0x88 hi 33 E33 V88).
    + exact (hvu_slot_chunk _ _ _ R 0xb0 c2hi 34 E34 Vb0).
    + exact (hvu_slot_chunk _ _ _ R 0xb8 c2lo 35 E35 Vb8).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVF_B16) with (Z_to_bv 64 HVF_B16).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite !hvu_denot0, E10 in Hc.
all: cbn [sv_denot] in Hc.
- (* taken: a0 = 0, impossible *)
  exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc.
- hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_SF_GE. hvu_mem.
  apply SRr_ret. hvu_post0_tac B hvf_b16_kept.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [|split; [|split; [|split]]].
  + hvu_sv. cbn [sv_denot]. reflexivity.
  + hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
    first [ exact (U_atom E 24 lo E24 ltac:(lia))
          | rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 24 lo E24 ltac:(lia)), U_SLit;
            unfold zcanon, M64; rewrite Z.add_0_r, Z.mod_small by lia; reflexivity ].
  + hvu_sv. rewrite hvu_denot0, E33. reflexivity.
  + hvu_sv. rewrite hvu_denot0, E35. reflexivity.
  + hvu_sv. rewrite hvu_denot0, E34. reflexivity.
Qed.

(* ================================ b17: 0x83604 `blez a0 -> unimp` (a0 = 1) -> CV 0x83608 ================ *)
Lemma hvf_b17 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 1 ->
SRr rsegs W (cfg_at rsegs HVF_B17 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_CV hvf_all (fun _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ H10.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 1) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs ex) (hvf_ss_nr HVF_B17)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVF_B17) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvf_ss_nr. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVF_B17) with (Z_to_bv 64 HVF_B17).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite !hvu_denot0, E10 in Hc.
all: cbn [sv_denot] in Hc.
- (* taken: 0 >= a0, impossible *)
  exfalso; revert Hc; vm_compute; intros Hc; discriminate Hc.
- hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_CV. hvu_mem.
  apply SRr_ret. hvu_post0_tac B hvf_all. exact I.
Qed.

End d.
End b.

(* ================================ small facts ================================ *)
Ltac hvf_ne := let E := fresh "E" in intro E; apply (f_equal (@bv_unsigned 5)) in E; vm_compute in E; discriminate E.
(* a register literal and its Z_to_bv form *)
Ltac hvf_lit H := first [exact H | (etransitivity; [|exact H]); f_equal; apply bv_eq; reflexivity].

Lemma hvf_al16 : forall R, R mod 32 = 0 -> R mod 16 = 0.
Proof.
intros R H. pose proof (Z.div_mod R 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D. replace (32 * (R / 32)) with ((2 * (R / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma hvf_rom_img : forall a, in_rom rsegs a -> in_img rsegs a.
Proof. intros a (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. Qed.

Lemma hvf_apresent_some : forall H mem a, apresent H mem a -> aview rsegs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma hvf_aview_mod : forall H mem a, aview rsegs H mem a = aview rsegs H mem (a mod 2 ^ 64).
Proof. intros H mem a. unfold aview, mbyte. rewrite HPgSteps.Z_to_bv_mod64. reflexivity. Qed.

(* four readable bytes make a 32-bit word *)
Lemma hvf_rd32_some : forall H mem a,
(forall kk, (kk < 4)%nat -> aview rsegs H mem (a + Z.of_nat kk) <> None) ->
exists v, rd32 (aview rsegs H mem) a v.
Proof.
intros H mem a Hk.
assert (G : forall kk, (kk < 4)%nat -> exists b : byte, mbyte rsegs (mrestrict H mem) (a + Z.of_nat kk) = Some b).
{ intros kk Hkk. specialize (Hk kk Hkk). unfold aview in Hk.
  destruct (mbyte rsegs (mrestrict H mem) (a + Z.of_nat kk)) as [b|];
    [exists b; reflexivity | exfalso; apply Hk; reflexivity]. }
destruct (G 0%nat ltac:(lia)) as (b0 & E0). destruct (G 1%nat ltac:(lia)) as (b1 & E1).
destruct (G 2%nat ltac:(lia)) as (b2 & E2). destruct (G 3%nat ltac:(lia)) as (b3 & E3).
exists (bytes_le_to_Z [b0; b1; b2; b3]).
intros kk Hkk. unfold aview.
destruct kk as [|[|[|[|kk]]]]; [rewrite E0 | rewrite E1 | rewrite E2 | rewrite E3 | lia]; cbn [option_map]; f_equal;
  symmetry; apply (HPgMem.hm_lez_le_byte [b0; b1; b2; b3]); cbn; lia.
Qed.

(* the float registers *)
Lemma hvf_fs_set_same : forall (f : YK11.FPState) k b,
  hqu_fs (FP.hvf_set k f (Sem.nan_box (Z_to_bv 32 b))) k b.
Proof.
intros f k b. unfold hqu_fs, FP.hvf_set. cbn [fp_regs]. unfold Sem.reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

Lemma hvf_fs_set_other : forall (f : YK11.FPState) k j w v, hqu_fs f j v -> 0 <= k < 32 -> 0 <= j < 32 -> k <> j ->
  hqu_fs (FP.hvf_set k f w) j v.
Proof.
intros f k j w v H Hk Hj Hne. unfold hqu_fs, FP.hvf_set in *. cbn [fp_regs]. unfold Sem.reg_get in *.
rewrite bvmap_get_set_other; [exact H|].
intros E. apply (f_equal (@bv_unsigned 5)) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 5) with 32 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma hvf_fs_tr : forall (fx1 fx2 : YK11.FPState) j w, hqu_fs fx1 j w -> hd_fxk [] fx1 fx2 -> hqu_fs fx2 j w.
Proof. intros fx1 fx2 j w H (H2 & _). unfold hqu_fs in *. rewrite (H2 _ (fun Hin => Hin)). exact H. Qed.

Section fxs. Context {fx : YK11.FPState}.
Lemma hvf_fxk_tr : forall (fx1 fx2 : YK11.FPState), hd_fxk HQU_FXK fx fx1 -> hd_fxk [] fx1 fx2 ->
  hd_fxk HQU_FXK fx fx2.
Proof.
intros fx1 fx2 (H1 & _) (H2 & Hz). split; [|exact Hz]. intros kk Hkk.
rewrite (H2 kk (fun Hin => Hin)). exact (H1 kk Hkk).
Qed.

Lemma hvf_fxk_set : forall (f : YK11.FPState) k w, hd_fxk HQU_FXK fx f -> In k HQU_FXK ->
  hd_fxk HQU_FXK fx (FP.hvf_set k f w).
Proof.
intros f k w (H1 & Hz) Hin. split; [|exact Hz]. intros kk Hkk. unfold FP.hvf_set. cbn [fp_regs].
unfold Sem.reg_get in *. rewrite bvmap_get_set_other; [exact (H1 kk Hkk)|].
intros E. apply Hkk. subst kk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
unfold HQU_FXK in Hin |- *. cbn [In] in Hin.
rewrite Z.mod_small by lia. cbn [In]. lia.
Qed.
End fxs.

(* ================================ the two float-cast checks ================================
   lib/U/Prog/HeadCheck/Near.v hn_traps (its first two conclusions) restated over lib/Prog/HeadCheck/NearVal.v and
   lib/CJ/Spec/NearSF.v: that file loads lib/U/Reusable, whose YI16 / YO0c / YN0d shadow the kit's. hvf_D5f and
   hvf_flt_2p63 are its D5f and flt_2p63, unchanged but for the names. *)
Lemma hvf_D5f : fp_decode fmt_single 0x5f000000 = SpecFloat.S754_finite false 8388608 40.
Proof. vm_compute. reflexivity. Qed.

Lemma hvf_flt_2p63 : forall b N D, Nearest.f32_ratio b = Some (N, D) -> N <= 256 * D ->
  fst (fp_lt fmt_single b 0x5f000000) = true.
Proof.
  intros b N D. unfold fp_lt, fp_compare, Nearest.f32_ratio. cbn [fst]. rewrite hvf_D5f. cbv zeta.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR HN; try discriminate HR.
  - reflexivity.
  - clear Hd. destruct s; [reflexivity|].
    rewrite NearVal.sfc_ff. pose proof (Pos2Z.pos_is_pos m) as Hm.
    destruct (Z.compare_spec e 40) as [E|E|E]; cbv iota; [exfalso | reflexivity | exfalso];
      revert HR HN; destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR HN;
      injection HR as HN' HD'; subst N D; try lia;
      assert (P : 1099511627776 <= 2^e) by (change 1099511627776 with (2^40); apply Z.pow_le_mono_r; lia);
      assert (P2 : 1 * 2^e <= Zpos m * 2^e) by (apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia | lia]);
      lia.
Qed.

(* after the NaN test and the range test -1.0f <= f <= 256.0f: f < 2^63 and __gttf2(d, -(2^63 + 1)) = 1 *)
Lemma hvf_traps : forall b, 0 <= b < 2 ^ 32 ->
  fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
  fst (fp_lt fmt_single 0x43800000 b) = false ->
  fst (fp_lt fmt_single b 0x5f000000) = true /\ SF.f128_ge (hvu_d b) NearSF.C2_128 = 1.
Proof.
  intros b Hb Heq Hl1 Hl2. unfold hvu_d.
  destruct (Nearest.f32_ratio b) as [[N D]|] eqn:HR.
  - rewrite (NearVal.flt_m1 b N D HR) in Hl1. rewrite (NearVal.flt_256 b N D HR) in Hl2.
    apply Z.ltb_ge in Hl1. apply Z.ltb_ge in Hl2.
    pose proof (proj2 (Nearest.near_f32_ratio b) N D HR) as HD.
    split.
    + exact (hvf_flt_2p63 b N D HR Hl2).
    + apply (NearSF.near_sf_c2 b N D Hb HR). unfold Nearest.INT32_MIN. lia.
  - exfalso. destruct (NearVal.ratio_none b HR) as [Hd|[Hd|Hd]].
    + rewrite (NearVal.feq_nan b Hd) in Heq. discriminate Heq.
    + rewrite (NearVal.flt_minf_m1 b Hd) in Hl1. discriminate Hl1.
    + rewrite (NearVal.flt_pinf_256 b Hd) in Hl2. discriminate Hl2.
Qed.

(* ================================ what the lane carries ================================ *)
(* the registers and real-frame cells fixed from FA to CV: the segment's (hqu_L_seg), the loop's cells, the body's
   cells, s7 = the param's top value and s5 = the channel *)
Definition hvf_Lb (cx : hsu_scx rsegs) (m : nat) (ch p : Z) : list (hd_loc * Z) :=
  hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2) ++
  [(LReg 23, hvm_top p); (LReg 21, ch)].
(* sp, gp, tp and the registers of hvf_Lb: all callee-saved *)
Definition hvf_keep : list Z := [2; 3; 4; 8; 9; 19; 27; 20; 22; 25; 26; 23; 21].
Ltac hvf_kin := unfold hvf_keep; cbn [In]; repeat (first [left; reflexivity | right]).
(* every register of hvf_keep is in a block's kept list *)
Ltac hvf_keepk :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq; unfold hvf_keep in Hq; cbn [In] in Hq;
  repeat (destruct Hq as [<-|Hq];
          [unfold hvf_all, hvf_b1_kept, hvf_b3_kept, hvf_rfl_kept, hvf_b9_kept, hvf_b10_kept, hvf_b16_kept,
             hvu_q6a_kept, hvu_q4_kept; apply in_map; cbn [In]; lia|]);
  destruct Hq.
Lemma hvf_keep_ne10 : forall q, In q hvf_keep -> Z_to_bv 5 q <> Z_to_bv 5 10.
Proof.
intros q Hq. unfold hvf_keep in Hq. cbn [In] in Hq.
repeat (destruct Hq as [<-|Hq]; [hvf_ne|]). destruct Hq.
Qed.
Lemma hvf_keep_callee : forall q, In q hvf_keep -> acallee_saved q.
Proof. intros q Hq. unfold hvf_keep in Hq. cbn [In] in Hq. unfold acallee_saved. lia. Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : KI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the cut base, the fixed registers and cells, the float constants, the pair's facts and x *)
Definition hvf_I (cx : hsu_scx rsegs) (r : Model.pod_rec) (at0 m : nat) (k : list byte) (v : Model.ent)
(ch p : Z) (cs : list cell) (keys rf : Z) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx rsegs cx W2 mem2 regs2 (hvf_Lb cx m ch p) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live rsegs cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
Model.e_type v = Model.POD_FLOAT /\
hqu_pair_inv rsegs cx r m k v cs keys rf /\ Z.of_nat (length cs) <= keys /\
hqu_x_at rsegs cx W2 mem2 cs (keys + 1) rf.

(* hvf_I across a block, a float step or a call: the new state has the segment's journal, the same frames,
   blocks and I/O state, a meter step of 0, float constants and kept registers, and every byte outside Wr (a part
   of the real-frame cells R+0x88 .. R+0x98) as before *)
Lemma hvf_move : forall (cx : hsu_scx rsegs) r ev at0 m k v ch p cs keys rf
(fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (Wr : Z -> Prop),
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
hvf_I cx r at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 ->
mo_le MT S2 S3 0 ->
hd_fxk HQU_FXK fx fx3 -> hqu_fs fx3 9 HQU_F32_M1 -> hqu_fs fx3 18 HQU_F32_256 -> hqu_fs fx3 19 HQU_F32_2P63 ->
(forall q, In q hvf_keep -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
(forall a, Wr a -> e_R (x_e rsegs cx) + 0x88 <= a < e_R (x_e rsegs cx) + 0x98) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hvf_I cx r at0 m k v ch p cs keys rf fx3 ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 ly3 S3 W3 regs3 mem3 md3 Wr
  HS HI HJ3 Hfr3 Hperm3 Hio3 Hmo3 Hfx3 F9 F18 F19 Hk3 HWb Hk.
destruct HI as (Hb3 & Hat & _ & _ & _ & Hlive & Ham & Hkey & Hty & Hpair & Hkcs & Hx).
destruct Hb3 as (HC & _ & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & Herr).
pose proof (hvu_start_pre B cx r ev HS) as Hpre.
pose proof (hvu_stack B cx _ Hpre) as (_ & _ & HR220 & Hwin & Hceil & HR47 & _).
pose proof (hvu_apart B cx _ Hpre) as (Hppin & _ & Hpp4096 & Hppc & _ & HF4096 & HFc & _ & _).
pose proof HS as (_ & _ & Hwf & Hlen & _ & _ & Hfpod & _ & _ & _ & _ & Hfout & _).
pose proof Hpre as Hpre'. unfold hsu_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (HJx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
pose proof HJx as (HARx & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof YCbq.asan_consts as (HCv & _).
assert (Ht : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : forall n, 0 <= n -> n <= req_size n)
  by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
(* every byte below the ceiling is kept *)
assert (Klow : forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Hk; [lia|]. intros HW. apply HWb in HW. lia. }
destruct Hfpod as (_ & Hpodin & _). destruct Hfout as (_ & Houtin & _).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HARx Hpodin) as (_ & Hpod4096 & Hpodc & _).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HARx Houtin) as (_ & Hout4096 & Houtc & _).
refine (conj _ (conj _ (conj F9 (conj F18 (conj F19 (conj Hlive (conj Ham (conj Hkey (conj Hty
  (conj Hpair (conj Hkcs _))))))))))).
- (* the cut base *)
  refine (conj _ (conj Hfx3 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  + unfold hsu_core, hsu_mid in *. destruct HC as (HJ2 & Hr2 & Hfr & Hperm & Hio & Hmo & Hmem).
    refine (conj HJ3 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    * intros q Hq. rewrite (Hk3 q) by (destruct Hq as [->|[->| ->]]; hvf_kin). exact (Hr2 q Hq).
    * rewrite Hfr3. exact Hfr.
    * exact (Permutation_trans Hperm3 Hperm).
    * exact (same_io_trans _ _ _ Hio Hio3).
    * exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3).
    * intros a Ha Hw HE. rewrite (Hk a Ha); [exact (Hmem a Ha Hw HE)|].
      intros HWa. apply HE. left. apply HWb in HWa. unfold hd_inw. cbn [hi_w3 headamp_himg_B].
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
  + (* the frame's shadow bytes *)
    unfold hsu_fsh_at in *. apply (HPgMem.hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
    rewrite hqu_shX_len in Hi. apply Klow.
    pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as DF.
    pose proof (Z.mod_pos_bound (e_F (x_e rsegs cx)) 8 ltac:(lia)) as MF.
    unfold shadow_addr, SHADOW_OFF. lia.
  + (* the read-only segments *)
    apply (HPgMem.hm_rom_kept rsegs W2 W3 mem2 mem3 Hrom). intros a Ha.
    pose proof (HPgSteps.img_segs_low a (hvf_rom_img a Ha)) as Hab.
    apply Klow. unfold kLowMemEnd in Hab. lia.
  + (* pp *)
    unfold hsu_pp_at in *. apply (HPgSiteA.hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ _); [|exact Hpp].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    pose proof (Layout.length_pp_bytes r Hwf) as HL. apply Klow. unfold Layout.PP_SIZE in *. lia.
  + (* pod *)
    apply (HPgSiteA.hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ _); [|exact Hpod].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    pose proof (Hrq (e_len (x_e rsegs cx)) ltac:(lia)). apply Klow. lia.
  + (* out *)
    apply (HPgSiteA.hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ _); [|exact Hout].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj.
    assert (Hcl : Z.of_nat (length (ans_cells (hqu_ans rsegs cx r))) <= e_cap (x_e rsegs cx)).
    { unfold hqu_ans. pose proof (Headamp.parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r))
        (e_cap (x_e rsegs cx)) ltac:(lia)) as Hok.
      destruct (answer_ok_parts _ _ Hok) as [[(_ & Hc0 & _)|(Hr0 & Hrl & _)] _].
      - rewrite Hc0. cbn. lia.
      - lia. }
    pose proof (Hrq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)). apply Klow. lia.
  + (* res *)
    apply (HPgSiteA.hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ _); [|exact Hres].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj. unfold ans_res_bytes in Hj.
    rewrite length_ha_res_bytes in Hj. unfold HQU_RES. apply Klow. lia.
  + (* errno: its bytes are kept or in the stack window, which the journal has present *)
    destruct Herr as (ev2 & Hev). apply hvf_rd32_some. intros kk Hkk.
    rewrite hvf_aview_mod.
    pose proof (Hev kk Hkk) as Hv. rewrite hvf_aview_mod in Hv.
    pose proof (Z.mod_pos_bound (as_errno B + Z.of_nat kk) (2 ^ 64) ltac:(lia)) as Hm.
    destruct (Z_le_gt_dec (e_R (x_e rsegs cx) + 0x88) ((as_errno B + Z.of_nat kk) mod 2 ^ 64)) as [L1|L1];
      [destruct (Z_lt_le_dec ((as_errno B + Z.of_nat kk) mod 2 ^ 64) (e_R (x_e rsegs cx) + 0x98)) as [L2|L2]|].
    * apply hvf_apresent_some. apply Hpres3. lia.
    * rewrite (Hk _ Hm); [rewrite Hv; discriminate|]. intros HW. apply HWb in HW. lia.
    * rewrite (Hk _ Hm); [rewrite Hv; discriminate|]. intros HW. apply HWb in HW. lia.
- (* the fixed registers and cells *)
  unfold hsu_at_cx, hsu_at in *.
  apply (HPgMem.hm_atl_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) _ Hat).
  intros f Hf. unfold hvf_Lb, hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_body in Hf. cbv zeta in Hf.
  cbn [In app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst HPgMem.hm_keeps hd_xv];
    first [ apply Hk3; hvf_kin
          | intros i Hi; apply Hk; [lia | intros HW; apply HWb in HW; lia] ] |]).
  destruct Hf.
- (* x *)
  destruct Hx as (Hxg & Hxr). split; [|exact Hxr].
  apply (HPgSiteA.hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ _); [|exact Hxg].
  intros j Hj. unfold hd_zbytes in Hj.
  rewrite length_map, hqu_x_open_len in Hj by (destruct Hxr as (Hl & _); exact Hl).
  unfold HQU_XO. apply Klow. lia.
Qed.

(* the register-only case: a block that stores nothing *)
Lemma hvf_I_regs : forall (cx : hsu_scx rsegs) r ev at0 m k v ch p cs keys rf
(fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
hvf_I cx r at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q, In q hvf_keep -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
hvf_I cx r at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3 Hk3.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
apply (hvf_move cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx2 ly2 S2 W2 regs3 mem2 md3
  (fun _ => False) HS HI HJ3 eq_refl (Permutation_refl _) Hio3 (mo_le_refl MT MTL S2) Hfx F9 F18 F19 Hk3);
  [intros a [] | intros a _ _; reflexivity].
Qed.

(* a block that stores into the cells Wr *)
Lemma hvf_I_mem : forall (cx : hsu_scx rsegs) r ev at0 m k v ch p cs keys rf
(fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (Wr : Z -> Prop),
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
hvf_I cx r at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q, In q hvf_keep -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
(forall a, Wr a -> e_R (x_e rsegs cx) + 0x88 <= a < e_R (x_e rsegs cx) + 0x98) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hvf_I cx r at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Wr HS HI HJ3 Hio3 Hk3 HWb Hk.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
exact (hvf_move cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx2 ly2 S2 W2 regs3 mem3 md3
  Wr HS HI HJ3 eq_refl (Permutation_refl _) Hio3 (mo_le_refl MT MTL S2) Hfx F9 F18 F19 Hk3 HWb Hk).
Qed.

(* a float step: the float state, a0 and the model's materialized pages may change *)
Lemma hvf_I_fx : forall (cx : hsu_scx rsegs) r ev at0 m k v ch p cs keys rf
(fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 (fx3 : YK11.FPState) regs3 X,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
hvf_I cx r at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 ->
hd_fxk HQU_FXK fx fx3 -> hqu_fs fx3 9 HQU_F32_M1 -> hqu_fs fx3 18 HQU_F32_256 -> hqu_fs fx3 19 HQU_F32_2P63 ->
(forall q, In q hvf_keep -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
hvf_I cx r at0 m k v ch p cs keys rf fx3 ly2 S2 W2 regs3 mem2 (with_vm_backing (m_vm_lazy md2) X md2).
Proof.
intros cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 regs3 X HS HI Hfx3 F9 F18 F19 Hk3.
pose proof HI as ((HC & _) & _). pose proof HC as (HJ & _).
assert (HJ' := HJ).
apply (ajournal_materialize rsegs B (AR_laws_ok rsegs B) HPgSteps.img_segs_low) with (X := X) in HJ'.
exact (hvf_move cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 ly2 S2 W2 regs3 mem2
  (with_vm_backing (m_vm_lazy md2) X md2) (fun _ => False) HS HI HJ' eq_refl (Permutation_refl _)
  (HPgSteps.same_io_wvb _ _ _) (mo_le_refl MT MTL S2) Hfx3 F9 F18 F19 Hk3 (fun a H => match H with end)
  (fun a _ _ => eq_refl)).
Qed.
End t.

(* ================================ the lane, pc by pc ================================
   Each hvf_at_<pc> is the lane from that pc on, given hvf_I and the registers and cells the rest of the lane reads;
   they are proved from the end (CV and the refusals) back to FA. *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : KI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variables (cx : hsu_scx rsegs) (POST : world rsegs -> config -> Prop) (r : Model.pod_rec) (ev : Z) (at0 m : nat)
  (k : list byte) (v : Model.ent) (ch p : Z) (cs : list cell) (keys rf : Z).
Hypothesis HS : @hqu_start_M03 fx rc SK rsegs B cx r ev.
Hypothesis HRF : @hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m.
Hypothesis HCV : @hvu_from_CV fx rc SK B MT cx r POST at0 m.

Local Notation RR := (e_R (x_e rsegs cx)).
Local Notation PP := (e_pp (x_e rsegs cx)).
Local Notation FI := (@hvf_I fx rc SK B MT cx r at0 m k v ch p cs keys rf).

(* hvf_I after a block that stores nothing, with its kept list *)
Ltac hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3 :=
  lazymatch type of HI with @hvf_I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?fx2 ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2 =>
  pose proof (hvf_I_regs B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3
    Hio3 ltac:(let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; apply Hk3; revert q Hq; hvf_keepk))
    as HI3 end.

Lemma hvf_geo : 2 ^ 46 <= RR <= 2 ^ 47 /\ RR mod 16 = 0 /\ RR + 0x220 <= x_sp0 rsegs cx /\
  x_sp0 rsegs cx - x_STK rsegs cx <= RR - T_SEG_STK /\ alloc_ceiling <= RR - T_SEG_STK.
Proof.
pose proof (hvu_stack B cx _ (hvu_start_pre B cx r ev HS)) as (_ & Hal & H220 & Hwin & Hceil & HR & _).
split; [exact HR|]. split; [exact (hvf_al16 _ Hal)|]. split; [exact H220|]. split; [exact Hwin | exact Hceil].
Qed.

Lemma hvf_pp : 4096 <= PP /\ PP + Layout.PP_SIZE <= alloc_ceiling /\
  0 <= shadow_addr (PP + Layout.OFF_PARAMS_STRUCT) < 2 ^ 64.
Proof.
pose proof (hvu_apart B cx _ (hvu_start_pre B cx r ev HS)) as (_ & _ & H4096 & Hc & _).
pose proof YCbq.asan_consts as (HCv & _).
pose proof (Z.div_mod (PP + Layout.OFF_PARAMS_STRUCT) 8 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (PP + Layout.OFF_PARAMS_STRUCT) 8 ltac:(lia)) as M.
split; [exact H4096|]. split; [exact Hc|].
unfold shadow_addr, SHADOW_OFF, Layout.OFF_PARAMS_STRUCT, Layout.PP_SIZE in *. lia.
Qed.

Lemma hvf_wfv : hqu_pair_inv rsegs cx r m k v cs keys rf -> Model.ent_wf v.
Proof.
intros (Hv & _ & Hm & _). pose proof (hvu_start_wf B cx r ev HS) as Hwf.
destruct (Model.ents_wf r Hwf) as (_ & Hall). rewrite Hv. exact (proj1 (Forall_forall _ _) Hall _ (nth_In _ _ Hm)).
Qed.

(* a Float entry whose word pod_nearest refuses: expect_cell refuses with OUT_OF_RANGE *)
Lemma hvf_refuse : forall b, 0 <= b < 2 ^ 32 -> Model.ent_wf v -> Model.e_type v = Model.POD_FLOAT ->
  4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) -> NearVal.hn_bin b = None ->
  Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p ->
  Headamp.expect_cell k v = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof.
intros b Hb Hwf Hty Hsz Hbody Hn Hkey. apply (hvm_cell_inl k v ch p Hkey). left.
rewrite (hvm_cv_float v Hwf Hty Hsz), <- Hbody, <- (hvm_hn_nearest b Hb), Hn. lia.
Qed.

(* the value entry's size and body word in the pp block, their shadow, and where the entry lies: lib/AU/HPgM3dDispU.v
   hvu_ent, at the lane's state *)
Lemma hvf_ent : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
Model.ent_wf v /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hvu_entA cx m + 4) 4 (Model.e_size v) /\
(4 <= Model.e_size v ->
 val_mem rsegs (mrestrict (w_H W2) mem2) (hvu_entA cx m + 8) 4 (Cursor.rd32 (Model.e_body v))) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hvu_entA cx m + 4) 4 /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hvu_entA cx m + 8) 4 /\
4096 <= hvu_entA cx m /\ hvu_entA cx m + 16 <= 0x7fffff800000 /\
(hvu_entA cx m + 16 <= kLowShadowBeg \/ kHighMemBeg <= hvu_entA cx m).
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI.
destruct HI as (Hb3 & _ & _ & _ & _ & _ & _ & _ & _ & Hpair & _).
destruct (hvu_ent B MT cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf HS Hb3 Hpair)
  as (Hwfv & _ & _ & Vsz & Vbody & _ & Rsz & Rbody & HA0 & HA1 & Happ).
pose proof YCbq.asan_consts as (HCv & _).
split; [exact Hwfv|]. split; [exact Vsz|]. split; [intros _; exact Vbody|].
split; [exact Rsz|]. split; [exact Rbody|]. split; [exact HA0|]. split; [lia | exact Happ].
Qed.

(* the frame of facts a call asks for *)
Lemma hvf_core : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2, FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2 regs2 RR.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI.
destruct hvf_geo as (HR & Hal & HR220 & Hwin & _).
pose proof HI as ((HC & _) & _). pose proof HC as (HJ & Hr234 & _).
pose proof (hvu_stack B cx _ (hvu_start_pre B cx r ev HS)) as (_ & _ & _ & _ & _ & _ & _ & Hev & X2 & X3 & X4).
assert (G2 : getr regs2 (Z_to_bv 5 2) = w64 RR)
  by (rewrite (Hr234 2 (or_introl eq_refl)); hvf_lit X2).
assert (G3 : getr regs2 (Z_to_bv 5 3) = w64 (as_gp B))
  by (rewrite (Hr234 3 (or_intror (or_introl eq_refl))); hvf_lit X3).
assert (G4 : getr regs2 (Z_to_bv 5 4) = w64 (as_tp B))
  by (rewrite (Hr234 4 (or_intror (or_intror eq_refl))); hvf_lit X4).
split; [exact HJ|]. split; [exact Hev|]. split; [hvf_lit G2|]. split; [hvf_lit G3|]. split; [hvf_lit G4|].
split; [exact Hal|]. split; [exact Hwin | lia].
Qed.

(* ---------------- the Float refusal 0x83664 -> RF ---------------- *)
Lemma hvf_at_rfl : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
Headamp.expect_cell k v = inl Headamp.REFUSE_OUT_OF_RANGE ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_RFL regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI Hcell.
destruct hvf_geo as (HR & _).
destruct hvf_pp as (Hpp0 & Hppc & Hsh).
pose proof YCbq.asan_consts as (HCv & _).
pose proof HI as ((HC & _) & Hat & _). pose proof HC as (HJ & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 RR Hat ltac:(unfold hvf_Lb; hvu_in)) as R9.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x110 (PP + Layout.OFF_PARAMS_STRUCT) Hat ltac:(unfold hvf_Lb; hvu_in)) as C110.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x108 (shadow_addr (PP + Layout.OFF_PARAMS_STRUCT)) Hat
  ltac:(unfold hvf_Lb; hvu_in)) as C108.
cbn [hd_xv] in C110, C108.
eapply SRr_bind.
{ exact (hvf_rfl (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 RR (PP + Layout.OFF_PARAMS_STRUCT)
    (shadow_addr (PP + Layout.OFF_PARAMS_STRUCT)) HJ R9 ltac:(lia) ltac:(lia)
    ltac:(unfold Layout.OFF_PARAMS_STRUCT, Layout.PP_SIZE in *; lia) Hsh C110 C108). }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & (Q30 & Q31 & Q15)).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
apply (HRF fx2 ly2 S2 W2 regs3 mem2 md3 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
destruct HI3 as (Hb3 & Hat3 & F9 & F18 & F19 & Hlive & Ham & _ & _ & Hpair & _ & Hx).
unfold hqu_cut_RF.
refine (conj Hb3 (conj _ (conj F9 (conj F18 (conj F19 (conj Hlive (conj Ham (conj Hcell
  (conj (or_intror eq_refl) (conj Hpair Hx)))))))))).
unfold hsu_at_cx, hvf_Lb in *.
apply hvu_at_app; split; [hvu_sub Hat3|].
apply hvu_at_app; split; [hvu_sub Hat3|].
apply hvu_at_app; split.
{ unfold hqu_L_t56, hsu_at. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
  - exact Q30.
  - exact Q31. }
apply hvu_at_app; split; [hvu_sub Hat3|].
unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd]. exact Q15.
Qed.

(* ---------------- b17 0x83604 -> CV ---------------- *)
Lemma hvf_at_b17 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 1 ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x88) (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
fst (fp_lt fmt_single 0x43800000 b) = false ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B17 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H10 H24 C88 C90 F8 Hb Hsz Hbody Heq Hlo Hhi.
pose proof HI as ((HC & _) & _). pose proof HC as (HJ & _).
eapply SRr_bind; [exact (hvf_b17 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 HJ H10)|].
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
apply (HCV fx2 ly2 S2 W2 regs3 mem2 md3 k v ch p b cs keys rf).
destruct HI3 as (Hb3 & Hat3 & F9 & F18 & F19 & Hlive & Ham & Hkey & Hty & Hpair & Hkcs & Hx).
unfold hvu_cut_CV.
refine (conj Hb3 (conj _ (conj F8 (conj F9 (conj F18 (conj F19 (conj Hlive (conj Ham (conj Hkey (conj Hty
  (conj Hsz (conj Hbody (conj Heq (conj Hlo (conj Hhi (conj Hpair (conj Hkcs Hx))))))))))))))))).
unfold hsu_at_cx, hvf_Lb in *.
apply hvu_at_app; split; [hvu_sub Hat3|].
apply hvu_at_app; split; [hvu_sub Hat3|].
apply hvu_at_app; split; [hvu_sub Hat3|].
unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
- rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvf_all; hvu_kin). exact H24.
- exact C88.
- exact C90.
- exact (hvu_at_get _ _ _ _ _ 23 (hvm_top p) Hat3 ltac:(hvu_in)).
- exact (hvu_at_get _ _ _ _ _ 21 ch Hat3 ltac:(hvu_in)).
Qed.

(* ---------------- the __gttf2 call 0x85474 (ra 0x83604) ---------------- *)
Lemma hvf_at_ge : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 1) = w64 HVU_RA_GT ->
getr regs2 (Z_to_bv 5 10) = w64 (SF.lo64 (hvu_d b)) -> getr regs2 (Z_to_bv 5 11) = w64 (SF.hi64 (hvu_d b)) ->
getr regs2 (Z_to_bv 5 12) = w64 HQU_C2LO -> getr regs2 (Z_to_bv 5 13) = w64 HQU_C2HI ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x88) (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
fst (fp_lt fmt_single 0x43800000 b) = false ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_SF_GE regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H1 H10 H11 H12 H13 H24 C88 C90 F8 Hb Hsz Hbody Heq Hlo Hhi.
destruct hvf_geo as (HR & _).
pose proof HI as ((_ & Hfx & _ & Hrom & _) & _ & F9 & F18 & F19 & _).
pose proof (hvm_lo64_rng (hvu_d b)) as Rlo. pose proof (hvm_hi64_rng (hvu_d b)) as Rhi.
apply (hsfu_ge_stmt (fx := fx2) B MT MTL HVU_RA_GT POST _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 regs2 RR
  (SF.lo64 (hvu_d b)) (SF.hi64 (hvu_d b)) HQU_C2LO HQU_C2HI (hvf_core fx2 ly2 S2 W2 regs2 mem2 md2 HI)).
- hvf_lit H1.
- unfold HVU_RA_GT; lia.
- reflexivity.
- hvf_lit H10.
- hvf_lit H11.
- hvf_lit H12.
- hvf_lit H13.
- exact Rlo.
- exact Rhi.
- unfold HQU_C2LO; lia.
- unfold HQU_C2HI; lia.
- exact Hrom.
- exact (proj2 Hfx).
- intros W3 fx3 ly3 S3 regs3 mem3 md3 Hwle Hfx3 Hcore3 Hpres3 Hfr3 Hperm3 Hio3 Hmo3 Hmem3 Hrom3 Ha0.
  pose proof Hcore3 as (HJ3 & _).
  assert (HI3 : FI fx3 ly3 S3 W3 regs3 mem3 md3).
  { apply (hvf_move B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 ly3 S3 W3 regs3 mem3
      md3 (fun _ => False) HS HI HJ3 Hfr3 Hperm3 Hio3 Hmo3 (hvf_fxk_tr _ _ Hfx Hfx3) (hvf_fs_tr _ _ _ _ F9 Hfx3)
      (hvf_fs_tr _ _ _ _ F18 Hfx3) (hvf_fs_tr _ _ _ _ F19 Hfx3)).
    - intros q Hq. apply Hpres3. exact (hvf_keep_callee q Hq).
    - intros a [].
    - intros a Ha _. exact (Hmem3 a Ha). }
  assert (Hge : SF.f128_ge (SF.lo64 (hvu_d b) + 2 ^ 64 * SF.hi64 (hvu_d b)) (HQU_C2LO + 2 ^ 64 * HQU_C2HI) = 1).
  { rewrite (hvm_w128 (hvu_d b) (hvm_ext_range b)).
    replace (HQU_C2LO + 2 ^ 64 * HQU_C2HI) with NearSF.C2_128 by (vm_compute; reflexivity).
    destruct (hvf_traps b Hb Heq Hlo Hhi) as (_ & T2). exact T2. }
  rewrite Hge in Ha0.
  apply (hvf_at_b17 fx3 ly3 S3 W3 regs3 mem3 md3 b HI3).
  + hvf_lit Ha0.
  + rewrite (Hpres3 24) by (unfold acallee_saved; lia). exact H24.
  + apply (HPgMem.hm_at_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) _ _ C88).
    intros i Hi. apply Hmem3. cbn [hd_xv]. lia.
  + apply (HPgMem.hm_at_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) _ _ C90).
    intros i Hi. apply Hmem3. cbn [hd_xv]. lia.
  + exact (hvf_fs_tr _ _ _ _ F8 Hfx3).
  + exact Hb.
  + exact Hsz.
  + exact Hbody.
  + exact Heq.
  + exact Hlo.
  + exact Hhi.
Qed.

(* ---------------- b16 0x835ec -> the __gttf2 call ---------------- *)
Lemma hvf_at_b16 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 1 ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x88) (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
fst (fp_lt fmt_single 0x43800000 b) = false ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B16 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H10 H24 C88 C90 F8 Hb Hsz Hbody Heq Hlo Hhi.
destruct hvf_geo as (HR & _).
pose proof HI as ((HC & _) & Hat & _). pose proof HC as (HJ & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 RR Hat ltac:(unfold hvf_Lb; hvu_in)) as R9.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xb0 HQU_C2HI Hat ltac:(unfold hvf_Lb; hvu_in)) as Cb0.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xb8 HQU_C2LO Hat ltac:(unfold hvf_Lb; hvu_in)) as Cb8.
cbn [hd_xv] in Cb0, Cb8.
pose proof (hvm_lo64_rng (hvu_d b)) as Rlo. pose proof (hvm_hi64_rng (hvu_d b)) as Rhi.
eapply SRr_bind.
{ exact (hvf_b16 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 RR (SF.lo64 (hvu_d b)) (SF.hi64 (hvu_d b))
    HQU_C2HI HQU_C2LO HJ R9 H10 H24 ltac:(lia) ltac:(lia) Rlo Rhi ltac:(unfold HQU_C2HI; lia)
    ltac:(unfold HQU_C2LO; lia) C88 Cb0 Cb8). }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & (Q1 & Q10 & Q11 & Q12 & Q13)).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
apply (hvf_at_ge fx2 ly2 S2 W2 regs3 mem2 md3 b HI3 Q1 Q10 Q11 Q12 Q13); try assumption.
rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvf_b16_kept; hvu_kin). exact H24.
Qed.

(* ---------------- lt3 0x835e8 `flt.s a0,fs0,fs3` ---------------- *)
Lemma hvf_at_lt3 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x88) (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
fst (fp_lt fmt_single 0x43800000 b) = false ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVFU_LT3 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H24 C88 C90 F8 Hb Hsz Hbody Heq Hlo Hhi.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
destruct (hvf_traps b Hb Heq Hlo Hhi) as (T1 & _).
unfold cfg_at. change (w64 HVFU_LT3) with (Z_to_bv 64 HVFU_LT3).
apply (hvfu_lt3 (fx := fx2) W2 regs2 mem2 md2 POST b F8 Hb F19 (proj2 Hfx)).
intros fx3 regs3 X Hd Hr3 H10.
replace (if fst (fp_lt fmt_single b 0x5f000000) then 1 else 0) with 1 in H10 by (rewrite T1; reflexivity).
apply (hvf_at_b16 fx3 ly2 S2 W2 regs3 mem2 (with_vm_backing (m_vm_lazy md2) X md2) b).
- apply (hvf_I_fx B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 regs3 X HS HI
    (hvf_fxk_tr _ _ Hfx Hd) (hvf_fs_tr _ _ _ _ F9 Hd) (hvf_fs_tr _ _ _ _ F18 Hd) (hvf_fs_tr _ _ _ _ F19 Hd)).
  intros q Hq. subst regs3. apply getr_other. exact (hvf_keep_ne10 q Hq).
- exact H10.
- subst regs3. rewrite getr_other by hvf_ne. exact H24.
- exact C88.
- exact C90.
- exact (hvf_fs_tr _ _ _ _ F8 Hd).
- exact Hb.
- exact Hsz.
- exact Hbody.
- exact Heq.
- exact Hlo.
- exact Hhi.
Qed.

(* ---------------- b14 0x835e4 `bnez a0`: 256.0f < b refuses ---------------- *)
Lemma hvf_at_b14 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single 0x43800000 b) then 1 else 0) ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x88) (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B14 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H10 H24 C88 C90 F8 Hb Hsz Hbody Heq Hlo.
pose proof HI as ((HC & _) & _ & _ & _ & _ & _ & _ & Hkey & Hty & Hpair & _). pose proof HC as (HJ & _).
eapply SRr_bind; [exact (hvf_b14 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ HJ H10)|].
intros W3 c3 _ [(Hc & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
              | (Hc & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)].
- hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
  apply (hvf_at_rfl fx2 ly2 S2 W2 regs3 mem2 md3 HI3).
  exact (hvf_refuse b Hb (hvf_wfv Hpair) Hty Hsz Hbody (hvm_hn_hi b Hc) Hkey).
- hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
  apply (hvf_at_lt3 fx2 ly2 S2 W2 regs3 mem2 md3 b HI3); try assumption.
  rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvf_all; hvu_kin). exact H24.
Qed.

(* ---------------- lt2 0x835e0 `flt.s a0,fs2,fs0` ---------------- *)
Lemma hvf_at_lt2 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x88) (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVFU_LT2 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H24 C88 C90 F8 Hb Hsz Hbody Heq Hlo.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
unfold cfg_at. change (w64 HVFU_LT2) with (Z_to_bv 64 HVFU_LT2).
apply (hvfu_lt2 (fx := fx2) W2 regs2 mem2 md2 POST b F8 Hb F18 (proj2 Hfx)).
intros fx3 regs3 X Hd Hr3 H10.
apply (hvf_at_b14 fx3 ly2 S2 W2 regs3 mem2 (with_vm_backing (m_vm_lazy md2) X md2) b).
- apply (hvf_I_fx B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 regs3 X HS HI
    (hvf_fxk_tr _ _ Hfx Hd) (hvf_fs_tr _ _ _ _ F9 Hd) (hvf_fs_tr _ _ _ _ F18 Hd) (hvf_fs_tr _ _ _ _ F19 Hd)).
  intros q Hq. subst regs3. apply getr_other. exact (hvf_keep_ne10 q Hq).
- exact H10.
- subst regs3. rewrite getr_other by hvf_ne. exact H24.
- exact C88.
- exact C90.
- exact (hvf_fs_tr _ _ _ _ F8 Hd).
- exact Hb.
- exact Hsz.
- exact Hbody.
- exact Heq.
- exact Hlo.
Qed.

(* ---------------- b12 0x835d8 `sd a1,0x88(s1); bnez a0`: b < -1.0f refuses ---------------- *)
Lemma hvf_at_b12 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single b 0xbf800000) then 1 else 0) ->
getr regs2 (Z_to_bv 5 11) = w64 (SF.hi64 (hvu_d b)) ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B12 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H10 H11 H24 C90 F8 Hb Hsz Hbody Heq.
destruct hvf_geo as (HR & Hal & HR220 & Hwin & _).
pose proof HI as ((HC & _) & Hat & _ & _ & _ & _ & _ & Hkey & Hty & Hpair & _). pose proof HC as (HJ & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 RR Hat ltac:(unfold hvf_Lb; hvu_in)) as R9.
pose proof (hvu_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(unfold hvf_Lb; hvu_in)) as R27.
pose proof (hvm_hi64_rng (hvu_d b)) as Rhi.
assert (Ht : T_SEG_STK = 16384) by reflexivity.
eapply SRr_bind.
{ exact (hvf_b12 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 RR (SF.hi64 (hvu_d b)) _ HJ R9 H10 H11 R27 HR Hal
    ltac:(lia) ltac:(lia) Rhi). }
intros W3 c3 _ [(Hc & -> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hkeep3 & C88)
              | (Hc & -> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hkeep3 & C88)].
- (* b < -1.0f: refused *)
  assert (HI3 : FI fx2 ly2 S2 W2 regs3 mem3 md3).
  { apply (hvf_I_mem B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
      (fun a => RR + 0x88 <= a < RR + 0x90) HS HI HJ3 Hio3); [ | intros a Ha; cbv beta in Ha; lia | exact Hkeep3].
    intros q Hq. apply Hk3. revert q Hq. hvf_keepk. }
  apply (hvf_at_rfl fx2 ly2 S2 W2 regs3 mem3 md3 HI3).
  exact (hvf_refuse b Hb (hvf_wfv Hpair) Hty Hsz Hbody (hvm_hn_lo b Hc) Hkey).
- assert (HI3 : FI fx2 ly2 S2 W2 regs3 mem3 md3).
  { apply (hvf_I_mem B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
      (fun a => RR + 0x88 <= a < RR + 0x90) HS HI HJ3 Hio3); [ | intros a Ha; cbv beta in Ha; lia | exact Hkeep3].
    intros q Hq. apply Hk3. revert q Hq. hvf_keepk. }
  apply (hvf_at_lt2 fx2 ly2 S2 W2 regs3 mem3 md3 b HI3).
  + rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvf_all; hvu_kin). exact H24.
  + cbn [hd_at hd_xv]. rewrite (Z.mod_small _ (2 ^ 64)) by exact Rhi. exact C88.
  + apply (HPgMem.hm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e rsegs cx) _ _ C90).
    intros i Hi. apply Hkeep3; cbn [hd_xv]; cbv beta; lia.
  + exact F8.
  + exact Hb.
  + exact Hsz.
  + exact Hbody.
  + exact Heq.
  + exact Hc.
Qed.

(* ---------------- lt1 0x835d4 `flt.s a0,fs0,fs1` ---------------- *)
Lemma hvf_at_lt1 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 24) = w64 (SF.lo64 (hvu_d b)) ->
getr regs2 (Z_to_bv 5 11) = w64 (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVFU_LT1 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H24 H11 C90 F8 Hb Hsz Hbody Heq.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
unfold cfg_at. change (w64 HVFU_LT1) with (Z_to_bv 64 HVFU_LT1).
apply (hvfu_lt1 (fx := fx2) W2 regs2 mem2 md2 POST b F8 Hb F9 (proj2 Hfx)).
intros fx3 regs3 X Hd Hr3 H10.
apply (hvf_at_b12 fx3 ly2 S2 W2 regs3 mem2 (with_vm_backing (m_vm_lazy md2) X md2) b).
- apply (hvf_I_fx B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 regs3 X HS HI
    (hvf_fxk_tr _ _ Hfx Hd) (hvf_fs_tr _ _ _ _ F9 Hd) (hvf_fs_tr _ _ _ _ F18 Hd) (hvf_fs_tr _ _ _ _ F19 Hd)).
  intros q Hq. subst regs3. apply getr_other. exact (hvf_keep_ne10 q Hq).
- exact H10.
- subst regs3. rewrite getr_other by hvf_ne. exact H11.
- subst regs3. rewrite getr_other by hvf_ne. exact H24.
- exact C90.
- exact (hvf_fs_tr _ _ _ _ F8 Hd).
- exact Hb.
- exact Hsz.
- exact Hbody.
- exact Heq.
Qed.

(* ---------------- b10 0x835d0 `mv s8,a0` ---------------- *)
Lemma hvf_at_b10 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (SF.lo64 (hvu_d b)) ->
getr regs2 (Z_to_bv 5 11) = w64 (SF.hi64 (hvu_d b)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B10 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H10 H11 C90 F8 Hb Hsz Hbody Heq.
pose proof HI as ((HC & _) & _). pose proof HC as (HJ & _).
eapply SRr_bind; [exact (hvf_b10 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ HJ H10 (hvm_lo64_rng _))|].
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & Q24).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
apply (hvf_at_lt1 fx2 ly2 S2 W2 regs3 mem2 md3 b HI3 Q24); try assumption.
rewrite (Hk3 (Z_to_bv 5 11)) by (unfold hvf_b10_kept; hvu_kin). exact H11.
Qed.

(* ---------------- the __extendsftf2 call 0x856c0 (ra 0x835d0) ---------------- *)
Lemma hvf_at_ext : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 1) = w64 HVU_RA_EXT ->
hqu_fs fx2 10 b ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_SF_EXT regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H1 F10 C90 F8 Hb Hsz Hbody Heq.
destruct hvf_geo as (HR & _).
pose proof HI as ((_ & Hfx & _ & Hrom & _) & _ & F9 & F18 & F19 & _).
apply (hsfu_ext_stmt (fx := fx2) B MT MTL HVU_RA_EXT POST _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 regs2 RR
  (NearVal.fbox b) (hvf_core fx2 ly2 S2 W2 regs2 mem2 md2 HI)).
- hvf_lit H1.
- unfold HVU_RA_EXT; lia.
- reflexivity.
- unfold NearVal.fbox. f_equal. unfold hqu_fs in F10. hvf_lit F10.
- exact Hrom.
- exact (proj2 Hfx).
- intros W3 fx3 ly3 S3 regs3 mem3 md3 Hwle Hfx3 Hcore3 Hpres3 Hfr3 Hperm3 Hio3 Hmo3 Hmem3 Hrom3 Ha0 Ha1.
  pose proof Hcore3 as (HJ3 & _).
  assert (HI3 : FI fx3 ly3 S3 W3 regs3 mem3 md3).
  { apply (hvf_move B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 ly3 S3 W3 regs3 mem3
      md3 (fun _ => False) HS HI HJ3 Hfr3 Hperm3 Hio3 Hmo3 (hvf_fxk_tr _ _ Hfx Hfx3) (hvf_fs_tr _ _ _ _ F9 Hfx3)
      (hvf_fs_tr _ _ _ _ F18 Hfx3) (hvf_fs_tr _ _ _ _ F19 Hfx3)).
    - intros q Hq. apply Hpres3. exact (hvf_keep_callee q Hq).
    - intros a [].
    - intros a Ha _. exact (Hmem3 a Ha). }
  rewrite (hvm_f128_fbox b Hb) in Ha0, Ha1.
  apply (hvf_at_b10 fx3 ly3 S3 W3 regs3 mem3 md3 b HI3).
  + hvf_lit Ha0.
  + hvf_lit Ha1.
  + apply (HPgMem.hm_at_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) _ _ C90).
    intros i Hi. apply Hmem3. cbn [hd_xv]. lia.
  + exact (hvf_fs_tr _ _ _ _ F8 Hfx3).
  + exact Hb.
  + exact Hsz.
  + exact Hbody.
  + exact Heq.
Qed.

(* ---------------- b9 0x835cc `jal __extendsftf2` ---------------- *)
Lemma hvf_at_b9 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
hqu_fs fx2 10 b ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B9 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI F10 C90 F8 Hb Hsz Hbody Heq.
pose proof HI as ((HC & _) & _). pose proof HC as (HJ & _).
eapply SRr_bind; [exact (hvf_b9 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 HJ)|].
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & Q1).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
exact (hvf_at_ext fx2 ly2 S2 W2 regs3 mem2 md3 b HI3 Q1 F10 C90 F8 Hb Hsz Hbody Heq).
Qed.

(* ---------------- fmv 0x835c8 `fmv.s fa0,fs0` ---------------- *)
Lemma hvf_at_fmv : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
fst (fp_eq fmt_single b b) = true ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVFU_FMV regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI C90 F8 Hb Hsz Hbody Heq.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
unfold cfg_at. change (w64 HVFU_FMV) with (Z_to_bv 64 HVFU_FMV).
apply (hvfu_fmv (fx := fx2) W2 regs2 mem2 md2 POST b F8).
intros X.
apply (hvf_at_b9 (FP.hvf_set 10 fx2 (Sem.nan_box (Z_to_bv 32 b))) ly2 S2 W2 regs2 mem2
  (with_vm_backing (m_vm_lazy md2) X md2) b).
- apply (hvf_I_fx B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2
    (FP.hvf_set 10 fx2 (Sem.nan_box (Z_to_bv 32 b))) regs2 X HS HI
    (hvf_fxk_set _ 10 _ Hfx ltac:(unfold HQU_FXK; cbn [In]; repeat (first [left; reflexivity | right])))
    (hvf_fs_set_other _ 10 9 _ _ F9 ltac:(lia) ltac:(lia) ltac:(lia))
    (hvf_fs_set_other _ 10 18 _ _ F18 ltac:(lia) ltac:(lia) ltac:(lia))
    (hvf_fs_set_other _ 10 19 _ _ F19 ltac:(lia) ltac:(lia) ltac:(lia))).
  intros q _. reflexivity.
- apply hvf_fs_set_same.
- exact C90.
- exact (hvf_fs_set_other _ 10 8 _ _ F8 ltac:(lia) ltac:(lia) ltac:(lia)).
- exact Hb.
- exact Hsz.
- exact Hbody.
- exact Heq.
Qed.

(* ---------------- b7 0x835c4 `beqz a0`: NaN refuses ---------------- *)
Lemma hvf_at_b7 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_eq fmt_single b b) then 1 else 0) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B7 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI H10 C90 F8 Hb Hsz Hbody.
pose proof HI as ((HC & _) & _ & _ & _ & _ & _ & _ & Hkey & Hty & Hpair & _). pose proof HC as (HJ & _).
eapply SRr_bind; [exact (hvf_b7 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ HJ H10)|].
intros W3 c3 _ [(Hc & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
              | (Hc & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)].
- hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
  apply (hvf_at_rfl fx2 ly2 S2 W2 regs3 mem2 md3 HI3).
  exact (hvf_refuse b Hb (hvf_wfv Hpair) Hty Hsz Hbody (hvm_hn_nan b Hc) Hkey).
- hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
  exact (hvf_at_fmv fx2 ly2 S2 W2 regs3 mem2 md3 b HI3 C90 F8 Hb Hsz Hbody Hc).
Qed.

(* ---------------- feq 0x835c0 `feq.s a0,fs0,fs0` ---------------- *)
Lemma hvf_at_feq : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 b,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
hqu_fs fx2 8 b -> 0 <= b < 2 ^ 32 -> 4 <= Model.e_size v -> b = Cursor.rd32 (Model.e_body v) ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVFU_FEQ regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 b HI C90 F8 Hb Hsz Hbody.
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
unfold cfg_at. change (w64 HVFU_FEQ) with (Z_to_bv 64 HVFU_FEQ).
apply (hvfu_feq (fx := fx2) W2 regs2 mem2 md2 POST b F8 Hb (proj2 Hfx)).
intros fx3 regs3 X Hd Hr3 H10.
apply (hvf_at_b7 fx3 ly2 S2 W2 regs3 mem2 (with_vm_backing (m_vm_lazy md2) X md2) b).
- apply (hvf_I_fx B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 fx3 regs3 X HS HI
    (hvf_fxk_tr _ _ Hfx Hd) (hvf_fs_tr _ _ _ _ F9 Hd) (hvf_fs_tr _ _ _ _ F18 Hd) (hvf_fs_tr _ _ _ _ F19 Hd)).
  intros q Hq. subst regs3. apply getr_other. exact (hvf_keep_ne10 q Hq).
- exact H10.
- exact C90.
- exact (hvf_fs_tr _ _ _ _ F8 Hd).
- exact Hb.
- exact Hsz.
- exact Hbody.
Qed.

(* ---------------- flw 0x835bc `flw fs0,0(s8)` ---------------- *)
Lemma hvf_at_flw : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 24) = w64 (hvu_entA cx m + 8) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
4 <= Model.e_size v ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVFU_FLW regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI H24 C90 Hsz.
destruct (hvf_ent fx2 ly2 S2 W2 regs2 mem2 md2 HI) as (_ & _ & Vbody & _ & _ & HA0 & HA1 & _).
pose proof HI as ((_ & Hfx & _) & _ & F9 & F18 & F19 & _).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hb.
unfold cfg_at. change (w64 HVFU_FLW) with (Z_to_bv 64 HVFU_FLW).
apply (hvfu_flw (fx := fx2) W2 regs2 mem2 md2 POST (hvu_entA cx m + 8) (Cursor.rd32 (Model.e_body v)) H24
  ltac:(lia) ltac:(lia) (Vbody Hsz) Hb).
intros X.
apply (hvf_at_feq (FP.hvf_set 8 fx2 (Sem.nan_box (Z_to_bv 32 (Cursor.rd32 (Model.e_body v))))) ly2 S2 W2 regs2 mem2
  (with_vm_backing (m_vm_lazy md2) X md2) (Cursor.rd32 (Model.e_body v))).
- apply (hvf_I_fx B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2
    (FP.hvf_set 8 fx2 (Sem.nan_box (Z_to_bv 32 (Cursor.rd32 (Model.e_body v))))) regs2 X HS HI
    (hvf_fxk_set _ 8 _ Hfx ltac:(unfold HQU_FXK; cbn [In]; repeat (first [left; reflexivity | right])))
    (hvf_fs_set_other _ 8 9 _ _ F9 ltac:(lia) ltac:(lia) ltac:(lia))
    (hvf_fs_set_other _ 8 18 _ _ F18 ltac:(lia) ltac:(lia) ltac:(lia))
    (hvf_fs_set_other _ 8 19 _ _ F19 ltac:(lia) ltac:(lia) ltac:(lia))).
  intros q _. reflexivity.
- exact C90.
- apply hvf_fs_set_same.
- exact Hb.
- exact Hsz.
- reflexivity.
Qed.

(* ---------------- b4 0x835a4: the body check ---------------- *)
Lemma hvf_at_b4 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (hvu_entA cx m + 8) ->
getr regs2 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)) ->
hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (LCell XR 0x90) p ->
4 <= Model.e_size v ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B4 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI H10 H24 C90 Hsz.
destruct hvf_geo as (HR & Hal & _).
destruct (hvf_ent fx2 ly2 S2 W2 regs2 mem2 md2 HI) as (_ & _ & _ & _ & Rbody & HA0 & HA1 & Happ).
pose proof HI as ((HC & _) & Hat & _). pose proof HC as (HJ & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 RR Hat ltac:(unfold hvf_Lb; hvu_in)) as R9.
pose proof (hvu_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(unfold hvf_Lb; hvu_in)) as R27.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xe8 (PP + Layout.OFF_ENT + 8) Hat ltac:(unfold hvf_Lb; hvu_in)) as Ce8.
cbn [hd_xv] in Ce8.
destruct hvf_pp as (Hpp0 & Hppc & _).
assert (EA : hvu_entA cx m = PP + Layout.OFF_ENT + Layout.ENT_SIZE * (Z.of_nat m + 1)) by reflexivity.
eapply SRr_bind.
{ exact (hvf_b4 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 RR (hvu_entA cx m + 8)
    (Layout.ENT_SIZE * (Z.of_nat m + 1)) (PP + Layout.OFF_ENT + 8) HJ R9 H10 H24 R27 HR Hal ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(unfold Layout.ENT_SIZE; lia) ltac:(unfold Layout.OFF_ENT; lia)
    ltac:(rewrite EA in HA1; unfold Layout.OFF_ENT, Layout.ENT_SIZE in *; lia) Rbody
    ltac:(destruct Happ as [Hx|Hx]; [left | right]; lia) Ce8). }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & Q24).
replace (PP + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * (Z.of_nat m + 1)) with (hvu_entA cx m + 8) in Q24
  by (rewrite EA; lia).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
exact (hvf_at_flw fx2 ly2 S2 W2 regs3 mem2 md3 HI3 Q24 C90 Hsz).
Qed.

(* ---------------- b3 0x83598: R+0x90 := the param, the body's address ---------------- *)
Lemma hvf_at_b3 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)) ->
getr regs2 (Z_to_bv 5 16) = w64 p ->
4 <= Model.e_size v ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B3 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI H24 H16 Hsz.
destruct hvf_geo as (HR & Hal & HR220 & Hwin & _).
destruct (hvf_ent fx2 ly2 S2 W2 regs2 mem2 md2 HI) as (_ & _ & _ & _ & _ & HA0 & HA1 & _).
pose proof HI as ((HC & _) & Hat & _ & _ & _ & _ & _ & Hkey & _). pose proof HC as (HJ & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 RR Hat ltac:(unfold hvf_Lb; hvu_in)) as R9.
pose proof (hvu_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(unfold hvf_Lb; hvu_in)) as R27.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xe0 (PP + Layout.OFF_ENT + 8) Hat ltac:(unfold hvf_Lb; hvu_in)) as Ce0.
cbn [hd_xv] in Ce0.
pose proof (hvm_key_cell _ ch p Hkey) as (_ & Hp).
assert (Hp3 : 0 <= p < 3)
  by (unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS in Hp; destruct Hp as [->|[->| ->]]; lia).
destruct hvf_pp as (Hpp0 & Hppc & _).
assert (Ht : T_SEG_STK = 16384) by reflexivity.
assert (EA : hvu_entA cx m = PP + Layout.OFF_ENT + Layout.ENT_SIZE * (Z.of_nat m + 1)) by reflexivity.
eapply SRr_bind.
{ exact (hvf_b3 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 RR p (Layout.ENT_SIZE * (Z.of_nat m + 1))
    (PP + Layout.OFF_ENT + 8) HJ R9 H16 H24 R27 HR Hal ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold Layout.ENT_SIZE; lia) ltac:(unfold Layout.OFF_ENT; lia)
    ltac:(rewrite EA in HA1; unfold Layout.OFF_ENT, Layout.ENT_SIZE in *; lia) Ce0). }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hkeep3 & (Q10 & C90)).
assert (HI3 : FI fx2 ly2 S2 W2 regs3 mem3 md3).
{ apply (hvf_I_mem B MT MTL cx r ev at0 m k v ch p cs keys rf fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    (fun a => RR + 0x90 <= a < RR + 0x98) HS HI HJ3 Hio3); [ | intros a Ha; cbv beta in Ha; lia | exact Hkeep3].
  intros q Hq. apply Hk3. revert q Hq. hvf_keepk. }
replace (PP + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * (Z.of_nat m + 1)) with (hvu_entA cx m + 8) in Q10
  by (rewrite EA; lia).
apply (hvf_at_b4 fx2 ly2 S2 W2 regs3 mem3 md3 HI3 Q10).
- rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvf_b3_kept; hvu_kin). exact H24.
- cbn [hd_at hd_xv]. rewrite (Z.mod_small p (2 ^ 64)) by lia. exact C90.
- exact Hsz.
Qed.

(* ---------------- b2 0x8357c: the size check and the size test ---------------- *)
Lemma hvf_at_b2 : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
FI fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (hvu_entA cx m) ->
getr regs2 (Z_to_bv 5 11) = w64 (hvu_entA cx m + 4) ->
getr regs2 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)) ->
getr regs2 (Z_to_bv 5 16) = w64 p ->
getr regs2 (Z_to_bv 5 15) = w64 Headamp.REFUSE_OUT_OF_RANGE ->
getr regs2 (Z_to_bv 5 30) = w64 (PP + Layout.OFF_PARAMS_STRUCT) ->
getr regs2 (Z_to_bv 5 31) = w64 (shadow_addr (PP + Layout.OFF_PARAMS_STRUCT)) ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVF_B2 regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 HI H10 H11 H24 H16 H15 H30 H31.
destruct hvf_geo as (HR & Hal & _).
destruct (hvf_ent fx2 ly2 S2 W2 regs2 mem2 md2 HI) as (Hwfv & Vsz & _ & Rsz & _ & HA0 & HA1 & Happ).
pose proof HI as ((HC & _) & Hat & _ & _ & _ & _ & _ & Hkey & _). pose proof HC as (HJ & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 RR Hat ltac:(unfold hvf_Lb; hvu_in)) as R9.
pose proof (hvu_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(unfold hvf_Lb; hvu_in)) as R27.
pose proof (hvm_ent_bounds v Hwfv) as (_ & Hsz).
eapply SRr_bind.
{ exact (hvf_b2 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 RR (hvu_entA cx m) (Model.e_size v)
    HJ R9 H10 H11 R27 HR Hal HA0 HA1 Hsz Rsz Happ Vsz). }
intros W3 c3 _ [(Hlt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
              | (Hge & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)].
- (* size below 4: RF, with a5, t5 and t6 as at FA *)
  hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
  apply (HRF fx2 ly2 S2 W2 regs3 mem2 md3 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
  destruct HI3 as (Hb3 & Hat3 & F9 & F18 & F19 & Hlive & Ham & _ & _ & Hpair & _ & Hx).
  assert (Hcell : Headamp.expect_cell k v = inl Headamp.REFUSE_OUT_OF_RANGE)
    by (apply (hvm_cell_inl k v ch p Hkey); left; rewrite (hvm_cv_small v Hwfv Hlt); lia).
  unfold hqu_cut_RF.
  refine (conj Hb3 (conj _ (conj F9 (conj F18 (conj F19 (conj Hlive (conj Ham (conj Hcell
    (conj (or_intror eq_refl) (conj Hpair Hx)))))))))).
  unfold hsu_at_cx, hvf_Lb in *.
  apply hvu_at_app; split; [hvu_sub Hat3|].
  apply hvu_at_app; split; [hvu_sub Hat3|].
  apply hvu_at_app; split.
  { unfold hqu_L_t56, hsu_at. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite (Hk3 (Z_to_bv 5 30)) by (unfold hvu_q6a_kept; hvu_kin). exact H30.
    - rewrite (Hk3 (Z_to_bv 5 31)) by (unfold hvu_q6a_kept; hvu_kin). exact H31. }
  apply hvu_at_app; split; [hvu_sub Hat3|].
  unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
  rewrite (Hk3 (Z_to_bv 5 15)) by (unfold hvu_q6a_kept; hvu_kin). exact H15.
- hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
  apply (hvf_at_b3 fx2 ly2 S2 W2 regs3 mem2 md3 HI3).
  + rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvu_q6a_kept; hvu_kin). exact H24.
  + rewrite (Hk3 (Z_to_bv 5 16)) by (unfold hvu_q6a_kept; hvu_kin). exact H16.
  + exact Hge.
Qed.

(* ---------------- FA 0x83578 ---------------- *)
Lemma hvf_at_fa : forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
@hvu_cut_FA fx rc SK B MT cx fx2 r at0 m k v ch p cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HVU_FA regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 Hcut.
assert (HI : FI fx2 ly2 S2 W2 regs2 mem2 md2).
{ destruct Hcut as (Hb3 & Hat & F9 & F18 & F19 & Hlive & Ham & Hkey & Hty & Hpair & Hkcs & Hx).
  refine (conj Hb3 (conj _ (conj F9 (conj F18 (conj F19 (conj Hlive (conj Ham (conj Hkey (conj Hty
    (conj Hpair (conj Hkcs Hx))))))))))).
  unfold hsu_at_cx, hvf_Lb in *. hvu_sub Hat. }
destruct Hcut as (Hb3 & Hat & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 10 (hvu_entA cx m) Hat ltac:(hvu_in)) as R10.
pose proof (hvu_at_get _ _ _ _ _ 13 (PP + Layout.OFF_ENT + 4) Hat ltac:(hvu_in)) as R13.
pose proof (hvu_at_get _ _ _ _ _ 24 (Layout.ENT_SIZE * (Z.of_nat m + 1)) Hat ltac:(hvu_in)) as R24.
pose proof (hvu_at_get _ _ _ _ _ 16 p Hat ltac:(hvu_in)) as R16.
pose proof (hvu_at_get _ _ _ _ _ 15 Headamp.REFUSE_OUT_OF_RANGE Hat ltac:(hvu_in)) as R15.
pose proof (hvu_at_get _ _ _ _ _ 30 (PP + Layout.OFF_PARAMS_STRUCT) Hat ltac:(hvu_in)) as R30.
pose proof (hvu_at_get _ _ _ _ _ 31 (shadow_addr (PP + Layout.OFF_PARAMS_STRUCT)) Hat ltac:(hvu_in)) as R31.
pose proof Hb3 as (HC & _). pose proof HC as (HJ & _).
destruct (hvf_ent fx2 ly2 S2 W2 regs2 mem2 md2 HI) as (_ & _ & _ & _ & _ & HA0 & HA1 & _).
destruct hvf_pp as (Hpp0 & Hppc & _).
assert (EA : hvu_entA cx m = PP + Layout.OFF_ENT + Layout.ENT_SIZE * (Z.of_nat m + 1)) by reflexivity.
eapply SRr_bind.
{ exact (hvf_b1 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (PP + Layout.OFF_ENT + 4)
    (Layout.ENT_SIZE * (Z.of_nat m + 1)) HJ R13 R24 ltac:(unfold Layout.OFF_ENT; lia)
    ltac:(unfold Layout.ENT_SIZE; lia) ltac:(rewrite EA in HA1; unfold Layout.OFF_ENT, Layout.ENT_SIZE in *; lia)). }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & Q11).
hvf_regs HI regs3 md3 HJ3 Hio3 Hk3 HI3.
apply (hvf_at_b2 fx2 ly2 S2 W2 regs3 mem2 md3 HI3).
- rewrite (Hk3 (Z_to_bv 5 10)) by (unfold hvf_b1_kept; hvu_kin). exact R10.
- replace (hvu_entA cx m + 4) with (PP + Layout.OFF_ENT + 4 + Layout.ENT_SIZE * (Z.of_nat m + 1))
    by (rewrite EA; lia). exact Q11.
- rewrite (Hk3 (Z_to_bv 5 24)) by (unfold hvf_b1_kept; hvu_kin). exact R24.
- rewrite (Hk3 (Z_to_bv 5 16)) by (unfold hvf_b1_kept; hvu_kin). exact R16.
- rewrite (Hk3 (Z_to_bv 5 15)) by (unfold hvf_b1_kept; hvu_kin). exact R15.
- rewrite (Hk3 (Z_to_bv 5 30)) by (unfold hvf_b1_kept; hvu_kin). exact R30.
- rewrite (Hk3 (Z_to_bv 5 31)) by (unfold hvf_b1_kept; hvu_kin). exact R31.
Qed.
End w.

(* ================================ the lane ================================ *)
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : KI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Theorem hvu_flt_B : @hvu_piece_flt_stmt fx rc SK B MT.
Proof.
unfold hvu_piece_flt_stmt. intros cx POST r ev at0 m HS HRF HCV.
unfold hvu_from_FA. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf Hcut.
exact (hvf_at_fa B MT MTL cx POST r ev at0 m k v ch p cs keys rf HS HRF HCV fx2 ly2 S2 W2 regs2 mem2 md2 Hcut).
Qed.
End z.

About hvu_flt_B.
Print Assumptions hvu_flt_B.

Print Assumptions hvf_b1.
Print Assumptions hvf_b2.
Print Assumptions hvf_b3.
Print Assumptions hvf_b4.
Print Assumptions hvf_b7.
Print Assumptions hvf_rfl.
Print Assumptions hvf_b9.
Print Assumptions hvf_b10.
Print Assumptions hvf_b12.
Print Assumptions hvf_b14.
Print Assumptions hvf_b16.
Print Assumptions hvf_b17.
