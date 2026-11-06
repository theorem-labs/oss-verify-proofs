(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module paths and module names changed; 1306 of its 1358 lines of code are new or changed and 689 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S06 of the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s16: from K85208 (the last
   turn's m_file(m, text, NULL) returned, 0x85208) through the inlined m_cross loop (fuzz_segconf.c:296-310) to
   K853bc (0x853bc), lt_seg_S06_stmt of LLVMFuzzerTestOneInput_defs.v.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new)

   THE CODE (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan.s lines 311-419, image A; listing SegList.v 358-466):
     0x85208 (K85208)  a3 = 176(s1) = the shadow base; 112(s1) = s10 = (m + 0x2000) >> 3; s2 = SH(m + 0x2000)
     0x85214           check 9 of m->n (its shadow byte is 0: m + 0x2000 .. + 7 lie in m's block)
     0x8521c           a0 = m->n; a4 = 168(s1) = m; blez a0 -> 0x853bc
     0x8522c           s9 = i = 0; s8 = 64(s1) = SH(m + 0x14); s10 = s4 = 72(s1) = m + 0x20
     0x8523c (KH i)    check 10; role_set = lw -12(s4); beqz -> 0x85298
     0x85250           s3 = &m->seg[i] + 0x10, s5 = SH(s3); checks 11, 12; role, model_set; beqz model_set -> 0x852dc;
                       role = 4 -> 0x852dc; else s3 = &model_set, j 0x852b4
     0x85298           check 13; model_set; s3 = s4; beqz -> latch
     0x852b4           jal m_refuse(m, 0)                                        -> KP1 i at 0x852c0
     0x852c0 (KP1 i)   a3 reloaded; check 14; sw zero,0(s3) (model_set = 0); a4 reloaded -> latch
     0x852dc           role != 4 -> latch; model_set != 0 -> latch; jal m_refuse(m, 0) -> KP2 i at 0x852f0
     0x852f0 (KP2 i)   check 15; sw zero,-12(s4) (role_set = 0); check 16; sw zero,-16(s4) (role = 0); a3, a4
                       reloaded -> latch
     0x85310 (KL i)    check 17 of m->n; a0 = m->n; i += 1; s10, s4 += 256; s8 += 32; blt i, a0 -> KH (i + 1);
                       j 0x853bc (K853bc)
   Every instrumented check of the segment (checks 9-17) vanishes in the run by a shadow entry: the 256 bytes of
   m->seg[i] and the 9236 bytes of m, addressable by the allocator's shadow law.
   The model: the loop after i passes holds s16_Mi (fold_left m_cross_seg (seq 0 i)) of m_file's result. The inner
   cuts (LLVMFuzzerTestOneInput_s16k.v) are proved in the order the loop needs them: KL from KH (i + 1) and K853bc
   (s16_latch), KP1 / KP2 from KL (s16_kp1, s16_kp2), KH from KL, KP1, KP2 (s16_head), K85208 from KH 0 and K853bc
   (s16_entry). m_refuse returns at an FP state of its own (its post is apost_baseF), so KP1 and KP2 are taken at
   every FP state, and the loop (s16_loop) is closed by induction on 32 - i, as chain_words_a.v's cw_loop, at every
   FP state.
   Section hypotheses: m_refuse's contract (lib/A/Prog/m_refuse_c.v) at every FP state, with fuzz_segconf.c's
   literal map seg_litA_fz; ameter_fs_laws (the meter across m_refuse's set_fs state change); seg_sig_prog (the
   call target of m_refuse). AR_laws is YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YI16 YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YI67.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaFx PaLibG PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s16k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the symbolic states ===================================== *)
(* atoms: 0 .. 31 the registers, 32 the shadow base SB, 33 m, 34 G = &m->seg[i], 35 role_set, 36 role,
   37 model_set (of m->seg[i]), 38 m->n *)
Definition shx (a : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff a c) (SLit 3)) (SOff 32 0).
Definition s16_Bx : sv := SOff 32 0.
Definition s16_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the s1 slots the segment reads: 168 m, 176 the shadow base, 184 &m->n; at the entry also 64 SH(m + 0x14) and
   72 m + 0x20, and the window of 112(s1) *)
Definition s16_slotsE : YP09.region := YP09.mkRegion (Some 9%nat) 64 192 112 120
  [YP09.mkChunk 64 (CVal 8 (shx 33 0x14)); YP09.mkChunk 72 (CVal 8 (SOff 33 0x20));
   YP09.mkChunk 168 (CVal 8 (SOff 33 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0x2000))].
Definition s16_slotsR : YP09.region := YP09.mkRegion (Some 9%nat) 168 192 0 0
  [YP09.mkChunk 168 (CVal 8 (SOff 33 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0x2000))].
(* m->seg[i]'s role, role_set and model_set; the windows of the two edits; m->n *)
Definition s16_seg : YP09.region := YP09.mkRegion (Some 34%nat) 0x10 0x24 0 0
  [YP09.mkChunk 0x10 (CVal 4 (SOff 36 0)); YP09.mkChunk 0x14 (CVal 4 (SOff 35 0)); YP09.mkChunk 0x20 (CVal 4 (SOff 37 0))].
Definition s16_segW1 : YP09.region := YP09.mkRegion (Some 34%nat) 0x20 0x24 0x20 0x24 [].
Definition s16_segW2 : YP09.region := YP09.mkRegion (Some 34%nat) 0x10 0x18 0x10 0x18 [].
Definition s16_n : YP09.region := YP09.mkRegion (Some 33%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 38 0))].
Definition s16_atomsE : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 (2 ^ 47 - 2 ^ 20) 4);
   (34%nat, mkAF 4096 (2 ^ 47 - 2 ^ 20) 4); (38%nat, mkAF 0 32 0)].
Definition s16_factsE : facts := mkFacts s16_atomsE [] [].
Definition s16_factsH : facts :=
  mkFacts (s16_atomsE ++ [(35%nat, mkAF 0 1 0); (36%nat, mkAF 0 (2 ^ 31 - 1) 0); (37%nat, mkAF 0 1 0)]) [] [].
Definition s16_SHE : list shent := [mkSHE 33 0 9236].
Definition s16_SH : list shent := [mkSHE 34 0 256; mkSHE 33 0 9236].
(* the register maps: the loop's (head and latch), after each call, at the entry *)
Definition s16_regsL :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 13 (SOff 32 0)) 14 (SOff 33 0)) 18 (shx 33 0x2000))
    20 (SOff 34 0x20)) 24 (shx 34 0x14)) 26 (SOff 34 0x20).
Definition s16_regsP1 :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 19 (SOff 34 0x20)) 18 (shx 33 0x2000))
    20 (SOff 34 0x20)) 24 (shx 34 0x14)) 26 (SOff 34 0x20).
Definition s16_regsP2 :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 21 (shx 34 0x10)) 18 (shx 33 0x2000))
    20 (SOff 34 0x20)) 24 (shx 34 0x14)) 26 (SOff 34 0x20).
Definition s16_regsE := sr_set sr_atoms 26 (SAlu ALU_SRL (SOff 33 0x2000) (SLit 3)).
Definition ss_ke : sstate := mkSS LO_K85208 s16_regsE [s16_slotsE; s16_n] None s16_factsE.
Definition ss_kh : sstate := mkSS LO_KH16 s16_regsL [s16_slotsR; s16_seg; s16_n] None s16_factsH.
Definition ss_kp1 : sstate := mkSS LO_KP1 s16_regsP1 [s16_slotsR; s16_segW1; s16_n] None s16_factsE.
Definition ss_kp2 : sstate := mkSS LO_KP2 s16_regsP2 [s16_slotsR; s16_segW2; s16_n] None s16_factsE.
Definition ss_kl : sstate := mkSS LO_KL16 s16_regsL [s16_slotsR; s16_n] None s16_factsE.

(* the static checks of the token runner on the five seeds *)
Lemma s16_static : sh_static_ok (run_K A_LIM s16_Bx s16_SHE ss_ke) s16_Bx s16_span s16_SHE (ss_facts ss_ke) (ss_mem ss_ke) = true /\
  sh_static_ok (run_K A_LIM s16_Bx s16_SH ss_kh) s16_Bx s16_span s16_SH (ss_facts ss_kh) (ss_mem ss_kh) = true /\
  sh_static_ok (run_K A_LIM s16_Bx s16_SH ss_kp1) s16_Bx s16_span s16_SH (ss_facts ss_kp1) (ss_mem ss_kp1) = true /\
  sh_static_ok (run_K A_LIM s16_Bx s16_SH ss_kp2) s16_Bx s16_span s16_SH (ss_facts ss_kp2) (ss_mem ss_kp2) = true /\
  sh_static_ok (run_K A_LIM s16_Bx s16_SH ss_kl) s16_Bx s16_span s16_SH (ss_facts ss_kl) (ss_mem ss_kl) = true.
Proof. vm_compute. repeat split. Qed.

(* ===================================== denotations ===================================== *)
Section den. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
(* the environment of every seed: the registers, then SB, m, G, role_set, role, model_set, m->n *)
Definition s16_E (regs : bvmap 5 word) (m g rs ro ms n : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [SB; m; g; rs; ro; ms; n])).
Lemma s16_E_reg : forall regs m g rs ro ms n k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (s16_E regs m g rs ro ms n) k = getr regs r.
Proof. intros. unfold s16_E. apply ew_Eimg_Ereg_nat. exact H. Qed.
Lemma s16_E_x : forall regs m g rs ro ms n,
  ew (s16_E regs m g rs ro ms n) 32 = Z_to_bv 64 SB /\ ew (s16_E regs m g rs ro ms n) 33 = Z_to_bv 64 m /\
  ew (s16_E regs m g rs ro ms n) 34 = Z_to_bv 64 g /\ ew (s16_E regs m g rs ro ms n) 35 = Z_to_bv 64 rs /\
  ew (s16_E regs m g rs ro ms n) 36 = Z_to_bv 64 ro /\ ew (s16_E regs m g rs ro ms n) 37 = Z_to_bv 64 ms /\
  ew (s16_E regs m g rs ro ms n) 38 = Z_to_bv 64 n.
Proof.
intros. unfold s16_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
repeat split; first [exact (ew_Ereg_extra regs _ 0) | exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
  | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4) | exact (ew_Ereg_extra regs _ 5)
  | exact (ew_Ereg_extra regs _ 6)].
Qed.
Lemma s16_den_off : forall (E : env) n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma s16_den_shx : forall (E : env) n x c, ew E n = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SB ->
  0 <= x < 2 ^ 47 -> 0 <= c < 2 ^ 16 ->
  sv_denot E (shx n c) = Z_to_bv 64 (SB + (x + c) / 8).
Proof.
intros E n x c Hn Hb Hx Hc. unfold shx. cbn [sv_denot].
rewrite Hn, Hb, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.add_0_r.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id (x + c)) by (unfold M64; lia). change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (H8 : 0 <= (x + c) / 8 < M64) by (unfold M64; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !(zcanon_id ((x + c) / 8) H8).
rewrite !(zcanon_id SB) by (unfold SB, M64; lia). f_equal. lia.
Qed.
Lemma s16_den_srl3 : forall (E : env) n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 47 -> 0 <= c < 2 ^ 16 ->
  sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)) = Z_to_bv 64 ((x + c) / 8).
Proof.
intros E n x c Hn Hx Hc. cbn [sv_denot]. rewrite Hn, !unsigned_lit_small by lia.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id (x + c)) by (unfold M64; lia). change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. reflexivity.
Qed.
End den.

(* ===================================== the seeds ===================================== *)
Section seeds. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* what a cut gives a seed: the frame's registers and slots, the block m *)
Lemma s16_basic : forall cx ly S (W : world SEGS) regs mem md k acc rem o O c m X,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE -> lt_slots cx (rdW W mem) (LT_L cx c m ++ X) ->
  AR SEGS B ly S W mem md /\ getr regs 2 = w64 (x_s1 cx) /\ getr regs 9 = w64 (x_s1 cx) /\
  2 ^ 46 <= x_s1 cx /\ x_s1 cx + 320 <= 2 ^ 47 /\ x_s1 cx mod 32 = 0 /\
  4096 <= m /\ m mod 16 = 0 /\ m + 9236 <= 2 ^ 47 - 2 ^ 23 /\ in_app m 9236 /\ m + 9236 <= x_s1 cx /\
  rdword (rdW W mem) (x_s1 cx + 168) = Some m /\ rdword (rdW W mem) (x_s1 cx + 176) = Some SHADOW_OFF /\
  rdword (rdW W mem) (x_s1 cx + 184) = Some (m + seg_spec.MC_N) /\
  rdword (rdW W mem) (x_s1 cx + 64) = Some (shadow_addr (m + 0x14)) /\
  rdword (rdW W mem) (x_s1 cx + 72) = Some (m + 0x20) /\
  (forall a, x_s1 cx <= a < x_s1 cx + 192 -> apresent (w_H W) mem a) /\
  (forall a, m <= a < m + 9236 -> apresent (w_H W) mem a) /\
  range_addressable (rdW W mem) SHADOW_OFF m 9236.
Proof.
intros cx ly S W regs mem md k acc rem o O c m X HB (HFR & _) Hm HSL.
destruct HFR as (HJ & R2 & _ & _ & _ & R9 & _ & _ & _ & _ & _ & H176 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (s16_stk B MT cx HB) as (Hsp16 & Hsp & Hs1m & Hs1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof Hm as (HmIn & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HmIn) as (Hm16 & Hm0 & Hmc & Hmapp & Hmpres & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmc, Hmapp, Hmpres.
assert (SL : forall oo vv, In (oo, vv) (LT_L cx c m) -> rdword (rdW W mem) (x_s1 cx + oo) = Some vv)
  by (intros oo vv Hin; apply HSL; apply in_or_app; left; exact Hin).
split; [exact HAR|]. split; [exact R2|]. split; [exact R9|].
split; [lia|]. split; [lia|]. split; [exact Hs1m|].
split; [lia|]. split; [exact Hm16|]. split; [lia|]. split; [exact Hmapp|]. split; [unfold x_sp0 in *; lia|].
split; [apply SL; unfold LT_L; cbn [In]; tauto|].
split; [exact H176|].
split; [apply SL; unfold LT_L; cbn [In]; tauto|].
split; [apply SL; unfold LT_L; cbn [In]; tauto|].
split; [apply SL; unfold LT_L; cbn [In]; tauto|].
split; [intros a Ha; apply Hpres; unfold x_sp0 in *; lia|].
split; [intros a Ha; exact (proj1 (Hmpres a Ha))|].
exact (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE m 9236 HAR HmIn
  ltac:(lia) ltac:(change (req_size seg_spec.SEG_M_SIZE) with 9236; lia)).
Qed.

Lemma s16_afact : forall (E : env) n v lo hi al,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al Hn Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.
Lemma s16_chunk8 : forall (E : env) mem base off e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS (fun _ => false) mem) (base + off) = Some v \/
  val_mem SEGS mem (base + off) 8 v -> val_mem SEGS mem (base + off) 8 v.
Proof. intros E mem base off e v _ _ [H|H]; [|exact H]. exact (val_mem_of_rdword SEGS _ _ _ _ H). Qed.

(* the facts of the seeds *)
Lemma s16_factsE_ok : forall regs m g rs ro ms n s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= m <= 2 ^ 47 - 2 ^ 20 -> m mod 16 = 0 -> 4096 <= g <= 2 ^ 47 - 2 ^ 20 -> g mod 16 = 0 -> 0 <= n <= 32 ->
  facts_ok (s16_E regs m g rs ro ms n) s16_factsE.
Proof.
intros regs m g rs ro ms n s1 R9 Hs1 Hs1m Hm Hm16 Hg Hg16 Hn.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
split; [|split; exact I]. cbn [s16_factsE f_atoms s16_atomsE atoms_ok].
split; [apply (s16_afact _ _ s1); [rewrite (s16_E_reg regs m g rs ro ms n 9 9%bv eq_refl); exact R9 | lia | lia
  | change (2 ^ 5) with 32; exact Hs1m | lia]|].
split; [apply (s16_afact _ _ SB); [exact X32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (s16_afact _ _ m); [exact X33 | lia | lia | change (2 ^ 4) with 16; exact Hm16 | lia]|].
split; [apply (s16_afact _ _ g); [exact X34 | lia | lia | change (2 ^ 4) with 16; exact Hg16 | lia]|].
split; [apply (s16_afact _ _ n); [exact X38 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
exact I.
Qed.
Lemma s16_factsH_ok : forall regs m g rs ro ms n s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= m <= 2 ^ 47 - 2 ^ 20 -> m mod 16 = 0 -> 4096 <= g <= 2 ^ 47 - 2 ^ 20 -> g mod 16 = 0 -> 0 <= n <= 32 ->
  0 <= rs <= 1 -> 0 <= ro <= 2 ^ 31 - 1 -> 0 <= ms <= 1 ->
  facts_ok (s16_E regs m g rs ro ms n) s16_factsH.
Proof.
intros regs m g rs ro ms n s1 R9 Hs1 Hs1m Hm Hm16 Hg Hg16 Hn Hrs Hro Hms.
destruct (s16_factsE_ok regs m g rs ro ms n s1 R9 Hs1 Hs1m Hm Hm16 Hg Hg16 Hn) as (HA & _).
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
split; [|split; exact I]. cbn [s16_factsH f_atoms]. cbn [s16_factsE f_atoms] in HA.
cbn [s16_atomsE app atoms_ok] in HA |- *.
destruct HA as (A1 & A2 & A3 & A4 & A5 & _).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [apply (s16_afact _ _ rs); [exact X35 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (s16_afact _ _ ro); [exact X36 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (s16_afact _ _ ms); [exact X37 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
exact I.
Qed.

(* the regions *)
Lemma s16_slotsR_ok : forall (W : world SEGS) regs mem m g rs ro ms n s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> 4096 <= m <= 2 ^ 47 - 2 ^ 20 ->
  rdword (rdW W mem) (s1 + 168) = Some m -> rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 184) = Some (m + seg_spec.MC_N) ->
  region_ok SEGS (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) s16_slotsR.
Proof.
intros W regs mem m g rs ro ms n s1 R9 Hs1 Hm H168 H176 H184.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (U9 : base_val (s16_E regs m g rs ro ms n) (Some 9%nat) = s1).
{ cbn [base_val]. rewrite (s16_E_reg regs m g rs ro ms n 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
unfold region_ok, s16_slotsR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U9.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS _ _ s1 168 8 (SOff 33 0) m); [rewrite (s16_den_off _ 33 m 0 X33) by lia; f_equal; lia | cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H168).
- apply (chunk_ok_val SEGS _ _ s1 176 8 (SOff 32 0) SB);
    [rewrite (s16_den_off _ 32 SB 0 X32) by (unfold SB; lia); f_equal; lia | unfold SB; cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H176).
- apply (chunk_ok_val SEGS _ _ s1 184 8 (SOff 33 0x2000) (m + seg_spec.MC_N));
    [rewrite (s16_den_off _ 33 m 0x2000 X33) by lia; reflexivity | unfold seg_spec.MC_N; cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H184).
Qed.
Lemma s16_slotsE_ok : forall (W : world SEGS) regs mem m g rs ro ms n s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> 4096 <= m <= 2 ^ 47 - 2 ^ 20 ->
  rdword (rdW W mem) (s1 + 64) = Some (shadow_addr (m + 0x14)) -> rdword (rdW W mem) (s1 + 72) = Some (m + 0x20) ->
  rdword (rdW W mem) (s1 + 168) = Some m -> rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 184) = Some (m + seg_spec.MC_N) ->
  (forall a, s1 <= a < s1 + 192 -> apresent (w_H W) mem a) ->
  region_ok SEGS (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) s16_slotsE.
Proof.
intros W regs mem m g rs ro ms n s1 R9 Hs1 Hm H64 H72 H168 H176 H184 Hpres.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (U9 : base_val (s16_E regs m g rs ro ms n) (Some 9%nat) = s1).
{ cbn [base_val]. rewrite (s16_E_reg regs m g rs ro ms n 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
unfold region_ok, s16_slotsE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U9.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS _ _ s1 64 8 (shx 33 0x14) (shadow_addr (m + 0x14)));
    [rewrite (s16_den_shx _ 33 m 0x14 X33 X32) by lia; reflexivity | unfold shadow_addr, SHADOW_OFF | cbn; lia |].
  + assert (0 <= (m + 0x14) / 8 <= m) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). cbn; lia.
  + exact (val_mem_of_rdword SEGS _ _ _ _ H64).
- apply (chunk_ok_val SEGS _ _ s1 72 8 (SOff 33 0x20) (m + 0x20)); [rewrite (s16_den_off _ 33 m 0x20 X33) by lia; reflexivity | cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H72).
- apply (chunk_ok_val SEGS _ _ s1 168 8 (SOff 33 0) m); [rewrite (s16_den_off _ 33 m 0 X33) by lia; f_equal; lia | cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H168).
- apply (chunk_ok_val SEGS _ _ s1 176 8 (SOff 32 0) SB);
    [rewrite (s16_den_off _ 32 SB 0 X32) by (unfold SB; lia); f_equal; lia | unfold SB; cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H176).
- apply (chunk_ok_val SEGS _ _ s1 184 8 (SOff 33 0x2000) (m + seg_spec.MC_N));
    [rewrite (s16_den_off _ 33 m 0x2000 X33) by lia; reflexivity | unfold seg_spec.MC_N; cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ H184).
Qed.
Lemma s16_n_ok : forall (W : world SEGS) regs mem m g rs ro ms n,
  4096 <= m <= 2 ^ 47 - 2 ^ 20 -> 0 <= n <= 32 -> rd32 (rdW W mem) (m + seg_spec.MC_N) n ->
  region_ok SEGS (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) s16_n.
Proof.
intros W regs mem m g rs ro ms n Hm Hn Hr.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (U : base_val (s16_E regs m g rs ro ms n) (Some 33%nat) = m) by (cbn [base_val]; rewrite X33; apply unsigned_lit_small; lia).
unfold region_ok, s16_n. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
apply (chunk_ok_val SEGS _ _ m 0x2000 4 (SOff 38 0) n); [rewrite (s16_den_off _ 38 n 0 X38) by lia; f_equal; lia | cbn; lia | cbn; lia |].
exact (val_mem_of_rd32 SEGS _ _ _ _ Hr).
Qed.
Lemma s16_seg_ok : forall (W : world SEGS) regs mem m g rs ro ms n,
  4096 <= g <= 2 ^ 47 - 2 ^ 20 -> 0 <= rs <= 1 -> 0 <= ro < 2 ^ 31 -> 0 <= ms <= 1 ->
  rd32 (rdW W mem) (g + 0x10) ro -> rd32 (rdW W mem) (g + 0x14) rs -> rd32 (rdW W mem) (g + 0x20) ms ->
  region_ok SEGS (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) s16_seg.
Proof.
intros W regs mem m g rs ro ms n Hg Hrs Hro Hms Hr1 Hr2 Hr3.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (U : base_val (s16_E regs m g rs ro ms n) (Some 34%nat) = g) by (cbn [base_val]; rewrite X34; apply unsigned_lit_small; lia).
unfold region_ok, s16_seg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS _ _ g 0x10 4 (SOff 36 0) ro); [rewrite (s16_den_off _ 36 ro 0 X36) by lia; f_equal; lia | cbn; lia | cbn; lia |].
  exact (val_mem_of_rd32 SEGS _ _ _ _ Hr1).
- apply (chunk_ok_val SEGS _ _ g 0x14 4 (SOff 35 0) rs); [rewrite (s16_den_off _ 35 rs 0 X35) by lia; f_equal; lia | cbn; lia | cbn; lia |].
  exact (val_mem_of_rd32 SEGS _ _ _ _ Hr2).
- apply (chunk_ok_val SEGS _ _ g 0x20 4 (SOff 37 0) ms); [rewrite (s16_den_off _ 37 ms 0 X37) by lia; f_equal; lia | cbn; lia | cbn; lia |].
  exact (val_mem_of_rd32 SEGS _ _ _ _ Hr3).
Qed.
Lemma s16_segW_ok : forall (W : world SEGS) regs mem m g rs ro ms n lo hi,
  4096 <= g <= 2 ^ 47 - 2 ^ 20 -> 0 <= lo /\ lo <= hi /\ hi <= 256 -> (forall a, g <= a < g + 256 -> apresent (w_H W) mem a) ->
  region_ok SEGS (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) (YP09.mkRegion (Some 34%nat) lo hi lo hi []).
Proof.
intros W regs mem m g rs ro ms n lo hi Hg Hlh Hp.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (U : base_val (s16_E regs m g rs ro ms n) (Some 34%nat) = g) by (cbn [base_val]; rewrite X34; apply unsigned_lit_small; lia).
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hp; lia | apply Forall_nil].
Qed.
(* the two shadow entries: m->seg[i]'s 256 bytes and m's 9236 *)
Lemma s16_shok : forall (W : world SEGS) regs mem m g rs ro ms n,
  4096 <= m -> in_app m 9236 -> m <= g -> g + 256 <= m + 9236 ->
  range_addressable (rdW W mem) SHADOW_OFF m 9236 ->
  sh_ok SEGS s16_Bx s16_SH (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) /\
  sh_ok SEGS s16_Bx s16_SHE (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem).
Proof.
intros W regs mem m g rs ro ms n Hm Happ Hg1 Hg2 Hra.
destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (UB : U (s16_E regs m g rs ro ms n) s16_Bx = SHADOW_OFF) by (unfold s16_Bx; apply U_atom; [exact X32 | unfold SB, SHADOW_OFF; lia]).
assert (Hm64 : m + 9236 < 2 ^ 64) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; pose proof asan_consts as (C1 & _); lia).
assert (E33 : shent_ok SEGS s16_Bx (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) (mkSHE 33 0 9236)).
{ apply (shent_ok_of_range SEGS (w_H W) mem _ s16_Bx 33 m 9236 m 0 9236 Hra UB); [apply U_atom; [exact X33 | lia] | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof asan_consts as (C1 & _). lia. }
assert (E34 : shent_ok SEGS s16_Bx (s16_E regs m g rs ro ms n) (mrestrict (w_H W) mem) (mkSHE 34 0 256)).
{ apply (shent_ok_of_range SEGS (w_H W) mem _ s16_Bx 34 m 9236 g 0 256 Hra UB); [apply U_atom; [exact X34 | lia] | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof asan_consts as (C1 & _). lia. }
split.
- unfold sh_ok, s16_SH. apply Forall_cons; [exact E34|]. apply Forall_cons; [exact E33|]. apply Forall_nil.
- unfold sh_ok, s16_SHE. apply Forall_cons; [exact E33|]. apply Forall_nil.
Qed.

(* ---- the five seeds ---- *)
Ltac s16_pd U9 U33 U34 :=
  apply pairwise_disjoint_of_extents; unfold extent_of_region;
  cbn [map s16_slotsE s16_slotsR s16_seg s16_segW1 s16_segW2 s16_n YP09.r_base YP09.r_lo YP09.r_hi];
  rewrite ?U9, ?U33, ?U34; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
Lemma s16_base9 : forall regs m g rs ro ms n s1, getr regs 9 = w64 s1 -> 0 <= s1 < 2 ^ 64 ->
  base_val (s16_E regs m g rs ro ms n) (Some 9%nat) = s1.
Proof. intros. cbn [base_val]. rewrite (s16_E_reg regs m g rs ro ms n 9 9%bv eq_refl), H. apply unsigned_lit_small. lia. Qed.
Lemma s16_base33 : forall regs m g rs ro ms n, 0 <= m < 2 ^ 64 -> base_val (s16_E regs m g rs ro ms n) (Some 33%nat) = m.
Proof. intros. cbn [base_val]. rewrite (proj1 (proj2 (s16_E_x regs m g rs ro ms n))). apply unsigned_lit_small. lia. Qed.
Lemma s16_base34 : forall regs m g rs ro ms n, 0 <= g < 2 ^ 64 -> base_val (s16_E regs m g rs ro ms n) (Some 34%nat) = g.
Proof. intros. cbn [base_val]. rewrite (proj1 (proj2 (proj2 (s16_E_x regs m g rs ro ms n)))). apply unsigned_lit_small. lia. Qed.
(* the register values of the loop's maps *)
Lemma s16_lregs_ok : forall regs m i rs ro ms n, (i < 32)%nat -> 4096 <= m <= 2 ^ 47 - 2 ^ 20 ->
  s16_lregs regs m i -> getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  regs_ok (s16_E regs m (m + 256 * Z.of_nat i) rs ro ms n) s16_regsL regs.
Proof.
intros regs m i rs ro ms n Hi Hm (R13 & R14 & R20 & R24 & R25 & R26) R18.
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) rs ro ms n) as (X32 & X33 & X34 & _).
unfold s16_regsL.
apply regs_ok_rereg; [| reflexivity | rewrite R26, (s16_den_off _ 34 _ 0x20 X34) by lia; unfold w64; f_equal; lia].
apply regs_ok_rereg; [| reflexivity |].
2:{ rewrite R24, (s16_den_shx _ 34 _ 0x14 X34 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF.
    replace (m + 256 * Z.of_nat i + 0x14) with (m + 0x14 + 256 * Z.of_nat i) by lia. reflexivity. }
apply regs_ok_rereg; [| reflexivity | rewrite R20, (s16_den_off _ 34 _ 0x20 X34) by lia; unfold w64; f_equal; lia].
apply regs_ok_rereg; [| reflexivity |].
2:{ rewrite R18, (s16_den_shx _ 33 _ 0x2000 X33 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF, seg_spec.MC_N.
    reflexivity. }
apply regs_ok_rereg; [| reflexivity | rewrite R14, (s16_den_off _ 33 m 0 X33) by lia; unfold w64; f_equal; lia].
apply regs_ok_rereg; [| reflexivity | rewrite R13, (s16_den_off _ 32 SB 0 X32) by (unfold SB; lia); reflexivity].
apply regs_ok_Eimg_Ereg.
Qed.
(* the callee-saved part after a call, with s3 (KP1) or s5 (KP2) *)
Lemma s16_sregs_ok : forall regs m i rs ro ms n, (i < 32)%nat -> 4096 <= m <= 2 ^ 47 - 2 ^ 20 ->
  s16_sregs regs m i -> getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  regs_ok (s16_E regs m (m + 256 * Z.of_nat i) rs ro ms n)
    (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (shx 33 0x2000)) 20 (SOff 34 0x20)) 24 (shx 34 0x14)) 26 (SOff 34 0x20))
    regs.
Proof.
intros regs m i rs ro ms n Hi Hm (R20 & R24 & R25 & R26) R18.
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) rs ro ms n) as (X32 & X33 & X34 & _).
apply regs_ok_rereg; [| reflexivity | rewrite R26, (s16_den_off _ 34 _ 0x20 X34) by lia; unfold w64; f_equal; lia].
apply regs_ok_rereg; [| reflexivity |].
2:{ rewrite R24, (s16_den_shx _ 34 _ 0x14 X34 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF.
    replace (m + 256 * Z.of_nat i + 0x14) with (m + 0x14 + 256 * Z.of_nat i) by lia. reflexivity. }
apply regs_ok_rereg; [| reflexivity | rewrite R20, (s16_den_off _ 34 _ 0x20 X34) by lia; unfold w64; f_equal; lia].
apply regs_ok_rereg; [| reflexivity |].
2:{ rewrite R18, (s16_den_shx _ 33 _ 0x2000 X33 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF, seg_spec.MC_N.
    reflexivity. }
apply regs_ok_Eimg_Ereg.
Qed.
(* 0x85208 *)
Lemma s16_seed_e : forall (W : world SEGS) regs mem m n s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 320 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= m -> m mod 16 = 0 -> m + 9236 <= 2 ^ 47 - 2 ^ 23 -> m + 9236 <= s1 -> 0 <= n <= 32 ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  rdword (rdW W mem) (s1 + 64) = Some (shadow_addr (m + 0x14)) -> rdword (rdW W mem) (s1 + 72) = Some (m + 0x20) ->
  rdword (rdW W mem) (s1 + 168) = Some m -> rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 184) = Some (m + seg_spec.MC_N) ->
  (forall a, s1 <= a < s1 + 192 -> apresent (w_H W) mem a) ->
  rd32 (rdW W mem) (m + seg_spec.MC_N) n ->
  st_ok_pi SEGS VAL (s16_E regs m m 0 0 0 n) ss_ke
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85208)) mem (seg_rom SEGS))).
Proof.
intros W regs mem m n s1 R9 Hs1 Hs1' Hs1m Hm Hm16 Hm' Hms1 Hn R26 H64 H72 H168 H176 H184 Hpres Hn32.
destruct (s16_E_x regs m m 0 0 0 n) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s16_regsE. apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
  rewrite R26, (s16_den_srl3 _ 33 m 0x2000 X33) by lia. reflexivity.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + exact (s16_slotsE_ok W regs mem m m 0 0 0 n s1 R9 ltac:(lia) ltac:(lia) H64 H72 H168 H176 H184 Hpres).
  + exact (s16_n_ok W regs mem m m 0 0 0 n ltac:(lia) Hn Hn32).
- pose proof (s16_base9 regs m m 0 0 0 n s1 R9 ltac:(lia)) as U9.
  pose proof (s16_base33 regs m m 0 0 0 n ltac:(lia)) as U33.
  pose proof asan_consts as (C1 & _). unfold seg_spec.MC_N. s16_pd U9 U33 U33.
- exact (s16_factsE_ok regs m m 0 0 0 n s1 R9 ltac:(lia) Hs1m ltac:(lia) Hm16 ltac:(lia) Hm16 Hn).
Qed.
(* the shared hypotheses of the loop's seeds *)
Definition s16_seedP (W : world SEGS) regs mem m i n s1 : Prop :=
  getr regs 9 = w64 s1 /\ 2 ^ 46 <= s1 /\ s1 + 320 <= 2 ^ 47 /\ s1 mod 32 = 0 /\
  4096 <= m /\ m mod 16 = 0 /\ m + 9236 <= 2 ^ 47 - 2 ^ 23 /\ (i < 32)%nat /\ 0 <= n <= 32 /\
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) /\
  rdword (rdW W mem) (s1 + 168) = Some m /\ rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF /\
  rdword (rdW W mem) (s1 + 184) = Some (m + seg_spec.MC_N) /\ rd32 (rdW W mem) (m + seg_spec.MC_N) n /\
  m + 9236 <= s1.
(* 0x8523c *)
Lemma s16_seed_h : forall (W : world SEGS) regs mem m i rs ro ms n s1,
  s16_seedP W regs mem m i n s1 -> s16_lregs regs m i ->
  0 <= rs <= 1 -> 0 <= ro < 2 ^ 31 -> 0 <= ms <= 1 ->
  rd32 (rdW W mem) (m + 256 * Z.of_nat i + 0x10) ro -> rd32 (rdW W mem) (m + 256 * Z.of_nat i + 0x14) rs ->
  rd32 (rdW W mem) (m + 256 * Z.of_nat i + 0x20) ms ->
  st_ok_pi SEGS VAL (s16_E regs m (m + 256 * Z.of_nat i) rs ro ms n) ss_kh
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_KH16)) mem (seg_rom SEGS))).
Proof.
intros W regs mem m i rs ro ms n s1
  (R9 & Hs1 & Hs1' & Hs1m & Hm & Hm16 & Hm' & Hi & Hn & R18 & H168 & H176 & H184 & Hn32 & Hms1)
  HL Hrs Hro Hms Hr1 Hr2 Hr3.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact (s16_lregs_ok regs m i rs ro ms n Hi ltac:(lia) HL R18).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + exact (s16_slotsR_ok W regs mem m (m + 256 * Z.of_nat i) rs ro ms n s1 R9 ltac:(lia) ltac:(lia) H168 H176 H184).
  + exact (s16_seg_ok W regs mem m (m + 256 * Z.of_nat i) rs ro ms n ltac:(lia) Hrs Hro Hms Hr1 Hr2 Hr3).
  + exact (s16_n_ok W regs mem m (m + 256 * Z.of_nat i) rs ro ms n ltac:(lia) Hn Hn32).
- pose proof (s16_base9 regs m (m + 256 * Z.of_nat i) rs ro ms n s1 R9 ltac:(lia)) as U9.
  pose proof (s16_base33 regs m (m + 256 * Z.of_nat i) rs ro ms n ltac:(lia)) as U33.
  pose proof (s16_base34 regs m (m + 256 * Z.of_nat i) rs ro ms n ltac:(lia)) as U34.
  pose proof asan_consts as (C1 & _). unfold seg_spec.MC_N. s16_pd U9 U33 U34.
- exact (s16_factsH_ok regs m (m + 256 * Z.of_nat i) rs ro ms n s1 R9 ltac:(lia) Hs1m ltac:(lia) Hm16 ltac:(lia) ltac:(lia) Hn Hrs
    ltac:(lia) Hms).
Qed.
(* 0x852c0 / 0x852f0 / 0x85310 *)
Lemma s16_seed_p1 : forall (W : world SEGS) regs mem m i n s1,
  s16_seedP W regs mem m i n s1 -> s16_sregs regs m i -> getr regs 19 = w64 (m + 0x20 + 256 * Z.of_nat i) ->
  (forall a, m <= a < m + 9236 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 n) ss_kp1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_KP1)) mem (seg_rom SEGS))).
Proof.
intros W regs mem m i n s1
  (R9 & Hs1 & Hs1' & Hs1m & Hm & Hm16 & Hm' & Hi & Hn & R18 & H168 & H176 & H184 & Hn32 & Hms1)
  HL R19 Hp.
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) 0 0 0 n) as (X32 & X33 & X34 & _).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s16_regsP1.
  pose proof (s16_sregs_ok regs m i 0 0 0 n Hi ltac:(lia) HL R18) as RG.
  (* s3 is set innermost; move it out *)
  apply regs_ok_rereg; [| reflexivity | destruct HL as (_ & _ & _ & R26); rewrite R26, (s16_den_off _ 34 _ 0x20 X34) by lia;
    unfold w64; f_equal; lia].
  apply regs_ok_rereg; [| reflexivity |].
  2:{ destruct HL as (_ & R24 & _). rewrite R24, (s16_den_shx _ 34 _ 0x14 X34 X32) by lia.
      unfold w64, shadow_addr, SB, SHADOW_OFF.
      replace (m + 256 * Z.of_nat i + 0x14) with (m + 0x14 + 256 * Z.of_nat i) by lia. reflexivity. }
  apply regs_ok_rereg; [| reflexivity | destruct HL as (R20 & _); rewrite R20, (s16_den_off _ 34 _ 0x20 X34) by lia;
    unfold w64; f_equal; lia].
  apply regs_ok_rereg; [| reflexivity |].
  2:{ rewrite R18, (s16_den_shx _ 33 _ 0x2000 X33 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF, seg_spec.MC_N.
      reflexivity. }
  apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
  rewrite R19, (s16_den_off _ 34 _ 0x20 X34) by lia. unfold w64. f_equal. lia.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + exact (s16_slotsR_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia) ltac:(lia) H168 H176 H184).
  + apply (s16_segW_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n 0x20 0x24 ltac:(lia) ltac:(lia)). intros a Ha. apply Hp. lia.
  + exact (s16_n_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia) Hn Hn32).
- pose proof (s16_base9 regs m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia)) as U9.
  pose proof (s16_base33 regs m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia)) as U33.
  pose proof (s16_base34 regs m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia)) as U34.
  pose proof asan_consts as (C1 & _). unfold seg_spec.MC_N. s16_pd U9 U33 U34.
- exact (s16_factsE_ok regs m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia) Hs1m ltac:(lia) Hm16 ltac:(lia) ltac:(lia) Hn).
Qed.
Lemma s16_seed_p2 : forall (W : world SEGS) regs mem m i n s1,
  s16_seedP W regs mem m i n s1 -> s16_sregs regs m i ->
  getr regs 21 = w64 (shadow_addr (m + 0x10 + 256 * Z.of_nat i)) ->
  (forall a, m <= a < m + 9236 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 n) ss_kp2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_KP2)) mem (seg_rom SEGS))).
Proof.
intros W regs mem m i n s1
  (R9 & Hs1 & Hs1' & Hs1m & Hm & Hm16 & Hm' & Hi & Hn & R18 & H168 & H176 & H184 & Hn32 & Hms1)
  HL R21 Hp.
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) 0 0 0 n) as (X32 & X33 & X34 & _).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s16_regsP2.
  apply regs_ok_rereg; [| reflexivity | destruct HL as (_ & _ & _ & R26); rewrite R26, (s16_den_off _ 34 _ 0x20 X34) by lia;
    unfold w64; f_equal; lia].
  apply regs_ok_rereg; [| reflexivity |].
  2:{ destruct HL as (_ & R24 & _). rewrite R24, (s16_den_shx _ 34 _ 0x14 X34 X32) by lia.
      unfold w64, shadow_addr, SB, SHADOW_OFF.
      replace (m + 256 * Z.of_nat i + 0x14) with (m + 0x14 + 256 * Z.of_nat i) by lia. reflexivity. }
  apply regs_ok_rereg; [| reflexivity | destruct HL as (R20 & _); rewrite R20, (s16_den_off _ 34 _ 0x20 X34) by lia;
    unfold w64; f_equal; lia].
  apply regs_ok_rereg; [| reflexivity |].
  2:{ rewrite R18, (s16_den_shx _ 33 _ 0x2000 X33 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF, seg_spec.MC_N.
      reflexivity. }
  apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
  rewrite R21, (s16_den_shx _ 34 _ 0x10 X34 X32) by lia. unfold w64, shadow_addr, SB, SHADOW_OFF.
  replace (m + 256 * Z.of_nat i + 0x10) with (m + 0x10 + 256 * Z.of_nat i) by lia. reflexivity.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + exact (s16_slotsR_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia) ltac:(lia) H168 H176 H184).
  + apply (s16_segW_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n 0x10 0x18 ltac:(lia) ltac:(lia)). intros a Ha. apply Hp. lia.
  + exact (s16_n_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia) Hn Hn32).
- pose proof (s16_base9 regs m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia)) as U9.
  pose proof (s16_base33 regs m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia)) as U33.
  pose proof (s16_base34 regs m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia)) as U34.
  pose proof asan_consts as (C1 & _). unfold seg_spec.MC_N. s16_pd U9 U33 U34.
- exact (s16_factsE_ok regs m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia) Hs1m ltac:(lia) Hm16 ltac:(lia) ltac:(lia) Hn).
Qed.
Lemma s16_seed_l : forall (W : world SEGS) regs mem m i n s1,
  s16_seedP W regs mem m i n s1 -> s16_lregs regs m i ->
  st_ok_pi SEGS VAL (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 n) ss_kl
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_KL16)) mem (seg_rom SEGS))).
Proof.
intros W regs mem m i n s1
  (R9 & Hs1 & Hs1' & Hs1m & Hm & Hm16 & Hm' & Hi & Hn & R18 & H168 & H176 & H184 & Hn32 & Hms1) HL.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact (s16_lregs_ok regs m i 0 0 0 n Hi ltac:(lia) HL R18).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + exact (s16_slotsR_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia) ltac:(lia) H168 H176 H184).
  + exact (s16_n_ok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia) Hn Hn32).
- pose proof (s16_base9 regs m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia)) as U9.
  pose proof (s16_base33 regs m (m + 256 * Z.of_nat i) 0 0 0 n ltac:(lia)) as U33.
  pose proof asan_consts as (C1 & _). unfold seg_spec.MC_N. s16_pd U9 U33 U33.
- exact (s16_factsE_ok regs m (m + 256 * Z.of_nat i) 0 0 0 n s1 R9 ltac:(lia) Hs1m ltac:(lia) Hm16 ltac:(lia) ltac:(lia) Hn).
Qed.
(* the loop's seed facts at a point of s16_inv *)
Lemma s16_seedP_inv : forall cx f ly S (W : world SEGS) regs mem md k acc c m t mc i,
  lt_base B MT cx -> s16_inv B MT cx f ly S W regs mem md k acc c m t mc -> (i < 32)%nat ->
  s16_seedP W regs mem m i (Z.of_nat (length (SegModel.mc_seg mc))) (x_s1 cx) /\
  (forall a, m <= a < m + 9236 -> apresent (w_H W) mem a) /\
  range_addressable (rdW W mem) SHADOW_OFF m 9236 /\ in_app m 9236 /\ AR SEGS B ly S W mem md.
Proof.
intros cx f ly S W regs mem md k acc c m t mc i HB HI Hi.
pose proof HI as (Hnf & HC & Hc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
destruct (s16_basic cx ly S W regs mem md k acc _ _ _ c m _ HB HC Hm HSL)
  as (HAR & R2 & R9 & Hs1 & Hs1' & Hs1m & Hm4 & Hm16 & Hm' & Happ & Hms1 & H168 & H176 & H184 & H64 & H72 & Hps & Hpm & Hra).
pose proof (s16_mconf_len _ _ _ HMC) as HL32.
split; [|split; [exact Hpm | split; [exact Hra | split; [exact Happ | exact HAR]]]].
refine (conj R9 (conj Hs1 (conj Hs1' (conj Hs1m (conj Hm4 (conj Hm16 (conj Hm' (conj Hi (conj _ (conj R18 (conj H168
  (conj H176 (conj H184 (conj (s16_rd_n _ _ _ HMC) Hms1)))))))))))))).
lia.
Qed.
End seeds.

(* ===================================== run helpers ===================================== *)
Section den2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
Lemma s16_den_reg : forall regs m g rs ro ms n (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r ->
  sv_denot (s16_E regs m g rs ro ms n) (SOff k 0) = getr regs r.
Proof.
intros regs m g rs ro ms n k r Hk. cbn [sv_denot]. rewrite (s16_E_reg regs m g rs ro ms n k r Hk), Z.add_0_r.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma s16_den_addl : forall (E : env) e a c, sv_denot E e = Z_to_bv 64 a -> 0 <= a -> 0 <= c -> a + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD e (SLit c)) = Z_to_bv 64 (a + c).
Proof.
intros E e a c He Ha Hc Hac. cbn [sv_denot]. rewrite He.
rewrite zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id a) by (unfold M64; lia). rewrite (zcanon_id c) by (unfold M64; lia). reflexivity.
Qed.
Lemma s16_blt : forall (E : env) a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb, YO0c.branch_lt, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
Lemma s16_bge : forall (E : env) a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb, YO0c.branch_ge, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
Lemma s16_beq : forall (E : env) a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (x =? y).
Proof. intros E a b x y Ha Hb Hx Hy. rewrite branch_eq_U. unfold U. rewrite Ha, Hb, !unsigned_lit_small by lia. reflexivity. Qed.
Lemma s16_bne : forall (E : env) a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (x =? y).
Proof. intros E a b x y Ha Hb Hx Hy. rewrite branch_ne_U. unfold U. rewrite Ha, Hb, !unsigned_lit_small by lia. reflexivity. Qed.
Lemma s16_den_lit : forall (E : env) c, sv_denot E (SLit c) = Z_to_bv 64 c.
Proof. reflexivity. Qed.
(* s2 = SH(m + 0x2000), and s8 after the latch's += 32 *)
Lemma s16_den_s2 : forall regs m g rs ro ms n, 0 <= m < 2 ^ 47 ->
  sv_denot (s16_E regs m g rs ro ms n) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 8192) (SLit 3)) (SOff 32 0)) =
  w64 (shadow_addr (m + seg_spec.MC_N)).
Proof.
intros regs m g rs ro ms n Hm. destruct (s16_E_x regs m g rs ro ms n) as (X32 & X33 & _).
etransitivity; [exact (s16_den_shx _ 33 m 0x2000 X33 X32 ltac:(lia) ltac:(lia))|].
unfold w64, shadow_addr, SB, SHADOW_OFF, seg_spec.MC_N. reflexivity.
Qed.
Lemma s16_den_s8 : forall regs m i rs ro ms n, 0 <= m -> m + 256 * Z.of_nat i < 2 ^ 47 - 2 ^ 10 ->
  sv_denot (s16_E regs m (m + 256 * Z.of_nat i) rs ro ms n)
    (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 20) (SLit 3)) (SOff 32 0)) (SLit 32)) =
  w64 (shadow_addr (m + 0x14 + 256 * (Z.of_nat i + 1))).
Proof.
intros regs m i rs ro ms n Hm Hg. destruct (s16_E_x regs m (m + 256 * Z.of_nat i) rs ro ms n) as (X32 & X33 & X34 & _).
assert (Q : 0 <= (m + 256 * Z.of_nat i + 20) / 8 <= m + 256 * Z.of_nat i + 20)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
etransitivity.
{ exact (s16_den_addl _ _ (SB + (m + 256 * Z.of_nat i + 20) / 8) 32
    (s16_den_shx _ 34 _ 20 X34 X32 ltac:(lia) ltac:(lia)) ltac:(unfold SB; lia) ltac:(lia) ltac:(unfold SB; lia)). }
unfold w64, shadow_addr, SB, SHADOW_OFF.
replace (m + 0x14 + 256 * (Z.of_nat i + 1)) with ((m + 256 * Z.of_nat i + 20) + 32 * 8) by lia.
rewrite Z.div_add by lia. f_equal. lia.
Qed.
(* a 4-byte chunk holding the literal 0 reads 0 at each of its bytes *)
Lemma s16_rd_z4 : forall (W : world (@pa_segs _ seg_listing PI)) mem E base off,
  YP09.chunk_ok (@pa_segs _ seg_listing PI) E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 (SLit 0))) ->
  forall j, 0 <= j < 4 -> aview (@pa_segs _ seg_listing PI) (w_H W) mem (base + off + j) = Some 0.
Proof.
intros W mem E base off Hc j Hj. destruct (Hc j ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. unfold byte_of_word.
change (bv_unsigned (sv_denot E (SLit 0))) with 0. rewrite Z.shiftr_0_l. reflexivity.
Qed.
(* s3 = (s9 << 8) + m + 32 at 0x85288 .. 0x85290 *)
Lemma s16_den_s3 : forall regs m i rs ro ms n, getr regs 25 = w64 (Z.of_nat i) -> (i < 32)%nat -> 0 <= m < 2 ^ 47 ->
  sv_denot (s16_E regs m (m + 256 * Z.of_nat i) rs ro ms n)
    (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 25 0) (SLit 8)) (SLit 32)) (SOff 33 0)) =
  w64 (m + 0x20 + 256 * Z.of_nat i).
Proof.
intros regs m i rs ro ms n R25 Hi Hm. destruct (s16_E_x regs m (m + 256 * Z.of_nat i) rs ro ms n) as (X32 & X33 & _).
cbn [sv_denot]. rewrite (s16_E_reg regs m _ rs ro ms n 25 25%bv eq_refl), R25, X33. unfold w64.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
repeat match goal with
  | |- context [zcanon ?x] =>
      lazymatch x with context [zcanon _] => fail | _ => rewrite (zcanon_id x) by (unfold M64; lia) end
  | |- context [Z.land 8 63] => change (Z.land 8 63) with 8
  | |- context [Z.shiftl (Z.of_nat i) 8] => rewrite (Z.shiftl_mul_pow2 (Z.of_nat i) 8) by lia
  end.
f_equal. lia.
Qed.
(* the three cases of m_cross_seg by the fields the loop's branches test *)
Lemma s16_cross_paths : forall c i,
  (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) = 0 ->
   seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) = 0 ->
   SegModel.m_cross_seg c i = c) /\
  (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) = 0 ->
   seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   SegModel.m_cross_seg c i = SegModel.m_upd (SegModel.m_refuse c 0 false) i SegModel.ms_drop_model) /\
  (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) = 0 ->
   SegModel.ms_role (nth i (SegModel.mc_seg c) SegModel.mseg_d) <> 4 -> SegModel.m_cross_seg c i = c) /\
  (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) = 0 ->
   SegModel.ms_role (nth i (SegModel.mc_seg c) SegModel.mseg_d) = 4 ->
   SegModel.m_cross_seg c i = SegModel.m_upd (SegModel.m_refuse c 0 false) i SegModel.ms_drop_role) /\
  (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   SegModel.ms_role (nth i (SegModel.mc_seg c) SegModel.mseg_d) = 4 -> SegModel.m_cross_seg c i = c) /\
  (seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg c) SegModel.mseg_d)) <> 0 ->
   SegModel.ms_role (nth i (SegModel.mc_seg c) SegModel.mseg_d) <> 4 ->
   SegModel.m_cross_seg c i = SegModel.m_upd (SegModel.m_refuse c 0 false) i SegModel.ms_drop_model).
Proof.
intros c i. unfold SegModel.m_cross_seg. cbv zeta.
remember (nth i (SegModel.mc_seg c) SegModel.mseg_d) as g eqn:Eg. clear Eg.
destruct (SegModel.ms_role_set g), (SegModel.ms_model_set g), (Z.eqb_spec (SegModel.ms_role g) 4);
  cbn [seg_spec.b2z andb negb]; repeat split; intros; first [reflexivity | lia].
Qed.
(* a word of a chunk of the final symbolic state, read through the reader (_s13's s13_chunk_word for st_ok_pi) *)
Lemma s16_chunk_word : forall (W : world (@pa_segs _ seg_listing PI)) E ss ms i rg p off e a v,
  st_ok_pi (@pa_segs _ seg_listing PI) (@pa_val _ seg_listing PI) E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview (@pa_segs _ seg_listing PI) (w_H W) (ms_mem ms)) (a + off) = Some v.
Proof.
intros W E ss ms i rg p off e a v HS Hi Hb Hc Ha He Hv.
pose proof HS as HSo. unfold st_ok_pi in HSo.
pose proof (YI67.st_chunk_val _ E _ (restrict (w_H W) ms) i rg p off 8 e a v HSo ltac:(destruct ss; exact Hi) Hb Hc Ha He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as HV.
cbn [ms_mem restrict] in HV.
exact (PaLibF.rdword_of_val_mem _ (w_H W) (ms_mem ms) (a + off) v HV Hv).
Qed.
End den2.

(* the register r of a state, as the denotation of its symbolic value *)
Ltac s16_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* awr_ok of a seed whose regions are all read-only *)
Ltac s16_awr_ro :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* a run that writes nothing: every byte kept *)
Ltac s16_keep0 sg HFr K :=
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq0 | Hin']; [injection Hq0 as <- <- <-; lia |]); destruct Hin')) as K.
(* a run whose only write window is [lo, hi) of the region based at atom 34 (U34 : bv_unsigned (ew E 34) = g) *)
Ltac s16_keepW sg HFr U34 g lo hi K :=
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun a => g + lo <= a < g + hi) HFr
    ltac:(intros b wlo whi a' Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq0 | Hin'];
                  [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?U34 in Hrr; cbv beta; lia |]);
          destruct Hin')) as K.

(* a register the run did not change: Q : getr regs r = sv_denot E e (at the seed) gives the same value now *)
Ltac s16_eq HS Q Er :=
  let P := fresh "P" in
  lazymatch type of Q with getr _ ?r = _ => s16_rg HS r P; pose proof (eq_trans P (eq_sym Q)) as Er; clear P end.
(* a further run that writes nothing, composed with KK (the bytes kept since the seed) *)
Ltac s16_kk sg HFr KK :=
  let K := fresh "K" in s16_keep0 sg HFr K;
  let KK' := fresh "KK" in pose proof (fun a Ha Hn => eq_trans (K a Ha Hn) (KK a Ha Hn)) as KK'; clear K KK;
  rename KK' into KK.

(* ===================================== the segment ===================================== *)
Section w. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's hypotheses: m_refuse's contract at every FP state, the meter across a set_fs state change, the call
   targets of the program functions *)
Hypothesis MREF : forall fx0 : YK11.FPState,
  @m_refuse_contract fx0 rc SK SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Section x. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* K853bc from a point of s16_inv after all N passes: m holds m_cross of m_file's model *)
Lemma s16_to_853bc : forall f cx ly S (W : world SEGS) regs mem md k acc c m t,
  LT_K853bc_stmt B MT f -> lt_base B MT cx -> sa_frm0 ->
  s16_inv B MT cx f ly S W regs mem md k acc c m t (s16_Mic cx f (length (SegModel.mc_seg (s16_M1c cx f)))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K853bc) regs mem md) (lt_post B MT cx).
Proof.
intros f cx ly S W regs mem md k acc c m t HX HB HFRM
  (Hnf & HC & Hc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
unfold s16_Mic in HMC. pose proof (s16_mconf_len _ _ _ HMC) as HL. rewrite s16_Mi_len in HL.
rewrite s16_Mi_all in HMC.
exact (HX cx ly S W regs mem md k acc c m t HB HFRM Hnf HC Hc Hm Ht R18 R23 R27 HSL HRC HMC HSTR
  (s16_cnt_exit (x_pl cx) f _ HL HCNT)).
Qed.

(* 0x85310 (KL i) .. 0x85330: check 17 of m->n, a0 = m->n, s9 = i + 1, s10 / s4 += 256, s8 += 32, blt s9, a0: to the
   head of pass i + 1 (0x8523c) or out to K853bc (j 0x853bc) *)
Lemma s16_latch : forall f i, LT16_KH_stmt B MT f (Datatypes.S i) -> LT_K853bc_stmt B MT f -> LT16_KL_stmt B MT f i.
Proof.
intros f i HKH HX. unfold LT16_KL_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM Hi HI HL.
pose proof (s16_Mi_len (s16_M1c cx f) (Datatypes.S i)) as HLEN.
change (s16_Mi (s16_M1c cx f) (Datatypes.S i)) with (s16_Mic cx f (Datatypes.S i)) in HLEN.
pose proof HI as (Hnf & HC & Hbc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
pose proof (s16_mconf_len _ _ _ HMC) as HN32. rewrite HLEN in HN32.
destruct (s16_seedP_inv B MT cx f ly S W regs mem md k acc c m t _ i HB HI ltac:(lia)) as (HSP & Hpm & Hra & Happ & HAR).
rewrite HLEN in HSP.
set (N := length (SegModel.mc_seg (s16_M1c cx f))) in *.
pose proof HSP as (R9 & Hs1 & Hs1' & Hs1m & Hm4 & Hm16 & Hm' & _ & _ & _ & _ & _ & _ & _ & Hms1).
pose proof (s16_seed_l W regs mem m i (Z.of_nat N) (x_s1 cx) HSP HL) as HS.
destruct (s16_shok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N) ltac:(lia) Happ ltac:(lia) ltac:(lia) Hra)
  as (SHOK & _).
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
pose proof HL as (R13 & R14 & R20 & R24 & R25 & R26).
assert (X25 : ew (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) 25 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite (s16_E_reg regs m _ 0 0 0 _ 25 25%bv eq_refl); exact R25).
set (E := s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s16_E; apply Eimg_env).
pose proof HC as ((HJ & _) & _ & _ & (_ & _ & _ & HMO & _)).
unfold cfg_at. change (w64 (BASE + LO_KL16)) with (Z_to_bv 64 (BASE + LO_KL16)).
(* 0x85310 .. 0x85330, to the blt *)
paj_run_tok RUN HS HJ SHOK s16_span.
{ s16_awr_ro. }
s16_keep0 (@pa_segs _ seg_listing PI) HFr K1. clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s16_span.
- (* taken: i + 1 < m->n, the head of pass i + 1 *)
  rewrite (s16_blt E _ _ (Z.of_nat i + 1) (Z.of_nat N + 0) (s16_den_off E 25 (Z.of_nat i) 1 X25 ltac:(lia))
    (s16_den_off E 38 (Z.of_nat N) 0 X38 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KH16.
  { s16_awr_ro. }
  s16_keep0 (@pa_segs _ seg_listing PI) HFr K2. clear HF HFr HG.
  s16_rg HS (2%bv : bv 5) P2. s16_rg HS (3%bv : bv 5) P3. s16_rg HS (4%bv : bv 5) P4. s16_rg HS (8%bv : bv 5) P8. s16_rg HS (9%bv : bv 5) P9.
  s16_rg HS (13%bv : bv 5) P13. s16_rg HS (14%bv : bv 5) P14. s16_rg HS (18%bv : bv 5) P18. s16_rg HS (20%bv : bv 5) P20. s16_rg HS (23%bv : bv 5) P23.
  s16_rg HS (24%bv : bv 5) P24. s16_rg HS (25%bv : bv 5) P25. s16_rg HS (26%bv : bv 5) P26. s16_rg HS (27%bv : bv 5) P27.
  pmkst HS.
  apply (HKH cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t HB HFRM ltac:(lia)).
  + apply (s16_inv_carry B MT LAWS cx f ly S W regs mem md k acc c m t _ ly S W (ms_regs ms) (ms_mem ms) _ _ HB HI HJ);
      first [ rewrite P2; exact (s16_den_reg regs m _ 0 0 0 _ 2 2%bv eq_refl)
            | rewrite P3; exact (s16_den_reg regs m _ 0 0 0 _ 3 3%bv eq_refl)
            | rewrite P4; exact (s16_den_reg regs m _ 0 0 0 _ 4 4%bv eq_refl)
            | rewrite P8; exact (s16_den_reg regs m _ 0 0 0 _ 8 8%bv eq_refl)
            | rewrite P9; exact (s16_den_reg regs m _ 0 0 0 _ 9 9%bv eq_refl)
            | rewrite P23; exact (s16_den_reg regs m _ 0 0 0 _ 23 23%bv eq_refl)
            | rewrite P27; exact (s16_den_reg regs m _ 0 0 0 _ 27 27%bv eq_refl)
            | idtac ].
    * rewrite P18, R18. apply s16_den_s2. lia.
    * apply Permutation_refl.
    * exact HMO.
    * intros a Ha _ _. rewrite (K2 a Ha ltac:(tauto)). exact (K1 a Ha ltac:(tauto)).
    * apply (s16_mconf_ext (rdW W mem)); [exact HMC|].
      intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha. rewrite (K2 a ltac:(lia) ltac:(tauto)). exact (K1 a ltac:(lia) ltac:(tauto)).
  + unfold s16_lregs. rewrite Nat2Z.inj_succ. split; [|split; [|split; [|split; [|split]]]].
    * rewrite P13, (s16_den_off E 32 SB 0 X32) by (unfold SB; lia). unfold w64, SB, SHADOW_OFF. reflexivity.
    * rewrite P14, (s16_den_off E 33 m 0 X33) by lia. unfold w64. f_equal. lia.
    * rewrite P20, (s16_den_off E 34 _ 288 X34) by lia. unfold w64. f_equal. lia.
    * rewrite P24. apply s16_den_s8; lia.
    * rewrite P25, (s16_den_off E 25 (Z.of_nat i) 1 X25) by lia. reflexivity.
    * rewrite P26, (s16_den_off E 34 _ 288 X34) by lia. unfold w64. f_equal. lia.
- (* not taken: i + 1 = m->n, out of the loop *)
  rewrite (s16_blt E _ _ (Z.of_nat i + 1) (Z.of_nat N + 0) (s16_den_off E 25 (Z.of_nat i) 1 X25 ltac:(lia))
    (s16_den_off E 38 (Z.of_nat N) 0 X38 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc.
  assert (HSN : Datatypes.S i = N) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_K853bc.
  { s16_awr_ro. }
  s16_keep0 (@pa_segs _ seg_listing PI) HFr K2. clear HF HFr HG.
  s16_rg HS (2%bv : bv 5) P2. s16_rg HS (3%bv : bv 5) P3. s16_rg HS (4%bv : bv 5) P4. s16_rg HS (8%bv : bv 5) P8. s16_rg HS (9%bv : bv 5) P9.
  s16_rg HS (18%bv : bv 5) P18. s16_rg HS (23%bv : bv 5) P23. s16_rg HS (27%bv : bv 5) P27.
  pmkst HS.
  apply (s16_to_853bc f cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t HX HB HFRM).
  fold N. rewrite <- HSN.
  apply (s16_inv_carry B MT LAWS cx f ly S W regs mem md k acc c m t _ ly S W (ms_regs ms) (ms_mem ms) _ _ HB HI HJ);
    first [ rewrite P2; exact (s16_den_reg regs m _ 0 0 0 _ 2 2%bv eq_refl)
          | rewrite P3; exact (s16_den_reg regs m _ 0 0 0 _ 3 3%bv eq_refl)
          | rewrite P4; exact (s16_den_reg regs m _ 0 0 0 _ 4 4%bv eq_refl)
          | rewrite P8; exact (s16_den_reg regs m _ 0 0 0 _ 8 8%bv eq_refl)
          | rewrite P9; exact (s16_den_reg regs m _ 0 0 0 _ 9 9%bv eq_refl)
          | rewrite P23; exact (s16_den_reg regs m _ 0 0 0 _ 23 23%bv eq_refl)
          | rewrite P27; exact (s16_den_reg regs m _ 0 0 0 _ 27 27%bv eq_refl)
          | idtac ].
  + rewrite P18, R18. apply s16_den_s2. lia.
  + apply Permutation_refl.
  + exact HMO.
  + intros a Ha _ _. rewrite (K2 a Ha ltac:(tauto)). exact (K1 a Ha ltac:(tauto)).
  + apply (s16_mconf_ext (rdW W mem)); [exact HMC|].
    intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha. rewrite (K2 a ltac:(lia) ltac:(tauto)). exact (K1 a ltac:(lia) ltac:(tauto)).
Qed.

(* what KP1 / KP2 share: the cut's facts, the seed facts, the m block not one of the entry's *)
Lemma s16_kp_facts : forall cx f ly S (W : world SEGS) regs mem md k acc c m t i,
  lt_base B MT cx -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  s16_inv B MT cx f ly S W regs mem md k acc c m t (SegModel.m_refuse (s16_Mic cx f i) 0 false) ->
  s16_seedP W regs mem m i (Z.of_nat (length (SegModel.mc_seg (s16_M1c cx f)))) (x_s1 cx) /\
  (forall a, m <= a < m + 9236 -> apresent (w_H W) mem a) /\
  range_addressable (rdW W mem) SHADOW_OFF m 9236 /\ in_app m 9236 /\
  In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) /\ ~ In (m, seg_spec.SEG_M_SIZE) (x_bl0 B cx) /\
  (length (SegModel.mc_seg (s16_M1c cx f)) <= 32)%nat /\
  length (SegModel.mc_seg (SegModel.m_refuse (s16_Mic cx f i) 0 false)) = length (SegModel.mc_seg (s16_M1c cx f)).
Proof.
intros cx f ly S W regs mem md k acc c m t i HB Hi HI.
assert (HLEN : length (SegModel.mc_seg (SegModel.m_refuse (s16_Mic cx f i) 0 false)) =
  length (SegModel.mc_seg (s16_M1c cx f))) by exact (s16_Mi_len (s16_M1c cx f) i).
pose proof HI as (Hnf & HC & Hbc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
pose proof (s16_mconf_len _ _ _ HMC) as HN32. rewrite HLEN in HN32.
destruct (s16_seedP_inv B MT cx f ly S W regs mem md k acc c m t _ i HB HI ltac:(lia)) as (HSP & Hpm & Hra & Happ & HAR).
rewrite HLEN in HSP.
pose proof HC as (_ & _ & HBL & _).
assert (Htn1 : 0 < x_tn cx f) by (unfold x_tn, seg_spec.seg_txt_n; lia).
destruct (s16_blocks_apart B LAWS cx ly S W mem md t (x_tn cx f) m c HAR HBL Htn1) as (_ & _ & _ & HmN).
pose proof Hm as (HmIn & _).
exact (conj HSP (conj Hpm (conj Hra (conj Happ (conj HmIn (conj HmN (conj HN32 HLEN))))))).
Qed.

(* 0x852c0 (KP1 i) .. 0x8530c: a3 reloaded, check 14 on &m->seg[i].model_set, sw zero (model_set = 0), a4 reloaded:
   the latch of pass i *)
Lemma s16_kp1 : forall f i, LT16_KL_stmt B MT f i -> LT16_KP1_stmt B MT f i.
Proof.
intros f i HKL. unfold LT16_KP1_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM Hi HCS HI HSR R19.
destruct (s16_kp_facts cx f ly S W regs mem md k acc c m t i HB Hi HI)
  as (HSP & Hpm & Hra & Happ & HmIn & HmN & HN32 & HLEN).
set (N := length (SegModel.mc_seg (s16_M1c cx f))) in *.
pose proof HI as (Hnf & HC & Hbc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
pose proof HSP as (R9 & Hs1 & Hs1' & Hs1m & Hm4 & Hm16 & Hm' & _ & _ & _ & _ & _ & _ & _ & Hms1).
pose proof (s16_seed_p1 W regs mem m i (Z.of_nat N) (x_s1 cx) HSP HSR R19 Hpm) as HS.
destruct (s16_shok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N) ltac:(lia) Happ ltac:(lia) ltac:(lia) Hra)
  as (SHOK & _).
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
pose proof HSR as (R20 & R24 & R25 & R26).
assert (X25 : ew (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) 25 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite (s16_E_reg regs m _ 0 0 0 _ 25 25%bv eq_refl); exact R25).
assert (U34 : bv_unsigned (ew (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) 34) = m + 256 * Z.of_nat i)
  by (rewrite X34; apply unsigned_lit_small; lia).
set (E := s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s16_E; apply Eimg_env).
pose proof HC as ((HJ & _) & _ & _ & (_ & _ & _ & HMO & _)).
unfold cfg_at. change (w64 (BASE + LO_KP1)) with (Z_to_bv 64 (BASE + LO_KP1)).
paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KL16.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (b := m + 256 * Z.of_nat i); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left. exists m, seg_spec.SEG_M_SIZE.
    split; [exact HmIn|]. split; [exact HmN|]. change (req_size seg_spec.SEG_M_SIZE) with 9236. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
s16_keepW (@pa_segs _ seg_listing PI) HFr U34 (m + 256 * Z.of_nat i) 0x20 0x24 K1. clear HF HFr HG.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite U34 in RGc.
pose proof (s16_rd_z4 W (ms_mem ms) E _ 32 (proj1 (Forall_forall _ _) RGc _ (or_introl eq_refl))) as Z1.
s16_rg HS (2%bv : bv 5) P2. s16_rg HS (3%bv : bv 5) P3. s16_rg HS (4%bv : bv 5) P4. s16_rg HS (8%bv : bv 5) P8.
s16_rg HS (9%bv : bv 5) P9. s16_rg HS (13%bv : bv 5) P13. s16_rg HS (14%bv : bv 5) P14. s16_rg HS (18%bv : bv 5) P18.
s16_rg HS (20%bv : bv 5) P20. s16_rg HS (23%bv : bv 5) P23. s16_rg HS (24%bv : bv 5) P24.
s16_rg HS (25%bv : bv 5) P25. s16_rg HS (26%bv : bv 5) P26. s16_rg HS (27%bv : bv 5) P27.
pmkst HS.
apply (HKL cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t HB HFRM Hi).
- unfold s16_Mic. rewrite s16_step. change (s16_Mi (s16_M1c cx f) i) with (s16_Mic cx f i). rewrite HCS.
  apply (s16_inv_carry B MT LAWS cx f ly S W regs mem md k acc c m t _ ly S W (ms_regs ms) (ms_mem ms) _ _ HB HI HJ);
    first [ rewrite P2; exact (s16_den_reg regs m _ 0 0 0 _ 2 2%bv eq_refl)
          | rewrite P3; exact (s16_den_reg regs m _ 0 0 0 _ 3 3%bv eq_refl)
          | rewrite P4; exact (s16_den_reg regs m _ 0 0 0 _ 4 4%bv eq_refl)
          | rewrite P8; exact (s16_den_reg regs m _ 0 0 0 _ 8 8%bv eq_refl)
          | rewrite P9; exact (s16_den_reg regs m _ 0 0 0 _ 9 9%bv eq_refl)
          | rewrite P23; exact (s16_den_reg regs m _ 0 0 0 _ 23 23%bv eq_refl)
          | rewrite P27; exact (s16_den_reg regs m _ 0 0 0 _ 27 27%bv eq_refl)
          | idtac ].
  + rewrite P18, R18. apply s16_den_s2. lia.
  + apply Permutation_refl.
  + exact HMO.
  + intros a Ha Hn _. apply K1; [exact Ha|]. unfold seg_spec.SEG_M_SIZE in Hn. lia.
  + apply (s16_mconf_drop_model (rdW W mem) _ m _ i HMC ltac:(lia) ltac:(lia) ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
    * intros a Ha Hn. apply K1; [exact Ha | lia].
    * intros j Hj. replace (m + 256 * Z.of_nat i + 0x20 + j) with (m + 256 * Z.of_nat i + 32 + j) by lia.
      exact (Z1 j Hj).
- split; [|split; [|split; [|split; [|split]]]].
  + rewrite P13, (s16_den_off E 32 SB 0 X32) by (unfold SB; lia). unfold w64, SB, SHADOW_OFF. reflexivity.
  + rewrite P14, (s16_den_off E 33 m 0 X33) by lia. unfold w64. f_equal. lia.
  + rewrite P20, (s16_den_off E 34 _ 32 X34) by lia. unfold w64. f_equal. lia.
  + rewrite P24. etransitivity; [exact (s16_den_shx E 34 _ 20 X34 X32 ltac:(lia) ltac:(lia))|].
    unfold w64, shadow_addr, SB, SHADOW_OFF. f_equal. f_equal. f_equal. lia.
  + rewrite P25. etransitivity; [exact (s16_den_reg regs m _ 0 0 0 _ 25 25%bv eq_refl)|]. exact R25.
  + rewrite P26, (s16_den_off E 34 _ 32 X34) by lia. unfold w64. f_equal. lia.
Qed.

(* 0x852f0 (KP2 i) .. 0x8530c: check 15, sw zero,-12(s4) (role_set = 0), check 16, sw zero,-16(s4) (role = 0), a3 and
   a4 reloaded: the latch of pass i *)
Lemma s16_kp2 : forall f i, LT16_KL_stmt B MT f i -> LT16_KP2_stmt B MT f i.
Proof.
intros f i HKL. unfold LT16_KP2_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM Hi HCS HI HSR R21.
destruct (s16_kp_facts cx f ly S W regs mem md k acc c m t i HB Hi HI)
  as (HSP & Hpm & Hra & Happ & HmIn & HmN & HN32 & HLEN).
set (N := length (SegModel.mc_seg (s16_M1c cx f))) in *.
pose proof HI as (Hnf & HC & Hbc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
pose proof HSP as (R9 & Hs1 & Hs1' & Hs1m & Hm4 & Hm16 & Hm' & _ & _ & _ & _ & _ & _ & _ & Hms1).
pose proof (s16_seed_p2 W regs mem m i (Z.of_nat N) (x_s1 cx) HSP HSR R21 Hpm) as HS.
destruct (s16_shok W regs mem m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N) ltac:(lia) Happ ltac:(lia) ltac:(lia) Hra)
  as (SHOK & _).
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
pose proof HSR as (R20 & R24 & R25 & R26).
assert (U34 : bv_unsigned (ew (s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) 34) = m + 256 * Z.of_nat i)
  by (rewrite X34; apply unsigned_lit_small; lia).
set (E := s16_E regs m (m + 256 * Z.of_nat i) 0 0 0 (Z.of_nat N)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s16_E; apply Eimg_env).
pose proof HC as ((HJ & _) & _ & _ & (_ & _ & _ & HMO & _)).
unfold cfg_at. change (w64 (BASE + LO_KP2)) with (Z_to_bv 64 (BASE + LO_KP2)).
paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KL16.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (b := m + 256 * Z.of_nat i); [reflexivity | exact U34 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left. exists m, seg_spec.SEG_M_SIZE.
    split; [exact HmIn|]. split; [exact HmN|]. change (req_size seg_spec.SEG_M_SIZE) with 9236. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
s16_keepW (@pa_segs _ seg_listing PI) HFr U34 (m + 256 * Z.of_nat i) 0x10 0x18 K1. clear HF HFr HG.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite U34 in RGc.
pose proof (s16_rd_z4 W (ms_mem ms) E _ 16 (proj1 (Forall_forall _ _) RGc _ (or_introl eq_refl))) as Z1.
pose proof (s16_rd_z4 W (ms_mem ms) E _ 20 (proj1 (Forall_forall _ _) RGc _ (or_intror (or_introl eq_refl)))) as Z2.
s16_rg HS (2%bv : bv 5) P2. s16_rg HS (3%bv : bv 5) P3. s16_rg HS (4%bv : bv 5) P4. s16_rg HS (8%bv : bv 5) P8.
s16_rg HS (9%bv : bv 5) P9. s16_rg HS (13%bv : bv 5) P13. s16_rg HS (14%bv : bv 5) P14. s16_rg HS (18%bv : bv 5) P18.
s16_rg HS (20%bv : bv 5) P20. s16_rg HS (23%bv : bv 5) P23. s16_rg HS (24%bv : bv 5) P24.
s16_rg HS (25%bv : bv 5) P25. s16_rg HS (26%bv : bv 5) P26. s16_rg HS (27%bv : bv 5) P27.
pmkst HS.
apply (HKL cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t HB HFRM Hi).
- unfold s16_Mic. rewrite s16_step. change (s16_Mi (s16_M1c cx f) i) with (s16_Mic cx f i). rewrite HCS.
  apply (s16_inv_carry B MT LAWS cx f ly S W regs mem md k acc c m t _ ly S W (ms_regs ms) (ms_mem ms) _ _ HB HI HJ);
    first [ rewrite P2; exact (s16_den_reg regs m _ 0 0 0 _ 2 2%bv eq_refl)
          | rewrite P3; exact (s16_den_reg regs m _ 0 0 0 _ 3 3%bv eq_refl)
          | rewrite P4; exact (s16_den_reg regs m _ 0 0 0 _ 4 4%bv eq_refl)
          | rewrite P8; exact (s16_den_reg regs m _ 0 0 0 _ 8 8%bv eq_refl)
          | rewrite P9; exact (s16_den_reg regs m _ 0 0 0 _ 9 9%bv eq_refl)
          | rewrite P23; exact (s16_den_reg regs m _ 0 0 0 _ 23 23%bv eq_refl)
          | rewrite P27; exact (s16_den_reg regs m _ 0 0 0 _ 27 27%bv eq_refl)
          | idtac ].
  + rewrite P18, R18. apply s16_den_s2. lia.
  + apply Permutation_refl.
  + exact HMO.
  + intros a Ha Hn _. apply K1; [exact Ha|]. unfold seg_spec.SEG_M_SIZE in Hn. lia.
  + apply (s16_mconf_drop_role (rdW W mem) _ m _ i HMC ltac:(lia) ltac:(lia) ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
    * intros a Ha Hn. apply K1; [exact Ha | lia].
    * intros j Hj. destruct (Z.lt_ge_cases j 4) as [Hj4 | Hj4].
      -- replace (m + 256 * Z.of_nat i + 0x10 + j) with (m + 256 * Z.of_nat i + 16 + j) by lia. exact (Z1 j ltac:(lia)).
      -- replace (m + 256 * Z.of_nat i + 0x10 + j) with (m + 256 * Z.of_nat i + 20 + (j - 4)) by lia.
         exact (Z2 (j - 4) ltac:(lia)).
- split; [|split; [|split; [|split; [|split]]]].
  + rewrite P13, (s16_den_off E 32 SB 0 X32) by (unfold SB; lia). unfold w64, SB, SHADOW_OFF. reflexivity.
  + rewrite P14, (s16_den_off E 33 m 0 X33) by lia. unfold w64. f_equal. lia.
  + rewrite P20, (s16_den_off E 34 _ 32 X34) by lia. unfold w64. f_equal. lia.
  + rewrite P24. etransitivity; [exact (s16_den_shx E 34 _ 20 X34 X32 ltac:(lia) ltac:(lia))|].
    unfold w64, shadow_addr, SB, SHADOW_OFF. f_equal. f_equal. f_equal. lia.
  + rewrite P25. etransitivity; [exact (s16_den_reg regs m _ 0 0 0 _ 25 25%bv eq_refl)|]. exact R25.
  + rewrite P26, (s16_den_off E 34 _ 32 X34) by lia. unfold w64. f_equal. lia.
Qed.

(* the cut's facts at a later state of the same allocator state whose kept registers and bytes are the same *)
Lemma s16_inv_same : forall cx f ly S (W : world SEGS) regs mem md k acc c m t mc regs2 mem2 md2,
  lt_base B MT cx -> s16_inv B MT cx f ly S W regs mem md k acc c m t mc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 23 = getr regs 23 -> getr regs2 27 = getr regs 27 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a) ->
  s16_inv B MT cx f ly S W regs2 mem2 md2 k acc c m t mc.
Proof.
intros cx f ly S W regs mem md k acc c m t mc regs2 mem2 md2 HB HI HJ2 E2 E3 E4 E8 E9 E18 E23 E27 HK.
pose proof HI as (_ & HC & _ & Hm & _ & _ & _ & _ & _ & _ & HMC & _).
pose proof HC as (_ & _ & _ & (_ & _ & _ & HMO & _)).
pose proof Hm as (_ & Hm4 & _).
pose proof (s16_basic B MT cx ly S W regs mem md k acc _ _ _ c m _ HB HC Hm (proj1 (proj2 (proj2 (proj2 (proj2
  (proj2 (proj2 (proj2 (proj2 HI)))))))))) as (_ & _ & _ & _ & _ & _ & _ & _ & Hm' & _).
apply (s16_inv_carry B MT LAWS cx f ly S W regs mem md k acc c m t mc ly S W regs2 mem2 md2 mc HB HI HJ2
  E2 E3 E4 E8 E9 E18 E23 E27 (Permutation_refl _) HMO).
- intros a Ha _ _. exact (HK a Ha).
- apply (s16_mconf_ext (rdW W mem)); [exact HMC|]. intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha. apply HK. lia.
Qed.

(* the m_refuse call of 0x852bc (model without a box), returning to KP1 at some FP state *)
Lemma s16_call_kp1 : forall f i cx ly S (W : world SEGS) regs mem md k acc c m t,
  (forall fx1 : YK11.FPState, LT16_KP1_stmt (fx := fx1) B MT f i) ->
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  SegModel.m_cross_seg (s16_Mic cx f i) i =
    SegModel.m_upd (SegModel.m_refuse (s16_Mic cx f i) 0 false) i SegModel.ms_drop_model ->
  s16_inv B MT cx f ly S W regs mem md k acc c m t (s16_Mic cx f i) ->
  getr regs 1 = w64 (BASE + LO_KP1) -> getr regs 10 = w64 m -> getr regs 11 = w64 0 ->
  s16_sregs regs m i -> getr regs 19 = w64 (m + 0x20 + 256 * Z.of_nat i) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_m_refuse)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros f i cx ly S W regs mem md k acc c m t HKP HB HFRM Hi HCS HI R1 R10 R11 HSR R19.
pose proof HI as (Hnf & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMC & _).
pose proof (LLVMFuzzerTestOneInput_s02.lt_nfiles_range (x_pl cx)) as HNF. unfold x_nf in Hnf.
pose proof (s16_mconf_len _ _ _ HMC) as HL. unfold s16_Mic in HL. rewrite s16_Mi_len in HL.
apply (s16_call B MT LAWS MREF MTFL cx f ly S W regs mem md k acc c m t _ LO_KP1 HB HFRM HI R1
  ltac:(unfold LO_KP1; lia) eq_refl R10 R11 (s16_refuse_room (x_pl cx) f i ltac:(lia) ltac:(lia))).
intros fx1 ly2 S2 W2 regs2 mem2 md2 H01 HI2 HP.
assert (HPr : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs r)
  by (intros r z Hz <-; exact (HP z Hz)).
destruct HSR as (R20 & R24 & R25 & R26).
exact (HKP fx1 cx ly2 S2 W2 regs2 mem2 md2 k acc c m t HB (fxrel_frm0 fx fx1 HFRM H01) Hi HCS HI2
  (conj (eq_trans (HPr 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R20)
  (conj (eq_trans (HPr 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R24)
  (conj (eq_trans (HPr 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R25)
        (eq_trans (HPr 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R26))))
  (eq_trans (HPr 19%bv 19 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R19)).
Qed.
(* the m_refuse call of 0x852ec (box without a model), returning to KP2 at some FP state *)
Lemma s16_call_kp2 : forall f i cx ly S (W : world SEGS) regs mem md k acc c m t,
  (forall fx1 : YK11.FPState, LT16_KP2_stmt (fx := fx1) B MT f i) ->
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  SegModel.m_cross_seg (s16_Mic cx f i) i =
    SegModel.m_upd (SegModel.m_refuse (s16_Mic cx f i) 0 false) i SegModel.ms_drop_role ->
  s16_inv B MT cx f ly S W regs mem md k acc c m t (s16_Mic cx f i) ->
  getr regs 1 = w64 (BASE + LO_KP2) -> getr regs 10 = w64 m -> getr regs 11 = w64 0 ->
  s16_sregs regs m i -> getr regs 21 = w64 (shadow_addr (m + 0x10 + 256 * Z.of_nat i)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_m_refuse)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros f i cx ly S W regs mem md k acc c m t HKP HB HFRM Hi HCS HI R1 R10 R11 HSR R21.
pose proof HI as (Hnf & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMC & _).
pose proof (LLVMFuzzerTestOneInput_s02.lt_nfiles_range (x_pl cx)) as HNF. unfold x_nf in Hnf.
pose proof (s16_mconf_len _ _ _ HMC) as HL. unfold s16_Mic in HL. rewrite s16_Mi_len in HL.
apply (s16_call B MT LAWS MREF MTFL cx f ly S W regs mem md k acc c m t _ LO_KP2 HB HFRM HI R1
  ltac:(unfold LO_KP2; lia) eq_refl R10 R11 (s16_refuse_room (x_pl cx) f i ltac:(lia) ltac:(lia))).
intros fx1 ly2 S2 W2 regs2 mem2 md2 H01 HI2 HP.
assert (HPr : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs r)
  by (intros r z Hz <-; exact (HP z Hz)).
destruct HSR as (R20 & R24 & R25 & R26).
exact (HKP fx1 cx ly2 S2 W2 regs2 mem2 md2 k acc c m t HB (fxrel_frm0 fx fx1 HFRM H01) Hi HCS HI2
  (conj (eq_trans (HPr 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R20)
  (conj (eq_trans (HPr 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R24)
  (conj (eq_trans (HPr 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R25)
        (eq_trans (HPr 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R26))))
  (eq_trans (HPr 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)) R21)).
Qed.

(* 0x8523c (KH i): check 10 and role_set (beqz), checks 11 / 12 or 13 and model_set, the role test, and either the
   latch of pass i or the jal m_refuse (0x852bc to KP1, 0x852ec to KP2): the six paths of fuzz_segconf.c:299-309 *)
Lemma s16_head : forall f i, LT16_KL_stmt B MT f i -> (forall fx1 : YK11.FPState, LT16_KP1_stmt (fx := fx1) B MT f i) ->
  (forall fx1 : YK11.FPState, LT16_KP2_stmt (fx := fx1) B MT f i) -> LT16_KH_stmt B MT f i.
Proof.
intros f i HKL HKP1 HKP2. unfold LT16_KH_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM Hi HI HL.
pose proof (s16_Mi_len (s16_M1c cx f) i) as HLEN.
change (s16_Mi (s16_M1c cx f) i) with (s16_Mic cx f i) in HLEN.
pose proof HI as (Hnf & HC & Hbc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
pose proof (s16_mconf_len _ _ _ HMC) as HN32. rewrite HLEN in HN32.
destruct (s16_seedP_inv B MT cx f ly S W regs mem md k acc c m t _ i HB HI ltac:(lia)) as (HSP & Hpm & Hra & Happ & HAR).
rewrite HLEN in HSP.
assert (Hi' : (i < length (SegModel.mc_seg (s16_Mic cx f i)))%nat) by (rewrite HLEN; exact Hi).
pose proof (s16_cross_paths (s16_Mic cx f i) i) as (MP1 & MP2 & MP3 & MP4 & MP5 & MP6).
pose proof (s16_rd_role_set (rdW W mem) m _ i HMC Hi') as Hrrs.
pose proof (s16_rd_model_set (rdW W mem) m _ i HMC Hi') as Hrms.
destruct (s16_rd_role (rdW W mem) m _ i HMC Hi') as (Hro0 & Hrro).
set (N := length (SegModel.mc_seg (s16_M1c cx f))) in *.
set (rsv := seg_spec.b2z (SegModel.ms_role_set (nth i (SegModel.mc_seg (s16_Mic cx f i)) SegModel.mseg_d))) in *.
set (msv := seg_spec.b2z (SegModel.ms_model_set (nth i (SegModel.mc_seg (s16_Mic cx f i)) SegModel.mseg_d))) in *.
set (rov := SegModel.ms_role (nth i (SegModel.mc_seg (s16_Mic cx f i)) SegModel.mseg_d)) in *.
assert (Hrs01 : 0 <= rsv <= 1) by (subst rsv; unfold seg_spec.b2z; destruct (SegModel.ms_role_set _); lia).
assert (Hms01 : 0 <= msv <= 1) by (subst msv; unfold seg_spec.b2z; destruct (SegModel.ms_model_set _); lia).
pose proof HSP as (R9 & Hs1 & Hs1' & Hs1m & Hm4 & Hm16 & Hm' & _ & _ & _ & _ & _ & _ & _ & Hms1).
pose proof (s16_seed_h W regs mem m i rsv rov msv (Z.of_nat N) (x_s1 cx) HSP HL Hrs01 Hro0 Hms01 Hrro Hrrs Hrms) as HS.
destruct (s16_shok W regs mem m (m + 256 * Z.of_nat i) rsv rov msv (Z.of_nat N) ltac:(lia) Happ ltac:(lia) ltac:(lia)
  Hra) as (SHOK & _).
destruct (s16_E_x regs m (m + 256 * Z.of_nat i) rsv rov msv (Z.of_nat N)) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
pose proof HL as (R13 & R14 & R20 & R24 & R25 & R26).
set (E := s16_E regs m (m + 256 * Z.of_nat i) rsv rov msv (Z.of_nat N)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s16_E; apply Eimg_env).
pose proof HC as ((HJ & _) & _).
unfold cfg_at. change (w64 (BASE + LO_KH16)) with (Z_to_bv 64 (BASE + LO_KH16)).
(* the seed's values of the registers every path keeps *)
s16_rg HS (2%bv : bv 5) Q2. s16_rg HS (3%bv : bv 5) Q3. s16_rg HS (4%bv : bv 5) Q4. s16_rg HS (8%bv : bv 5) Q8.
s16_rg HS (9%bv : bv 5) Q9. s16_rg HS (13%bv : bv 5) Q13. s16_rg HS (14%bv : bv 5) Q14. s16_rg HS (18%bv : bv 5) Q18.
s16_rg HS (20%bv : bv 5) Q20. s16_rg HS (23%bv : bv 5) Q23. s16_rg HS (24%bv : bv 5) Q24.
s16_rg HS (25%bv : bv 5) Q25. s16_rg HS (26%bv : bv 5) Q26. s16_rg HS (27%bv : bv 5) Q27.
(* 0x8523c .. 0x8524c: check 10 (role_set's shadow byte), lw role_set; beqz *)
paj_run_tok RUN HS HJ SHOK s16_span.
{ s16_awr_ro. }
s16_keep0 (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK s16_span.
- (* role_set = 0: 0x85298, check 13, lw model_set; beqz *)
  rewrite (s16_beq E _ _ (rsv + 0) 0 (s16_den_off E 35 rsv 0 X35 ltac:(lia)) (s16_den_lit E 0) ltac:(lia) ltac:(lia))
    in Hc.
  apply Z.eqb_eq in Hc. rename Hc into Hrs.
  paj_run_tok RUN HS HJ SHOK s16_span.
  { s16_awr_ro. }
  s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK s16_span.
  + (* model_set = 0: the latch, m unchanged *)
    rewrite (s16_beq E _ _ (msv + 0) 0 (s16_den_off E 37 msv 0 X37 ltac:(lia)) (s16_den_lit E 0) ltac:(lia) ltac:(lia))
      in Hc.
    apply Z.eqb_eq in Hc. rename Hc into Hms.
    paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KL16.
    { s16_awr_ro. }
    s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
    s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9. s16_eq HS Q13 E13.
    s16_eq HS Q14 E14. s16_eq HS Q18 E18. s16_eq HS Q20 E20. s16_eq HS Q23 E23. s16_eq HS Q24 E24.
    s16_eq HS Q25 E25. s16_eq HS Q26 E26. s16_eq HS Q27 E27.
    pmkst HS.
    eapply (HKL cx ly S W _ _ _ k acc c m t HB HFRM Hi).
    { unfold s16_Mic. rewrite s16_step. change (s16_Mi (s16_M1c cx f) i) with (s16_Mic cx f i). rewrite (MP1 ltac:(lia) ltac:(lia)).
      exact (s16_inv_same cx f ly S W regs mem md k acc c m t _ _ _ _ HB HI HJ E2 E3 E4 E8 E9 E18 E23 E27
        (fun a Ha => KK a Ha (fun x => x))). }
    exact (conj (eq_trans E13 R13) (conj (eq_trans E14 R14) (conj (eq_trans E20 R20) (conj (eq_trans E24 R24)
      (conj (eq_trans E25 R25) (eq_trans E26 R26)))))).
  + (* model_set <> 0: a model without a box, jal m_refuse(m, 0) at 0x852bc *)
    rewrite (s16_beq E _ _ (msv + 0) 0 (s16_den_off E 37 msv 0 X37 ltac:(lia)) (s16_den_lit E 0) ltac:(lia) ltac:(lia))
      in Hc.
    apply Z.eqb_neq in Hc. rename Hc into Hms.
    paj_run_tok RUN HS HJ SHOK s16_span.
    { s16_awr_ro. }
    s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
    s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9.
    s16_eq HS Q18 E18. s16_eq HS Q20 E20. s16_eq HS Q23 E23. s16_eq HS Q24 E24.
    s16_eq HS Q25 E25. s16_eq HS Q26 E26. s16_eq HS Q27 E27.
    s16_rg HS (1%bv : bv 5) P1. s16_rg HS (10%bv : bv 5) P10. s16_rg HS (11%bv : bv 5) P11.
    s16_rg HS (19%bv : bv 5) P19. s16_rg HS (21%bv : bv 5) P21.
    pmkst HS.
    rewrite (SIGP SS_m_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
    replace (seg_af SS_m_refuse) with AF_m_refuse by (vm_compute; reflexivity).
    eapply (s16_call_kp1 f i cx ly S W _ _ _ k acc c m t HKP1 HB HFRM Hi (MP2 ltac:(lia) ltac:(lia))).
    * exact (s16_inv_same cx f ly S W regs mem md k acc c m t _ _ _ _ HB HI HJ E2 E3 E4 E8 E9 E18 E23 E27
        (fun a Ha => KK a Ha (fun x => x))).
    * rewrite P1. exact (codeptr_val E 1420 HEI).
    * rewrite P10. etransitivity; [exact (s16_den_off E 33 m 0 X33 ltac:(lia))|]. unfold w64. f_equal. lia.
    * rewrite P11. reflexivity.
    * exact (conj (eq_trans E20 R20) (conj (eq_trans E24 R24) (conj (eq_trans E25 R25) (eq_trans E26 R26)))).
    * rewrite P19. etransitivity; [exact (s16_den_off E 34 _ 32 X34 ltac:(lia))|]. unfold w64. f_equal. lia.
- (* role_set <> 0: 0x85250, s3 / s5, checks 11 and 12, lw role and model_set; beqz model_set *)
  rewrite (s16_beq E _ _ (rsv + 0) 0 (s16_den_off E 35 rsv 0 X35 ltac:(lia)) (s16_den_lit E 0) ltac:(lia) ltac:(lia))
    in Hc.
  apply Z.eqb_neq in Hc. rename Hc into Hrs.
  paj_run_tok RUN HS HJ SHOK s16_span.
  { s16_awr_ro. }
  s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK s16_span.
  + (* model_set = 0: 0x852dc, bne role, 4 *)
    rewrite (s16_beq E _ _ (msv + 0) 0 (s16_den_off E 37 msv 0 X37 ltac:(lia)) (s16_den_lit E 0) ltac:(lia) ltac:(lia))
      in Hc.
    apply Z.eqb_eq in Hc. rename Hc into Hms.
    paj_run_tok RUN HS HJ SHOK s16_span.
    { s16_awr_ro. }
    s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK s16_span.
    * (* role <> 4: the latch, m unchanged *)
      rewrite (s16_bne E _ _ (rov + 0) 4 (s16_den_off E 36 rov 0 X36 ltac:(lia)) (s16_den_lit E 4) ltac:(lia)
        ltac:(lia)) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hro.
      paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KL16.
      { s16_awr_ro. }
      s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
      s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9. s16_eq HS Q13 E13.
      s16_eq HS Q14 E14. s16_eq HS Q18 E18. s16_eq HS Q20 E20. s16_eq HS Q23 E23. s16_eq HS Q24 E24.
      s16_eq HS Q25 E25. s16_eq HS Q26 E26. s16_eq HS Q27 E27.
      pmkst HS.
      eapply (HKL cx ly S W _ _ _ k acc c m t HB HFRM Hi).
      { unfold s16_Mic. rewrite s16_step. change (s16_Mi (s16_M1c cx f) i) with (s16_Mic cx f i). rewrite (MP3 ltac:(lia) ltac:(lia) ltac:(lia)).
        exact (s16_inv_same cx f ly S W regs mem md k acc c m t _ _ _ _ HB HI HJ E2 E3 E4 E8 E9 E18 E23 E27
          (fun a Ha => KK a Ha (fun x => x))). }
      exact (conj (eq_trans E13 R13) (conj (eq_trans E14 R14) (conj (eq_trans E20 R20) (conj (eq_trans E24 R24)
        (conj (eq_trans E25 R25) (eq_trans E26 R26)))))).
    * (* role = 4 (a box without a model): jal m_refuse(m, model_set = 0) at 0x852ec *)
      rewrite (s16_bne E _ _ (rov + 0) 4 (s16_den_off E 36 rov 0 X36 ltac:(lia)) (s16_den_lit E 4) ltac:(lia)
        ltac:(lia)) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hro.
      paj_run_tok RUN HS HJ SHOK s16_span.
      { s16_awr_ro. }
      s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
      s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9.
      s16_eq HS Q18 E18. s16_eq HS Q20 E20. s16_eq HS Q23 E23. s16_eq HS Q24 E24.
      s16_eq HS Q25 E25. s16_eq HS Q26 E26. s16_eq HS Q27 E27.
      s16_rg HS (1%bv : bv 5) P1. s16_rg HS (10%bv : bv 5) P10. s16_rg HS (11%bv : bv 5) P11.
      s16_rg HS (19%bv : bv 5) P19. s16_rg HS (21%bv : bv 5) P21.
      pmkst HS.
      rewrite (SIGP SS_m_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
      replace (seg_af SS_m_refuse) with AF_m_refuse by (vm_compute; reflexivity).
      eapply (s16_call_kp2 f i cx ly S W _ _ _ k acc c m t HKP2 HB HFRM Hi (MP4 ltac:(lia) ltac:(lia) ltac:(lia))).
      -- exact (s16_inv_same cx f ly S W regs mem md k acc c m t _ _ _ _ HB HI HJ E2 E3 E4 E8 E9 E18 E23 E27
           (fun a Ha => KK a Ha (fun x => x))).
      -- rewrite P1. exact (codeptr_val E 1468 HEI).
      -- rewrite P10. etransitivity; [exact (s16_den_off E 33 m 0 X33 ltac:(lia))|]. unfold w64. f_equal. lia.
      -- rewrite P11. etransitivity; [exact (s16_den_off E 37 msv 0 X37 ltac:(lia))|]. unfold w64. f_equal. lia.
      -- exact (conj (eq_trans E20 R20) (conj (eq_trans E24 R24) (conj (eq_trans E25 R25) (eq_trans E26 R26)))).
      -- rewrite P21. etransitivity; [exact (s16_den_shx E 34 _ 16 X34 X32 ltac:(lia) ltac:(lia))|].
         unfold w64, shadow_addr, SB, SHADOW_OFF. f_equal. f_equal. f_equal. lia.
  + (* model_set <> 0: 0x85280, beq role, 4 *)
    rewrite (s16_beq E _ _ (msv + 0) 0 (s16_den_off E 37 msv 0 X37 ltac:(lia)) (s16_den_lit E 0) ltac:(lia) ltac:(lia))
      in Hc.
    apply Z.eqb_neq in Hc. rename Hc into Hms.
    paj_run_tok RUN HS HJ SHOK s16_span.
    { s16_awr_ro. }
    s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK s16_span.
    * (* role = 4 (a box with a model): 0x852dc, bnez model_set, the latch, m unchanged *)
      rewrite (s16_beq E _ _ (rov + 0) 4 (s16_den_off E 36 rov 0 X36 ltac:(lia)) (s16_den_lit E 4) ltac:(lia)
        ltac:(lia)) in Hc.
      apply Z.eqb_eq in Hc. rename Hc into Hro.
      paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KL16.
      { s16_awr_ro. }
      s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
      s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9. s16_eq HS Q13 E13.
      s16_eq HS Q14 E14. s16_eq HS Q18 E18. s16_eq HS Q20 E20. s16_eq HS Q23 E23. s16_eq HS Q24 E24.
      s16_eq HS Q25 E25. s16_eq HS Q26 E26. s16_eq HS Q27 E27.
      pmkst HS.
      eapply (HKL cx ly S W _ _ _ k acc c m t HB HFRM Hi).
      { unfold s16_Mic. rewrite s16_step. change (s16_Mi (s16_M1c cx f) i) with (s16_Mic cx f i). rewrite (MP5 ltac:(lia) ltac:(lia) ltac:(lia)).
        exact (s16_inv_same cx f ly S W regs mem md k acc c m t _ _ _ _ HB HI HJ E2 E3 E4 E8 E9 E18 E23 E27
          (fun a Ha => KK a Ha (fun x => x))). }
      exact (conj (eq_trans E13 R13) (conj (eq_trans E14 R14) (conj (eq_trans E20 R20) (conj (eq_trans E24 R24)
        (conj (eq_trans E25 R25) (eq_trans E26 R26)))))).
    * (* role <> 4 (a model without a box): s3 = &model_set, jal m_refuse(m, 0) at 0x852bc *)
      rewrite (s16_beq E _ _ (rov + 0) 4 (s16_den_off E 36 rov 0 X36 ltac:(lia)) (s16_den_lit E 4) ltac:(lia)
        ltac:(lia)) in Hc.
      apply Z.eqb_neq in Hc. rename Hc into Hro.
      paj_run_tok RUN HS HJ SHOK s16_span.
      { s16_awr_ro. }
      s16_kk (@pa_segs _ seg_listing PI) HFr KK. clear HF HFr HG.
      s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9.
      s16_eq HS Q18 E18. s16_eq HS Q20 E20. s16_eq HS Q23 E23. s16_eq HS Q24 E24.
      s16_eq HS Q25 E25. s16_eq HS Q26 E26. s16_eq HS Q27 E27.
      s16_rg HS (1%bv : bv 5) P1. s16_rg HS (10%bv : bv 5) P10. s16_rg HS (11%bv : bv 5) P11.
      s16_rg HS (19%bv : bv 5) P19. s16_rg HS (21%bv : bv 5) P21.
      pmkst HS.
      rewrite (SIGP SS_m_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
      replace (seg_af SS_m_refuse) with AF_m_refuse by (vm_compute; reflexivity).
      eapply (s16_call_kp1 f i cx ly S W _ _ _ k acc c m t HKP1 HB HFRM Hi (MP6 ltac:(lia) ltac:(lia) ltac:(lia))).
      -- exact (s16_inv_same cx f ly S W regs mem md k acc c m t _ _ _ _ HB HI HJ E2 E3 E4 E8 E9 E18 E23 E27
           (fun a Ha => KK a Ha (fun x => x))).
      -- rewrite P1. exact (codeptr_val E 1420 HEI).
      -- rewrite P10. etransitivity; [exact (s16_den_off E 33 m 0 X33 ltac:(lia))|]. unfold w64. f_equal. lia.
      -- rewrite P11. reflexivity.
      -- exact (conj (eq_trans E20 R20) (conj (eq_trans E24 R24) (conj (eq_trans E25 R25) (eq_trans E26 R26)))).
      -- rewrite P19. exact (s16_den_s3 regs m i rsv rov msv (Z.of_nat N) R25 ltac:(lia) ltac:(lia)).
Qed.

(* 0x85208 (K85208) .. 0x85228: a3 = the shadow base, 112(s1) = s10 = (m + 0x2000) >> 3, s2 = SH(m + 0x2000), check 9,
   a0 = m->n, a4 = m, blez a0: out to K853bc (no segment), else s9 = 0, s8 = 64(s1), s10 = s4 = 72(s1) and the head of
   pass 0 (0x8523c) *)
Lemma s16_entry : forall f, LT16_KH_stmt B MT f 0 -> LT_K853bc_stmt B MT f -> LT_K85208_stmt B MT f.
Proof.
intros f HKH HX. unfold LT_K85208_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM Hnf HCORE Hbc Hm Ht R23 R26 R27 HSL HRC HMC HSTR HCNT.
change (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None) with (s16_M1c cx f)
  in HMC, HCNT.
assert (HI0 : s16_inv0 B MT cx f ly S W regs mem md k acc c m t (s16_M1c cx f))
  by exact (conj Hnf (conj HCORE (conj Hbc (conj Hm (conj Ht (conj R23 (conj R27 (conj HSL (conj HRC (conj HMC
    (conj HSTR HCNT))))))))))).
destruct (s16_basic B MT cx ly S W regs mem md k acc _ _ _ c m _ HB HCORE Hm HSL)
  as (HAR & R2 & R9 & Hs1 & Hs1' & Hs1m & Hm4 & Hm16 & Hm' & Happ & Hms1 & H168 & H176 & H184 & H64 & H72 & Hps & Hpm
      & Hra).
pose proof (s16_mconf_len _ _ _ HMC) as HN32.
set (N := length (SegModel.mc_seg (s16_M1c cx f))) in *.
pose proof (s16_seed_e W regs mem m (Z.of_nat N) (x_s1 cx) R9 Hs1 Hs1' Hs1m Hm4 Hm16 Hm' Hms1 ltac:(lia) R26 H64 H72
  H168 H176 H184 Hps (s16_rd_n _ _ _ HMC)) as HS.
destruct (s16_shok W regs mem m m 0 0 0 (Z.of_nat N) Hm4 Happ ltac:(lia) ltac:(lia) Hra) as (_ & SHOK).
destruct (s16_E_x regs m m 0 0 0 (Z.of_nat N)) as (X32 & X33 & X34 & X35 & X36 & X37 & X38).
assert (U9 : bv_unsigned (ew (s16_E regs m m 0 0 0 (Z.of_nat N)) 9) = x_s1 cx)
  by (rewrite (s16_E_reg regs m m 0 0 0 _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
set (E := s16_E regs m m 0 0 0 (Z.of_nat N)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s16_E; apply Eimg_env).
pose proof HCORE as ((HJ & _) & _ & _ & (_ & _ & _ & HMO & _)).
destruct (s16_stk B MT cx HB) as (Hsp16 & Hsp & _ & Hs1b).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
unfold cfg_at. change (w64 (BASE + LO_K85208)) with (Z_to_bv 64 (BASE + LO_K85208)).
s16_rg HS (2%bv : bv 5) Q2. s16_rg HS (3%bv : bv 5) Q3. s16_rg HS (4%bv : bv 5) Q4. s16_rg HS (8%bv : bv 5) Q8.
s16_rg HS (9%bv : bv 5) Q9. s16_rg HS (23%bv : bv 5) Q23. s16_rg HS (27%bv : bv 5) Q27.
(* 0x85208 .. 0x85228: to the blez *)
paj_run_tok RUN HS HJ SHOK s16_span.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply awr_ok_cons_stack_off with (d := x_s1 cx - x_sp0 cx); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
s16_keepW (@pa_segs _ seg_listing PI) HFr U9 (x_s1 cx) 112 120 K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK s16_span.
- (* m->n <= 0: no segment, j 0x853bc *)
  rewrite (s16_bge E _ _ 0 (Z.of_nat N + 0) (s16_den_lit E 0) (s16_den_off E 38 (Z.of_nat N) 0 X38 ltac:(lia))
    ltac:(lia) ltac:(lia)) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc. assert (HN0 : N = 0%nat) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_K853bc.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply awr_ok_cons_stack_off with (d := x_s1 cx - x_sp0 cx); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s16_keepW (@pa_segs _ seg_listing PI) HFr U9 (x_s1 cx) 112 120 K2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (W112 : rdword (rdW W (ms_mem msx)) (x_s1 cx + 112) = Some ((m + seg_spec.MC_N) / 8)) end.
  { apply (s16_chunk_word W E _ _ 0 _ 9 112 (SAlu ALU_SRL (SOff 33 8192) (SLit 3)) (x_s1 cx) _ HS eq_refl eq_refl);
      [cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | exact U9 |
       exact (s16_den_srl3 E 33 m 8192 X33 ltac:(lia) ltac:(lia)) |].
    split; [apply Z.div_pos; unfold seg_spec.MC_N; lia | apply Z.div_lt_upper_bound; unfold seg_spec.MC_N; lia]. }
  s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9. s16_eq HS Q23 E23.
  s16_eq HS Q27 E27. s16_rg HS (18%bv : bv 5) P18.
  pmkst HS.
  eapply (s16_to_853bc f cx ly S W _ _ _ k acc c m t HX HB HFRM).
  fold N. rewrite HN0. change (s16_Mic cx f 0) with (s16_M1c cx f).
  apply (s16_inv_carry0 B MT LAWS cx f ly S W regs mem md k acc c m t _ ly S W _ _ _ _ HB HI0 HJ E2 E3 E4 E8 E9
    ltac:(rewrite P18; apply s16_den_s2; lia) E23 E27 (Permutation_refl _) HMO); [| exact W112 |].
  + intros a Ha _ _ Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
  + apply (s16_mconf_ext (rdW W mem)); [exact HMC|].
    intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha. rewrite (K2 a ltac:(lia) ltac:(lia)). exact (K1 a ltac:(lia) ltac:(lia)).
- (* m->n > 0: the head of pass 0 *)
  rewrite (s16_bge E _ _ 0 (Z.of_nat N + 0) (s16_den_lit E 0) (s16_den_off E 38 (Z.of_nat N) 0 X38 ltac:(lia))
    ltac:(lia) ltac:(lia)) in Hc.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s16_span LO_KH16.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply awr_ok_cons_stack_off with (d := x_s1 cx - x_sp0 cx); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s16_keepW (@pa_segs _ seg_listing PI) HFr U9 (x_s1 cx) 112 120 K2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (W112 : rdword (rdW W (ms_mem msx)) (x_s1 cx + 112) = Some ((m + seg_spec.MC_N) / 8)) end.
  { apply (s16_chunk_word W E _ _ 0 _ 9 112 (SAlu ALU_SRL (SOff 33 8192) (SLit 3)) (x_s1 cx) _ HS eq_refl eq_refl);
      [cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | exact U9 |
       exact (s16_den_srl3 E 33 m 8192 X33 ltac:(lia) ltac:(lia)) |].
    split; [apply Z.div_pos; unfold seg_spec.MC_N; lia | apply Z.div_lt_upper_bound; unfold seg_spec.MC_N; lia]. }
  s16_eq HS Q2 E2. s16_eq HS Q3 E3. s16_eq HS Q4 E4. s16_eq HS Q8 E8. s16_eq HS Q9 E9. s16_eq HS Q23 E23.
  s16_eq HS Q27 E27. s16_rg HS (18%bv : bv 5) P18.
  s16_rg HS (13%bv : bv 5) P13. s16_rg HS (14%bv : bv 5) P14. s16_rg HS (20%bv : bv 5) P20.
  s16_rg HS (24%bv : bv 5) P24. s16_rg HS (25%bv : bv 5) P25. s16_rg HS (26%bv : bv 5) P26.
  pmkst HS.
  eapply (HKH cx ly S W _ _ _ k acc c m t HB HFRM ltac:(lia)).
  + change (s16_Mic cx f 0) with (s16_M1c cx f).
    apply (s16_inv_carry0 B MT LAWS cx f ly S W regs mem md k acc c m t _ ly S W _ _ _ _ HB HI0 HJ E2 E3 E4 E8 E9
      ltac:(rewrite P18; apply s16_den_s2; lia) E23 E27 (Permutation_refl _) HMO); [| exact W112 |].
    * intros a Ha _ _ Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
    * apply (s16_mconf_ext (rdW W mem)); [exact HMC|].
      intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha. rewrite (K2 a ltac:(lia) ltac:(lia)). exact (K1 a ltac:(lia) ltac:(lia)).
  + unfold s16_lregs. cbn [Z.of_nat]. rewrite !Z.mul_0_r, !Z.add_0_r.
    split; [|split; [|split; [|split; [|split]]]].
    * rewrite P13, (s16_den_off E 32 SB 0 X32) by (unfold SB; lia). unfold w64, SB, SHADOW_OFF. reflexivity.
    * rewrite P14, (s16_den_off E 33 m 0 X33) by lia. unfold w64. f_equal. lia.
    * rewrite P20, (s16_den_off E 33 m 32 X33) by lia. reflexivity.
    * rewrite P24. etransitivity; [exact (s16_den_shx E 33 m 20 X33 X32 ltac:(lia) ltac:(lia))|].
      unfold w64, shadow_addr, SB, SHADOW_OFF. reflexivity.
    * rewrite P25. reflexivity.
    * rewrite P26, (s16_den_off E 33 m 32 X33) by lia. reflexivity.
Qed.
End x.

(* the loop: by induction on the passes left, 32 - i (cw_loop's form, chain_words_a.v:37-48); a pass i >= m->n has
   no state (LT16_KH_stmt asks i < m->n <= 32) *)
Lemma s16_loop : forall f, LTA_K853bc B MT f -> forall i (fx1 : YK11.FPState), LT16_KH_stmt (fx := fx1) B MT f i.
Proof.
intros f HX.
assert (H : forall n i, (32 - i <= n)%nat -> forall fx1 : YK11.FPState, LT16_KH_stmt (fx := fx1) B MT f i).
{ induction n as [|n IH]; intros i Hn fx1.
  - intros cx ly S W regs mem md k acc c m t _ _ Hi HI _. exfalso.
    pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMC & _).
    pose proof (s16_mconf_len _ _ _ HMC) as HL. unfold s16_Mic in HL. rewrite s16_Mi_len in HL. lia.
  - assert (HKL : forall fx2 : YK11.FPState, LT16_KL_stmt (fx := fx2) B MT f i)
      by (intros fx2; exact (s16_latch (fx := fx2) f i (IH (Datatypes.S i) ltac:(lia) fx2) (HX fx2))).
    exact (s16_head (fx := fx1) f i (HKL fx1) (fun fx2 => s16_kp1 (fx := fx2) f i (HKL fx2))
      (fun fx2 => s16_kp2 (fx := fx2) f i (HKL fx2))). }
intros i fx1. exact (H _ i (le_n _) fx1).
Qed.

Section y. Context {fx : YK11.FPState}.
(* S06: from K85208 f through the inlined m_cross loop to K853bc f *)
Theorem lt_seg_S06 : lt_seg_S06_stmt (fx := fx) B MT.
Proof. intros f HX. exact (s16_entry (fx := fx) f (s16_loop f HX 0 fx) (HX fx)). Qed.
End y.
End w.
