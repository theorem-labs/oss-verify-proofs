(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 174 of its 211 lines of code are new or changed and 253 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4; ported to reac-pw/fuzz_rate's image A: module paths changed (images.Asan for lib/A/Img0, RtPgBase / RtPgCSpec / RtPgSteps / RtPgW6aBase for the RPg files, RtPgSteps' rts_wx / rts_segs_low / same_io_wvb / regs_kept_of_st_ok / rts_post for RPgCfgChanges' and RPgSteps' facts and w6_post); rate's pcs and the cell [R+0x138] for [R+0xf0]; rate's tail stores in.n to s8 (`mv s8,a1`) instead of the cell [R+0xf8], so the s1-based region is read-only, the post has three stored values and s8 in place of s9; the frame facts use the kit's AR_laws_ok instead of a LAWS hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aTail.v, with its module paths and module names changed; 405 of its 470 lines of code are new or changed and 146 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC4.v; 1003 of its 1068 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 616508a91de2 (its helpers
   c2_all256, c2_notin, c2_nz, c2_regv and c2_kio, renamed c5_*; the engine usage of its entry states and runs) and
   proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v at 527e8d2097d9 (the memcpy call into e.body and the e-byte
   assembly), for reac-pw/fuzz_rate's image A and ent_build's case 5; everything else is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC5.v, with its module paths, addresses and numbers changed; 590 of its 1105 lines of code are new or changed and 553 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bC5B.v at a191d52e2a9a for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgSteps.v's rl_ names, lib/AU/RPgMem.v's rm_ names); every pc, register, real-frame cell, data
   address and the write set are role B's: the real frame is 0x200 bytes; the kind byte is kept in the register s10
   across the call (role makes no [R+0x128] write), so block A writes no memory and the sign test `bltz s10` reads the
   register; the shadow offset is s11, the T1 test's 1 is s4, the kind byte's address a6; the count n is in s8, e62.body
   in s4, what is left after the copy in s6; the cells read are [R+0x110] (e62.body, block A), [R+0xf0] (~e62.body),
   [R+0x130] (pp + 0x4000), [R+0x140] (pp), [R+0x158] (&e62); at J a3 = the cursor, t1 = what is left, s6 = pp + 0x4000,
   a5 = pp; checked_memcpy is 0x5116c; the block statement is lib/AU/RPgW6bBase.v's w6bb_c5_stmt. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the block lemma w6bb_c5 of
   lib/AU/RPgW6bBase.v, case 5 of ent_build's `switch (kind % 10)` (pod.h:336-337; ent_text pod.h:209-219) inside
   LLVMFuzzerTestOneInput (0x80020), from the case entry 0x8113c to the join J 0x818d8. Proves no function (kind:
   segment lemma); the callee checked_memcpy (0x5116c) is the Section hypothesis AMEMCPY, the kernel's
   YG0d.aintrin_realizes.

   THE CODE (registers as in RPgW6bBase.v: s1 = R, s11 = SHADOW_OFF, s2 = c, a6 = c - 1, s6 = |r|, t1 = |r| + 1,
   s4 = 1, a3 = the kind byte sign-extended):
     0x8113c  beqz s6 -> 0x814c4                       no byte left
     0x81140  a0 := s2 + 1; 0x81144 bltu s4,a0 (T1: the other arm `j 0x82604` is the trap)
     0x8114c  s10 := a3 (the kind byte, sign-extended; kept in the register across the call)
     0x81150 .. 0x81160  the instrumented check of s2 (bnez to the slow block 0x81ad4; `ld s4,0x110(s1)` (= e62.body)
                         between its load and branch)
     0x81164  lbu a0,0(s2) (= b); s6 := t1 - 2 (= |r| - 1); s2 := a6 + 2 (= c + 1); s8 := b & 31
     0x81174  bltu s8,s6 -> 0x8117c; 0x81178 s8 := s6 (n = min (b & 31, |r| - 1))
     0x8117c  a0 := ~s2; 0x81180 bgeu a0,s8 (T2: s2 + n does not wrap)
     0x81188  a0 := s4 (e62.body); a1 := s2; a2 := s8; 0x81194 jal checked_memcpy (e62.body, the input after b, n)
     0x81198  a0 := s8; 0x8119c bltz s10 -> 0x811b8 (kind & 0x80: no NUL)
     0x811a0  a0 := [R+0xf0] (= ~(F + 0x218)); 0x811a4 bgeu a0,s8 (T3); a1 := s4 + s8; a0 := s8 + 1;
              0x811b4 sb zero,0(a1) (the NUL, an uninstrumented store)
     0x811b8  a3 := s2 + s8; t1 := s6 - s8; a1 := [R+0x158] (= F + 0x210, e62); sw 8,0(a1); sw a0,4(a1);
              a5 := [R+0x140] (= pp); j 0x814bc
     0x814c4  s10 := a3; s8 := 0; s4 := [R+0x110]; bgeu zero,s6 -> 0x81178 (always): n = 0
     0x814bc  s6 := [R+0x130] (= pp + 0x4000); J.
   THE PROOF, in three lemmas and the glue:
     c5b_A1 / c5b_A0  the case entry .. the memcpy entry (the byte arm: T1 and the check in the run, the branch on n
                      and T2 split by srr_branch_tok, T2's trap arm refuted; the no-byte arm with s6 pinned to 0, T2
                      split and refuted), post c5b_apost: the registers the call reads and the callee-saved ones block B
                      reads (s10 = the kind byte), every byte kept;
     c5b_CB           the call (RPgSteps.rl_intrin_at) and the block 0x81198 .. J (the branch on s10 split; T3 decided
                      by the range of [R+0xf0]; the NUL arm stops at 0x811b4 and pins a1 to the NUL's own atom,
                      F + 0x218 + n), post an rl_wpost over the call's start;
     w6bb_c5          the model (ent_build's case 5, ent_text with |p| <= 31) and the two arms. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgSteps RPgW6bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs and the engine's shadow ======================================== *)
Definition C5B_RET : Z := 0x81198.     (* after the memcpy *)
Definition C5B_NUL : Z := 0x811b4.     (* sb zero,0(a1): the NUL *)
Definition C5B_RLO : Z := 0x10007fff8000.
Definition C5B_FHI : Z := 0x7fffff800000.
(* the closed bounds of [R+0xf0] = 2^64 - 1 - (F + 0x218) for 4096 <= F <= C5B_FHI *)
Definition C5B_NLO : Z := 18446603336229584359.
Definition C5B_NHI : Z := 18446744073709546983.
Definition c5b_Bx : sv := SOff 27 0.
Definition c5b_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the kind byte sign-extended, as the 64-bit register s10 holds it *)
Definition c5b_ksx (kd : Z) : Z := (kd - 256 * (kd / 128)) mod 2 ^ 64.

(* ======================================== block A: entry .. the memcpy entry ========================================
   atoms 32 = F, 33 = b (the byte after the kind byte; 0 when none). Regions: the cell [R+0x110, R+0x118) (read only,
   = F + 0x218 = e62.body) and, with a byte, the input byte at s2. Block A writes no memory. *)
Definition c5b_rA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x110 0x118 0 0 [YP09.mkChunk 0x110 (CVal 8 (SOff 32 0x218))].
Definition c5b_rI : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition c5b_fA1 : list (nat * afact) :=
  [(9%nat, mkAF C5B_RLO (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (22%nat, mkAF 1 (2 ^ 47 - 3) 0); (6%nat, mkAF 2 (2 ^ 47 - 2) 0); (18%nat, mkAF 2 (2 ^ 47 - 2) 0);
   (16%nat, mkAF 1 (2 ^ 47 - 3) 0); (20%nat, mkAF 1 1 0); (32%nat, mkAF 4096 C5B_FHI 5); (33%nat, mkAF 0 255 0)].
Definition c5b_fA0 : list (nat * afact) :=
  [(9%nat, mkAF C5B_RLO (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (18%nat, mkAF 2 (2 ^ 47 - 1) 0); (32%nat, mkAF 4096 C5B_FHI 5)].
Definition c5b_ssA1 : sstate := mkSS W6BB_D5 sr_atoms [c5b_rA; c5b_rI] None (mkFacts c5b_fA1 [] []).
Definition c5b_ssA0 : sstate := mkSS W6BB_D5 sr_atoms [c5b_rA] None (mkFacts c5b_fA0 [] []).
Definition c5b_extA (F n : Z) : list word := [w64 F; w64 n].
(* the registers block A writes *)
Definition c5b_clobA : list (bv 5) := [1; 10; 11; 12; 18; 20; 22; 24; 26]%bv.

(* ======================================== block B: 0x81198 .. J ========================================
   atoms 32 = F + 0x210 (e62), 33 = F + 0x218 + n (the NUL's byte), 34 = [R+0xf0], 35 = pp + 0x4000, 36 = pp. The kind
   byte sign-extended is the callee-saved register s10 (atom 26), not an extra. Regions: the cells [R+0xf0, R+0x160)
   (read only), e62's header (written) and the NUL's byte (written, 0 before and after). *)
Definition c5b_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0xf0 0x160 0 0
  [YP09.mkChunk 0xf0 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x140 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
Definition c5b_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition c5b_rN : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition c5b_fB : list (nat * afact) :=
  [(9%nat, mkAF C5B_RLO (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (24%nat, mkAF 0 31 0); (32%nat, mkAF 4096 C5B_FHI 4); (33%nat, mkAF 4096 C5B_FHI 0);
   (34%nat, mkAF C5B_NLO C5B_NHI 0)].
Definition c5b_SHB : list shent := [mkSHE 32 0 8; mkSHE 33 0 1].
Definition c5b_ssB : sstate := mkSS C5B_RET sr_atoms [c5b_rR; c5b_rE; c5b_rN] None (mkFacts c5b_fB [] []).
Definition c5b_extB (F m pp : Z) : list word :=
  [w64 (F + 0x210); w64 (F + 0x218 + m); w64 (2 ^ 64 - 1 - (F + 0x218)); w64 (pp + 0x4000); w64 pp].
Definition c5b_clobB : list (bv 5) := [6; 10; 11; 12; 13; 15; 22]%bv.
Definition c5b_wrB (R F : Z) : Z -> Prop := fun a => (R - ESTACK <= a < R) \/ (F + 0x210 <= a < F + 0x278).

(* ======================================== small helpers ======================================== *)
Lemma c5b_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.
Lemma c5b_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma c5b_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma c5b_af : forall E n v lo hi al, bv_unsigned (ew E n) = v -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H. auto. Qed.
Lemma c5b_ureg : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.
Lemma c5b_ux : forall regs extra j v, nth j extra (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Ereg regs extra) (32 + j)) = v.
Proof. intros regs extra j v H Hv. rewrite ew_Ereg_extra, H. apply unsigned_lit_small. lia. Qed.
Lemma c5b_eq_lit : forall E n v, bv_unsigned (ew E n) = v -> ew E n = Z_to_bv 64 v.
Proof. intros E n v H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma c5b_U : forall E n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. intros E n v H Hv. apply U_atom; [apply c5b_eq_lit; exact H | exact Hv]. Qed.
Lemma c5b_Uoff : forall E n v c, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof. intros E n v c H Hv. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.
Lemma c5b_den : forall E e v, U E e = v -> sv_denot E e = w64 v.
Proof. intros E e v H. rewrite denot_lit_U, H. reflexivity. Qed.
Lemma c5b_U_add : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb H1 H2 H3. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.
(* the role's `sub t1,s6,s8` normalises to ADD b (MUL a (-1)) (the minuend s6 = atom 22 has the smaller index) *)
Lemma c5b_U_sub : forall E a b x y, U E a = x -> U E b = y -> 0 <= x <= y -> y < 2 ^ 64 ->
  U E (SAlu ALU_ADD b (SMd M_MUL a (SLit (-1)))) = y - x.
Proof.
intros E a b x y Ha Hb H1 H2. rewrite U_SAlu, U_SMd, Ha, Hb, U_SLit. cbn [zalu_raw zmd_raw].
unfold zcanon, M64. rewrite Zplus_mod_idemp_r. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (y + x * (2 ^ 64 - 1)) with ((y - x) + x * 2 ^ 64) by ring. rewrite Z_mod_plus_full.
apply Z.mod_small. lia.
Qed.
Lemma c5b_U_and31 : forall E a v, U E a = v -> 0 <= v < 256 -> U E (SAlu ALU_AND a (SLit 31)) = v mod 32.
Proof.
intros E a v Ha Hv. rewrite U_and_lit by lia. rewrite Ha. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.
(* the complement `not t,x`, and T2's compare: ~x >= y when x + y does not wrap *)
Lemma c5b_U_not : forall E a x, U E a = x -> 0 <= x < 2 ^ 64 -> U E (SAlu ALU_XOR a (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E a x Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma c5b_t2 : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SAlu ALU_XOR a (SLit (-1)))) (sv_denot E b) = true.
Proof.
intros E a b x y Ha Hb H1 H2 H3. rewrite branch_geu_U, (c5b_U_not E a x Ha ltac:(lia)), Hb.
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma c5b_ksx_range : forall kd, 0 <= c5b_ksx kd < 2 ^ 64.
Proof. intros kd. unfold c5b_ksx. apply Z.mod_pos_bound. lia. Qed.
Lemma c5b_w64_ksx : forall kd, w64 (kd - 256 * (kd / 128)) = w64 (c5b_ksx kd).
Proof. intros kd. unfold c5b_ksx, w64. symmetry. apply Z_to_bv64_mod. Qed.
(* `bltz s10` with s10 = the register (the kind byte sign-extended) is taken exactly when kind >= 128 *)
Lemma c5b_lt_all : forall kd, 0 <= kd < 256 ->
  branch_taken BC_LT (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (c5b_ksx kd)) + 0)) (Z_to_bv 64 0) = (128 <=? kd).
Proof.
intros kd Hk. apply Bool.eqb_prop.
exact (c5b_all256 (fun kd => Bool.eqb (branch_taken BC_LT (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (c5b_ksx kd)) + 0))
  (Z_to_bv 64 0)) (128 <=? kd)) ltac:(vm_compute; reflexivity) kd Hk).
Qed.
Lemma c5b_bltz : forall E n kd, ew E n = w64 (c5b_ksx kd) -> 0 <= kd < 256 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (128 <=? kd).
Proof. intros E n kd H Hk. cbn [sv_denot]. rewrite H. exact (c5b_lt_all kd Hk). Qed.
Lemma c5b_bit7 : forall kd, 0 <= kd < 256 -> Z.testbit kd 7 = (128 <=? kd).
Proof.
intros kd Hk. apply Bool.eqb_prop.
exact (c5b_all256 (fun kd => Bool.eqb (Z.testbit kd 7) (128 <=? kd)) ltac:(vm_compute; reflexivity) kd Hk).
Qed.
Lemma c5b_F16 : forall F, F mod 32 = 0 -> (F + 0x210) mod 2 ^ 4 = 0.
Proof.
intros F HF. change (2 ^ 4) with 16. apply (proj2 (Z.mod_divide _ 16 ltac:(lia))).
apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF. destruct HF as [q Hq]. exists (2 * q + 33). lia.
Qed.
Lemma c5b_mod0 : forall v, v mod 2 ^ 0 = 0.
Proof. intros v. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity. Qed.
(* the shadow hull of a range below 2 ^ 47 lies below kHighMemBeg + 8 (the engine's lia has no division) *)
Lemma c5b_div8 : forall z, 0 <= z -> 0 <= z / 8 <= z /\ z / 8 * 8 <= z < z / 8 * 8 + 8.
Proof.
intros z Hz. pose proof (Z.div_mod z 8 ltac:(lia)) as E. pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as M.
pose proof (Z.div_pos z 8 ltac:(lia) ltac:(lia)) as D. split; [split; [exact D | lia] | lia].
Qed.
Lemma c5b_hull_bnd : forall x n s, 0 <= x -> x + n <= 2 ^ 47 -> 0 < n ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < kHighMemBeg + 8.
Proof.
intros x n s Hx Hxn Hn Hs. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (c5b_div8 x Hx) as (Dx & _).
pose proof (c5b_div8 (x + n - 1) ltac:(lia)) as (Dy & _).
pose proof (c5b_div8 (0x7fff8000 + x / 8) ltac:(lia)) as (Ex0 & Ex).
pose proof (c5b_div8 (0x7fff8000 + (x + n - 1) / 8) ltac:(lia)) as (Ey0 & Ey).
assert (Hx8 : x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Hy8 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
unfold kHighMemBeg. lia.
Qed.

(* a run's frame through the regions' write windows: every window lies in one of the windows ws *)
Definition c5b_win (ws : list (nat * Z * Z)) (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  existsb (fun w => match w with (k, lo, hi) =>
    obase_eqb (YP09.r_base r) (Some k) && (lo <=? YP09.r_wlo r) && (YP09.r_whi r <=? hi) end) ws.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c5b_keep_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) ws (P : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (c5b_win ws) rs = true ->
  (forall a k lo hi, In (k, lo, hi) ws -> bv_unsigned (ew E k) + lo <= a < bv_unsigned (ew E k) + hi -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 ws P K HF Hw HP a Ha Hn. rewrite <- (K a Ha Hn).
apply (aview_eq_of rsegs). apply HF. intros (r & Hin & Hr).
rewrite unsigned_lit_small in Hr by lia.
pose proof (proj1 (forallb_forall _ _) Hw r Hin) as Hc. unfold c5b_win in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as ([[k lo] hi] & Hk & Hb).
apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate H0].
cbn [obase_eqb] in H0. apply Nat.eqb_eq in H0. subst n.
apply Hn. apply (HP a k lo hi Hk). cbn [base_val] in Hr. lia.
Qed.
End k.

(* a register of the state after a run, as its symbolic value's denotation *)
Ltac c5b_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity)
  end.
Ltac c5b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; c5b_kio].
(* the frame of the run that just ended, composed with the frame so far (KE); HW: the windows lie in Pv *)
Ltac c5b_keep KE wsv Pv HW :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KS := fresh "KS" in
    pose proof (c5b_keep_step _ _ _ _ _ _ wsv Pv KE HFr ltac:(vm_compute; reflexivity) HW) as KS;
    clear KE HFr HW; rename KS into KE
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ => clear old end.
(* the env of a state *)
Ltac c5b_env HS := lazymatch type of HS with st_ok _ ?E _ _ => E end.
(* T2's trap arm: `bgeu (~a) b` falls through only if a + b wraps, which ua + ub < 2^64 excludes; the arm's
   hypothesis is found by its shape (srr_branch_tok names it with a fresh name) *)
Ltac c5b_t2_refute HS ua ub tA tB :=
  let E := c5b_env HS in
  lazymatch goal with
  | Hc : branch_taken BC_GEU (sv_denot _ (SAlu ALU_XOR ?a (SLit (-1)))) (sv_denot _ ?b) = false |- _ =>
    let UA := fresh "UA" in let UB := fresh "UB" in
    assert (UA : U E a = ua) by tA; assert (UB : U E b = ub) by tB;
    rewrite (c5b_t2 E a b ua ub UA UB) in Hc by lia; discriminate Hc
  | |- _ => idtac "c5b_t2_refute: no T2 arm hypothesis"; fail
  end.

(* ======================================== the model ======================================== *)
Lemma c5b_build : forall (b : byte) r, bv_unsigned b mod 10 = 5 ->
  ent_build (b :: r) =
  (ent_text (firstn (Z.to_nat (fst (fuzz_u8 r) mod 32)) (snd (fuzz_u8 r))) (negb (Z.testbit (bv_unsigned b) 7)),
   skipn (Z.to_nat (fst (fuzz_u8 r) mod 32)) (snd (fuzz_u8 r))).
Proof.
intros b r H. unfold ent_build. cbn [fuzz_u8]. rewrite H. change (Z.to_nat 5) with 5%nat. cbv iota beta.
destruct (fuzz_u8 r) as [n r1]. reflexivity.
Qed.
Lemma c5b_ent : forall (p : list byte) (nul : bool), (length p <= 31)%nat ->
  ent_mem (ent_text p nul) = le32 8 ++ le32 (Z.of_nat (length p) + (if nul then 1 else 0)) ++ p ++ zeros (96 - length p).
Proof.
intros p nul Hp. unfold ent_text, ent_mem. rewrite (firstn_all2 (n := 95)) by lia.
destruct nul; cbn [e_type e_size e_body]; unfold POD_STRING.
- rewrite length_app. cbn [length]. f_equal. f_equal; [f_equal; lia|]. rewrite <- app_assoc. f_equal.
  replace (96 - length p)%nat with (S (96 - (length p + 1)))%nat by lia. reflexivity.
- f_equal. f_equal. f_equal. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6BB_MEMCPY.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.
Local Abbreviation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* the state at the memcpy entry: a0 = e62.body, a1 = x the source, a2 = m the count; the callee-saved s2 = x,
   s4 = e62.body, s6 = nl what is left after the copy's source, s8 = m, s10 = the kind byte sign-extended; block A
   writes no memory. *)
Definition c5b_apost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
(F kd x m nl : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs1 mem1 md1,
c2 = mkCfg (mkst regs1 (Z_to_bv 64 W6BB_MEMCPY) mem1 (seg_rom rsegs)) md1 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\ same_io mdc md1 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r c5b_clobA -> getr regs1 r = getr regs r) /\
getr regs1 1 = w64 C5B_RET /\ getr regs1 10 = w64 (F + 0x218) /\ getr regs1 11 = w64 x /\ getr regs1 12 = w64 m /\
getr regs1 18 = w64 x /\ getr regs1 20 = w64 (F + 0x218) /\ getr regs1 22 = w64 nl /\ getr regs1 24 = w64 m /\
getr regs1 26 = w64 (c5b_ksx kd) /\
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a).

(* the write rights of block A's read-only regions: all windows are empty *)
Ltac c5b_awrA :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* the frame of a block-A run: no write window, so every byte is kept *)
Ltac c5b_keepA KE :=
  lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let HW := fresh "HW" in
    assert (HW : forall a0 kx lo0 hi0, In (kx, lo0, hi0) (@nil (nat * Z * Z)) ->
      bv_unsigned (ew E kx) + lo0 <= a0 < bv_unsigned (ew E kx) + hi0 -> False) by (intros a0 kx lo0 hi0 []);
    c5b_keep KE (@nil (nat * Z * Z)) (fun _ : Z => False) HW
  end.
(* region i of the state HS, as region_ok at its memory *)
Ltac c5b_region HS i HRn :=
  lazymatch type of HS with st_ok _ ?E2 ?ssf (restrict ?H ?msx) =>
    let ri := eval vm_compute in (nth_error (ss_mem ssf) i) in
    lazymatch ri with Some ?rg =>
      assert (HRn : region_ok rsegs E2 (mrestrict H (ms_mem msx)) rg)
        by (apply (rl_region_nth E2 ssf msx i rg H HS); vm_compute; reflexivity)
    end
  end.

(* a value read back out of a region's chunk *)
Lemma c5b_chunk_val : forall E m (n : nat) b lo hi wlo whi cs off (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk off (CVal w e)) cs -> U E e = v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem rsegs m (b + off) (N.to_nat w) v.
Proof.
intros E m n b lo hi wlo whi cs off w e v HR Hb Hin He Hv Hw.
apply (val_of_chunk_ok rsegs E m b off w e v (rl_chunks E m n b cs lo hi wlo whi HR Hb _ Hin)); [| exact Hv | exact Hw].
rewrite denot_lit_U, He. reflexivity.
Qed.

(* the leaf of a block-A run at the memcpy entry *)
Lemma c5b_A_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) F kd x m nl
  E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = W6BB_MEMCPY ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r c5b_clobA -> getr (ms_regs ms) r = getr regs r) ->
getr (ms_regs ms) 1 = w64 C5B_RET -> getr (ms_regs ms) 10 = w64 (F + 0x218) -> getr (ms_regs ms) 11 = w64 x ->
getr (ms_regs ms) 12 = w64 m -> getr (ms_regs ms) 18 = w64 x -> getr (ms_regs ms) 20 = w64 (F + 0x218) ->
getr (ms_regs ms) 22 = w64 nl -> getr (ms_regs ms) 24 = w64 m -> getr (ms_regs ms) 26 = w64 (c5b_ksx kd) ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
SRr rsegs W (mkCfg ms md) (c5b_apost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd x m nl).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd x m nl E ss ms md HS Hrv Hpc HJ Hio Hk
  H1 H10 H11 H12 H18 H20 H22 H24 H26 Hm.
apply SRr_ret. unfold c5b_apost. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
repeat (split; [eassumption|]). exact Hm.
Qed.

(* ---- block A, a byte left ---- *)
Lemma c5b_A1 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F c kd
  (b : byte) (r' : list byte),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
R mod 16 = 0 -> R + 0x200 <= sp0 -> sp0 - STK <= R - T_SEG_STK -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
F mod 32 = 0 ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 c -> getr regs 16 = w64 (c - 1) ->
getr regs 22 = w64 (Z.of_nat (length r') + 1) -> getr regs 6 = w64 (Z.of_nat (length r') + 2) ->
getr regs 20 = w64 1 -> getr regs 13 = w64 (c5b_ksx kd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0x218) ->
0 < c - 1 -> w6bb_inp W memc R F c (b :: r') ->
SRr rsegs W (cfg_at rsegs W6BB_D5 regs memc mdc)
(c5b_apost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd (c + 1)
  (Z.of_nat (length (firstn (Z.to_nat (bv_unsigned b mod 32)) r'))) (Z.of_nat (length r'))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F c kd b r' HJ HR16 HRsp HRlo HF4 HFc HF32
  H9 H27 H18 H16 H22 H6 H20 H13 V110 Hc1 Hin.
pose proof LAWS as HL. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _ & _ & _ & _).
unfold T_SEG_STK, ASTACK in HRlo.
destruct Hin as (Hg & Hra & Hc0 & Hc63 & Ham & _ & Hdis).
assert (HLr : Z.of_nat (length (b :: r')) = Z.of_nat (length r') + 1) by (cbn [length]; lia).
set (n := bv_unsigned b) in *. set (L := Z.of_nat (length r')) in *.
assert (HLeq : L = Z.of_nat (length r')) by reflexivity. clearbody L.
rewrite HLr in Hra, Hc63, Ham, Hdis.
assert (Hn : 0 <= n < 256) by apply Cursor.byte_range.
assert (HcL : c + L + 1 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (HL0 : 0 <= L) by lia.
assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 n).
{ destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
assert (Hcd : c + 1 <= R + 0x110 \/ R + 0x118 <= c).
{ destruct (Hdis c ltac:(lia)) as (_ & D & _). lia. }
assert (U9 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 9) = R) by (apply (c5b_ureg regs _ 9 9%bv R eq_refl H9); lia).
assert (U27 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 27) = SHADOW_OFF)
  by (apply (c5b_ureg regs _ 27 27%bv _ eq_refl H27); unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 22) = L + 1) by (apply (c5b_ureg regs _ 22 22%bv _ eq_refl H22); lia).
assert (U6 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 6) = L + 2) by (apply (c5b_ureg regs _ 6 6%bv _ eq_refl H6); lia).
assert (U18 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 18) = c) by (apply (c5b_ureg regs _ 18 18%bv _ eq_refl H18); lia).
assert (U16 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 16) = c - 1) by (apply (c5b_ureg regs _ 16 16%bv _ eq_refl H16); lia).
assert (U20 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 20) = 1) by (apply (c5b_ureg regs _ 20 20%bv _ eq_refl H20); lia).
assert (U13 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 13) = c5b_ksx kd)
  by (apply (c5b_ureg regs _ 13 13%bv _ eq_refl H13); apply c5b_ksx_range).
assert (U32 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 32) = F) by (exact (c5b_ux regs (c5b_extA F n) 0 F eq_refl ltac:(lia))).
assert (U33 : bv_unsigned (ew (Ereg regs (c5b_extA F n)) 33) = n) by (exact (c5b_ux regs (c5b_extA F n) 1 n eq_refl ltac:(lia))).
assert (HS : st_ok rsegs (Ereg regs (c5b_extA F n)) c5b_ssA1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D5) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rm_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0x110 8 (SOff 32 0x218) (F + 0x218)); [| cbn; lia | cbn; lia | exact V110].
      cbn [sv_denot]. rewrite U32. reflexivity.
    + apply (rm_ro_region rsegs _ (w_H W) memc 18%nat c); [exact U18 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ c 0 1 (SOff 33 0) n); [| cbn; lia | cbn; lia | exact Hm0].
      cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c5b_rA, c5b_rI.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18.
    split; [split; [lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias c5b_fA1 atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold C5B_RLO, C5B_FHI, SHADOW_OFF in *.
    repeat match goal with
    | |- True => exact I
    | |- afact_ok _ _ _ /\ _ => split
    | |- afact_ok _ _ _ => eapply c5b_af; [eassumption | lia | first [apply c5b_mod0 | (change (2 ^ 4) with 16; assumption)
                                                              | (change (2 ^ 5) with 32; assumption)] | lia]
    end. }
assert (SHOK : sh_ok rsegs c5b_Bx [] (Ereg regs (c5b_extA F n)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (c5b_extA F n)) (Ereg regs (c5b_extA F n))) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (False : Prop) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 W6BB_D5) with (Z_to_bv 64 W6BB_D5).
(* 0x8113c .. the branch on n at 0x81174: T1 (decided), the check of s2 *)
aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY.
{ apply (obl_of_range rsegs (w_H W) memc _ c5b_Bx _ _ c (L + 1) Hra).
  - unfold c5b_Bx. apply c5b_U; [exact U27 | unfold SHADOW_OFF; lia].
  - rewrite (c5b_U _ 18 c U18) by lia. lia.
  - rewrite (c5b_U _ 18 c U18) by lia. lia. }
{ c5b_awrA. }
c5b_keepA KE.
pose proof (Z.mod_pos_bound n 32 ltac:(lia)) as Hn32.
srr_branch_tok w6bb_tbl_ok HS SHOK c5b_Bspan.
- (* n mod 32 < |r'|: m = n mod 32 *)
  let E' := c5b_env HS in
  assert (V33 : bv_unsigned (ew E' 33) = n) by (rewrite ?ew_ewset_other by lia; exact U33);
  assert (V6 : bv_unsigned (ew E' 6) = L + 2) by (rewrite ?ew_ewset_other by lia; exact U6);
  assert (V9 : bv_unsigned (ew E' 9) = R) by (rewrite ?ew_ewset_other by lia; exact U9);
  assert (V16 : bv_unsigned (ew E' 16) = c - 1) by (rewrite ?ew_ewset_other by lia; exact U16);
  assert (V32 : bv_unsigned (ew E' 32) = F) by (rewrite ?ew_ewset_other by lia; exact U32);
  assert (V13 : bv_unsigned (ew E' 13) = c5b_ksx kd) by (rewrite ?ew_ewset_other by lia; exact U13);
  assert (A31 : U E' (SAlu ALU_AND (SOff 33 0) (SLit 31)) = n mod 32)
    by (apply c5b_U_and31; [apply c5b_U; [exact V33 | lia] | exact Hn]).
  rewrite branch_ltu_U, A31, (c5b_Uoff _ 6 (L + 2) (-2) V6) in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Em : Z.of_nat (length (firstn (Z.to_nat (n mod 32)) r')) = n mod 32) by (rewrite length_firstn; lia).
  rewrite Em.
  (* 0x8117c .. T2 at 0x81180 *)
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY; [c5b_awrA|].
  c5b_keepA KE.
  srr_branch_tok w6bb_tbl_ok HS SHOK c5b_Bspan.
  + aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY; [c5b_awrA|].
    c5b_keepA KE.
    eapply (c5b_A_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd (c + 1) (n mod 32) L
      _ _ _ _ HS).
    * reflexivity.
    * vm_compute. reflexivity.
    * exact HJ.
    * c5b_kio.
    * eapply (regs_kept_of_st_ok rsegs _ _ _ regs (c5b_extA F n) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * c5b_regv HS (1%bv : bv 5). reflexivity.
    * c5b_regv HS (10%bv : bv 5). apply c5b_den. apply (c5b_Uoff _ 32 F 0x218 V32). lia.
    * c5b_regv HS (11%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 16 (c - 1) 2 V16) by lia. lia.
    * c5b_regv HS (12%bv : bv 5). apply c5b_den.
      rewrite (c5b_U_add _ _ _ _ _ A31 (U_lit _ 0 ltac:(lia))) by lia. lia.
    * c5b_regv HS (18%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 16 (c - 1) 2 V16) by lia. lia.
    * c5b_regv HS (20%bv : bv 5). apply c5b_den. apply (c5b_Uoff _ 32 F 0x218 V32). lia.
    * c5b_regv HS (22%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 6 (L + 2) (-2) V6) by lia. lia.
    * c5b_regv HS (24%bv : bv 5). apply c5b_den. exact A31.
    * c5b_regv HS (26%bv : bv 5). apply c5b_den. apply (c5b_U _ 13 (c5b_ksx kd) V13). apply c5b_ksx_range.
    * intros a Ha. apply KE; [exact Ha | intros bot; exact bot].
  + exfalso.
    c5b_t2_refute HS (c + 1) (n mod 32)
      ltac:(rewrite (c5b_Uoff _ 16 (c - 1) 2 V16) by lia; lia) ltac:(exact A31).
- (* n mod 32 >= |r'|: m = |r'| *)
  let E' := c5b_env HS in
  assert (V33 : bv_unsigned (ew E' 33) = n) by (rewrite ?ew_ewset_other by lia; exact U33);
  assert (V6 : bv_unsigned (ew E' 6) = L + 2) by (rewrite ?ew_ewset_other by lia; exact U6);
  assert (V9 : bv_unsigned (ew E' 9) = R) by (rewrite ?ew_ewset_other by lia; exact U9);
  assert (V16 : bv_unsigned (ew E' 16) = c - 1) by (rewrite ?ew_ewset_other by lia; exact U16);
  assert (V32 : bv_unsigned (ew E' 32) = F) by (rewrite ?ew_ewset_other by lia; exact U32);
  assert (V13 : bv_unsigned (ew E' 13) = c5b_ksx kd) by (rewrite ?ew_ewset_other by lia; exact U13);
  assert (A31 : U E' (SAlu ALU_AND (SOff 33 0) (SLit 31)) = n mod 32)
    by (apply c5b_U_and31; [apply c5b_U; [exact V33 | lia] | exact Hn]).
  rewrite branch_ltu_U, A31, (c5b_Uoff _ 6 (L + 2) (-2) V6) in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Em : Z.of_nat (length (firstn (Z.to_nat (n mod 32)) r')) = L) by (rewrite length_firstn; lia).
  rewrite Em.
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY; [c5b_awrA|].
  c5b_keepA KE.
  srr_branch_tok w6bb_tbl_ok HS SHOK c5b_Bspan.
  + aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY; [c5b_awrA|].
    c5b_keepA KE.
    eapply (c5b_A_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd (c + 1) L L _ _ _ _ HS).
    * reflexivity.
    * vm_compute. reflexivity.
    * exact HJ.
    * c5b_kio.
    * eapply (regs_kept_of_st_ok rsegs _ _ _ regs (c5b_extA F n) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * c5b_regv HS (1%bv : bv 5). reflexivity.
    * c5b_regv HS (10%bv : bv 5). apply c5b_den. apply (c5b_Uoff _ 32 F 0x218 V32). lia.
    * c5b_regv HS (11%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 16 (c - 1) 2 V16) by lia. lia.
    * c5b_regv HS (12%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 6 (L + 2) (-2) V6) by lia. lia.
    * c5b_regv HS (18%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 16 (c - 1) 2 V16) by lia. lia.
    * c5b_regv HS (20%bv : bv 5). apply c5b_den. apply (c5b_Uoff _ 32 F 0x218 V32). lia.
    * c5b_regv HS (22%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 6 (L + 2) (-2) V6) by lia. lia.
    * c5b_regv HS (24%bv : bv 5). apply c5b_den. rewrite (c5b_Uoff _ 6 (L + 2) (-2) V6) by lia. lia.
    * c5b_regv HS (26%bv : bv 5). apply c5b_den. apply (c5b_U _ 13 (c5b_ksx kd) V13). apply c5b_ksx_range.
    * intros a Ha. apply KE; [exact Ha | intros bot; exact bot].
  + exfalso.
    c5b_t2_refute HS (c + 1) L
      ltac:(rewrite (c5b_Uoff _ 16 (c - 1) 2 V16) by lia; lia)
      ltac:(rewrite (c5b_Uoff _ 6 (L + 2) (-2) V6) by lia; lia).
Qed.

(* ---- block A, no byte left ---- *)
Lemma c5b_A0 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F c kd,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
R mod 16 = 0 -> R + 0x200 <= sp0 -> sp0 - STK <= R - T_SEG_STK -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
F mod 32 = 0 ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 c -> getr regs 22 = w64 0 ->
getr regs 13 = w64 (c5b_ksx kd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0x218) ->
0 < c - 1 -> c <= 2 ^ 47 - 1 ->
SRr rsegs W (cfg_at rsegs W6BB_D5 regs memc mdc)
(c5b_apost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd c 0 0).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F c kd HJ HR16 HRsp HRlo HF4 HFc HF32
  H9 H27 H18 H22 H13 V110 Hc1 Hc47.
pose proof LAWS as HL. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _ & _ & _ & _).
unfold T_SEG_STK, ASTACK in HRlo.
assert (U9 : bv_unsigned (ew (Ereg regs (c5b_extA F 0)) 9) = R) by (apply (c5b_ureg regs _ 9 9%bv R eq_refl H9); lia).
assert (U27 : bv_unsigned (ew (Ereg regs (c5b_extA F 0)) 27) = SHADOW_OFF)
  by (apply (c5b_ureg regs _ 27 27%bv _ eq_refl H27); unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew (Ereg regs (c5b_extA F 0)) 18) = c) by (apply (c5b_ureg regs _ 18 18%bv _ eq_refl H18); lia).
assert (U13 : bv_unsigned (ew (Ereg regs (c5b_extA F 0)) 13) = c5b_ksx kd)
  by (apply (c5b_ureg regs _ 13 13%bv _ eq_refl H13); apply c5b_ksx_range).
assert (U32 : bv_unsigned (ew (Ereg regs (c5b_extA F 0)) 32) = F) by (exact (c5b_ux regs (c5b_extA F 0) 0 F eq_refl ltac:(lia))).
assert (HS0 : st_ok rsegs (Ereg regs (c5b_extA F 0)) c5b_ssA0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D5) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rm_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x110 8 (SOff 32 0x218) (F + 0x218)); [| cbn; lia | cbn; lia | exact V110].
    cbn [sv_denot]. rewrite U32. reflexivity.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias c5b_fA0 atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold C5B_RLO, C5B_FHI, SHADOW_OFF in *.
    repeat match goal with
    | |- True => exact I
    | |- afact_ok _ _ _ /\ _ => split
    | |- afact_ok _ _ _ => eapply c5b_af; [eassumption | lia | first [apply c5b_mod0 | (change (2 ^ 4) with 16; assumption)
                                                              | (change (2 ^ 5) with 32; assumption)] | lia]
    end. }
pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H22; reflexivity)) as HS.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts c5b_ssA0] in HS.
assert (SHOK : sh_ok rsegs c5b_Bx [] (Ereg regs (c5b_extA F 0)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (c5b_extA F 0)) (Ereg regs (c5b_extA F 0))) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (False : Prop) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 W6BB_D5) with (Z_to_bv 64 W6BB_D5).
(* 0x8113c .. T2 at 0x81180 (beqz s6 and the branch on n decided on the literal 0) *)
aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY; [c5b_awrA|].
c5b_keepA KE.
let E' := c5b_env HS in
assert (V18 : bv_unsigned (ew E' 18) = c) by (rewrite ?ew_ewset_other by lia; exact U18);
assert (V9 : bv_unsigned (ew E' 9) = R) by (rewrite ?ew_ewset_other by lia; exact U9);
assert (V32 : bv_unsigned (ew E' 32) = F) by (rewrite ?ew_ewset_other by lia; exact U32);
assert (V13 : bv_unsigned (ew E' 13) = c5b_ksx kd) by (rewrite ?ew_ewset_other by lia; exact U13).
srr_branch_tok w6bb_tbl_ok HS SHOK c5b_Bspan.
- aj_run_to_tok w6bb_tbl_ok HS HJ SHOK c5b_Bspan W6BB_MEMCPY; [c5b_awrA|].
  c5b_keepA KE.
  eapply (c5b_A_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F kd c 0 0 _ _ _ _ HS).
  + reflexivity.
  + vm_compute. reflexivity.
  + exact HJ.
  + c5b_kio.
  + eapply (regs_kept_of_st_ok rsegs _ _ _ regs (c5b_extA F 0) (w_H W) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + c5b_regv HS (1%bv : bv 5). reflexivity.
  + c5b_regv HS (10%bv : bv 5). apply c5b_den. apply (c5b_Uoff _ 32 F 0x218 V32). lia.
  + c5b_regv HS (11%bv : bv 5). apply c5b_den. apply (c5b_U _ 18 c V18). lia.
  + c5b_regv HS (12%bv : bv 5). reflexivity.
  + c5b_regv HS (18%bv : bv 5). apply c5b_den. apply (c5b_U _ 18 c V18). lia.
  + c5b_regv HS (20%bv : bv 5). apply c5b_den. apply (c5b_Uoff _ 32 F 0x218 V32). lia.
  + c5b_regv HS (22%bv : bv 5). reflexivity.
  + c5b_regv HS (24%bv : bv 5). reflexivity.
  + c5b_regv HS (26%bv : bv 5). apply c5b_den. apply (c5b_U _ 13 (c5b_ksx kd) V13). apply c5b_ksx_range.
  + intros a Ha. apply KE; [exact Ha | intros bot; exact bot].
- exfalso.
  c5b_t2_refute HS c 0 ltac:(apply (c5b_U _ 18 c V18); lia) ltac:(apply U_lit; lia).
Qed.

(* ---- the leaf of block B ---- *)
Lemma c5b_B_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (clob : list (bv 5)) (Wr : Z -> Prop) (Rr : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
  E ss ms md pc,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
Rr W (ms_regs ms) (ms_mem ms) ->
SRr rsegs W (mkCfg ms md)
  (rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr Rr).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs clob Wr Rr E ss ms md pc
  HS Hrv Hpc HJ Hio Hk Hm HR.
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hk|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split; [exact Hio|]. split; [apply mo_le_refl; exact MTL|]. split; [exact Hm | exact HR].
Qed.

Lemma c5b_aview0 : forall (H : word -> bool) mem a, mbyte rsegs (mrestrict H mem) a = Some (Z_to_bv 8 0) ->
  aview rsegs H mem a = Some 0.
Proof. intros H mem a Hm. unfold aview. rewrite Hm. reflexivity. Qed.
Lemma c5b_mb0 : forall (H : word -> bool) mem a, aview rsegs H mem a = Some 0 ->
  mbyte rsegs (mrestrict H mem) a = Some (Z_to_bv 8 0).
Proof.
intros H mem a Ha. unfold aview in Ha.
destruct (mbyte rsegs (mrestrict H mem) a) as [bb|] eqn:Eb; [|discriminate Ha].
cbn [option_map] in Ha. injection Ha as Ha. f_equal. rewrite <- Ha. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma c5b_map_zeros : forall n, map (fun x : byte => bv_unsigned x) (zeros n) = repeat 0 n.
Proof.
induction n as [|n IH]; [reflexivity|].
unfold zeros in *. cbn [repeat map]. rewrite IH. unfold NUL. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* e62's 104 bytes at J, from the header values, the copied bytes and the zeros after them *)
Lemma c5b_eJ : forall (H : word -> bool) mem F m sz (p : list byte),
  m = Z.of_nat (length p) -> (length p <= 31)%nat ->
  val_mem rsegs (mrestrict H mem) (F + 0x210) 4 8 ->
  val_mem rsegs (mrestrict H mem) (F + 0x214) 4 sz ->
  rm_bytes rsegs H mem (F + 0x218) p ->
  (forall a, F + 0x218 + m <= a < F + 0x278 -> mbyte rsegs (mrestrict H mem) a = Some (Z_to_bv 8 0)) ->
  garr8 rsegs (mrestrict H mem) (F + 0x210) (u8s (le32 8 ++ le32 sz ++ p ++ zeros (96 - length p))).
Proof.
intros H mem F m sz p Hm Hp V0 V4 Hbs Hz.
rewrite !map_app, c5b_map_zeros.
apply (proj2 (garr8_app rsegs _ _ _ _)). split;
  [exact (rm_bytes_of_val rsegs H mem (F + 0x210) 4%nat 8 V0)|].
rewrite length_map, length_le32. replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia.
apply (proj2 (garr8_app rsegs _ _ _ _)). split;
  [exact (rm_bytes_of_val rsegs H mem (F + 0x214) 4%nat sz V4)|].
rewrite length_map, length_le32. replace (F + 0x214 + Z.of_nat 4) with (F + 0x218) by lia.
apply (proj2 (garr8_app rsegs _ _ _ _)). split; [exact Hbs|].
rewrite length_map. replace (F + 0x218 + Z.of_nat (length p)) with (F + 0x218 + m) by lia.
apply garr8_zeros. intros a Ha. apply Hz. lia.
Qed.

(* the write rights of block B's regions: e62's header and the NUL's byte lie in the frame (4, pos) *)
Ltac c5b_awrB W32v W33v posv HFav Hownv offv :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat posv 0x210);
    [ reflexivity | rewrite W32v, <- HFav; reflexivity | exact Hownv
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  eapply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 33%nat posv offv);
    [ reflexivity | rewrite W33v, <- HFav; lia | exact Hownv
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  apply awr_ok_nil.
(* the frame of a block-B run: its windows are e62's header and the NUL's byte *)
Ltac c5b_keepB KE W32v W33v Fv mv :=
  lazymatch goal with HFr : frame_of ?Ex _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let HW := fresh "HW" in
    assert (HW : forall a k lo hi, In (k, lo, hi) [(32%nat, 0, 8); (33%nat, 0, 1)] ->
      bv_unsigned (ew Ex k) + lo <= a < bv_unsigned (ew Ex k) + hi ->
      (Fv + 0x210 <= a < Fv + 0x218) \/ (Fv + 0x218 + mv <= a < Fv + 0x218 + mv + 1))
      by (let a0 := fresh "a" in let k0 := fresh "k" in let lo0 := fresh "lo" in let hi0 := fresh "hi" in
          let Hin0 := fresh "Hin" in let Ha0 := fresh "Ha" in
          intros a0 k0 lo0 hi0 Hin0 Ha0; cbn [In] in Hin0;
          destruct Hin0 as [Hin0|[Hin0|[]]]; injection Hin0 as <- <- <-;
          [rewrite W32v in Ha0; left | rewrite W33v in Ha0; right]; lia);
    c5b_keep KE [(32%nat, 0, 8); (33%nat, 0, 1)]
      (fun a : Z => (Fv + 0x210 <= a < Fv + 0x218) \/ (Fv + 0x218 + mv <= a < Fv + 0x218 + mv + 1)) HW
  end.

(* ---- the call and block B: 0x5116c .. J ---- *)
Lemma c5b_CB : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos x m nl kd pp : Z) (p : list byte),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
R mod 16 = 0 -> R + 0x200 <= sp0 -> sp0 - STK <= R - T_SEG_STK ->
In (4, pos) own -> F = frame_addr lyc 4 pos -> F mod 32 = 0 -> in_app F 1024 -> F + 1024 <= alloc_ceiling ->
4096 <= F ->
getr regs 1 = w64 C5B_RET -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
getr regs 10 = w64 (F + 0x218) -> getr regs 11 = w64 x -> getr regs 12 = w64 m ->
getr regs 18 = w64 x -> getr regs 20 = w64 (F + 0x218) -> getr regs 22 = w64 nl -> getr regs 24 = w64 m ->
getr regs 26 = w64 (c5b_ksx kd) ->
0 <= kd < 256 -> m = Z.of_nat (length p) -> (length p <= 31)%nat -> 0 <= nl < 2 ^ 47 -> m <= nl ->
0 < x -> x + m <= 2 ^ 47 - 1 -> amem_range x m -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
rm_bytes rsegs (w_H W) memc x p ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF x m ->
(0 < m -> shadow_hull_vis (aview rsegs (w_H W) memc) x m) ->
(forall a, x <= a < x + m -> ~ (R - T_SEG_STK <= a < R) /\ ~ (F + 0x20 <= a < F + 0x278)) ->
(forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x210 + i) = Some (Z_to_bv 8 0)) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 ->
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (2 ^ 64 - 1 - (F + 0x218)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (pp + 0x4000) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6BB_MEMCPY) memc (seg_rom rsegs)) mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6BB_J
  (rl_caller_saved ++ c5b_clobB) (c5b_wrB R F)
  (fun W2 regs2 mem2 =>
   getr regs2 22 = w64 (pp + 0x4000) /\ getr regs2 15 = w64 pp /\
   getr regs2 13 = w64 (x + m) /\ getr regs2 6 = w64 (nl - m) /\
   garr8 rsegs (mrestrict (w_H W2) mem2) (F + 0x210)
     (u8s (le32 8 ++ le32 (m + (if kd <? 128 then 1 else 0)) ++ p ++ zeros (96 - length p))))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos x m nl kd pp p
  HJ HR16 HRsp HRlo Hown HFa HF32 HFapp HFc HF4 H1 H2 H3 H4 H9 H27 H10 H11 H12 H18 H20 H22 H24 H26
  Hkd Hm Hp Hnl Hmnl Hx0 Hxm Hamx Hpp0 Hpp1 Hbs Hrax Hhux Hdisx HE0 HraE HhuE Vf0 V130 V140 V158.
pose proof LAWS as HL. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _ & _ & _ & _).
destruct (rl_fbounds F HF32 HFapp) as (_ & _ & _ & _ & _ & Hamf).
unfold T_SEG_STK, ASTACK in HRlo.
assert (Hm0 : 0 <= m <= 31) by lia.
assert (HspR : spZ regs = R) by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
(* ---- the memcpy ---- *)
eapply SRr_bind.
{ apply (rl_intrin_at B LAWS OCpy W6BB_MEMCPY AMEMCPY W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k
    (F + 0x218) x m (R - sp0) (w64 C5B_RET) HJ H10 H11 H12).
  - lia.
  - lia.
  - lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + apply (rl_awr_fobj STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own pos a Hown).
      rewrite <- HFa. lia.
    + unfold ESTACK. lia.
  - apply (Hamf 0x218 m); lia.
  - eapply ra_sub; [exact HraE | lia | lia].
  - intros Hmp. apply (rm_hull_sub (aview rsegs (w_H W) memc) (F + 0x210) 104); [exact HhuE | lia | lia | lia].
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - pose proof (proj1 (rm_bytes_aview rsegs (w_H W) memc x p) Hbs (Z.to_nat (a - x)) ltac:(lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. replace (x + (a - x)) with a in Hv by lia. rewrite Hv. discriminate.
      - rewrite HspR. destruct (Hdisx a Ha) as [D1 _].
        unfold T_SEG_STK, ASTACK in D1. unfold ESTACK. lia. }
    split.
    { destruct (Z_le_gt_dec (F + 0x218 + m) x) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (x + m) (F + 0x218)) as [Y|Y]; [right; exact Y|].
      exfalso. destruct (Z.eq_dec m 0) as [->|Hne]; [lia|].
      destruct (Hdisx (Z.max x (F + 0x218)) ltac:(lia)) as [_ D2]. apply D2. lia. }
    split; [exact Hamx|]. split; [exact Hrax | exact Hhux]. }
cbv beta. intros W1 c1 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & Ha02 & Heff & Hfr).
pose proof HJ2 as (HAR2 & _).
destruct (al_frames _ _ LAWS lyc Sc W mem2 md2 4 pos HAR2 Hin4) as (_ & _ & HFpres2 & _).
rewrite <- HFa in HFpres2. change (fs_frame_bytes 4) with 1024 in HFpres2.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x218 <= a < F + 0x218 + m) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha D1 D2. apply Hfr; [exact Ha | exact D2 | unfold ESTACK in *; lia]. }
assert (KBsh : forall y, 0 <= y < 2 ^ 47 ->
  aview rsegs (w_H W) mem2 (shadow_of_addr SHADOW_OFF y) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF y)).
{ intros y Hy. pose proof (rm_shadow_band y ltac:(unfold kHighMemEnd; lia)) as Hb.
  pose proof (rm_shadow_not_app y F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Hna.
  apply KB; unfold kLowMemEnd, kHighMemBeg, ESTACK in *; lia. }
assert (E9 : getr regs2 9 = w64 R) by exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) H9).
assert (E27 : getr regs2 27 = w64 SHADOW_OFF) by exact (eq_trans (HP2 27 ltac:(unfold acallee_saved; lia)) H27).
assert (E18 : getr regs2 18 = w64 x) by exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) H18).
assert (E20 : getr regs2 20 = w64 (F + 0x218)) by exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) H20).
assert (E22 : getr regs2 22 = w64 nl) by exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) H22).
assert (E24 : getr regs2 24 = w64 m) by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) H24).
assert (E26 : getr regs2 26 = w64 (c5b_ksx kd)) by exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) H26).
assert (W9 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 9) = R)
  by (apply (c5b_ureg regs2 _ 9 9%bv R eq_refl E9); lia).
assert (W27 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 27) = SHADOW_OFF)
  by (apply (c5b_ureg regs2 _ 27 27%bv _ eq_refl E27); unfold SHADOW_OFF; lia).
assert (W18 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 18) = x)
  by (apply (c5b_ureg regs2 _ 18 18%bv x eq_refl E18); lia).
assert (W20 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 20) = F + 0x218)
  by (apply (c5b_ureg regs2 _ 20 20%bv _ eq_refl E20); lia).
assert (W22 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 22) = nl)
  by (apply (c5b_ureg regs2 _ 22 22%bv nl eq_refl E22); lia).
assert (W24 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 24) = m)
  by (apply (c5b_ureg regs2 _ 24 24%bv m eq_refl E24); lia).
assert (E26w : ew (Ereg regs2 (c5b_extB F m pp)) 26 = w64 (c5b_ksx kd))
  by (rewrite (ew_Ereg_nat regs2 (c5b_extB F m pp) 26 26%bv eq_refl); exact E26).
assert (W32 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 32) = F + 0x210)
  by (exact (c5b_ux regs2 (c5b_extB F m pp) 0 (F + 0x210) eq_refl ltac:(lia))).
assert (W33 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 33) = F + 0x218 + m)
  by (exact (c5b_ux regs2 (c5b_extB F m pp) 1 (F + 0x218 + m) eq_refl ltac:(lia))).
assert (W34 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 34) = 2 ^ 64 - 1 - (F + 0x218))
  by (exact (c5b_ux regs2 (c5b_extB F m pp) 2 (2 ^ 64 - 1 - (F + 0x218)) eq_refl ltac:(lia))).
assert (W35 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 35) = pp + 0x4000)
  by (exact (c5b_ux regs2 (c5b_extB F m pp) 3 (pp + 0x4000) eq_refl ltac:(lia))).
assert (W36 : bv_unsigned (ew (Ereg regs2 (c5b_extB F m pp)) 36) = pp)
  by (exact (c5b_ux regs2 (c5b_extB F m pp) 4 pp eq_refl ltac:(lia))).
(* the cells and e62 at mem2 *)
assert (V2f0 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf0) 8 (2 ^ 64 - 1 - (F + 0x218))).
{ apply (rl_val_kept (w_H W) memc mem2); [|exact Vf0].
  intros j Hj. apply KB; [lia | unfold ESTACK; lia | lia]. }
assert (V2130 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x130) 8 (pp + 0x4000)).
{ apply (rl_val_kept (w_H W) memc mem2); [|exact V130].
  intros j Hj. apply KB; [lia | unfold ESTACK; lia | lia]. }
assert (V2140 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x140) 8 pp).
{ apply (rl_val_kept (w_H W) memc mem2); [|exact V140].
  intros j Hj. apply KB; [lia | unfold ESTACK; lia | lia]. }
assert (V2158 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x158) 8 (F + 0x210)).
{ apply (rl_val_kept (w_H W) memc mem2); [|exact V158].
  intros j Hj. apply KB; [lia | unfold ESTACK; lia | lia]. }
assert (HN0 : aview rsegs (w_H W) mem2 (F + 0x218 + m) = Some 0).
{ rewrite (KB (F + 0x218 + m) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia)).
  apply c5b_aview0. replace (F + 0x218 + m) with (F + 0x210 + (8 + m)) by lia. apply HE0. lia. }
assert (HVN0 : val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x218 + m + 0) 1 0).
{ rewrite Z.add_0_r. exact (proj1 (rm_aview_val1 rsegs (w_H W) mem2 (F + 0x218 + m) 0 HN0)). }
assert (HBS2 : rm_bytes rsegs (w_H W) mem2 (F + 0x218) p).
{ apply (rm_memcpy_bytes rsegs (w_H W) memc (w_H W) mem2 x (F + 0x218) p Hbs).
  intros i Hi. apply Heff. lia. }
assert (HraE2 : range_addressable (aview rsegs (w_H W) mem2) SHADOW_OFF (F + 0x210) 104).
{ apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem2); [exact HraE|]. intros y Hy. apply KBsh. lia. }
(* the entry state of block B *)
assert (HSB : st_ok rsegs (Ereg regs2 (c5b_extB F m pp)) c5b_ssB
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 C5B_RET) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (rm_ro_region rsegs _ (w_H W) mem2 9%nat R); [exact W9 | lia | lia |].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val rsegs _ _ R 0xf0 8 (SOff 34 0) (2 ^ 64 - 1 - (F + 0x218))); [| cbn; lia | cbn; lia | exact V2f0].
        cbn [sv_denot]. rewrite W34, Z.add_0_r. reflexivity.
      * apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 35 0) (pp + 0x4000)); [| cbn; lia | cbn; lia | exact V2130].
        cbn [sv_denot]. rewrite W35, Z.add_0_r. reflexivity.
      * apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 36 0) pp); [| cbn; lia | cbn; lia | exact V2140].
        cbn [sv_denot]. rewrite W36, Z.add_0_r. reflexivity.
      * apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) (F + 0x210)); [| cbn; lia | cbn; lia | exact V2158].
        cbn [sv_denot]. rewrite W32, Z.add_0_r. reflexivity.
    + apply (rm_rw_region rsegs _ (w_H W) mem2 32%nat (F + 0x210)); [exact W32 | lia | lia | | constructor].
      intros o Ho. exact (proj1 (HFpres2 (F + 0x210 + o) ltac:(lia))).
    + apply (rm_rw_region rsegs _ (w_H W) mem2 33%nat (F + 0x218 + m)); [exact W33 | lia | lia | |].
      * intros o Ho. exact (proj1 (HFpres2 (F + 0x218 + m + o) ltac:(lia))).
      * constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ (F + 0x218 + m) 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HVN0].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c5b_rR, c5b_rE, c5b_rN.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite W9, W32, W33.
    split; [split; [lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; exact I]].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias c5b_fB atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold C5B_RLO, C5B_FHI, C5B_NLO, C5B_NHI, SHADOW_OFF in *.
    repeat match goal with
    | |- True => exact I
    | |- afact_ok _ _ _ /\ _ => split
    | |- afact_ok _ _ _ => eapply c5b_af; [eassumption | lia | first [apply c5b_mod0 | (change (2 ^ 4) with 16; assumption)
                                                              | (change (2 ^ 4) with 16; apply c5b_F16; assumption)] | lia]
    end. }
assert (SHOKB : sh_ok rsegs c5b_Bx c5b_SHB (Ereg regs2 (c5b_extB F m pp)) (mrestrict (w_H W) mem2)).
{ unfold sh_ok, c5b_SHB. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H W) mem2 _ c5b_Bx 32 (F + 0x210) 104 (F + 0x210) 0 8 HraE2);
      [unfold c5b_Bx; apply c5b_U; [exact W27 | unfold SHADOW_OFF; lia] | apply c5b_U; [exact W32 | lia] | lia | lia |].
    intros y Hy. change (Z.min 0 8) with 0 in Hy. change (Z.max 0 8) with 8 in Hy.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range rsegs (w_H W) mem2 _ c5b_Bx 33 (F + 0x210) 104 (F + 0x218 + m) 0 1 HraE2);
      [unfold c5b_Bx; apply c5b_U; [exact W27 | unfold SHADOW_OFF; lia] | apply c5b_U; [exact W33 | lia] | lia | lia |].
    intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
assert (HAE2 : env_agree 32 (Ereg regs2 (c5b_extB F m pp)) (Ereg regs2 (c5b_extB F m pp)))
  by apply env_agree_refl.
assert (KE2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((F + 0x210 <= a < F + 0x218) \/ (F + 0x218 + m <= a < F + 0x218 + m + 1)) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem2 a) by (intros; reflexivity).
assert (HU11 : U (Ereg regs2 (c5b_extB F m pp)) (SAlu ALU_ADD (SOff 20 0) (SOff 24 0)) = F + 0x218 + m).
{ rewrite (c5b_U_add _ (SOff 20 0) (SOff 24 0) (F + 0x218) m
    ltac:(apply (c5b_U _ 20 (F + 0x218) W20); lia) ltac:(apply (c5b_U _ 24 m W24); lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  lia. }
change (w64 C5B_RET) with (Z_to_bv 64 C5B_RET).
(* 0x81198 .. the branch on s10 at 0x8119c *)
aj_run_to_tok w6bb_tbl_ok HSB HJ2 SHOKB c5b_Bspan W6BB_J; [c5b_awrB W32 W33 pos HFa Hown (0x218 + m)|].
c5b_keepB KE2 W32 W33 F m. cbv beta in KE2.
srr_branch_tok w6bb_tbl_ok HSB SHOKB c5b_Bspan.
- (* kd >= 128: no NUL *)
  rewrite (c5b_bltz _ 26 kd E26w Hkd) in Hc. apply Z.leb_le in Hc.
  replace (if kd <? 128 then 1 else 0) with 0 by (destruct (Z.ltb_spec kd 128); [lia | reflexivity]).
  aj_run_to_tok w6bb_tbl_ok HSB HJ2 SHOKB c5b_Bspan W6BB_J; [c5b_awrB W32 W33 pos HFa Hown (0x218 + m)|].
  c5b_keepB KE2 W32 W33 F m. cbv beta in KE2.
  c5b_region HSB 1%nat HRE. c5b_region HSB 2%nat HRN.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (VT : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (F + 0x210 + 0) 4 8) by
      (eapply (c5b_chunk_val _ _ 32%nat (F + 0x210) _ _ _ _ _ 0 4%N (SLit 8) 8 HRE W32);
       [cbn [In]; right; left; reflexivity | apply U_lit; lia | cbn; lia | cbn; lia]);
    assert (VS : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (F + 0x210 + 4) 4 (m + 0)) by
      (eapply (c5b_chunk_val _ _ 32%nat (F + 0x210) _ _ _ _ _ 4 4%N (SOff 24 0) (m + 0) HRE W32);
       [cbn [In]; left; reflexivity | rewrite (c5b_U _ 24 m W24) by lia; lia | cbn; lia | cbn; lia]);
    assert (HNZf : aview rsegs (w_H W) (ms_mem msx) (F + 0x218 + m) = Some 0) by
      (replace (F + 0x218 + m) with (F + 0x218 + m + 0) by lia;
       eapply (rl_chunk0 _ (w_H W) (ms_mem msx) (F + 0x218 + m) 0);
       refine (rl_chunks _ _ 33%nat (F + 0x218 + m) _ _ _ _ _ HRN W33 _ _); cbn [In]; left; reflexivity);
    assert (HZf : forall a, F + 0x218 + m <= a < F + 0x278 ->
      mbyte rsegs (mrestrict (w_H W) (ms_mem msx)) a = Some (Z_to_bv 8 0)) by
      (intros a Ha; apply c5b_mb0; destruct (Z.eq_dec a (F + 0x218 + m)) as [->|Hne]; [exact HNZf|];
       rewrite (KE2 a ltac:(lia) ltac:(lia));
       rewrite (KB a ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia));
       apply c5b_aview0; replace a with (F + 0x210 + (a - (F + 0x210))) by lia; apply HE0; lia);
    assert (HBSf : rm_bytes rsegs (w_H W) (ms_mem msx) (F + 0x218) p) by
      (apply (rm_bytes_kept rsegs (w_H W) mem2 (w_H W) (ms_mem msx) (F + 0x218) p HBS2);
       intros y Hy; apply KE2; lia)
  end.
  rewrite Z.add_0_r in VT. replace (F + 0x210 + 4) with (F + 0x214) in VS by lia.
  eapply c5b_B_leaf.
  + exact HSB.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + exact HJ2.
  + eapply same_io_trans; [exact (same_io_materialized mdc md2 Hsame)|]. c5b_kio.
  + intros rr Hr0 Hn.
    rewrite (regs_kept_of_st_ok rsegs _ _ _ regs2 (c5b_extB F m pp) (w_H W) c5b_clobB HSB
      ltac:(env_agree_chain HAE2) ltac:(vm_compute; reflexivity) rr Hr0
      ltac:(intros X; apply Hn; apply in_or_app; right; exact X)).
    rewrite <- (Z_to_bv_bv_unsigned 5 rr). apply HP2. apply rl_callee; [exact Hr0|].
    intros X; apply Hn; apply in_or_app; left; exact X.
  + intros a Ha Hn. unfold c5b_wrB, ESTACK in Hn. cbv beta in Hn.
    rewrite (KE2 a Ha ltac:(lia)). apply KB; [exact Ha | unfold ESTACK; lia | lia].
  + cbv beta.
    split; [c5b_regv HSB (22%bv : bv 5); apply c5b_den; apply (c5b_U _ 35 (pp + 0x4000) W35); lia|].
    split; [c5b_regv HSB (15%bv : bv 5); apply c5b_den; apply (c5b_U _ 36 pp W36); lia|].
    split; [c5b_regv HSB (13%bv : bv 5); apply c5b_den;
            rewrite (c5b_U_add _ (SOff 18 0) (SOff 24 0) x m ltac:(apply (c5b_U _ 18 x W18); lia)
              ltac:(apply (c5b_U _ 24 m W24); lia) ltac:(lia) ltac:(lia) ltac:(lia)); lia|].
    split; [c5b_regv HSB (6%bv : bv 5); apply c5b_den;
            rewrite (c5b_U_sub _ (SOff 24 0) (SOff 22 0) m nl ltac:(apply (c5b_U _ 24 m W24); lia)
              ltac:(apply (c5b_U _ 22 nl W22); lia) ltac:(lia) ltac:(lia)); reflexivity|].
    exact (c5b_eJ _ _ F m (m + 0) p Hm Hp VT VS HBSf HZf).
- (* kd < 128: T3 (decided) and the NUL at e62.body[m] *)
  rewrite (c5b_bltz _ 26 kd E26w Hkd) in Hc. apply Z.leb_gt in Hc.
  replace (if kd <? 128 then 1 else 0) with 1 by (destruct (Z.ltb_spec kd 128); [reflexivity | lia]).
  aj_run_to_tok w6bb_tbl_ok HSB HJ2 SHOKB c5b_Bspan C5B_NUL; [c5b_awrB W32 W33 pos HFa Hown (0x218 + m)|].
  c5b_keepB KE2 W32 W33 F m. cbv beta in KE2.
  lazymatch type of HSB with
  | st_ok ?segs ?Ex ?ssx (restrict ?Hx ?msx) =>
    assert (HPIN : sv_denot Ex (SOff 33 0) = getr (ms_regs (restrict Hx msx)) (11%bv : bv 5));
    [ rewrite (st_ok_reg segs Ex ssx (restrict Hx msx) (11%bv : bv 5) HSB);
      replace (sr_get (ss_regs ssx) (11%bv : bv 5)) with (SAlu ALU_ADD (SOff 20 0) (SOff 24 0))
        by (vm_compute; reflexivity);
      rewrite (denot_lit_U Ex (SOff 33 0)), (denot_lit_U Ex (SAlu ALU_ADD (SOff 20 0) (SOff 24 0))), HU11;
      f_equal; apply (c5b_U Ex 33 (F + 0x218 + m) W33); lia
    | pose proof (st_ok_pin_sv rsegs Ex ssx (restrict Hx msx) (11%bv : bv 5) (SOff 33 0) HSB eq_refl HPIN) as HS1;
      clear HSB HPIN; rename HS1 into HSB ]
  end.
  aj_run_to_tok w6bb_tbl_ok HSB HJ2 SHOKB c5b_Bspan W6BB_J; [c5b_awrB W32 W33 pos HFa Hown (0x218 + m)|].
  c5b_keepB KE2 W32 W33 F m. cbv beta in KE2.
  c5b_region HSB 1%nat HRE. c5b_region HSB 2%nat HRN.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (VT : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (F + 0x210 + 0) 4 8) by
      (eapply (c5b_chunk_val _ _ 32%nat (F + 0x210) _ _ _ _ _ 0 4%N (SLit 8) 8 HRE W32);
       [cbn [In]; right; left; reflexivity | apply U_lit; lia | cbn; lia | cbn; lia]);
    assert (VS : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (F + 0x210 + 4) 4 (m + 1)) by
      (eapply (c5b_chunk_val _ _ 32%nat (F + 0x210) _ _ _ _ _ 4 4%N (SOff 24 1) (m + 1) HRE W32);
       [cbn [In]; left; reflexivity | rewrite (c5b_Uoff _ 24 m 1 W24) by lia; lia | cbn; lia | cbn; lia]);
    assert (HNZf : aview rsegs (w_H W) (ms_mem msx) (F + 0x218 + m) = Some 0) by
      (replace (F + 0x218 + m) with (F + 0x218 + m + 0) by lia;
       eapply (rl_chunk0 _ (w_H W) (ms_mem msx) (F + 0x218 + m) 0);
       refine (rl_chunks _ _ 33%nat (F + 0x218 + m) _ _ _ _ _ HRN W33 _ _); cbn [In]; left; reflexivity);
    assert (HZf : forall a, F + 0x218 + m <= a < F + 0x278 ->
      mbyte rsegs (mrestrict (w_H W) (ms_mem msx)) a = Some (Z_to_bv 8 0)) by
      (intros a Ha; apply c5b_mb0; destruct (Z.eq_dec a (F + 0x218 + m)) as [->|Hne]; [exact HNZf|];
       rewrite (KE2 a ltac:(lia) ltac:(lia));
       rewrite (KB a ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia));
       apply c5b_aview0; replace a with (F + 0x210 + (a - (F + 0x210))) by lia; apply HE0; lia);
    assert (HBSf : rm_bytes rsegs (w_H W) (ms_mem msx) (F + 0x218) p) by
      (apply (rm_bytes_kept rsegs (w_H W) mem2 (w_H W) (ms_mem msx) (F + 0x218) p HBS2);
       intros y Hy; apply KE2; lia)
  end.
  rewrite Z.add_0_r in VT. replace (F + 0x210 + 4) with (F + 0x214) in VS by lia.
  eapply c5b_B_leaf.
  + exact HSB.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + exact HJ2.
  + eapply same_io_trans; [exact (same_io_materialized mdc md2 Hsame)|]. c5b_kio.
  + intros rr Hr0 Hn.
    rewrite (regs_kept_of_st_ok rsegs _ _ _ regs2 (c5b_extB F m pp) (w_H W) c5b_clobB HSB
      ltac:(env_agree_chain HAE2) ltac:(vm_compute; reflexivity) rr Hr0
      ltac:(intros X; apply Hn; apply in_or_app; right; exact X)).
    rewrite <- (Z_to_bv_bv_unsigned 5 rr). apply HP2. apply rl_callee; [exact Hr0|].
    intros X; apply Hn; apply in_or_app; left; exact X.
  + intros a Ha Hn. unfold c5b_wrB, ESTACK in Hn. cbv beta in Hn.
    rewrite (KE2 a Ha ltac:(lia)). apply KB; [exact Ha | unfold ESTACK; lia | lia].
  + cbv beta.
    split; [c5b_regv HSB (22%bv : bv 5); apply c5b_den; apply (c5b_U _ 35 (pp + 0x4000) W35); lia|].
    split; [c5b_regv HSB (15%bv : bv 5); apply c5b_den; apply (c5b_U _ 36 pp W36); lia|].
    split; [c5b_regv HSB (13%bv : bv 5); apply c5b_den;
            rewrite (c5b_U_add _ (SOff 18 0) (SOff 24 0) x m ltac:(apply (c5b_U _ 18 x W18); lia)
              ltac:(apply (c5b_U _ 24 m W24); lia) ltac:(lia) ltac:(lia) ltac:(lia)); lia|].
    split; [c5b_regv HSB (6%bv : bv 5); apply c5b_den;
            rewrite (c5b_U_sub _ (SOff 24 0) (SOff 22 0) m nl ltac:(apply (c5b_U _ 24 m W24); lia)
              ltac:(apply (c5b_U _ 22 nl W22); lia) ltac:(lia) ltac:(lia)); reflexivity|].
    exact (c5b_eJ _ _ F m (m + 1) p Hm Hp VT VS HBSf HZf).
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem w6bb_c5 : w6bb_c5_stmt B MT.
Proof using MTL AMEMCPY.
unfold w6bb_c5_stmt, w6bb_case_stmt. cbv beta.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx HP Hin _.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & HRom).
unfold w6bb_in in Hin.
destruct Hin as (Hr2 & Hr3 & Hr4 & H9 & H27 & H19 & H18 & H16 & H22 & H6 & H20 & H13 & M48 & Mf0 & M110
  & M130 & M140 & M158 & Hkd & Hpp0 & Hpp1 & HF0 & HFc & HF32 & HFapp & Hez & Hra & Hhull & Hc1 & Hwin).
pose proof Hwin as (Hg & Hrain & Hc0 & Hcb & Ham & Hhull2 & Hdis).
specialize (H13 ltac:(lia)). rewrite c5b_w64_ksx in H13.
pose proof LAWS as HL. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof asan_consts as (Hac & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (Hcmax : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
(* the facts the call block needs at the memory before the call *)
assert (Hshkeep : forall (mem1 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
  forall y, 0 <= y < 2 ^ 47 ->
  aview rsegs (w_H W) mem1 (shadow_of_addr SHADOW_OFF y) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF y)).
{ intros mem1 KM y Hy. pose proof (rm_shadow_band y ltac:(unfold kHighMemEnd; lia)) as Hb.
  apply KM. unfold kLowMemEnd, kHighMemBeg in *. lia. }
unfold cfg_at. change (w64 W6BB_D5) with (Z_to_bv 64 W6BB_D5).
destruct r as [|b1 r1].
- (* ============ no byte left ============ *)
  eapply SRr_bind.
  { apply (c5b_A0 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F c (bv_unsigned b) HJ HR16 HRsp
      ltac:(unfold T_SEG_STK, ASTACK; lia) HF0 HFc HF32 H9 H27 H18 ltac:(cbn [length] in H22; exact H22) H13
      M110 Hc1 ltac:(cbn [length] in Hcmax; lia)). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & Hk1 & P1 & P10 & P11 & P12 & P18
    & P20 & P22 & P24 & P26 & KM1).
  eapply SRr_mono.
  { apply (c5b_CB STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem1 md1 regs1 R F pos c 0 0
      (bv_unsigned b) pp [] HJ1 HR16 HRsp ltac:(unfold T_SEG_STK, ASTACK; lia) Hown HFa HF32 HFapp HFc HF0
      P1 ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact Hr2)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact Hr3)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact Hr4)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact H9)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact H27)
      P10 P11 P12 P18 P20 P22 P24 P26 Hkd eq_refl ltac:(cbn [length]; lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(cbn [length] in Hcmax; lia)
      ltac:(cbn [length] in Ham; unfold amem_range in *; lia) ltac:(lia) Hpp1
      ltac:(apply garr8_nil) ltac:(intros y Hy; lia) ltac:(intros Hq; lia) ltac:(intros a Ha; lia)
      ltac:(intros i Hi; apply c5b_mb0; rewrite (KM1 (F + 0x210 + i) ltac:(lia));
            apply c5b_aview0; apply Hez; lia)
      ltac:(apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem1); [exact Hra|];
            intros y Hy; apply (Hshkeep mem1 KM1); lia)
      ltac:(apply (rm_hull_kept rsegs (w_H W) memc (w_H W) mem1); [exact Hhull|];
            intros s Hs Hns;
            pose proof (c5b_hull_bnd (F + 0x210) 104 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hsb;
            unfold kHighMemBeg in Hsb;
            rewrite (KM1 s ltac:(lia)); exact Hns)
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact Mf0])
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact M130])
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact M140])
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact M158])). }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hk2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
  destruct HR2 as (R22 & R15 & R13 & R6 & RB).
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|].
  split; [intros rr Hr0 Hn; rewrite (Hk2 rr Hr0 ltac:(intros X; apply Hn; unfold w6bb_clob, rl_caller_saved,
            c5b_clobB in X |- *; cbn [app In] in X |- *; tauto));
          apply Hk1; [exact Hr0 | intros X; apply Hn; unfold w6bb_clob, c5b_clobA in X |- *; cbn [In] in X |- *; tauto]|].
  split; [exact Hf2|]. split; [exact Hp2|].
  split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
  split; [exact Hmo2|].
  split; [intros a Ha Hn; unfold w6bb_wr in Hn; cbv beta in Hn; unfold T_SEG_STK, ASTACK in Hn;
          rewrite (Hm2 a Ha ltac:(unfold c5b_wrB; cbv beta; unfold ESTACK; lia));
          apply KM1; exact Ha|].
  unfold w6bb_J_R. rewrite (c5b_build b [] HP). cbn [fst snd fuzz_u8].
  rewrite firstn_nil, skipn_nil.
  split; [exact R22|].
  split; [exact R15|].
  split; [rewrite R13; unfold w64; f_equal; cbn [length]; lia|].
  split; [rewrite R6; unfold w64; f_equal; cbn [length]; lia|].
  rewrite (c5b_ent [] (negb (Z.testbit (bv_unsigned b) 7)) ltac:(cbn [length]; lia)).
  rewrite c5b_bit7 by lia. rewrite <- Z.ltb_antisym. exact RB.
- (* ============ a byte ============ *)
  pose proof (Cursor.byte_range b1) as Hb1r.
  set (kk := Z.to_nat (bv_unsigned b1 mod 32)) in *.
  assert (Hkk : Z.of_nat kk <= 31) by (unfold kk; pose proof (Z.mod_pos_bound (bv_unsigned b1) 32 ltac:(lia)); lia).
  assert (Hpl : (length (firstn kk r1) <= 31)%nat) by (rewrite length_firstn; lia).
  assert (Hplr : (length (firstn kk r1) <= length r1)%nat) by (rewrite length_firstn; lia).
  assert (Hbs : rm_bytes rsegs (w_H W) memc (c + 1) (firstn kk r1)).
  { assert (Hb0 : rm_bytes rsegs (w_H W) memc c ([b1] ++ r1)) by exact Hg.
    apply (proj1 (rm_bytes_app rsegs (w_H W) memc c [b1] r1)) in Hb0.
    destruct Hb0 as [_ Hb2]. cbn [length] in Hb2. replace (c + Z.of_nat 1) with (c + 1) in Hb2 by lia.
    rewrite <- (firstn_skipn kk r1) in Hb2.
    exact (proj1 (proj1 (rm_bytes_app rsegs (w_H W) memc (c + 1) (firstn kk r1) (skipn kk r1)) Hb2)). }
  eapply SRr_bind.
  { apply (c5b_A1 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F c (bv_unsigned b) b1 r1 HJ HR16 HRsp
      ltac:(unfold T_SEG_STK, ASTACK; lia) HF0 HFc HF32 H9 H27 H18 H16
      ltac:(cbn [length] in H22; rewrite H22; unfold w64; f_equal; lia)
      ltac:(cbn [length] in H6; rewrite H6; unfold w64; f_equal; lia)
      H20 H13 M110 Hc1 Hwin). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & Hk1 & P1 & P10 & P11 & P12 & P18
    & P20 & P22 & P24 & P26 & KM1).
  eapply SRr_mono.
  { apply (c5b_CB STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem1 md1 regs1 R F pos (c + 1)
      (Z.of_nat (length (firstn kk r1))) (Z.of_nat (length r1)) (bv_unsigned b) pp (firstn kk r1)
      HJ1 HR16 HRsp ltac:(unfold T_SEG_STK, ASTACK; lia) Hown HFa HF32 HFapp HFc HF0
      P1 ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact Hr2)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact Hr3)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact Hr4)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact H9)
      ltac:(rewrite Hk1 by (first [apply c5b_nz | apply c5b_notin]; reflexivity); exact H27)
      P10 P11 P12 P18 P20 P22 P24 P26 Hkd eq_refl Hpl ltac:(cbn [length] in Hcmax; lia) ltac:(lia)
      ltac:(lia) ltac:(cbn [length] in Hcmax; lia)
      ltac:(cbn [length] in Ham; unfold amem_range in *; lia) ltac:(lia) Hpp1
      ltac:(apply (rm_bytes_kept rsegs (w_H W) memc (w_H W) mem1); [exact Hbs|];
            intros y Hy; apply KM1; cbn [length] in Hcmax; lia)
      ltac:(apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem1);
            [eapply ra_sub; [exact Hrain | lia | cbn [length]; lia]|];
            intros y Hy; apply (Hshkeep mem1 KM1); cbn [length] in Hcmax; lia)
      ltac:(intros Hq; apply (rm_hull_kept rsegs (w_H W) memc (w_H W) mem1);
            [apply (rm_hull_sub (aview rsegs (w_H W) memc) c (Z.of_nat (length (b1 :: r1))));
             [apply Hhull2; cbn [length]; lia | lia | cbn [length]; lia | lia]|];
            intros s Hs Hns;
            pose proof (c5b_hull_bnd (c + 1) (Z.of_nat (length (firstn kk r1))) s
              ltac:(lia) ltac:(cbn [length] in Hcmax; lia) ltac:(lia) Hs) as Hsb;
            unfold kHighMemBeg in Hsb;
            rewrite (KM1 s ltac:(lia)); exact Hns)
      ltac:(intros a Ha; pose proof (Hdis a ltac:(cbn [length]; lia)) as Hq;
            unfold T_SEG_STK, ASTACK in *; split; lia)
      ltac:(intros i Hi; apply c5b_mb0; rewrite (KM1 (F + 0x210 + i) ltac:(lia));
            apply c5b_aview0; apply Hez; lia)
      ltac:(apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem1); [exact Hra|];
            intros y Hy; apply (Hshkeep mem1 KM1); lia)
      ltac:(apply (rm_hull_kept rsegs (w_H W) memc (w_H W) mem1); [exact Hhull|];
            intros s Hs Hns;
            pose proof (c5b_hull_bnd (F + 0x210) 104 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hsb;
            unfold kHighMemBeg in Hsb;
            rewrite (KM1 s ltac:(lia)); exact Hns)
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact Mf0])
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact M130])
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact M140])
      ltac:(apply (rl_val_kept (w_H W) memc mem1); [intros j Hj; apply KM1; lia | exact M158])). }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hk2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
  destruct HR2 as (R22 & R15 & R13 & R6 & RB).
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|].
  split; [intros rr Hr0 Hn; rewrite (Hk2 rr Hr0 ltac:(intros X; apply Hn; unfold w6bb_clob, rl_caller_saved,
            c5b_clobB in X |- *; cbn [app In] in X |- *; tauto));
          apply Hk1; [exact Hr0 | intros X; apply Hn; unfold w6bb_clob, c5b_clobA in X |- *; cbn [In] in X |- *; tauto]|].
  split; [exact Hf2|]. split; [exact Hp2|].
  split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
  split; [exact Hmo2|].
  split; [intros a Ha Hn; unfold w6bb_wr in Hn; cbv beta in Hn; unfold T_SEG_STK, ASTACK in Hn;
          rewrite (Hm2 a Ha ltac:(unfold c5b_wrB; cbv beta; unfold ESTACK; lia));
          apply KM1; exact Ha|].
  unfold w6bb_J_R. rewrite (c5b_build b (b1 :: r1) HP). cbn [fst snd fuzz_u8].
  change (Z.to_nat (bv_unsigned b1 mod 32)) with kk.
  split; [exact R22|].
  split; [exact R15|].
  split; [rewrite R13; unfold w64; f_equal; rewrite length_skipn, length_firstn; cbn [length]; lia|].
  split; [rewrite R6; unfold w64; f_equal; rewrite length_skipn, length_firstn; lia|].
  rewrite (c5b_ent (firstn kk r1) (negb (Z.testbit (bv_unsigned b) 7)) Hpl).
  rewrite c5b_bit7 by lia. rewrite <- Z.ltb_antisym. exact RB.
Qed.

End d.
End b.
