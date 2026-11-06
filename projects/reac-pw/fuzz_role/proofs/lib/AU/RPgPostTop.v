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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module names changed; 292 of its 322 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPostTop.v, with its module paths, module names, addresses and numbers changed; 107 of its 343 lines of code are new or changed and 86 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostTop.v at 8af9cea6f917; ported to image B
   (fuzz_rate.asan-ubsan): image B's code and cuts (lib/AU/RtPgSegB.v), its registers and real-frame cells, the kit
   lib/AU/RtPgPostKB.v; pp, pp + 0x4000 and ~pp are atoms of the cells R+0x28 / R+0x158 / R+0x108 (no register holds
   them at P1), the check of pp->len reads its shadow address from R+0x170, and the run decides the two B-only trap
   branches 0x826ac / 0x826b4. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPostTopB.v at db4fc362bebf for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role and the segments
   lib/AU/Img0.v rsegs; RtPgMemB / RtPgSegB / RtPgStepsB / RtPgPostKB become RPgMem / RPgSeg / RPgSteps / RPgPostK
   (rtmb_ -> rm_, rsb_ -> rs_, rtsb_ -> rl_, rt_ -> rl_, q_X -> e_X, wb10_ -> w10_, wb10t_ -> w10t_); rate B's P / P1
   / T (0x82684 / 0x82688 / 0x8270c) become role B's 0x81e6c / 0x81e70 / 0x81eec and its trap branches 0x826ac /
   0x826b4 become 0x81e8c / 0x81e94; pp + 0x4000 is the register s6 (atom 22) at P1, so only pp and ~pp are extra
   atoms (33 / 34, the cells R+0x30 / R+0xf8 in place of R+0x28 / R+0x108); the top word's offset 0 is R+0x28 (rate
   R+0x20), &pp->n_ent R+0x120 (rate R+0x138), the shadow address of &pp->len R+0x148 (rate R+0x170); K is s11
   (atom 27, rate s4 atom 20); the run writes s7 = &pp->corrupt (rate s8) and no t2; the cursor moves from s4 to a7
   at P (rate s2 to s10). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPostB.v at db4fc362bebf (its joiner
   wb10_post) for reac-pw/fuzz_role image B: wb10_post becomes w10_post, over lib/AU/RPgPostK.v w10_post_of_halves,
   this file's w10_top and lib/AU/RPgPostArms.v w10_arms; its Print Assumptions lines are dropped. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the first half of the post
   piece of the walk of LLVMFuzzerTestOneInput (0x80020), from the builder's end P 0x81e6c / P1 0x81e70
   (lib/AU/RPgSeg.v rs_cut_P, rs_cut_P1) to the piece's own cut T 0x81eec (lib/AU/RPgPostK.v w10_cut_T), pod.h:440.
   Proves no function (kind: segment lemma).
   THE CODE
     0x81e6c mv a7,s4                                     P only: the cursor moves from s4 to a7
     0x81e70 ld a0,0x148(s1) / lbu a0,0(a0) / bnez a0 -> 0x829e4
                                                          the instrumented check of the 8-byte load of pp->len
                                                          (R+0x148 holds the shadow address of pp + 0x4000; 0x829e4
                                                          / 0x829e8 is its error path)
     0x81e7c lui / addiw a0 = 0x4001
     0x81e84 ld a4,0x30(s1) / ld a5,0x28(s1)              a4 = pp, a5 = 0 (the top word's offset)
     0x81e8c bgeu a5,a0 -> 0x82604 (unimp)                not taken: 0 < 0x4001
     0x81e90 ld a0,0xf8(s1) / 0x81e94 bltu a0,a5 -> 0x82604 (unimp)   not taken: nothing is unsigned-below 0
     0x81e98 srli / add / lb a0                           the instrumented check of the shadow byte of a4; ld a1,0(s6)
                                                          (pp->len); bnez a0 -> 0x82614 (second test 0x82614 /
                                                          0x82618 back to 0x81eac, error path 0x8261c .. 0x82624)
     0x81eac addi / srli / add / lb a2 (a4 + 3)           bnez a2 -> 0x82628 (second test back to 0x81ec0, error path
                                                          after 0x8262c)
     0x81ec0 subw a0,a1,a5 / addi a0,a0,-8 / 3 srli / 4 sb at 0(a4) .. 3(a4)    le32 (len - 8) at pp + 0
     0x81ee4 ld s7,0x120(s1) / addi s7,s7,4               s7 = pp + 0x4d18 (&pp->corrupt)
     0x81eec T (`beqz t3,0x8214c`, the corruption's first test), not run here.
   HOW. The run P1 -> T is one run of the token engine (lib/Reusable/YCbn.v) from a symbolic state rebuilt from P1's
   cut: the registers as the atoms of Ereg regs [len; pp; ~pp] (atoms 32 .. 34), s6 = pp + 0x4000 its own atom 22, a
   read-only region at s1 with the five real-frame cells the code loads (R+0x28 = 0, R+0x30 = pp, R+0xf8 = ~pp,
   R+0x120 = pp + 0x4d14, R+0x148 = the shadow address of pp + 0x4000 as the engine's shadow form of atom 22), a
   read-only region at atom 22 with pp->len, and the write window [pp, pp + 4) at atom 33. Every atom bound is a
   closed numeral; ~pp's range [2^63, 2^64 - 1] and the literal 0 of R+0x28 decide the two trap branches. The three
   checks are covered by the shadow entries (atom 22, 0, 8) and (atom 33, 0, 16) over bytes of the first block
   (RPgPostK.w10_shent_blk), so their shadow bytes read as 0 and no error path is reached. The end state gives T's
   cut: the journal (RPgPostK.w10_core_run, writes only in pp), the value list (every register outside the clobber
   list and every real-frame cell kept, s7 new), the frame's shadow kept, the block's bytes with the top word patched
   (RPgPostK.w10_img_top: the record's image with no corruption) and the model tie (RPgPostK.w10_build_tie).
   P -> P1 is one run of `mv a7,s4`.
   w10_post: RPgSeg's rs_piece_W10_post_stmt (P / P1 -> R at kk = 0 / RT 0x82134 / C2 0x82164), from its two halves
   at the cut T (RPgPostK.w10_post_of_halves): w10_top here (P / P1 -> T, with image B's two patch32 trap branches
   0x81e8c / 0x81e94) and RPgPostArms.w10_arms (T -> R / RT / C2). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps RPgPostK RPgPostArms.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the fields of RPgSeg's segment record take the segments implicitly in this walk's files *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ---- the symbolic state at P1 = 0x81e70 ---- *)
(* atoms 32 .. 34: pp->len, pp, ~pp (as an unsigned 64-bit word); s6 = pp + 0x4000 is atom 22 *)
(* R+0x148 = (atom 22 >> 3) + s11, the shadow address of &pp->len in the engine's shadow form *)
Definition w10t_sh22 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 27 0).
(* the real-frame cells the run loads: the top word's offset (0) and address (pp), ~pp, &pp->n_ent and the shadow
   address of &pp->len *)
Definition w10t_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x28 0x150 0 0
   [YP09.mkChunk 0x28 (CVal 8 (SLit 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0xf8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x120 (CVal 8 (SOff 33 0x4d14));
    YP09.mkChunk 0x148 (CVal 8 w10t_sh22)].
(* pp->len at pp + 0x4000 (atom 22), atom 32 *)
Definition w10t_rL : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
(* the top size word [pp, pp + 4), written *)
Definition w10t_rT : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition w10t_G : facts :=
  mkFacts [(33%nat, mkAF 4096 W10_HI 4); (22%nat, mkAF 4096 W10_HI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 8 5440 0); (34%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] [].
Definition w10t_ss : sstate := mkSS 0x81e70 sr_atoms [w10t_rR; w10t_rL; w10t_rT] None w10t_G.
(* the checks' bytes: &pp->len's granule and pp's first two granules *)
Definition w10t_SH : list shent := [mkSHE 22 0 8; mkSHE 33 0 16].
(* the registers the run P1 -> T writes: a0 .. a5 and s7 *)
Definition w10t_clob : list (bv 5) := [Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13;
  Z_to_bv 5 14; Z_to_bv 5 15; Z_to_bv 5 23].

(* the byte a one-byte chunk of a final state holds *)
Lemma w10t_mbyte_chunk1 : forall segs E (m : word -> option byte) base off e,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 e)) ->
  mbyte segs m (base + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros segs E m base off e H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.

(* the four stored bytes: (len - 8) >> k as the engine computes it *)
Lemma w10t_U_srl : forall E v k, ew E 32 = Z_to_bv 64 v -> 8 <= v < 2 ^ 32 -> (k = 8 \/ k = 16 \/ k = 24) ->
  U E (SAlu ALU_SRL (SOff 32 (-8)) (SLit k)) = Z.shiftr (v - 8) k.
Proof.
intros E v k H32 Hv Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 32 v (-8) H32) by lia.
rewrite U_SLit.
assert (HL : Z.land (zcanon k) 63 = k) by (destruct Hk as [-> | [-> | ->]]; reflexivity).
rewrite HL.
assert (0 <= Z.shiftr (v + -8) k <= v + -8).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
rewrite zcanon_id by (unfold M64; lia). replace (v - 8) with (v + -8) by lia. reflexivity.
Qed.

(* ~pp as the unsigned 64-bit word the cell R+0xf8 holds *)
Lemma w10t_lnot_mod : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof. intros p Hp. unfold Z.lnot. symmetry. apply (Z.mod_unique _ _ (-1)); lia. Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ======================================== P1 -> T ======================================== *)
Lemma w10t_P1 : forall cx POST rest, rs_start_M01 rsegs B cx rest -> w10_from_T B MT cx POST rest ->
  rs_from_P1 rsegs B MT cx POST rest.
Proof.
intros cx POST rest Hst HT. unfold rs_from_P1.
intros ly2 S2 W2 regs2 mem2 md2 sh np ps r [HPb HL].
destruct Hst as (HP & _ & _ & _ & _).
destruct HPb as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hl & Hps).
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
(* P1's facts *)
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_P in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (A8 & A9 & A19 & A27 & A28 & A22 & C18 & C20 & C28 & C30 & C40 & C38 & Ce8 & Cf8 & Cc0 & C120
  & C140 & C148 & A17 & _).
cbn [fst snd rl_at rl_xv] in A8, A9, A19, A27, A28, A22, C18, C20, C28, C30, C40, C38, Ce8, Cf8, Cc0, C120,
  C140, C148, A17.
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
set (plen := rs_plen sh ps) in *.
assert (Hplen : 8 <= plen <= 5440) by (unfold plen, rs_plen; lia).
(* pp->len, from the block's image *)
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000 + 0) 8 plen).
{ rewrite Z.add_0_r.
  pose proof (pc_ents_final sh ps None) as Hents.
  apply (rm_pp_len rsegs (pc_buf (PbCut sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false);
    [unfold POD_BUF_MAX; lia | rewrite Hents; exact HW3 | rewrite Hents; exact HW4 | exact Hpp]. }
(* the cells' values as the region's chunks read them *)
assert (HSA : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. split; [pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound (pp + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
pose proof C28 as C28'. pose proof C30 as C30'. pose proof Cf8 as Cf8'. pose proof C120 as C120'.
pose proof C148 as C148'.
rewrite (Z.mod_small 0) in C28' by lia. rewrite (w10t_lnot_mod pp) in Cf8' by lia.
rewrite Z.mod_small in C30', C120', C148' by lia.
pose proof HC as (HJ & _).
remember (Ereg regs2 [Z_to_bv 64 plen; Z_to_bv 64 pp; Z_to_bv 64 (2 ^ 64 - 1 - pp)]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact A9).
assert (E22 : ew E 22 = Z_to_bv 64 (pp + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 (Z_to_bv 5 22) eq_refl); exact A22).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact A27).
assert (E32 : ew E 32 = Z_to_bv 64 plen) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - pp)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = pp + 0x4000) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = plen) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = 2 ^ 64 - 1 - pp) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HD22 : sv_denot E w10t_sh22 = Z_to_bv 64 (shadow_addr (pp + 0x4000))).
{ unfold w10t_sh22. exact (w10_den_sh E 22 27 (pp + 0x4000) E22 ltac:(lia) E27). }
(* the symbolic state at P1 *)
assert (HS : st_ok rsegs E w10t_ss (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81e70) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w10t_ss. rewrite HE. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - rewrite <- HE. unfold w10t_rR, w10t_rL, w10t_rT.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (rm_ro_region rsegs E (w_H W2) mem2 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
        [|apply Forall_cons; [|apply Forall_nil]]]]].
      * apply (chunk_ok_val rsegs E _ R 0x28 8 (SLit 0) 0); [reflexivity | cbn; lia | lia | exact C28'].
      * apply (chunk_ok_val rsegs E _ R 0x30 8 (SOff 33 0) pp);
          [exact (w10_den_atom E 33 pp E33) | cbn; lia | lia | exact C30'].
      * apply (chunk_ok_val rsegs E _ R 0xf8 8 (SOff 34 0) (2 ^ 64 - 1 - pp));
          [exact (w10_den_atom E 34 _ E34) | cbn; lia | lia | exact Cf8'].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SOff 33 0x4d14) (pp + 0x4d14));
          [exact (w10_den_off E 33 pp 0x4d14 E33) | cbn; lia | lia | exact C120'].
      * apply (chunk_ok_val rsegs E _ R 0x148 8 w10t_sh22 (shadow_addr (pp + 0x4000)));
          [exact HD22 | cbn; lia | lia | exact C148'].
    + apply (rm_ro_region rsegs E (w_H W2) mem2 22 (pp + 0x4000)); [exact U22 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ (pp + 0x4000) 0 8 (SOff 32 0) plen);
        [exact (w10_den_atom E 32 plen E32) | cbn; lia | lia | exact HLv].
    + apply (rm_rw_region rsegs E (w_H W2) mem2 33 pp); [exact U33 | lia | lia | | apply Forall_nil].
      intros o Ho. apply Hpres. lia.
  - rewrite <- HE. unfold w10t_rR, w10t_rL, w10t_rT. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U33.
    repeat split; try exact I; unfold T_SEG_STK, ASTACK in *; lia.
  - rewrite <- HE. unfold facts_ok, w10t_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, U22, U27, U32, U34.
    assert (Hm16 : (pp + 0x4000) mod 16 = 0).
    { rewrite Z.add_mod by lia. rewrite Hal. reflexivity. }
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; try assumption; unfold W10_HI, SHADOW_OFF in *; lia. }
(* the checks' bytes are covered: they lie in the first block *)
assert (UB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)).
assert (SHOK : sh_ok rsegs W10Bx w10t_SH E (mrestrict (w_H W2) mem2)).
{ unfold w10t_SH. constructor; [|constructor; [|constructor]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 22 0 8 HAR Hinp); change (req_size PP_SIZE) with 19744;
      [exact Happ | exact UB | | | lia]; rewrite (w10_U_atom E 22 _ E22 ltac:(lia)); unfold PP_SIZE; lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 33 0 16 HAR Hinp); change (req_size PP_SIZE) with 19744;
      [exact Happ | exact UB | | | lia]; rewrite (w10_U_atom E 33 _ E33 ltac:(lia)); unfold PP_SIZE; lia. }
unfold cfg_at. change (w64 RS_P1) with (Z_to_bv 64 0x81e70).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan W10_T.
{ (* the write window [pp, pp + 4) is in the first block, made since the segment's start *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 33%nat pp pp);
    [reflexivity | exact U33 | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | apply awr_ok_nil]. }
(* ---- the end state at T ---- *)
(* the run wrote only [pp, pp + 4) *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hb).
  unfold w10t_ss, w10t_rR, w10t_rL, w10t_rT in Hr. cbn [ss_mem] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?U9, ?U22, ?U33 in Hb; [lia | lia | apply Hn; lia]. }
(* every register outside a0 .. a5 and s7 as at P1 *)
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr w10t_clob -> getr (ms_regs ms) rr = getr regs2 rr).
{ apply (regs_kept_of_st_ok rsegs E _ ms regs2
    [Z_to_bv 64 plen; Z_to_bv 64 pp; Z_to_bv 64 (2 ^ 64 - 1 - pp)] (w_H W2) w10t_clob HS).
  - rewrite HE. apply env_agree_refl.
  - vm_compute. reflexivity. }
(* s7 = pp + 0x4d18 *)
assert (R23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (pp + 0x4d18)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) E _ ms (Z_to_bv 5 23) HS). w10_sr_eval.
  exact (w10_den_off E 33 pp 0x4d18 E33). }
(* the four stored bytes, from the end state's region at atom 33 *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem restrict ms_mem] in HOK.
apply Forall_inv_tail, Forall_inv_tail, Forall_inv in HOK.
destruct HOK as (_ & _ & _ & Cs). cbn [YP09.r_chunks YP09.r_base base_val] in Cs. rewrite U33 in Cs.
rewrite !Forall_cons_iff in Cs. destruct Cs as (K3 & K2 & K1 & K0 & _).
pose proof (w10t_mbyte_chunk1 rsegs E _ pp 0 _ K0) as M0.
pose proof (w10t_mbyte_chunk1 rsegs E _ pp 1 _ K1) as M1.
pose proof (w10t_mbyte_chunk1 rsegs E _ pp 2 _ K2) as M2.
pose proof (w10t_mbyte_chunk1 rsegs E _ pp 3 _ K3) as M3.
rewrite (U_atom_off E 32 plen (-8) E32) in M0 by lia.
rewrite (w10t_U_srl E plen 8 E32) in M1 by lia.
rewrite (w10t_U_srl E plen 16 E32) in M2 by lia.
rewrite (w10t_U_srl E plen 24 E32) in M3 by lia.
assert (Hnew : rm_bytes rsegs (w_H W2) (ms_mem ms) (pp + Z.of_nat 0) (le32 (plen - 8))).
{ change (pp + Z.of_nat 0) with (pp + 0). rewrite Z.add_0_r.
  apply rm_bytes_aview. intros i Hi. unfold le32 in *. rewrite length_Z_to_le_bytes in Hi.
  rewrite rm_nth_le_bytes by exact Hi. unfold aview.
  destruct i as [|[|[|[|i]]]]; [| | | | lia].
  - change (pp + Z.of_nat 0) with (pp + 0). rewrite M0. cbn [option_map].
    replace (plen + -8) with (plen - 8) by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - change (Z.of_nat 1) with 1. rewrite M1. reflexivity.
  - change (Z.of_nat 2) with 2. rewrite M2. reflexivity.
  - change (Z.of_nat 3) with 3. rewrite M3. reflexivity. }
assert (Lpc : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
{ unfold pc_image. rewrite (pc_ents_final sh ps None). apply length_pp_image; [lia | exact HW3 | exact HW4]. }
assert (HF8 : 0 <= e_F (x_e cx) / 8 < 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold w10_from_T in HT.
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) at 1. cbn [ss_pc].
apply (HT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r).
unfold w10_cut_T.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- (* the journal, the frame and the bytes outside the segment's write set: the run wrote only in pp *)
  apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun a => pp <= a < pp + 4) HC HJ).
  + intros rr Hr. destruct Hr as [->|[->| ->]];
      (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]).
  + apply same_io_wvb.
  + exact HK.
  + intros a Ha. apply w10_E1_pp. change (e_pp (x_e cx)) with pp. unfold PP_SIZE. lia.
- (* the value list: rs_L_post, ~pp, what is left and the cursor *)
  unfold rs_at_cx, rs_at, rs_L_post. cbv zeta. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil.
  all: cbn [fst snd rl_at rl_xv]; change (e_pp (x_e cx)) with pp; change (e_R (x_e cx)) with R.
  all: first
    [ exact R23
    | (rewrite RK; [assumption | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
    | (apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem ms));
       [intros k Hk; apply HK; unfold T_SEG_STK, ASTACK in *; lia | assumption]) ].
- (* the frame's shadow bytes: apart from pp *)
  apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. replace (Z.of_nat (length rs_P0)) with 88 in Hi by reflexivity.
  pose proof (w10_shadow_not_pp pp (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- (* the block: the top size word patched, the record's image with no corruption *)
  rewrite w10_bytes_none, <- (w10_img_top sh ps Hwf).
  apply (rm_bytes_patch rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp (pc_image (PbCut sh ps None)) 0
    (le32 (plen - 8)));
    [exact Hpp | exact Hnew | rewrite length_le32; unfold PP_SIZE in Lpc; lia |].
  intros y Hy Hn. rewrite Lpc in Hy. unfold PP_SIZE in Hy. apply HK; [lia|].
  intros X. apply Hn. rewrite length_le32. cbn [Nat.add]. lia.
- exact Hin.
- exact Hsuf.
- exact Hwf.
- exact Hlen.
- (* the record pod_build makes is the corruption step of what is left *)
  rewrite (w10_build_tie rest sh np ps r Hsh Hnp Hl Hps), HW2. reflexivity.
Qed.

(* ======================================== P -> P1 ======================================== *)
Lemma w10t_P : forall cx POST rest, rs_start_M01 rsegs B cx rest -> rs_from_P1 rsegs B MT cx POST rest ->
  rs_from_P rsegs B MT cx POST rest.
Proof.
intros cx POST rest Hst HP1. unfold rs_from_P, rs_from_P1 in *.
intros ly2 S2 W2 regs2 mem2 md2 sh np ps r [HPb HL].
destruct Hst as (HP & _ & _ & _ & _).
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HPb as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hl & Hps).
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HF8 : 0 <= e_F (x_e cx) / 8 < 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Lpc : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
{ unfold pc_image. rewrite (pc_ents_final sh ps None). apply length_pp_image; [lia | exact HW3 | exact HW4]. }
unfold rs_at_cx, rs_at in HL. rewrite Forall_app in HL. destruct HL as [HLP HL20].
rewrite Forall_cons_iff in HL20. destruct HL20 as [A20 _]. cbn [fst snd rl_at] in A20.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E20 : ew E 20 = Z_to_bv 64 (rs_cur rsegs cx rest r))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact A20).
assert (HS : st_ok rsegs E (mkSS 0x81e6c sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x81e6c) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok rsegs W10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 RS_P) with (Z_to_bv 64 0x81e6c).
(* 0x81e6c mv a7,s4 *)
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan RS_P1.
{ awr_ok_tac. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & _). cbn [ss_mem] in Hr. destruct Hr. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [Z_to_bv 5 17] -> getr (ms_regs ms) rr = getr regs2 rr).
{ apply (regs_kept_of_st_ok rsegs E _ ms regs2 [] (w_H W2) [Z_to_bv 5 17] HS).
  - rewrite HE. apply env_agree_refl.
  - vm_compute. reflexivity. }
assert (R17 : getr (ms_regs ms) (Z_to_bv 5 17) = w64 (rs_cur rsegs cx rest r)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) E _ ms (Z_to_bv 5 17) HS). w10_sr_eval.
  exact (w10_den_atom E 20 _ E20). }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) at 1. cbn [ss_pc].
apply (HP1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh np ps r).
split.
- split; [|split; [|split]].
  + apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    * intros rr Hr. destruct Hr as [->|[->| ->]];
        (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]).
    * apply same_io_wvb.
    * intros a Ha _. exact (HK a Ha).
    * intros a [].
  + apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
    intros i Hi. replace (Z.of_nat (length rs_P0)) with 88 in Hi by reflexivity.
    apply HK. unfold shadow_addr, SHADOW_OFF. lia.
  + apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ Hpp).
    intros x Hx. rewrite Lpc in Hx. unfold PP_SIZE in Hx. apply HK. lia.
  + exact (conj Hin (conj Hsuf (conj Hwf (conj Hlen (conj Hsh (conj Hnp (conj Hl Hps))))))).
- unfold rs_at_cx, rs_at. apply Forall_app. split.
  + apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLP).
    intros f Hf. unfold rs_L_P in Hf. cbv zeta in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
      first [ (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply HK; unfold T_SEG_STK, ASTACK in *; lia) ] |]).
    destruct Hf.
  + apply Forall_cons; [cbn [fst snd rl_at]; exact R17 | apply Forall_nil].
Qed.

(* ======================================== P / P1 -> T ======================================== *)
Theorem w10_top : w10_top_stmt B MT.
Proof.
intros cx POST rest Hst HT.
pose proof (w10t_P1 cx POST rest Hst HT) as H1.
split; [exact (w10t_P cx POST rest Hst H1) | exact H1].
Qed.
End t.

(* ======================================== the post piece: P / P1 -> R / RT / C2 ======================================== *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Theorem w10_post : rs_piece_W10_post_stmt rsegs B MT.
Proof. exact (w10_post_of_halves B MT (w10_top B MT) (w10_arms B MT)). Qed.
End p.
