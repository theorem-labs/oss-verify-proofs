(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 314 of its 345 lines of code are new or changed and 295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostTop.v at 8af9cea6f917; ported to image B
   (fuzz_rate.asan-ubsan): image B's code and cuts (lib/AU/RtPgSegB.v), its registers and real-frame cells, the kit
   lib/AU/RtPgPostKB.v; pp, pp + 0x4000 and ~pp are atoms of the cells R+0x28 / R+0x158 / R+0x108 (no register holds
   them at P1), the check of pp->len reads its shadow address from R+0x170, and the run decides the two B-only trap
   branches 0x826ac / 0x826b4. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the first half of the post piece of the walk
   of LLVMFuzzerTestOneInput (0x8076c), from the builder's end P 0x82684 / P1 0x82688 (lib/AU/RtPgSegB.v rsb_cut_P,
   rsb_cut_P1) to the piece's own cut T 0x8270c (lib/AU/RtPgPostKB.v wb10_cut_T), pod.h:440. Proves no function
   (kind: segment lemma).
   THE CODE
     0x82684 mv s10,s2                                    P only: the cursor moves from s2 to s10
     0x82688 ld a0,0x170(s1) / lbu a0,0(a0) / beqz a0,+8 / j 0x834bc
                                                          the check of the 8-byte load of pp->len (R+0x170 holds the
                                                          shadow address of pp + 0x4000)
     0x82698 lui / addiw a0 = 0x4001
     0x826a0 ld t2,0x158(s1) / ld a4,0x28(s1) / ld a5,0x20(s1)   t2 = pp + 0x4000, a4 = pp, a5 = 0 (the top word's
                                                          offset)
     0x826ac bgeu a5,a0 -> 0x83098 (unimp)                not taken: 0 < 0x4001
     0x826b0 ld a0,0x108(s1) / 0x826b4 bltu a0,a5 -> 0x83098 (unimp)   not taken: nothing is unsigned-below 0
     0x826b8 srli / add / lb a0                           the shadow byte of a4; ld a1,0(t2) (pp->len);
             bnez a0 -> 0x8309c (second test, back to 0x826cc)
     0x826cc addi / srli / add / lb a2 (a4 + 3)           bnez a2 -> 0x830b0 (second test, back to 0x826e0)
     0x826e0 subw a0,a1,a5 / addi a0,a0,-8 / 3 srli / 4 sb at 0(a4) .. 3(a4)    le32 (len - 8) at pp + 0
     0x82704 ld s8,0x138(s1) / addi s8,s8,4               s8 = pp + 0x4d18 (&pp->corrupt)
     0x8270c T (`beqz t4,0x82a14`, the corruption's first test), not run here.
   HOW. The run P1 -> T is one run of the token engine (lib/Reusable/YCbn.v) from a symbolic state rebuilt from P1's
   cut: the registers as the atoms of Ereg regs [len; pp; pp + 0x4000; ~pp] (atoms 32 .. 35), a read-only region at
   s1 with the six real-frame cells the code loads (R+0x20 = 0, R+0x28 = pp, R+0x108 = ~pp, R+0x138 = pp + 0x4d14,
   R+0x158 = pp + 0x4000, R+0x170 = the shadow address of pp + 0x4000 as the engine's shadow form of atom 34), a
   read-only region at atom 34 with pp->len, and the write window [pp, pp + 4) at atom 33. Every atom bound is a closed
   numeral; ~pp's range [2^63, 2^64 - 1] and the literal 0 of R+0x20 decide the two trap branches. The two checks
   are covered by the shadow entries (atom 34, 0, 8) and (atom 33, 0, 16) over bytes of the first block
   (RtPgPostKB.wb10_shent_blk), so their shadow bytes read as 0 and no error path is reached. The end state gives
   T's cut: the journal (RtPgPostKB.wb10_core_run, writes only in pp), the value list (every register outside the
   clobber list and every real-frame cell kept, t2 and s8 new), the frame's shadow kept, the block's bytes with the
   top word patched (RtPgPostKB.wb10_img_top: the record's image with no corruption) and the model tie
   (RtPgPostKB.wb10_build_tie).
   P -> P1 is one run of `mv s10,s2`. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgPostKB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* the fields of RtPgSegB's segment record take the segments implicitly in this walk's files *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ---- the symbolic state at P1 = 0x82688 ---- *)
(* atoms 32 .. 35: pp->len, pp, pp + 0x4000, ~pp (as an unsigned 64-bit word) *)
(* R+0x170 = (atom 34 >> 3) + s4, the shadow address of &pp->len in the engine's shadow form *)
Definition wb10t_sh34 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 20 0).
(* the real-frame cells the run loads: the top word's offset (0) and address (pp), ~pp, &pp->n_ent, &pp->len and
   the shadow address of &pp->len *)
Definition wb10t_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x20 0x178 0 0
   [YP09.mkChunk 0x20 (CVal 8 (SLit 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x108 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x138 (CVal 8 (SOff 33 0x4d14));
    YP09.mkChunk 0x158 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x170 (CVal 8 wb10t_sh34)].
(* pp->len at pp + 0x4000 (atom 34), atom 32 *)
Definition wb10t_rL : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
(* the top size word [pp, pp + 4), written *)
Definition wb10t_rT : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition wb10t_G : facts :=
  mkFacts [(33%nat, mkAF 4096 WB10_HI 4); (34%nat, mkAF 4096 WB10_HI 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 8 5440 0); (35%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] [].
Definition wb10t_ss : sstate := mkSS 0x82688 sr_atoms [wb10t_rR; wb10t_rL; wb10t_rT] None wb10t_G.
(* the two checks' bytes: &pp->len's granule and pp's first two granules *)
Definition wb10t_SH : list shent := [mkSHE 34 0 8; mkSHE 33 0 16].
(* the registers the run P1 -> T writes: t2, a0 .. a5 and s8 *)
Definition wb10t_clob : list (bv 5) := [Z_to_bv 5 7; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13;
  Z_to_bv 5 14; Z_to_bv 5 15; Z_to_bv 5 24].

(* the byte a one-byte chunk of a final state holds *)
Lemma wb10t_mbyte_chunk1 : forall segs E (m : word -> option byte) base off e,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 e)) ->
  mbyte segs m (base + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros segs E m base off e H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.

(* the four stored bytes: (len - 8) >> k as the engine computes it *)
Lemma wb10t_U_srl : forall E v k, ew E 32 = Z_to_bv 64 v -> 8 <= v < 2 ^ 32 -> (k = 8 \/ k = 16 \/ k = 24) ->
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

(* ~pp as the unsigned 64-bit word the cell R+0x108 holds *)
Lemma wb10t_lnot_mod : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof. intros p Hp. unfold Z.lnot. symmetry. apply (Z.mod_unique _ _ (-1)); lia. Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ======================================== P1 -> T ======================================== *)
Lemma wb10t_P1 : forall cx POST rest, rsb_start_M01 rsegs B cx rest -> wb10_from_T B MT cx POST rest ->
  rsb_from_P1 rsegs B MT cx POST rest.
Proof.
intros cx POST rest Hst HT. unfold rsb_from_P1.
intros ly2 S2 W2 regs2 mem2 md2 sh np ps r [HPb HL].
destruct Hst as (HP & _ & _ & _ & _).
destruct HPb as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hl & Hps).
pose proof RtPgStepsB.rtsb_wx as Hwx. pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
(* P1's facts *)
pose proof HL as HL0.
unfold rsb_at_cx, rsb_at, rsb_L_P, rsb_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (A8 & A9 & A19 & A20 & A29 & C8 & C10 & C20 & C28 & C50 & C60 & Cf8 & C108 & C120 & C138 & C158
  & C168 & C170 & C48 & C30 & C38 & C40 & C18 & C148 & A26 & _).
cbn [fst snd rt_at rt_xv] in A8, A9, A19, A20, A29, C8, C10, C20, C28, C50, C60, Cf8, C108, C120, C138, C158,
  C168, C170, C48, C30, C38, C40, C18, C148, A26.
set (pp := q_pp (x_e cx)) in *. set (R := q_R (x_e cx)) in *.
set (plen := rsb_plen sh ps) in *.
assert (Hplen : 8 <= plen <= 5440) by (unfold plen, rsb_plen; lia).
(* pp->len, from the block's image *)
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000 + 0) 8 plen).
{ rewrite Z.add_0_r.
  pose proof (pc_ents_final sh ps None) as Hents.
  apply (rtmb_pp_len rsegs (pc_buf (PbCut sh ps None)) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false);
    [unfold POD_BUF_MAX; lia | rewrite Hents; exact HW3 | rewrite Hents; exact HW4 | exact Hpp]. }
(* the cells' values as the region's chunks read them *)
assert (HSA : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. split; [pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound (pp + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
pose proof C20 as C20'. pose proof C28 as C28'. pose proof C108 as C108'. pose proof C138 as C138'.
pose proof C158 as C158'. pose proof C170 as C170'.
rewrite (Z.mod_small 0) in C20' by lia. rewrite (wb10t_lnot_mod pp) in C108' by lia.
rewrite Z.mod_small in C28', C138', C158', C170' by lia.
pose proof HC as (HJ & _).
remember (Ereg regs2 [Z_to_bv 64 plen; Z_to_bv 64 pp; Z_to_bv 64 (pp + 0x4000); Z_to_bv 64 (2 ^ 64 - 1 - pp)])
  as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact A9).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact A20).
assert (E32 : ew E 32 = Z_to_bv 64 plen) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pp + 0x4000)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (2 ^ 64 - 1 - pp)) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF) by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = plen) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp + 0x4000) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = 2 ^ 64 - 1 - pp) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HD34 : sv_denot E wb10t_sh34 = Z_to_bv 64 (shadow_addr (pp + 0x4000))).
{ unfold wb10t_sh34. exact (wb10_den_sh E 34 20 (pp + 0x4000) E34 ltac:(lia) E20). }
(* the symbolic state at P1 *)
assert (HS : st_ok rsegs E wb10t_ss (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82688) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold wb10t_ss. rewrite HE. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - rewrite <- HE. unfold wb10t_rR, wb10t_rL, wb10t_rT.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (rtmb_ro_region rsegs E (w_H W2) mem2 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
        [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
      * apply (chunk_ok_val rsegs E _ R 0x20 8 (SLit 0) 0); [reflexivity | cbn; lia | lia | exact C20'].
      * apply (chunk_ok_val rsegs E _ R 0x28 8 (SOff 33 0) pp);
          [exact (wb10_den_atom E 33 pp E33) | cbn; lia | lia | exact C28'].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 35 0) (2 ^ 64 - 1 - pp));
          [exact (wb10_den_atom E 35 _ E35) | cbn; lia | lia | exact C108'].
      * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 33 0x4d14) (pp + 0x4d14));
          [exact (wb10_den_off E 33 pp 0x4d14 E33) | cbn; lia | lia | exact C138'].
      * apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 34 0) (pp + 0x4000));
          [exact (wb10_den_atom E 34 _ E34) | cbn; lia | lia | exact C158'].
      * apply (chunk_ok_val rsegs E _ R 0x170 8 wb10t_sh34 (shadow_addr (pp + 0x4000)));
          [exact HD34 | cbn; lia | lia | exact C170'].
    + apply (rtmb_ro_region rsegs E (w_H W2) mem2 34 (pp + 0x4000)); [exact U34 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ (pp + 0x4000) 0 8 (SOff 32 0) plen);
        [exact (wb10_den_atom E 32 plen E32) | cbn; lia | lia | exact HLv].
    + apply (rtmb_rw_region rsegs E (w_H W2) mem2 33 pp); [exact U33 | lia | lia | | apply Forall_nil].
      intros o Ho. apply Hpres. lia.
  - rewrite <- HE. unfold wb10t_rR, wb10t_rL, wb10t_rT. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U34, U33.
    repeat split; try exact I; unfold T_SEG_STK, ASTACK in *; lia.
  - rewrite <- HE. unfold facts_ok, wb10t_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, U34, U20, U32, U35.
    assert (Hm16 : (pp + 0x4000) mod 16 = 0).
    { rewrite Z.add_mod by lia. rewrite Hal. reflexivity. }
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; try assumption; unfold WB10_HI, SHADOW_OFF in *; lia. }
(* the checks' bytes are covered: they lie in the first block *)
assert (UB : U E WB10Bx = SHADOW_OFF) by exact (wb10_U_atom E 20 SHADOW_OFF E20 ltac:(unfold SHADOW_OFF; lia)).
assert (SHOK : sh_ok rsegs WB10Bx wb10t_SH E (mrestrict (w_H W2) mem2)).
{ unfold wb10t_SH. constructor; [|constructor; [|constructor]].
  - apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 8 HAR Hinp); change (req_size PP_SIZE) with 19744;
      [exact Happ | exact UB | | | lia]; rewrite (wb10_U_atom E 34 _ E34 ltac:(lia)); unfold PP_SIZE; lia.
  - apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 33 0 16 HAR Hinp); change (req_size PP_SIZE) with 19744;
      [exact Happ | exact UB | | | lia]; rewrite (wb10_U_atom E 33 _ E33 ltac:(lia)); unfold PP_SIZE; lia. }
unfold cfg_at. change (w64 RSB_P1) with (Z_to_bv 64 0x82688).
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan WB10_T.
{ (* the write window [pp, pp + 4) is in the first block, made since the segment's start *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (wb10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 33%nat pp pp);
    [reflexivity | exact U33 | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | apply awr_ok_nil]. }
(* ---- the end state at T ---- *)
(* the run wrote only [pp, pp + 4) *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hb).
  unfold wb10t_ss, wb10t_rR, wb10t_rL, wb10t_rT in Hr. cbn [ss_mem] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?U9, ?U34, ?U33 in Hb; [lia | lia | apply Hn; lia]. }
(* every register outside t2, a0 .. a5 and s8 as at P1 *)
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr wb10t_clob -> getr (ms_regs ms) rr = getr regs2 rr).
{ apply (RtPgStepsB.regs_kept_of_st_ok rsegs E _ ms regs2
    [Z_to_bv 64 plen; Z_to_bv 64 pp; Z_to_bv 64 (pp + 0x4000); Z_to_bv 64 (2 ^ 64 - 1 - pp)] (w_H W2) wb10t_clob HS).
  - rewrite HE. apply env_agree_refl.
  - vm_compute. reflexivity. }
(* t2 = pp + 0x4000 and s8 = pp + 0x4d18 *)
assert (R7 : getr (ms_regs ms) (Z_to_bv 5 7) = w64 (pp + 0x4000)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) E _ ms (Z_to_bv 5 7) HS). wb10_sr_eval.
  exact (wb10_den_atom E 34 _ E34). }
assert (R24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (pp + 0x4d18)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) E _ ms (Z_to_bv 5 24) HS). wb10_sr_eval.
  exact (wb10_den_off E 33 pp 0x4d18 E33). }
(* the four stored bytes, from the end state's region at atom 33 *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem restrict ms_mem] in HOK.
apply Forall_inv_tail, Forall_inv_tail, Forall_inv in HOK.
destruct HOK as (_ & _ & _ & Cs). cbn [YP09.r_chunks YP09.r_base base_val] in Cs. rewrite U33 in Cs.
rewrite !Forall_cons_iff in Cs. destruct Cs as (K3 & K2 & K1 & K0 & _).
pose proof (wb10t_mbyte_chunk1 rsegs E _ pp 0 _ K0) as M0.
pose proof (wb10t_mbyte_chunk1 rsegs E _ pp 1 _ K1) as M1.
pose proof (wb10t_mbyte_chunk1 rsegs E _ pp 2 _ K2) as M2.
pose proof (wb10t_mbyte_chunk1 rsegs E _ pp 3 _ K3) as M3.
rewrite (U_atom_off E 32 plen (-8) E32) in M0 by lia.
rewrite (wb10t_U_srl E plen 8 E32) in M1 by lia.
rewrite (wb10t_U_srl E plen 16 E32) in M2 by lia.
rewrite (wb10t_U_srl E plen 24 E32) in M3 by lia.
assert (Hnew : rtmb_bytes rsegs (w_H W2) (ms_mem ms) (pp + Z.of_nat 0) (le32 (plen - 8))).
{ change (pp + Z.of_nat 0) with (pp + 0). rewrite Z.add_0_r.
  apply rtmb_bytes_aview. intros i Hi. unfold le32 in *. rewrite length_Z_to_le_bytes in Hi.
  rewrite rtmb_nth_le_bytes by exact Hi. unfold aview.
  destruct i as [|[|[|[|i]]]]; [| | | | lia].
  - change (pp + Z.of_nat 0) with (pp + 0). rewrite M0. cbn [option_map].
    replace (plen + -8) with (plen - 8) by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - change (Z.of_nat 1) with 1. rewrite M1. reflexivity.
  - change (Z.of_nat 2) with 2. rewrite M2. reflexivity.
  - change (Z.of_nat 3) with 3. rewrite M3. reflexivity. }
assert (Lpc : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
{ unfold pc_image. rewrite (pc_ents_final sh ps None). apply length_pp_image; [lia | exact HW3 | exact HW4]. }
assert (HF8 : 0 <= q_F (x_e cx) / 8 < 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold wb10_from_T in HT.
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) at 1. cbn [ss_pc].
apply (HT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r).
unfold wb10_cut_T.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- (* the journal, the frame and the bytes outside the segment's write set: the run wrote only in pp *)
  apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun a => pp <= a < pp + 4) HC HJ).
  + intros rr Hr. destruct Hr as [->|[->| ->]];
      (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]).
  + apply RtPgStepsB.same_io_wvb.
  + exact HK.
  + intros a Ha. apply wb10_E1_pp. change (q_pp (x_e cx)) with pp. unfold PP_SIZE. lia.
- (* the value list: rsb_L_post, ~pp, what is left and the cursor *)
  unfold rsb_at_cx, rsb_at, rsb_L_post, rsb_Hc. cbv zeta. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil.
  all: cbn [fst snd rt_at rt_xv]; change (q_pp (x_e cx)) with pp; change (q_R (x_e cx)) with R.
  all: first
    [ exact R7
    | exact R24
    | (rewrite RK; [assumption | vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
    | (apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem ms));
       [intros k Hk; apply HK; unfold T_SEG_STK, ASTACK in *; lia | assumption]) ].
- (* the frame's shadow bytes: apart from pp *)
  apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rsb_P0 Hfsh).
  intros i Hi. replace (Z.of_nat (length rsb_P0)) with 88 in Hi by reflexivity.
  pose proof (wb10_shadow_not_pp pp (q_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- (* the block: the top size word patched, the record's image with no corruption *)
  rewrite wb10_bytes_none, <- (wb10_img_top sh ps Hwf).
  apply (rtmb_bytes_patch rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp (pc_image (PbCut sh ps None)) 0
    (le32 (plen - 8)));
    [exact Hpp | exact Hnew | rewrite length_le32; unfold PP_SIZE in Lpc; lia |].
  intros y Hy Hn. rewrite Lpc in Hy. unfold PP_SIZE in Hy. apply HK; [lia|].
  intros X. apply Hn. rewrite length_le32. cbn [Nat.add]. lia.
- exact Hin.
- exact Hsuf.
- exact Hwf.
- exact Hlen.
- (* the record pod_build makes is the corruption step of what is left *)
  rewrite (wb10_build_tie rest sh np ps r Hsh Hnp Hl Hps), HW2. reflexivity.
Qed.

(* ======================================== P -> P1 ======================================== *)
Lemma wb10t_P : forall cx POST rest, rsb_start_M01 rsegs B cx rest -> rsb_from_P1 rsegs B MT cx POST rest ->
  rsb_from_P rsegs B MT cx POST rest.
Proof.
intros cx POST rest Hst HP1. unfold rsb_from_P, rsb_from_P1 in *.
intros ly2 S2 W2 regs2 mem2 md2 sh np ps r [HPb HL].
destruct Hst as (HP & _ & _ & _ & _).
pose proof RtPgStepsB.rtsb_wx as Hwx. pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HPb as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hl & Hps).
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HF8 : 0 <= q_F (x_e cx) / 8 < 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Lpc : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
{ unfold pc_image. rewrite (pc_ents_final sh ps None). apply length_pp_image; [lia | exact HW3 | exact HW4]. }
unfold rsb_at_cx, rsb_at in HL. rewrite Forall_app in HL. destruct HL as [HLP HL18].
rewrite Forall_cons_iff in HL18. destruct HL18 as [A18 _]. cbn [fst snd rt_at] in A18.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E18 : ew E 18 = Z_to_bv 64 (rsb_cur rsegs cx rest r))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact A18).
assert (HS : st_ok rsegs E (mkSS 0x82684 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82684) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 RSB_P) with (Z_to_bv 64 0x82684).
(* 0x82684 mv s10,s2 *)
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan RSB_P1.
{ awr_ok_tac. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & _). cbn [ss_mem] in Hr. destruct Hr. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [Z_to_bv 5 26] -> getr (ms_regs ms) rr = getr regs2 rr).
{ apply (RtPgStepsB.regs_kept_of_st_ok rsegs E _ ms regs2 [] (w_H W2) [Z_to_bv 5 26] HS).
  - rewrite HE. apply env_agree_refl.
  - vm_compute. reflexivity. }
assert (R26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (rsb_cur rsegs cx rest r)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) E _ ms (Z_to_bv 5 26) HS). wb10_sr_eval.
  exact (wb10_den_atom E 18 _ E18). }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) at 1. cbn [ss_pc].
apply (HP1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh np ps r).
split.
- split; [|split; [|split]].
  + apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    * intros rr Hr. destruct Hr as [->|[->| ->]];
        (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]).
    * apply RtPgStepsB.same_io_wvb.
    * intros a Ha _. exact (HK a Ha).
    * intros a [].
  + apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rsb_P0 Hfsh).
    intros i Hi. replace (Z.of_nat (length rsb_P0)) with 88 in Hi by reflexivity.
    apply HK. unfold shadow_addr, SHADOW_OFF. lia.
  + apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ Hpp).
    intros x Hx. rewrite Lpc in Hx. unfold PP_SIZE in Hx. apply HK. lia.
  + exact (conj Hin (conj Hsuf (conj Hwf (conj Hlen (conj Hsh (conj Hnp (conj Hl Hps))))))).
- unfold rsb_at_cx, rsb_at. apply Forall_app. split.
  + apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLP).
    intros f Hf. unfold rsb_L_P, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
      first [ (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply HK; unfold T_SEG_STK, ASTACK in *; lia) ] |]).
    destruct Hf.
  + apply Forall_cons; [cbn [fst snd rt_at]; exact R26 | apply Forall_nil].
Qed.

(* ======================================== P / P1 -> T ======================================== *)
Theorem wb10_top : wb10_top_stmt B MT.
Proof.
intros cx POST rest Hst HT.
pose proof (wb10t_P1 cx POST rest Hst HT) as H1.
split; [exact (wb10t_P cx POST rest Hst H1) | exact H1].
Qed.
End t.

Print Assumptions wb10_top.
