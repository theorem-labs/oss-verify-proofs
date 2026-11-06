(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 637 of its 652 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_box_model_blockRB_case0F.v, with its module names and addresses changed; 180 of its 292 lines of code are new or changed and 540 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case12F.v is the re-based copy of lib/B/Prog/reac_box_model_block_case12F.v at 20372bbcc3a
   (source sha256 6da284bddef10166ebb02b7be434c01e704ef19feb84c34fb979caac71446063) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: nothing. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  C_reac_box_model_blockRB C_reac_box_model_blockRB_case12 C_reac_box_model_blockRBF.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c_on asan_stack_malloc_cF_on asan_memset_c_on asan_memset_cF_on
  asan_memcpy_c_on asan_memcpy_cF_on sh_word_on C_reac_box_model_blockOnHB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import name_field_c_on.
Import ListNotations.
Open Scope Z_scope.

(* The footprint twin of C_reac_box_model_blockRB_case12.v (image B, asan-ubsan; RECIPE.md step 1, route 2 (a working note, not in this delivery)):
   cases b = 1 and b = 2 of the body of reac_box_model_block as ExecF.evtF runs under the footprint RNG, by the
   scripts of the plain file over StepF's step.  The plain file's pure lemmas (c12_sh_app, c12_sh_out, c12_j14,
   c12_j13, c12_sub_post, c12_o_fs, c12_fk) are used from there; this file restates only what mentions `evt`. *)

(* The store hook of C_reac_box_model_blockRBF.v, copied (it is Local there). *)
Ltac mbF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt :=
  try mbF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt.

(* The shadow-access hook of C_reac_box_model_blockRBF.v, copied (it is Local there). *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

Section Case12F.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  Hypothesis HMS : asan_memset_contract_F_on.
  Hypothesis HMC : asan_memcpy_contract_F_on.
  Hypothesis HBD : build_dt1_single_contract_F_on.
  Hypothesis HDH : dt1_head_contract_F_on.
  Hypothesis HNF : name_field_contract_F_on.

  (* The frame release at 0x86e14 (rel_stmt of the interface pin), as an evtF run under RNG. *)
  Hypothesis Hrel :
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
      FK FS A fr f spc j n w56 ->
      ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
         (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
      (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
      evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
                (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).

  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  (* 0x86a4c: a2 = 32, a0 = o, checked_memcpy (o, S, 32); then 0x86a58: j 0x86e10; s5 = 1; the release at 0x86e14.
     Beyond c12_join's premises, the copy's source S carries its footprint (the range and its 8-aligned shadow word
     cover, which asan_memcpy_contract_F asks of the source): c12_join quantifies S, and the run's footprint covers
     only the JOIN block that b selects, so c12_case1F / c12_case2F supply them from RIMG and RJ4 / RJ3. *)
  Lemma c12_joinF : forall (S : Z) (JJ : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    addressable m S 32 -> bytes_at rsegs mc S JJ -> length JJ = 32%nat ->
    0 <= S -> S + 32 <= ASAN_GT -> (o + 32 <= S \/ S + 32 <= o) ->
    JJ = synth row b nb -> rc row b = 1 ->
    rng RNG S 32 -> shkov RNG S 32 ->
    (forall a, sh_word_on S 32 a -> reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 (Z_to_bv 64 S) x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86a4c) fc None mc (seg_rom rsegs)).
  Proof.
    intros S JJ fr f spc j n w56 mc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp Ho HK HB HOc AS HJ LJ S0 SG DJ EJ Er RS KS HSR.
    mbF_open HRNG.
    destruct HB as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    assert (Epo : (p =? 0) || (o =? 0) = false)
      by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
    pose proof (c12_sub_post sp m p b o FS A row nb ob HA HS16 Rp Rb Ro HP HO fr f spc j n w56 HK) as SP.
    rewrite Epo in SP. cbv iota in SP.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSb & HApp & _ & _).
    destruct (HO Ho) as (_ & HOsp & _).
    destruct (AO Ho) as (AOa & AOe & AOr).
    destruct (c12_o_fs sp tp m p b o FS row nb FP0 Rp Rb Ro HP Ho) as (Dh & Df).
    pose proof (c12_fk sp m p b o FS A row nb Rp Rb Ro HP fr f spc j n w56 HK) as HF.
    assert (HAb : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160)
      by (rewrite HA; clear - Rsp HS16; Z.div_mod_to_equations; lia).
    assert (Hoapp : o <> 0 -> forall y, o <= y < o + 32 -> app_mem y).
    { intros _ y Hy. replace y with (o + (y - o)) by (clear - Hy; lia).
      exact (acl_app_in m o 32 (y - o) AOa ltac:(clear - Hy; lia)). }
    unfold ASAN_GT in P3, SG. unfold FS_SIZE in HFSb.
    (* the source and the destination are addressable at mc: their shadow bytes are outside the run's writes *)
    assert (ADS : addressable mc S 32).
    { apply (addr_munch _ m mc S 32 AS MU). intros i Hi. apply SP.
      apply (c12_sh_out (bv_unsigned sp) FS o (S + i) HApp P4 P2 HS16 Hoapp (acl_app_in m S 32 i AS Hi)).
      - clear - Hi SG P3 HFSb. lia.
      - clear - Hi SG P3. lia. }
    assert (ADD : addressable mc o 32).
    { apply (addr_munch _ m mc o 32 AOa MU). intros i Hi. apply SP.
      apply (c12_sh_out (bv_unsigned sp) FS o (o + i) HApp P4 P2 HS16 Hoapp (acl_app_in m o 32 i AOa Hi)).
      - clear - Hi HOsp. lia.
      - clear - Hi Df. lia. }
    assert (Hspc : bv_unsigned sp - 4272 <= spc - 2224 /\ spc <= bv_unsigned sp - 160)
      by (clear - HF HAb; lia).
    pose proof (stk_mono m mc _ _ ST0 WM RM) as STm.
    destruct (stk_split rsegs mc _ spc _ STm ltac:(clear - Hspc; lia)) as [STc _].
    pose proof (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO _ mc MU SP) as ACc.
    assert (SRc : shadow_rw_on (asan_memcpy_shadow_R (Z_to_bv 64 o) (Z_to_bv 64 S) (Z_to_bv 64 32)) mc).
    { apply (mbHB_cpy _ mc o S 32 (mbHB_carry _ m mc SR0 WM RM));
        [clear - Ro; lia | clear - S0 SG; lia | lia | exact HSR |].
      intros a Ha. apply (mbHB_R_o (bv_unsigned sp) FS p b o row nb o 32 a); [lia | exact Ho | lia | lia | exact Ha]. }
    assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; clear - S0 SG; lia).
    assert (UO : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; exact Ro).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; clear - Hspc HHM Rsp; unfold HIGHMEM_BEG in HHM; lia).
    assert (Hsv : forall x, bv_unsigned sp + -88 <= x < bv_unsigned sp -> ~ (o <= x < o + 32) /\ ~ (spc - 2224 <= x < spc))
      by (intros x Hx; clear - Hx HOsp Hspc; lia).
    assert (Hfh : forall x, FS <= x < FS + 8 -> ~ (o <= x < o + 32) /\ ~ (spc - 2224 <= x < spc))
      by (intros x Hx; clear - Hx Dh Hspc HFSb; lia).
    assert (Hf56 : forall x, fr + 56 <= x < fr + 64 -> ~ (o <= x < o + 32) /\ ~ (spc - 2224 <= x < spc))
      by (intros x Hx; clear - Hx HF HOsp Df HAb HFSb; lia).
    assert (HSlo : S + 32 <= spc - 2224) by (clear - SG P3 HFSb Hspc; lia).
    pose proof HMC as HM. unfold asan_memcpy_contract_F_on in HM. cbv zeta in HM.
    clear SP HApp HSM Hoff HA HS16 ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF.
    step. step. step.
    eapply evtF_cut.
    { eapply HM with (src := JJ) (junk := zeros 32) (lo := bv_unsigned sp - 4272).
      all: rewrite ?US, ?UO, ?U32, ?USP; try unfold ASAN_MEMCPY_K.
      - exact HJ.
      - rewrite LJ. reflexivity.
      - exact HOc.
      - clear - DJ. lia.
      - clear - U32. lia.
      - exact ADS.
      - exact ADD.
      - right. unfold app_mem, LOWMEM_END. left. clear - S0 SG. lia.
      - right. exact AOe.
      - right. split; [unfold app_mem, LOWMEM_END; left; clear - S0 SG; lia|].
        exact (acl_app_in mc o 32 7 ADD ltac:(clear - U32; lia)).
      - exact AOr.
      - clear - HOsp Hspc. lia.
      - clear - HSlo. lia.
      - exact STc.
      - clear - Hspc. lia.
      - exact HHM.
      - clear - Hspc HAE. lia.
      - exact ACc.
      - exact SRc.
      - exact MI.
      (* the regions of the call (a Theorem Labs lane's order): the byte-wise footprint, the image, its window below spc,
         the 32 bytes written at o, the 32 bytes read at S, the 8-aligned shadow word cover of each of those two
         and of the window *)
      - exact RBY.
      - eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact RWIN | clear - Hspc; lia | clear - Hspc; lia].
      - destruct (ROUT Hp Ho) as (ROUTr & _ & _ & _). exact ROUTr.
      - exact RS.
      - destruct (ROUT Hp Ho) as (_ & _ & _ & ROUTk). apply (mbF_shw RNG o 32 o 32 ROUTk); clear - Ro; lia.
      - apply (mbF_shw RNG S 32 S 32 KS); clear - S0; lia.
      - apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 (spc - 2224) 2224 KWIN); clear - Hspc; lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & m2
                    & E & MU2 & WM2 & MI2 & ST2 & RW2 & SB2 & AC2 & SR2).
    subst ms'.
    rewrite UO, U32, USP in MU2. rewrite USP in ST2. rewrite UO, U32 in RW2. unfold ASAN_MEMCPY_K in MU2.
    replace (ret_pc (Z_to_bv 64 0x86a58)) with (Z_to_bv 64 0x86a58)
      by (symmetry; apply ret_pc_even; [clear - U32; lia | reflexivity]).
    (* the run's state at m2 *)
    assert (BI2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 m2).
    { assert (Hsub : sub_fp [(o, o + 32); (spc - 2224, spc)] (Wf sp FS fr j n ++ [(o, o + 32)])).
      { unfold sub_fp, Wf. intros x Hx. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & _ & _ & _ & _ & H6 & _).
        split; [exact H6|]. split; [|exact I]. clear - H1 Hspc. lia. }
      split; [exact (munch_trans _ m mc m2 MU (munch_weaken _ _ mc m2 Hsub MU2))|].
      split; [exact (wmono_trans rsegs m mc m2 WM WM2)|].
      split.
      { apply (rd_mono_trans m mc m2 RM). apply (rd_mono_list _ mc m2 MU2).
        constructor; [cbn [fst snd]; intros y Hy; apply (rd_of_bytes m2 o JJ (mb_rw1 _ _ _ _ _ RW2));
                      rewrite LJ; exact Hy|].
        constructor; [cbn [fst snd]; intros y Hy; exact (rd_of_stk m2 _ _ ST2 y ltac:(clear - Hy Hspc; lia))|].
        constructor. }
      split; [exact MI2|].
      split.
      { apply (acl_rw _ mc m2 _ _ SV MU2 WM2). intros x Hx.
        assert (Hx' : bv_unsigned sp + -88 <= x < bv_unsigned sp)
          by (unfold SAVES in Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx; lia).
        destruct (Hsv x Hx') as (Ha & Hb'). cbn [outside]. split; [exact Ha|]. split; [exact Hb' | exact I]. }
      split.
      { exists hh. apply (rc_bytes_at_munch rsegs _ mc m2 FS _ HH MU2). intros x Hx.
        rewrite length_le8 in Hx.
        destruct (Hfh x Hx) as (Ha & Hb'). cbn [outside]. split; [exact Ha|]. split; [exact Hb' | exact I]. }
      apply (rc_bytes_at_munch rsegs _ mc m2 (fr + 56) _ F56 MU2). intros x Hx.
      rewrite length_le8 in Hx.
      destruct (Hf56 x ltac:(clear - Hx; lia)) as (Ha & Hb'). cbn [outside].
      split; [exact Ha|]. split; [exact Hb' | exact I]. }
    step. step.
    eapply (Hrel fr f spc j n w56 m2 1).
    - exact HK.
    - rewrite Epo. symmetry. exact Er.
    - rewrite Epo. exact BI2.
    - rewrite Epo. rewrite <- EJ. exact (mb_rw1 _ _ _ _ _ RW2).
  Qed.

  (* b = 1 (0x86a44): a1 = JOIN_0014, then the copy at 0x86a4c. *)
  Lemma c12_case1F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 1 -> p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86a44) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 Hb Hp Ho HK HB HOc.
    pose proof HRNG as HR. mbF_open HR.
    pose proof HB as (_ & _ & _ & MI & _).
    pose proof (AJ1 Hb) as AS.
    destruct (HO Ho) as (_ & _ & HOj).
    pose proof c12_j14 as (J0 & JG).
    assert (DJ : o + 32 <= JOIN_0014 \/ JOIN_0014 + 32 <= o)
      by (clear - HOj; unfold JOIN_0013, JOIN_0014 in HOj |- *; lia).
    step. step.
    eapply (c12_joinF JOIN_0014 J14 fr f spc j n w56 mc);
      [exact Hp | exact Ho | exact HK | exact HB | exact HOc | exact AS | | reflexivity | exact J0 | exact JG
      | exact DJ | rewrite Hb; reflexivity | rewrite Hb; reflexivity
      | eapply rng_sub; [exact RIMG | clear - Hb; unfold JOIN_0014; lia | clear - Hb; unfold JOIN_0014; lia]
      | destruct (RJ4 Hb) as (_ & _ & RJ4k); exact RJ4k
      | intros a Ha; exact (mbHB_R_j14 (bv_unsigned sp) FS p b o row nb a Hb Ha)].
    apply rc_ro_in_image; [exact MI | vm_compute; reflexivity].
  Qed.

  (* b = 2 (0x869fc): a1 = JOIN_0013, j 0x86a4c, then the copy. *)
  Lemma c12_case2F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 2 -> p <> 0 -> o <> 0 -> FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x869fc) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 Hb Hp Ho HK HB HOc.
    pose proof HRNG as HR. mbF_open HR.
    pose proof HB as (_ & _ & _ & MI & _).
    pose proof (AJ2 Hb) as AS.
    destruct (HO Ho) as (_ & _ & HOj).
    pose proof c12_j13 as (J0 & JG).
    assert (DJ : o + 32 <= JOIN_0013 \/ JOIN_0013 + 32 <= o)
      by (clear - HOj; unfold JOIN_0013, JOIN_0014 in HOj |- *; lia).
    step. step. step.
    eapply (c12_joinF JOIN_0013 J13 fr f spc j n w56 mc);
      [exact Hp | exact Ho | exact HK | exact HB | exact HOc | exact AS | | reflexivity | exact J0 | exact JG
      | exact DJ | rewrite Hb; reflexivity | rewrite Hb; reflexivity
      | eapply rng_sub; [exact RIMG | clear - Hb; unfold JOIN_0013; lia | clear - Hb; unfold JOIN_0013; lia]
      | destruct (RJ3 Hb) as (_ & _ & RJ3k); exact RJ3k
      | intros a Ha; exact (mbHB_R_j13 (bv_unsigned sp) FS p b o row nb a Hb Ha)].
    apply rc_ro_in_image; [exact MI | vm_compute; reflexivity].
  Qed.
End Case12F.
