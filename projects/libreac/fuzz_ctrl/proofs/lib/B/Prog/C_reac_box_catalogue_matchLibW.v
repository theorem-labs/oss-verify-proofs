(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths and numbers changed; 1731 of its 2038 lines of code are new or changed and 2794 lines of the source are left out. *)
(* reac_box_catalogue_match (0x84e40) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): stretches 2, 3, 4 and 6
   of C_reac_box_catalogue_matchLib.v, re-based on their own base memory mb as there, but each with ITS OWN write list
   (brief LIBW-BRIEF.md (a working note, not in this delivery); rulings
   decisions.md item 28 (a working note, not in this delivery) and a Theorem Labs lane's re-base form).  rule 24:
   no function proved; this file re-states green scripts of this lane's own proof with a narrower write list.

   WHY.  The cmRB_* lemmas of C_reac_box_catalogue_matchLib.v instantiate reac_box_catalogue_matchF_on.v, so their posts
   carry that file's list aWc Sp FS = window :: fp_w [0; 1; 2] FS ++ [window shadow] (stretch 6: the same list in
   cmPost).  fp_w names allocator-owned bytes (the class hints, every flag byte, every class-0/1/2 frame), so the glue
   cannot journal those stretches.  Inside a re-based stretch the code writes less:
     cmWst Sp fr = [(Sp - 9136, Sp); (fr, fr + 256); (shadow_addr fr, shadow_addr fr + 32)]
   (the window, the stretch's own class-2 frame and that frame's shadow; stretch 6 writes nothing).

   HOW.  The scripts behind the four stretches are copied from reac_box_catalogue_matchF.v (077bb7bcf14, the accepted
   text; line numbers below are of that file), re-pointed at its route-(C) `_on` copy reac_box_catalogue_matchF_on.v
   (same lemma names; its Section hypothesis SRo : shadow_rw_on R m, R := reac_box_catalogue_match_shadow_R f len Sp FS,
   is each copy's `SR` premise; the copies take that file's patches where they copy its text: the frame's shadow bytes
   by cm_srw_fr, the invariant's transport cmSRT across a callee by cmSRT_step, the bcmp wrapper's region by
   cmOn_R_bcmp, cm_mk_inv without SR, cm_shadow_rw_write over cmSRT).
   The ONE change of each copy beyond those: the invariant carries cmWst from the stretch's base
   memory.  cmInvW = cmInv /\ munch (cmWst Sp fr) m mc; the munch hypothesis stays in the context of every store
   step, so StepF's store_done (footprint_after_store, "store outside the declared footprint") checks each store
   against cmWst.  No store fell outside cmWst.  The one callee inside a stretch (stretch 4's bcmp wrapper) writes
   [(sp2 - 4560, sp2)] by its contract, inside the window (the sub_fp step at the end of cmW_bc).
     cmW_header        <- cm_header        :1898-1973
     cmW_post_sm2_side <- cm_post_sm2_side :2298-2479 (x1 free at the start state: the world rule
                                                      YCbq.aj_stack_malloc_at leaves ra unconstrained)
     cmW_pre_parse     <- cm_pre_parse     :3943-4087
     cmW_tail_K        <- cm_tail_K        :2637-2659 (the Ltacs cm_sh_begin :2592 and cm_sh_rd :2625 inlined)
     cmW_pre_mb        <- cm_pre_mb        :3292-3315
     cmW_turn_head     <- cm_turn_head     :3320-3370
     cmW_post_parse_K  <- cm_post_parse_K  :4092-4179 (start state cmW_parse_post <- cm_parse_post :3923-3938,
                                                      x1 free: TPARSE's world post keeps only callee-saved ones)
     cmW_bc            <- cm_bc            :3569-3661
     cmW_post_mb_K     <- cm_post_mb_K     :3668-3782 (x1 free at the start: likewise for TMB)
     cmW_post_rel      <- cm_post_rel      :972-1158 (its assertion SUB :1064-1073 dropped: it only fed the
                                                     replaced munch conjunct of cmPost)
   The invariant cmJ :492 / cmInv :1536 and its step lemmas (cm_inv_step :1804, cm_mk_inv :2002, cm_call_inv :2922,
   cm_win_inv :3169) are used as they are; the write list is the added conjunct.  The tactics of the F file
   (:93-148, :202-208, :1872-1893, :2059-2079, :2690-2699, :3152-3166, :3867-3890) are local to its sections, so they
   are copied below.  Changes beyond the write list, all from closing the F file's sections: each copy quantifies the
   section variables and exactly the section hypotheses its source's discharged form takes, in the same order; the
   F file's lemmas are applied to their section arguments (posed as a local hypothesis of the same name); its
   definitions take their arguments (CA Sp, cmFK Sp FS, cmSAVES ra s0 .. s11, ...).
   The base of stretches 2 and 3 is the callee's return memory (premise ms_mem ms' = m), as in the re-based lemmas;
   stretches 4 and 6 start from cmInvW / cmAtRel at their base.  Beyond the source, cmKBW's continuation and every
   end state (cm_exit_atW, cmQw_gate) take the frame (fr sp2 jj nn) as parameters, where the source quantifies it
   per exit: the script never changes fr, so each end is at the frame the stretch starts with (stretch 2: the
   request's frame j, cmW_fs_post_2 taking j as a parameter for the source's `exists j`).

   THE RE-BASED LEMMAS (shape of cmRB_post_sm2_side / cmRB_post_parse / cmRB_post_mb / cmRB_post_rel; the run on
   MemNorm.normalize rsegs mb, back through MemNormF.evtF_normalize_ro / evtF_rel_ro, posts relative to mb with
   ro_agree, never mem_inv):
     cmRBw_post_sm2_side  exports munch (cmWst Sp fr) mb mc (cmRBw_J), at fr = fs_frame FS 2 j, sp2 = CA Sp,
                          jj = j, nn = 1 (cmRBw_gate's frame parameters)
     cmRBw_post_parse     exports munch (cmWst Sp fr) mb mc (cmRBw_J), at the incoming fr sp2 jj nn
     cmRBw_post_mb        exports munch (cmWst Sp fr) mb mc (cmRBw_J), at the incoming fr sp2 jj nn
     cmRBw_post_rel       exports munch [] m0 m', m0 the memory after the release store (cmRBw_Post)
   cmBase and its helpers are C_reac_box_catalogue_matchLib.v's, Required qualified. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* StepF after Step, as in reac_box_catalogue_matchF_on.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_catalogue_match reac_box_catalogue_matchF_on.
(* route (C): the region form, its transports, the bcmp wrapper's `_on` contract and region inclusion *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c_on reac_box_catalogue_matchF_onIncl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds C_reac_box_catalogue_matchLib.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The tactics of reac_box_catalogue_matchF.v, copied (local to its sections there).  Three adaptations: cm_wv
   matches any base memory (the F file's version names its section's m); cm_wst and cm_rdm apply wv_store_ok and
   rd_mono_list at their section arguments, which each proof poses and these tactics find by type; cm_hdr_out takes
   cm_sh_add8 at its section arguments as its third argument.  cm_rdm finds the bounds of CA in the context (the F
   file's script poses CA_facts before every call). *)
Ltac acc_close_with H :=
  lazymatch goal with
  | |- acc_in ?RG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | lib.Lib.ExecF.rng RG ?lo ?len =>
          apply (rng_acc_litZ' RG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
          Z.div_mod_to_equations; lia
      end
  | |- acc_in ?RG (?a, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | lib.Lib.ExecF.rng RG ?lo ?len =>
          apply (rng_acc_varZ RG lo len a n nz H (@eq_refl Z nz));
          Z.div_mod_to_equations; lia
      end
  end.
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RG (?a, ?n) =>
      let E := addr_expr a in
      lazymatch E with
      | context[Z.div _ _] =>
          first [ let X := leftmost E in
                  match goal with
                  | H : lib.Lib.ExecF.rng RG ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with H
                  end
                | match goal with H : lib.Lib.ExecF.rng RG _ _ |- _ => acc_close_with H end ]
      end
  end.

Ltac cmF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (lib.Lib.Tac.le8_lit z) by lia
  | |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (lib.Lib.Tac.le4_lit z) by lia
  | |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (lib.Lib.Tac.le2_lit z) by lia
  | |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (lib.Lib.Tac.le1_zlit z) by lia
  | _ => idtac
  end.

Ltac cmF_store_opt :=
  try cmF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (lib.Lib.MState.MS _ _ _ _ _ (write_to_mem ?m (lib.Lib.Mem.wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : lib.Lib.Step.rw_cells segs m A _ |- _ => OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= cmF_store_opt.

Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (lib.Lib.MState.MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (lib.Lib.Mem.wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs _ (lib.Lib.Mem.wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs _ (lib.Lib.Mem.wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs _ (lib.Lib.Mem.wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      lazymatch goal with
      | WVS : forall (m0 mc : word -> option byte) (a0 : Z) (n0 : nat), _ -> _ -> _ -> _ ->
                store_ok _ _ _ _ = true |- _ =>
          assert (HS : store_ok rsegs mm (lib.Lib.Mem.wa a) n = true)
            by (eapply WVS;
                [ cm_wv | eassumption
                | try unfold ASAN_K; Z.div_mod_to_equations; lia
                | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
      end
  end.

Ltac cm_hdr_out HFSapp HHm8 SA8 :=
  cbn [lib.Lib.Frame.outside]; unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in *
               | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in *
               | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in *
               | change (2 ^ (15 - 2)) with 8192 in *
               | change (2 ^ 14) with 16384 in *
               | change (2 ^ 13) with 8192 in *
               | change (2 ^ 12) with 4096 in * ];
  repeat split; try exact I;
  first
    [ lia
    | match goal with
      | |- ~ (shadow_addr ?frr <= ?xx < _) =>
          let A := fresh "A" in let B := fresh "B" in intros [A B];
          pose proof (acl_sh_out xx frr (frr + 8 * 32) ltac:(apply HFSapp; unfold FS_SIZE; lia)
                        ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso;
          rewrite (SA8 frr 32 HHm8) in Hso; apply Hso; split; [exact A | exact B]
      end ].

Ltac fs_num :=
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in * | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in * | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in * | change (2 ^ (15 - 2)) with 8192 in *
               | change (2 ^ (14 - 2)) with 4096 in * | change (2 ^ 14) with 16384 in *
               | change (2 ^ 13) with 8192 in * | change (2 ^ 12) with 4096 in *
               | change (2 ^ 20) with 1048576 in * | change (2 ^ 0) with 1 in * | change (2 ^ 1) with 2 in *
               | change (2 ^ 2) with 4 in * ];
  unfold FS_SIZE in *.

Ltac cm_keep HB :=
  lazymatch goal with
  | |- evtF ?segs ?RG ?Q (lib.Lib.MState.MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (lib.Lib.Mem.wa E) bs);
      assert (HB : lib.Lib.Mem.bytes_at segs (write_to_mem mm (lib.Lib.Mem.wa E) bs) E bs)
        by (apply lib.Lib.Mem.bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.

Ltac cm_rdm MU STW STF STS :=
  lazymatch goal with
  | RML : forall (W : list lib.Lib.Frame.ivl) (mm mm' : word -> option byte), lib.Lib.Frame.munch W mm mm' -> _ -> rd_mono mm mm' |- _ =>
      apply (RML _ _ _ MU); repeat constructor; cbn [fst snd]; intros y Hy;
      [ apply (rd_of_stk _ _ _ STW); lia
      | apply (rd_of_stk _ _ _ STF); lia
      | apply (rd_of_stk _ _ _ STS); lia ]
  end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold lib.Lib.Mem.sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RG ?Q (lib.Lib.MState.MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RG Q (lib.Lib.MState.MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(lib.Lib.MState.unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
          replace (X mod 8 <? bv_signed k) with true
            by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]);
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(lib.Lib.MState.unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac no_extra X := idtac.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The stretch's own write list and the invariant that carries it from the base memory m. *)
Definition cmWst (Sp fr : Z) : list lib.Lib.Frame.ivl :=
  [(Sp - 9136, Sp); (fr, fr + 256); (shadow_addr fr, shadow_addr fr + 32)].

(* cmInv (= cmJ) with the stretch's write list. *)
Definition cmInvW (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc /\
  lib.Lib.Frame.munch (cmWst Sp fr) m mc.

(* cmKB :1540 over cmInvW.  The continuation Q takes the frame (fr sp2 jj nn) of the invariant it is called with, so
   a post built from it keeps that frame (no fresh frame per exit). *)
Definition cmKBW (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint)
    (Q : Z -> Z -> Z -> Z -> machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
    cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
    evtF rsegs RNG (Q fr sp2 jj nn)
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
               ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
               rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84f88) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).

(* cm_exit_at :1377 over cmInvW, at a given frame (fr sp2 jj nn): the frame is a parameter, not a witness. *)
Definition cm_exit_atW (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  exists (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
    r = want CM_T len fb /\ cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc /\
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp)) y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
                 (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x850fc) fc None mc (lib.Lib.PropExec.seg_rom rsegs).

(* cm_exit_at_intro :1386 for cm_exit_atW. *)
Lemma cmW_exit_at_intro : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z)
    (mc : word -> option byte) (r : Z) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  cm_exit_atW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850fc) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn mc r
    x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HJ.
  exists mc, r, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9, z10, z11, u3, u4, u5, u6.
  split; [exact Er|]. split; [exact HJ | reflexivity].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* cm_header :1898-1973.  The header's 27 stores (CA + 16, fr .. fr + 16, the 24 shadow bytes of fr) are checked
   against cmWst Sp fr by store_done (MUw). *)
Lemma cmW_header : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (Q : Z -> Z -> Z -> Z -> machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rs7 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
  cmKBW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG Q ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  evtF rsegs RNG (Q fr sp2 jj nn)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
             rs6 rs7 (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84ee4) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (fk_facts tp m f len Sp FS fb Rf Rlen S16 HK ST Hfb SR AW FP0) as fk_facts.
  pose proof (cm_srw_fr m f len Sp FS SR) as cm_srw_fr.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (cm_sh_add8 f len Sp fb Rf Rlen Hfb) as cm_sh_add8.
  pose proof (rd_mono_list f len Sp fb Rf Rlen Hfb) as rd_mono_list.
  pose proof (cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_inv_step.
  pose proof (wv_store_ok f len Sp fb Rf Rlen Hfb) as cmW_wvs.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rs7 rs9 rs10 rs11 rt3 rt4 rt5 rt6 K INVW.
  destruct INVW as (INV & MUw).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & MIg & (ACg & SRg & FPg & TLg) & AWXg & EXTg & STWg & STFg & SVg & FLg).
  clear MUg AWXg EXTg SVg FLg FPg TLg ACg.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & _).
  pose proof RFS as RFS'. unfold shadow_addr in RFS'.
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  unfold shadow_addr in FSW.
  assert (cmSTW : forall a, Sp - 9136 <= a < Sp -> wview rsegs m (lib.Lib.Mem.wa a) <> None)
    by (intros a Ha; exact (cm_stk_wv m _ _ _ ST Ha)).
  assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (fr / 8 + ASAN_K + k)).
  { intros k Hk. pose proof (rt_app_shadow (fr + 8 * k) (FAP (8 * k) ltac:(lia))) as H.
    rewrite (cm_sh_add8 fr k FR8) in H. unfold shadow_addr in H. exact H. }
  assert (SHlo : 0 <= fr / 8 + ASAN_K) by (pose proof (rt_shadow_bound _ (SHIN 0 ltac:(lia))); lia).
  assert (SHhi : fr / 8 + ASAN_K + 24 <= 2 ^ 64) by (pose proof (rt_shadow_bound _ (SHIN 23 ltac:(lia))); lia).
  assert (STSH : lib.Lib.Frame.stk rsegs mc (fr / 8 + ASAN_K) (fr / 8 + ASAN_K + 24)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    replace a with (fr / 8 + ASAN_K + (a - (fr / 8 + ASAN_K))) by lia.
    apply (cm_srw_fr fr sp2 jj nn mc _ FK SRg); [unfold shadow_addr; lia | apply SHIN; lia]. }
  clear SRg.
  assert (MUh : lib.Lib.Frame.munch (cmHF Sp fr) mc mc) by apply lib.Lib.Frame.munch_refl.
  assert (WMh : lib.Lib.Frame.wmono rsegs mc mc) by apply lib.Lib.Frame.wmono_refl.
  unfold cmHF, shadow_addr in MUh.
  unfold cmWst, shadow_addr in MUw.
  cm_wst (CA Sp + 16) 8%nat. step. store_done.
  do 3 step.
  step. rewrite (lib.Lib.MState.unsigned_lit fr) by lia. rewrite rc_shr3.
  do 6 step.
  cm_wst fr 8%nat. step. store_done.
  cm_wst (fr + 8) 8%nat. step. store_done.
  cm_wst (fr + 16) 8%nat. step. store_done.
  step. step.
  cm_wst (fr / 8 + ASAN_K) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 1) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 2) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 3) 1%nat. step. store_done.
  step.
  cm_wst (fr / 8 + ASAN_K + 4) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 5) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 6) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 7) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 8) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 9) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 10) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 11) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 12) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 13) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 14) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 15) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 20) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 21) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 22) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 23) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 16) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 17) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 18) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 19) 1%nat. step. store_done.
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
    assert (RMh : rd_mono mc mf)
      by (apply (rd_mono_list _ mc mf MUh); repeat constructor; cbn [fst snd]; intros y Hy;
          [ apply (rd_of_stk _ _ _ STWg); lia
          | apply (rd_of_stk _ _ _ STFg); lia
          | apply (rd_of_stk _ _ _ STSH); lia ]) end.
  eapply (K fr sp2 jj nn).
  split; [eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg] | exact MUw].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* cm_fs_post_2 :2097 with x1 free (the world rule YCbq.aj_stack_malloc_at 2 at the class-2 return leaves ra
   unconstrained; a Theorem Labs lane, from a Theorem Labs lane) and the frame index j a parameter (the source's `exists j`), so the
   stretch's post can name the frame the request returned. *)
Definition cmW_fs_post_2 (gp tp s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (f len Sp FS : Z)
    (j : Z) (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : word -> option byte),
    ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra' (Z_to_bv 64 (CA Sp)) gp tp t0' t1' t2' (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                  a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                  s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (lib.Lib.MState.ret_pc (Z_to_bv 64 544436)) fc None m2 (lib.Lib.PropExec.seg_rom rsegs) /\
    lib.Lib.Frame.wmono rsegs m0 m2 /\ lib.Lib.Mem.mem_inv rsegs m2 /\ lib.Lib.Frame.stk rsegs m2 (Sp - 9136) (CA Sp) /\
    lib.Lib.Frame.stk rsegs m2 FS (FS + FS_SIZE) /\
    (exists h', lib.Lib.Mem.bytes_at rsegs m2 (fs_hint FS 2) (lib.Lib.Mem.le8 h')) /\
    (0 <= j < fs_M 2 /\
       a0' = Z_to_bv 64 (fs_frame FS 2 j) /\ fs_frame FS 2 j mod 64 = 0 /\
       lib.Lib.Mem.bytes_at rsegs m2 (fs_flag FS 2 j) [Z_to_bv 8 1] /\
       lib.Lib.Mem.bytes_at rsegs m2 (fs_frame FS 2 j + 256 - 8) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 j))) /\
       lib.Lib.Mem.bytes_at rsegs m2 (shadow_addr (fs_frame FS 2 j)) (repeat (Z_to_bv 8 0) (Z.to_nat 32)) /\
       lib.Lib.Frame.stk rsegs m2 (fs_frame FS 2 j) (fs_frame FS 2 j + 256) /\
       (forall a, fs_frame FS 2 j <= a < fs_frame FS 2 j + 256 -> app_mem a) /\
       FS <= fs_frame FS 2 j /\ fs_frame FS 2 j + 256 <= FS + FS_SIZE /\ ASAN_GT <= fs_frame FS 2 j /\
       fs_frame FS 2 j + 256 <= CA Sp - ASAN_STACK_MALLOC_K /\
       (forall (c' : nat) (j' : Z), (c' <= 10)%nat -> 0 <= j' < fs_M c' -> (c' <> 2%nat \/ j' <> j) ->
          fs_frame FS c' j' + fs_B c' <= fs_frame FS 2 j \/
          fs_frame FS 2 j + 256 <= fs_frame FS c' j') /\
       lib.Lib.Frame.munch [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 j, fs_flag FS 2 j + 1);
              (fs_frame FS 2 j + 24, fs_frame FS 2 j + 32);
              (fs_frame FS 2 j + 256 - 8, fs_frame FS 2 j + 256);
              (shadow_addr (fs_frame FS 2 j), shadow_addr (fs_frame FS 2 j) + 32);
              (CA Sp - ASAN_STACK_MALLOC_K, CA Sp)] m0 m2).

(* cm_post_sm2_side :2298-2479.  The base m is the request's return memory (ms_mem ms' = m), so the invariant's
   write list starts empty there (munch_refl); the request's own writes (the hint, the flag byte, the frame words) are
   before the base.  x1 is free at the start.  The continuation is reached at the request's frame j:
   fr = fs_frame FS 2 j, sp2 = CA Sp, jj = j, nn = 1. *)
Lemma cmW_post_sm2_side : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  asan_cells m -> shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) -> addressable m CM_T 3256 ->
  addressable m REAC_CTRL_PARSE_BC 6 -> lib.Lib.Mem.bytes_at rsegs m REAL_BCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa BCMP)) ->
  lib.Lib.Mem.bytes_at rsegs m REAL_MEMCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa MEMCMP)) -> lib.Lib.Mem.bytes_at rsegs m GOT_CF (lib.Lib.Mem.le8 (lib.Lib.Mem.wa CF)) ->
  lib.Lib.Mem.bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> lib.Lib.Mem.bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  reac_box_catalogue_match_tls m (bv_unsigned tp) FS (Sp - 9136) Sp ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  lib.Lib.Mem.bytes_at rsegs m CM_T CM_TBL ->
  forall (Q : Z -> Z -> Z -> Z -> machine_state -> Prop) (m0 : word -> option byte) (j : Z) (ms' : machine_state),
  cmKBW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG Q ->
  cmAtSM2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Sp m0 ->
  cmW_fs_post_2 gp tp s2 s6 s7 s8 s9 s10 s11 F fc f len Sp FS j m0 ms' -> ms_mem ms' = m ->
  evtF rsegs RNG (Q (fs_frame FS 2 j) (CA Sp) j 1) ms'.
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen RS S16 HK ST Hfb HF AC SR HHM HAE AW AFU AT ABC HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0
    RWIN RWSH RFPW BT.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (acl_fs tp m f len Sp FS FP0) as acl_fs.
  pose proof (cm_sh_add8 f len Sp fb Rf Rlen Hfb) as cm_sh_add8.
  pose proof (rd_mono_list f len Sp fb Rf Rlen Hfb) as rd_mono_list.
  pose proof (rd_of_bytes f len Sp fb Rf Rlen HK Hfb) as rd_of_bytes.
  pose proof (cm_stk_sub f len Sp fb Rf Rlen HK Hfb) as cm_stk_sub.
  pose proof (sh_out_app f len Sp fb Rf Rlen Hfb) as sh_out_app.
  pose proof (cm_flag_upd f len Sp FS fb Rf Rlen HK Hfb) as cm_flag_upd.
  pose proof (cm_mk_inv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb Rf Rlen S16 HK ST Hfb HF AC
                HHM HAE AW AFU AT ABC HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0 BT) as cm_mk_inv.
  pose proof (cmW_header ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
                Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW) as cm_header.
  intros Q m0 jj ms' K HAt PO Hbase.
  destruct HAt as (MU & WM & MI0 & STW & FR).
  destruct PO as (ra' & u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E &
                  WM2 & MI2 & ST2 & FQstk & (h2 & HH2') & (Hjj & FRM)).
  subst ms'. change (m2 = m) in Hbase.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  (* the class-2 flag array at the call memory m0 *)
  pose proof (fl_fp [0%nat;1%nat;2%nat] m m0 (bv_unsigned tp) FS (Sp - 9136) Sp [] (aDf f len)
                [(Sp - 9136, Sp)] FP0 MU WM ltac:(intros x Hx; exact Hx)) as FP1.
  destruct FP1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCL1 & _).
  pose proof HCL1 as HCL1'. do 2 apply Forall_cons_iff in HCL1' as [_ HCL1']. apply Forall_cons_iff in HCL1' as [HC2 _].
  destruct HC2 as (_ & h & flags & HH2 & HF2 & HFl2 & HFb2).
  replace (lib.Lib.MState.ret_pc (Z_to_bv 64 544436)) with (Z_to_bv 64 544436)
    by (symmetry; apply lib.Lib.MState.ret_pc_even; [lia | reflexivity]).
  step. step. step. step.
  pose proof acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof FP0 as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & _ & _ & _ & HCLx & _).
  pose proof HCLx as HCLy.
  apply Forall_cons_iff in HCLy as [(_ & h0 & flags0 & HH0 & HF0 & HFl0 & HFb0) HCLy1].
  apply Forall_cons_iff in HCLy1 as [(_ & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1) HCLy2].
  apply Forall_cons_iff in HCLy2 as [(_ & h2m & flags2m & HH2m & HF2m & HFl2m & HFb2m) _].
    destruct FRM as (Ex0 & Hm64 & HFL & Hflagword & HSH & STF & APF & FSlo & FShi' & GT & FRA' & DIS & MU2).
    remember (fs_frame FS 2 jj) as fr eqn:Efr.
    subst x0.
    unfold FS_SIZE in FShi'. change (fs_M 2) with 4096 in Hjj.
    unfold ASAN_STACK_MALLOC_K in MU2, FRA'.
    replace (fr + 256 - 8) with (fr + 248) in * by lia.
    assert (Hm8 : fr mod 8 = 0) by (clear -Hm64; Z.div_mod_to_equations; lia).
    unfold ASAN_GT in GT.
    assert (Hfrlo : FS + 36864 <= fr) by
      (rewrite Efr; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576;
       change (2 ^ 2) with 4; lia).
    rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
    assert (FLb : FS + 28672 <= fs_flag FS 2 jj < FS + 32768).
    { unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 15) with 32768. change (2 ^ (15 - 2)) with 8192.
      lia. }
    assert (SHb : shadow_addr fr + 32 <= Sp - 9136).
    { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (STW2 : lib.Lib.Frame.stk rsegs m2 (Sp - 9136) Sp).
    { apply (fl_stk _ m0 m2 _ _ STW MU2 WM2). intros x Hx.
      destruct (Z_lt_le_dec x (CA Sp - 208)) as [L|L]; [|destruct (Z_lt_le_dec x (CA Sp)) as [L2|L2]].
      - left. cbn [lib.Lib.Frame.outside]. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat].
        repeat split; try exact I; lia.
      - right. apply (rd_of_stk _ _ _ ST2). lia.
      - left. cbn [lib.Lib.Frame.outside]. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat].
        repeat split; try exact I; lia. }
    assert (WMw : lib.Lib.Frame.wmono rsegs m m2) by (apply (lib.Lib.Frame.wmono_trans _ _ _ _ WM WM2)).
    assert (FR2 : lib.Lib.Step.rw_cells rsegs m2 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (lib.Lib.Frame.rw_cells_transport rsegs _ m0 m2 _ _ FR MU2 WM2).
      cbn [lib.Lib.Frame.disjoint_from lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add cmSAVES].
      unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat].
      repeat split; right; first [ lia | (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia) ]. }
    assert (MUw : lib.Lib.Frame.munch [(Sp - 9136, Sp); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                         (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32);
                         (CA Sp - 208, CA Sp)]
                        m m2).
    { apply (lib.Lib.Frame.munch_trans _ m m0 m2).
      - eapply lib.Lib.Frame.munch_weaken; [|exact MU]. intros x Hx. cbn [lib.Lib.Frame.outside] in *.
        split; [exact (proj1 Hx) | exact I].
      - eapply lib.Lib.Frame.munch_weaken; [|exact MU2]. intros x Hx. cbn [lib.Lib.Frame.outside] in Hx. exact (proj2 Hx). }
    assert (RMw : rd_mono m m2).
    { apply (rd_mono_list _ m m2 MUw). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_stk _ _ _ STW2). lia.
      - apply (rd_of_stk _ _ _ FQstk). unfold fs_hint in Hy. cbn [Z.of_nat Pos.of_succ_nat] in Hy. unfold FS_SIZE. lia.
      - apply (rd_of_stk _ _ _ FQstk). unfold FS_SIZE. lia.
      - apply (rd_of_stk _ _ _ STF). lia.
      - apply (rd_of_stk _ _ _ STF). lia.
      - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    eapply (cm_header Q fr (CA Sp) jj 1 m2); [exact K|].
    (* the write list at the join: m2 is the base *)
    split; [|rewrite Hbase; apply lib.Lib.Frame.munch_refl].
    apply (cm_mk_inv fr (CA Sp) jj 1 m2 [(Sp - 9136, Sp); (fs_hint FS 2, fs_hint FS 2 + 8);
                     (fs_flag FS 2 jj, fs_flag FS 2 jj + 1); (fr + 24, fr + 32); (fr + 248, fr + 256);
                     (shadow_addr fr, shadow_addr fr + 32); (CA Sp - 208, CA Sp)]).
    + right. split; [exact Hjj | split; [exact Efr | split; reflexivity]].
    + exact MUw.
    + exact WMw.
    + exact RMw.
    + exact MI2.
    + intros x Hx. unfold aWc in Hx. cbn [lib.Lib.Frame.outside] in Hx. destruct Hx as (Hwn & Hxs).
      unfold aXs in Hxs. apply fl_out_app_inv in Hxs. destruct Hxs as (Hfpw & Hws).
      cbn [lib.Lib.Frame.outside] in Hws. destruct Hws as (Hws & _).
      cbn [lib.Lib.Frame.outside]. split; [exact Hwn|]. split.
      { exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))). }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_flag FS 2 ltac:(cbn; tauto))).
        unfold fs_flag, fs_M in *. destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
        change (2 ^ 12) with 4096 in *. destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
        change (2 ^ 12) with 4096 in *. destruct Hc. split; lia. }
      split.
      { pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
        assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr).
        { apply acl_sh_ge. rewrite Efr. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
          change (2 ^ 20) with 1048576. lia. }
        assert (LE : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
        { rewrite Efr. unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
          change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
          change (2 ^ 12) with 4096 in *. Z.div_mod_to_equations; lia. }
        intros [A B]. clear -HFin GE LE A B. lia. }
      split; [|exact I].
      intros Hc. apply Hwn. clear -Hc CAlo CAhi. lia.
    + intros y Hy _.
      assert (Hap : app_mem y) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
      pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [lib.Lib.Frame.outside]. split.
      { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. cbn [Z.of_nat Pos.of_succ_nat] in *. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
        intros z Hz. apply FSapp. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 24) (fr + 32) Hsh).
        intros z Hz. apply APF. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 248) (fr + 256) Hsh).
        intros z Hz. apply APF. lia. }
      split; [|split; [|exact I]].
      { intros [A B]. pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
        rewrite (cm_sh_add8 fr 32 Hm8) in G. lia. }
      { apply (sh_out_app (shadow_addr y) (CA Sp - 208) (CA Sp) Hsh).
        intros z Hz. right. unfold HIGHMEM_BEG, APPMEM_END. clear -Hz Hy HHM' HAE' CAlo CAhi. lia. }
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (lib.Lib.Mem.le8 h0) HH0 MUw).
           intros x Hx. rewrite lib.Lib.Mem.length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8 cm_sh_add8.
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUw).
           intros x Hx. rewrite HFl0 in Hx.
           cm_hdr_out FSapp Hm8 cm_sh_add8.
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (lib.Lib.Mem.le8 h1) HH1 MUw).
           intros x Hx. rewrite lib.Lib.Mem.length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8 cm_sh_add8.
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUw).
           intros x Hx. rewrite HFl1 in Hx.
           cm_hdr_out FSapp Hm8 cm_sh_add8.
      * split.
        -- exists h2. exact HH2'.
        -- apply (cm_flag_upd m0 m2
             [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
              (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA Sp - 208, CA Sp)]
             flags jj Hjj HFl2 HFb2 HF2 MU2); [| exact HFL].
           intros x Hx Hxne.
           assert (Hxap : app_mem x) by (apply FSapp; unfold fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *;
             change (2 ^ (14 - 2)) with 4096 in *; change (2 ^ 12) with 4096 in *; unfold FS_SIZE; lia).
           assert (FL0 : fs_flag FS 2 0 = FS + 28672).
           { unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 15) with 32768.
             change (2 ^ (15 - 2)) with 8192. lia. }
           assert (FLj : fs_flag FS 2 jj = FS + 28672 + jj) by (unfold fs_flag in *; lia).
           change (fs_M 2) with 4096 in Hx.
           cbn [lib.Lib.Frame.outside]. split.
           { unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
           split.
           { intros [A B]. apply Hxne. lia. }
           split; [lia|].
           split; [lia|].
           split; [|split; [|exact I]].
           { intros [A B]. pose proof (acl_sh_out x fr (fr + 8 * 32) Hxap ltac:(lia) ltac:(unfold APPMEM_END; lia))
               as Hso.
             rewrite (cm_sh_add8 fr 32 Hm8) in Hso. apply Hso. split; [exact A | exact B]. }
           { lia. }
    + apply (cm_stk_sub _ fr (fr + 256)); [exact STF | lia | lia].
    + exact FR2.
    + intros _. exact Hflagword.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* cmAtParse :3915 over cmInvW. *)
Definition cmAtParseW (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (m0 : word -> option byte) : Prop :=
  50 <= len /\
  bv_unsigned (nth 12 fb (Z_to_bv 8 0)) = 136 /\ bv_unsigned (nth 13 fb (Z_to_bv 8 0)) = 25 /\
  bv_unsigned (nth 16 fb (Z_to_bv 8 0)) = 205 /\ bv_unsigned (nth 17 fb (Z_to_bv 8 0)) = 234 /\
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn m0 /\
  addressable m0 (fr + 32) 36.

(* cm_pre_parse :3943-4087.  The five shadow stores of the parse buffer are checked against cmWst Sp fr (MUw). *)
Lemma cmW_pre_parse : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  evtF rsegs RNG
    (fun ms => cm_exit_atW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn ms \/
       exists m0, ms =
         lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                 rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x83e04) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
         cmAtParseW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn m0)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
             rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x84f88) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU FP0 RWIN RWSH RFD RFW RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (cm_fr_bounds tp m f len Sp FS fb Rf Rlen S16 HK Hfb HHM FP0) as cm_fr_bounds.
  pose proof (fk_facts tp m f len Sp FS fb Rf Rlen S16 HK ST Hfb SR AW FP0) as fk_facts.
  pose proof (acl_fs tp m f len Sp FS FP0) as acl_fs.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (cm_shst_pre ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb SR AW FP0) as cm_shst_pre.
  pose proof (cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_inv_step.
  pose proof (cm_parse_addr f len Sp fb Rf Rlen Hfb) as cm_parse_addr.
  pose proof (cm_miss_short len fb) as cm_miss_short.
  pose proof (cm_miss_hdr len fb) as cm_miss_hdr.
  pose proof (rd_mono_list f len Sp fb Rf Rlen Hfb) as rd_mono_list.
  pose proof (wv_store_ok f len Sp fb Rf Rlen Hfb) as cmW_wvs.
  pose proof (cmW_exit_at_intro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb)
    as cm_exit_at_intro.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INVkW.
  pose proof INVkW as (INVk & MUw).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  pose proof Rf as Rfb. pose proof Rlen as Rlenb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  pose proof INVk as INVc.
  destruct INVc as (FK & _ & _ & MIg0 & (ACg0 & SRg0 & FPg0 & TLg0) & AWXg0 & EXTg0 & STWg0 & STFg0 & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup). unfold ASAN_GT in FRgt.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj0).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  (* 0x84f88: the length gate *)
  step. rewrite cm_ltu_lit by lia.
  destruct (Z.ltb_spec len 50) as [Lshort|L]; cbv iota.
  { step. apply evtF_done. cbv beta. left.
    apply (cm_exit_at_intro fr sp2 jj nn mc 0); [symmetry; exact (cm_miss_short Lshort) | exact INVkW]. }
  destruct EXTg0 as (EF & EAT & EBT & EBC & ECL).
  destruct (EF L) as (BF & AF).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  destruct (AFU L) as (_ & APf50).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & RFC).
  pose proof (RFD L) as RF50.
  pose proof (RFW L f 50 ltac:(lia) ltac:(lia) ltac:(lia)) as RFW0.
  (* 0x84f8c .. 0x84f94: the wrap tests of the input pointer (not taken) *)
  step. rewrite (rc_neq0_64 f) by lia. cbv iota.
  step. step. rewrite cm_ltu_neg_r by lia.
  replace (f <? -12 + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  (* the four header bytes *)
  pose proof (rd_byte rsegs mc f fb 12 BF ltac:(rewrite Hfb; clear; lia)) as R12.
  pose proof (rd_byte rsegs mc f fb 13 BF ltac:(rewrite Hfb; clear; lia)) as R13.
  pose proof (rd_byte rsegs mc f fb 16 BF ltac:(rewrite Hfb; clear; lia)) as R16.
  pose proof (rd_byte rsegs mc f fb 17 BF ltac:(rewrite Hfb; clear; lia)) as R17.
  change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
  change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
  pose proof (byte_range (nth 12 fb (Z_to_bv 8 0))) as BR12.
  pose proof (byte_range (nth 13 fb (Z_to_bv 8 0))) as BR13.
  pose proof (byte_range (nth 16 fb (Z_to_bv 8 0))) as BR16.
  pose proof (byte_range (nth 17 fb (Z_to_bv 8 0))) as BR17.
  assert (RX12 : 0 <= f + 12 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  assert (RX13 : 0 <= f + 13 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  assert (RX16 : 0 <= f + 16 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  assert (RX17 : 0 <= f + 17 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  pose proof (acl_shadow mc f 50 12 1 (f + 12) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 eq_refl); clear -H; lia) eq_refl) as SH12.
  pose proof (acl_shadow mc f 50 13 1 (f + 13) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 eq_refl); clear -H; lia) eq_refl) as SH13.
  pose proof (acl_shadow mc f 50 16 1 (f + 16) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 16) 8 eq_refl); clear -H; lia) eq_refl) as SH16.
  pose proof (acl_shadow mc f 50 17 1 (f + 17) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 17) 8 eq_refl); clear -H; lia) eq_refl) as SH17.
  (* byte 12: 0x88 *)
  step.
  pose proof (shc_byte RNG f 50 (f + 12) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 12 fb (Z_to_bv 8 0))) 136) as [E12|E12]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 12%nat 136 L ltac:(clear; lia) E12) | exact INVkW]. }
  (* byte 13: 0x19 *)
  step. step. rewrite cm_ltu_neg_l by lia.
  replace (-14 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  pose proof (shc_byte RNG f 50 (f + 13) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 13 fb (Z_to_bv 8 0))) 25) as [E13|E13]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 13%nat 25 L ltac:(clear; lia) E13) | exact INVkW]. }
  (* byte 16: 0xcd *)
  step. step. rewrite cm_ltu_neg_l by lia.
  replace (-17 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  pose proof (shc_byte RNG f 50 (f + 16) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 16 fb (Z_to_bv 8 0))) 205) as [E16|E16]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 16%nat 205 L ltac:(clear; lia) E16) | exact INVkW]. }
  (* byte 17: 0xea *)
  step. step. rewrite cm_ltu_neg_l by lia.
  replace (-18 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  pose proof (shc_byte RNG f 50 (f + 17) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 17) RX17 (Z_to_bv 5 12) SH17 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 17 fb (Z_to_bv 8 0))) 234) as [E17|E17]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 17%nat 234 L ltac:(clear; lia) E17) | exact INVkW]. }
  clear R12 R13 R16 R17 BR12 BR13 BR16 BR17 RX12 RX13 RX16 RX17.
  (* 0x85030 .. 0x85048: the parse buffer at fr + 32 is marked usable (shadow bytes 4..8 := 0,0,0,0,4) *)
  clear EF EAT EBT EBC ECL BF AF ACg0 SRg0 FPg0 TLg0 AWXg0 MIg0 STWg0 STFg0.
  destruct (cm_shst_pre _ _ _ _ _ INVk)
    as (FR8 & _ & _ & FAPc & FSWm & SHlo & SHhi & WMm & MIg & STWg & STFg & STSH).
  assert (MUh : lib.Lib.Frame.munch (cmHF Sp fr) mc mc) by apply lib.Lib.Frame.munch_refl.
  assert (WMh : lib.Lib.Frame.wmono rsegs mc mc) by apply lib.Lib.Frame.wmono_refl.
  unfold cmHF in MUh.
  unfold cmWst in MUw.
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. cm_keep B4.
  cm_wst (shadow_addr fr + 5) 1%nat. step. cm_keep B5.
  cm_wst (shadow_addr fr + 6) 1%nat. step. cm_keep B6.
  cm_wst (shadow_addr fr + 7) 1%nat. step. cm_keep B7.
  step.
  cm_wst (shadow_addr fr + 8) 1%nat. step. cm_keep B8.
  step. step.
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
    assert (RM1 : rd_mono mc mf) by (cm_rdm MUh STWg STFg STSH);
    assert (INV1 : cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mf)
      by (split; [eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RM1 | exact MIg] | exact MUw]);
    assert (AD1 : addressable mf (fr + 32) 36)
      by (apply (cm_parse_addr mf fr FR8 ltac:(lia) ltac:(unfold APPMEM_END; lia)
                   ltac:(intros ii Hii; replace (fr + 32 + ii) with (fr + (32 + ii)) by lia; apply FAPc; lia));
          [exact B4 | exact B5 | exact B6 | exact B7 | exact B8])
  end.
  clear B4 B5 B6 B7 B8 MUh WMh RM1.
  (* 0x85054: the call *)
  step.
  apply evtF_done. cbv beta. right. eexists. split; [reflexivity|].
  exact (conj L (conj E12 (conj E13 (conj E16 (conj E17 (conj INV1 AD1)))))).
Qed.

(* cm_tail_K :2637-2659, with the Ltacs cm_sh_begin :2592-2623 and cm_sh_rd :2625-2633 inlined.  The five shadow
   stores of the parse buffer are checked against cmWst Sp fr (MUw). *)
Lemma cmW_tail_K : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  evtF rsegs RNG (cm_exit_atW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850dc) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (fk_facts tp m f len Sp FS fb Rf Rlen S16 HK ST Hfb SR AW FP0) as fk_facts.
  pose proof (cm_srw_fr m f len Sp FS SR) as cm_srw_fr.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (cm_sh_add8 f len Sp fb Rf Rlen Hfb) as cm_sh_add8.
  pose proof (rd_mono_list f len Sp fb Rf Rlen Hfb) as rd_mono_list.
  pose proof (cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_inv_step.
  pose proof (wv_store_ok f len Sp fb Rf Rlen Hfb) as cmW_wvs.
  pose proof (cmW_exit_at_intro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb)
    as cm_exit_at_intro.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er INVkW.
  pose proof INVkW as (INVk & MUw).
  (* cm_sh_begin INVk *)
  pose proof INVk as INV.
  destruct INV as (FK & _ & WMg & MIg & (_ & SRg & _ & _) & _ & _ & STWg & STFg & _ & _).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & _).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (shadow_addr fr + k))
    by (intros k Hk; rewrite <- (cm_sh_add8 fr k FR8); apply rt_app_shadow; apply FAP; lia).
  assert (SHlo : 0 <= shadow_addr fr) by (pose proof (rt_shadow_bound _ (SHIN 0 ltac:(lia))); lia).
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64) by (pose proof (rt_shadow_bound _ (SHIN 23 ltac:(lia))); lia).
  assert (STSH : lib.Lib.Frame.stk rsegs mc (shadow_addr fr) (shadow_addr fr + 24))
    by (split; [lia|]; split; [lia|]; intros a Ha;
        replace a with (shadow_addr fr + (a - shadow_addr fr)) by lia;
        apply (cm_srw_fr fr sp2 jj nn mc _ FK SRg); [lia | apply SHIN; lia]).
  clear SRg.
  assert (MUh : lib.Lib.Frame.munch (cmHF Sp fr) mc mc) by apply lib.Lib.Frame.munch_refl.
  assert (WMh : lib.Lib.Frame.wmono rsegs mc mc) by apply lib.Lib.Frame.wmono_refl.
  unfold cmHF in MUh.
  unfold cmWst in MUw.
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 5) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 6) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 7) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 8) 1%nat. step. store_done.
  step.
  (* cm_sh_rd *)
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
    assert (RMh : rd_mono mc mf)
      by (apply (rd_mono_list _ mc mf MUh); repeat constructor; cbn [fst snd]; intros y Hy;
          [ apply (rd_of_stk _ _ _ STWg); pose proof CA_facts; lia
          | apply (rd_of_stk _ _ _ STFg); lia
          | apply (rd_of_stk _ _ _ STSH); lia ]) end.
  apply evtF_done.
  eapply (cm_exit_at_intro fr sp2 jj nn _ r); [exact Er|].
  split; [eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg] | exact MUw].
Qed.

(* cmAtMB :3269 over cmInvW. *)
Definition cmAtMBW (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (i : nat) (fr sp2 jj nn : Z) (m0 : word -> option byte) : Prop :=
  (i < 11)%nat /\ cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn m0 /\
  addressable m0 (fr + 112) 32.

(* cm_pre_mb :3292-3315 (no store). *)
Lemma cmW_pre_mb : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint)
    (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (w4 w9 : word) (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (i < 11)%nat -> w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  addressable mc (fr + 112) 32 ->
  evtF rsegs RNG
    (fun ms => exists m0, ms =
       lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
               w4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
               (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x865d8) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
       cmAtMBW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb i fr sp2 jj nn m0)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x8508c) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hi E4 INVk ADo.
  subst w4.
  do 4 step.
  apply evtF_done. cbv beta. exists mc. split; [reflexivity | exact (conj Hi (conj INVk ADo))].
Qed.

(* cm_turn_head :3320-3370.  The four shadow stores 14..17 are checked against cmWst Sp fr (MUw). *)
Lemma cmW_turn_head : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) (w4 w9 : word)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  cm_gate len fb = true -> (i < 11)%nat -> w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  evtF rsegs RNG
    (fun ms => exists m0, ms =
       lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
               w4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
               (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x865d8) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
       cmAtMBW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb i fr sp2 jj nn m0)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x8507c) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (cm_gate_len len fb) as cm_gate_len.
  pose proof (cm_shst_pre ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb SR AW FP0) as cm_shst_pre.
  pose proof (cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_inv_step.
  pose proof (cm_z4 f len Sp fb Rf Rlen HK Hfb) as cm_z4.
  pose proof (rd_mono_list f len Sp fb Rf Rlen Hfb) as rd_mono_list.
  pose proof (wv_store_ok f len Sp fb Rf Rlen Hfb) as cmW_wvs.
  pose proof (cmW_pre_mb ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG) as cm_pre_mb.
  intros i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hi E4 INVkW.
  pose proof INVkW as (INVk & MUw).
  subst w4.
  pose proof INVk as (FKl & _). pose proof (cm_fr_rng fr sp2 jj nn FKl) as (RFR & RFS & _). clear FKl.
  pose proof (cm_gate_len G) as L.
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  (* the four shadow bytes 14..17 of the frame := 0 *)
  destruct (cm_shst_pre _ _ _ _ _ INVk)
    as (FR8 & FRpos & FR192 & FAP & FSWm & SHlo & SHhi & WMm & MIg & STWg & STFg & STSH).
  assert (MUh : lib.Lib.Frame.munch (cmHF Sp fr) mc mc) by apply lib.Lib.Frame.munch_refl.
  assert (WMh : lib.Lib.Frame.wmono rsegs mc mc) by apply lib.Lib.Frame.wmono_refl.
  unfold cmHF in MUh.
  unfold cmWst in MUw.
  cm_wst (shadow_addr fr + 14) 1%nat. step. cm_keep B14.
  cm_wst (shadow_addr fr + 15) 1%nat. step. cm_keep B15.
  cm_wst (shadow_addr fr + 16) 1%nat. step. cm_keep B16.
  cm_wst (shadow_addr fr + 17) 1%nat. step. cm_keep B17.
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
    assert (RM1 : rd_mono mc mf) by (cm_rdm MUh STWg STFg STSH);
    assert (INV1 : cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mf)
      by (split; [eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RM1 | exact MIg] | exact MUw]);
    assert (AD1 : addressable mf (fr + 112) 32)
      by (replace (fr + 112) with (fr + 8 * 14) by lia;
          apply (cm_z4 mf fr 14 FR8 ltac:(lia) ltac:(lia) ltac:(unfold APPMEM_END; lia)
                   ltac:(intros ii Hii; replace (fr + 8 * 14 + ii) with (fr + (112 + ii)) by lia; apply FAP; lia));
          [exact B14 | exact B15 | exact B16 | exact B17])
  end.
  clear B14 B15 B16 B17 MUh WMh RM1.
  (* 0x8508c .. 0x85098: the stretch into the call of reac_box_model_block *)
  eapply cm_pre_mb; [exact Hi | reflexivity | exact INV1 | exact AD1].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* cm_parse_post :3923-3938 with x1 free (ra'): the callee's world post at the return (TPARSE) gives only the
   callee-saved registers, and ra is not one.  x1 is dead from the return 0x85058 on: the next write is the jal of
   reac_box_model_block at 0x85098, and the exit path ends at 0x850fc with x1 existential. *)
Definition cmW_parse_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (f len Sp FS : Z) (fb : list byte)
    (fr sp2 nn : Z) (rs6 rs9 rs10 rs11 : word) (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mp : word -> option byte),
    ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra' (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                  (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                  rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 t3' t4' t5' t6')
             F (lib.Lib.MState.ret_pc (Z_to_bv 64 0x85058)) fc None mp (lib.Lib.PropExec.seg_rom rsegs) /\
    lib.Lib.Frame.munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
           [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) m0 mp /\
    lib.Lib.Frame.wmono rsegs m0 mp /\ lib.Lib.Mem.mem_inv rsegs mp /\
    lib.Lib.Frame.stk rsegs mp (sp2 - REAC_CTRL_PARSE_K) sp2 /\
    lib.Lib.Step.rw_cells rsegs mp (fr + 32) [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))] /\
    (forall P, shadow_rw_on P m0 -> shadow_rw_on P mp) /\ addressable mp (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
    fp [1%nat] mp (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2 (reac_ctrl_parse_W (fr + 32) sp2)
      (reac_ctrl_parse_D f len (fr + 32)) /\
    reac_ctrl_parse_tls mp (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2.

(* cm_post_parse_K :4092-4179.  The base m is reac_ctrl_parse's return memory (ms_mem ms' = m): the invariant's
   write list starts empty there (munch_refl), the callee's writes being before the base.  The start state is
   cmW_parse_post's (x1 free). *)
Lemma cmW_post_parse_K : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (fr sp2 jj nn : Z) (mc : word -> option byte) (rs6 rs9 rs10 rs11 : word) (ms' : machine_state),
  cmAtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  cmW_parse_post gp tp F fc f len Sp FS fb fr sp2 nn rs6 rs9 rs10 rs11 mc ms' -> ms_mem ms' = m ->
  evtF rsegs RNG
    (fun ms => cm_exit_atW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn ms \/
       exists (m0 : word -> option byte) (v4 v9 : word)
              (zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
         ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp zt0 zt1 zt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                      v4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) za3 za4 za5 za6 za7
                      (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) v4 (Z_to_bv 64 (fr + 112))
                      (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) v9 (Z_to_bv 64 1)
                      (Z_to_bv 64 (-8)) zt3 zt4 zt5 zt6)
                 F (Z_to_bv 64 0x865d8) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
         cm_gate len fb = true /\ v4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat 0) /\
         v9 = Z_to_bv 64 (Z.of_nat 11) /\
         cmAtMBW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb 0 fr sp2 jj nn m0)
    ms'.
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU FP0 RWIN RWSH RFD RFW RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (cm_fr_bounds tp m f len Sp FS fb Rf Rlen S16 HK Hfb HHM FP0) as cm_fr_bounds.
  pose proof (fk_facts tp m f len Sp FS fb Rf Rlen S16 HK ST Hfb SR AW FP0) as fk_facts.
  pose proof (acl_fs tp m f len Sp FS FP0) as acl_fs.
  pose proof (rd_of_bytes f len Sp fb Rf Rlen HK Hfb) as rd_of_bytes.
  pose proof (cm_call_inv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_call_inv.
  pose proof (cmW_tail_K ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW) as cm_tail_K.
  pose proof (cmW_turn_head ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
                Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW) as cm_turn_head.
  intros fr sp2 jj nn mc rs6 rs9 rs10 rs11 ms' HAt PO Hbase.
  destruct HAt as (L & E12 & E13 & E16 & E17 & INV1 & AD1).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  pose proof Rf as Rfb. pose proof Rlen as Rlenb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  pose proof INV1 as INVc.
  destruct INVc as (FK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup). unfold ASAN_GT in FRgt.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj0).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  assert (Rlo : Sp - 9136 <= sp2 - 8800 <= sp2) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  assert (Lo8 : (sp2 - 8800) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  destruct PO as (ra' & p0 & p1 & p2 & pa1 & pa2 & pa3 & pa4 & pa5 & pa6 & pa7 & p3 & p4 & p5 & p6 & mp & -> &
                  MUp & WMp & MIp' & STp & RWp & SRp' & ADp & FPp' & TLp').
  change (mp = m) in Hbase.
  rewrite lib.Lib.MState.ret_pc_even by (try lia; reflexivity).
  rewrite ?lib.Lib.MState.unsigned_lit in MUp, STp, ADp, FPp', TLp' by lia.
  unfold reac_ctrl_parse_fp in MUp. unfold REAC_CTRL_PARSE_K in MUp, STp, ADp.
  replace (fr + 32 =? 0) with false in MUp by (symmetry; apply Z.eqb_neq; lia).
  cbn [app] in MUp.
  replace (fr + 32 + 36) with (fr + 68) in MUp by lia.
  apply (lib.Lib.Frame.munch_weaken _ (cmCF FS sp2 (sp2 - 8800) 32 68 1%nat fr)) in MUp;
    [| intros x Hx; unfold cmCF in Hx; cbn [fp_w flat_map fp_w1 app lib.Lib.Frame.outside] in Hx |- *; tauto].
  pose proof FPp' as FPc.
  destruct FPc as (DTp & TSp & Cp & Tp & DBp & kkp & _ & _ & HPp & _ & _ & HCLp & _).
  pose proof HPp as (_ & _ & _ & _ & STfsp).
  apply Forall_cons_iff in HCLp as [CL1 _].
  assert (INV2 : cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mp).
  { apply (cm_call_inv fr sp2 jj nn _ mp (cmCF FS sp2 (sp2 - 8800) 32 68 1%nat fr) (sp2 - 8800) 32 68 1%nat
             INV1 ltac:(lia) Rlo Lo8 ltac:(lia) ltac:(lia) MUp ltac:(intros x Hx; exact Hx) WMp MIp' STp).
    - replace (sp2 - (sp2 - 8800)) with 8800 by lia. exact ADp.
    - intros x Hx.
      destruct (cm_bytes_of_rw rsegs mp (fr + 32) 36 (snd (ctrlparse len fb)) RWp) as (BBp & LBp).
      apply (rd_of_bytes mp (fr + 32) _ BBp). rewrite LBp. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - exact STfsp.
    - exact (cmSRT_step m mc mp
               (cm_inv_srt ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc INV1) SRp').
    - exact CL1. }
  (* the write list at the base: mp is the base m *)
  assert (INV2W : cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mp)
    by (split; [exact INV2 | rewrite Hbase; apply lib.Lib.Frame.munch_refl]).
  (* 0x85058, 0x8505c: the parse result *)
  step. step.
  pose proof (ctrlparse_kind_range len fb) as KR.
  rewrite cm_eqb_lit by lia.
  destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
  2: { step.
       eapply evtF_mono;
         [ apply (cm_tail_K fr sp2 jj nn mp 0);
           [ symmetry; apply cm_gate_false; unfold cm_gate, cp_v, cp_b, cp_z;
             rewrite (proj2 (Z.eqb_neq _ _) K9); rewrite !andb_false_r; reflexivity
           | exact INV2W ]
         | intros msx Hx; cbv beta; left; exact Hx ]. }
  assert (G : cm_gate len fb = true).
  { unfold cm_gate, cp_v, cp_b, cp_z. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
  (* 0x85060 .. 0x85078: the loop's registers, then the first turn's head *)
  do 7 step.
  eapply evtF_cut;
    [ eapply (cm_turn_head 0%nat fr sp2 jj nn mp);
      [ exact G | lia
      | first [reflexivity | (unfold CM_T; f_equal; lia) | (vm_compute; reflexivity)]
      | exact INV2W ]|].
  intros msx (m0 & -> & HAtMB).
  apply evtF_done. cbv beta. right.
  exists m0. do 14 eexists.
  split; [reflexivity|].
  split; [exact G|].
  split; [first [reflexivity | (unfold CM_T; f_equal; lia) | (vm_compute; reflexivity)]|].
  split; [first [reflexivity | (f_equal; lia) | (vm_compute; reflexivity)]|].
  exact HAtMB.
Qed.

(* cm_bc :3569-3661.  The bcmp wrapper's contract writes [sp2 - 4560, sp2) (its window, inside Sp's window); that
   list is inside cmWst Sp fr, so the continuation gets cmInvW. *)
Lemma cmW_bc : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  bcmp_wrap_c_on.bcmp_wrap_contract_F_on ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  rng_bytes RNG -> lib.Lib.ExecF.rng RNG 65536 6217728 ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (Q : machine_state -> Prop) (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (w4 w9 : word) (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (i < 11)%nat -> 50 <= len ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  lib.Lib.Mem.bytes_at rsegs mc (fr + 112) (nth i DECLS []) -> addressable mc (fr + 112) 32 ->
  (forall (mc' : word -> option byte) (v : Z) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc' -> -256 < v < 256 ->
     (v = 0 <-> cm_blk fb = nth i DECLS []) ->
     evtF rsegs RNG Q
       (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x850b8) (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                (Z_to_bv 64 v) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
                (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
                (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
           F (Z_to_bv 64 0x850b8) fc None mc' (lib.Lib.PropExec.seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x850a8) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    HBC Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU FP0 RB RIMG RWIN RWSH RFD RFW RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (fk_facts tp m f len Sp FS fb Rf Rlen S16 HK ST Hfb SR AW FP0) as fk_facts.
  pose proof (cm_fr_bounds tp m f len Sp FS fb Rf Rlen S16 HK Hfb HHM FP0) as cm_fr_bounds.
  pose proof (acl_fs tp m f len Sp FS FP0) as acl_fs.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (cm_win_inv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_win_inv.
  pose proof (cm_stk_sub f len Sp fb Rf Rlen HK Hfb) as cm_stk_sub.
  intros Q i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    Hi L INVkW BB ADo K.
  pose proof INVkW as (INVk & MUw).
  pose proof INVk as INVc.
  destruct INVc as (FK & _ & _ & MIg & (ACg & SRg & FPg & TLg) & AWXg & EXTg & STWg & STFg & _ & _).
  destruct EXTg as (EF & EAT & EBT & EBC & ECL).
  destruct (EF L) as (BF & AF).
  destruct ECL as (C1 & C2 & C3 & C4 & C5).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  destruct (AFU L) as (_ & APf50).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSP).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt, FRgt.
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & _ & RFC). unfold sh_cover in RFC.
  pose proof (RFD L) as RF50. pose proof (RFW L) as RFW50. unfold sh_cover in RFW50.
  assert (Rlo : Sp - 9136 <= sp2 - 4560 <= sp2) by (destruct FSP; lia).
  assert (Lo8 : (sp2 - 4560) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  assert (FRsp : fr + 256 <= sp2 - 4560 \/ sp2 <= fr)
    by (destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)]; [right; lia | left; subst fr sp2; fs_num; lia]).
  pose proof (bytes_at_sub rsegs mc f fb 18 32 BF ltac:(lia)) as BK.
  apply (bytes_at_addr rsegs mc _ (f + 18)) in BK; [|lia].
  fold (cm_blk fb) in BK.
  assert (LK : length (cm_blk fb) = 32%nat) by (unfold cm_blk; rewrite length_firstn, length_skipn; lia).
  destruct (memcmp_model_total (cm_blk fb) (nth i DECLS []) 32 ltac:(lia) ltac:(rewrite cm_decl_len; lia))
    as [v Hv].
  pose proof (mm_spec 32 (cm_blk fb) (nth i DECLS []) v LK (cm_decl_len i Hi) Hv) as [MM VR].
  do 4 step.
  eapply evtF_cut.
  { eapply HBC with (RNG := RNG) (ls := cm_blk fb) (rs := nth i DECLS []) (v := v) (lo := sp2 - 4560).
    all: cbv zeta.
    all: rewrite ?lib.Lib.MState.unsigned_lit by lia.
    all: unfold BCMP_WRAP_K.
    all: lazymatch goal with
         | |- lib.Lib.Mem.bytes_at _ _ _ _ => first [exact BK | exact BB | exact C1 | exact C2 | exact C3 | exact C4 | exact C5]
         | |- memcmp_model _ _ _ = Some _ => exact Hv
         | |- lib.Lib.Mem.mem_inv _ _ => exact MIg
         | |- asan_cells _ => exact ACg
         | |- shadow_rw_on _ _ =>
             exact (shadow_rw_on_mono _ _ mc
                      (reac_box_catalogue_matchF_onIncl.cmOn_R_bcmp f len Sp FS fr sp2 jj nn L FK)
                      (cmSRT_R m f len Sp FS SR mc SRg))
         | |- lib.Lib.Frame.stk _ _ _ _ => apply (cm_stk_sub mc (Sp - 9136) Sp); [exact STWg | lia | lia]
         | |- addressable _ _ _ =>
             first [ exact ADo | exact (acl_addr_sub mc f 50 (f + 18) 32 AF ltac:(lia) ltac:(lia) ltac:(lia)) ]
         | |- end_in_app _ _ =>
             right; first [ replace (f + 18 + 32) with (f + 50) by lia; exact APf50
                          | replace (fr + 112 + 32) with (fr + 144) by lia; apply FAP; lia ]
         | |- rng_bytes _ => exact RB
         | |- lib.Lib.ExecF.rng _ _ _ =>
             first [ exact RIMG | apply (rng_sub RNG _ _ _ _ RF50); lia | apply (rng_sub RNG _ _ _ _ RFR); lia
                   | apply (rng_sub RNG _ _ _ _ RWIN); lia ]
         | |- _ = 0 \/ lib.Lib.ExecF.rng _ _ _ =>
             right; rewrite ?(Z.mul_comm 8); first [ apply RFW50; lia | apply RFC; lia ]
         | |- _ = 0 \/ app_mem _ =>
             right; first [ replace (f + 18 + 7) with (f + 25) by lia;
                            exact (acl_app_in mc f 50 25 AF ltac:(lia))
                          | replace (fr + 112 + 7) with (fr + 119) by lia; apply FAP; lia ]
         | |- _ \/ _ => first [ destruct Hfd; [left; lia | right; destruct FSP; lia]
                              | destruct FRsp; [left; lia | right; lia] ]
         | |- _ => unfold HIGHMEM_BEG, APPMEM_END; lia
         end. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m'' & -> &
              MUb & WMb & MIb & STb & ACb & SRb & _ & _).
  rewrite lib.Lib.MState.ret_pc_even by (try lia; reflexivity).
  rewrite ?(lib.Lib.MState.unsigned_lit sp2) in MUb, STb by lia.
  unfold BCMP_WRAP_K in MUb, STb.
  apply K; [| exact VR | exact MM].
  split; [exact (cm_win_inv fr sp2 jj nn mc m'' (sp2 - 4560) INVk Rlo Lo8 MUb WMb MIb STb (cmSRT_step m mc m'' SRg SRb))|].
  (* the wrapper's write list [(sp2 - 4560, sp2)] is inside the window of cmWst Sp fr *)
  apply (lib.Lib.Frame.munch_trans _ m mc m'' MUw).
  apply (lib.Lib.Frame.munch_weaken [(sp2 - 4560, sp2)] _ mc m''); [|exact MUb].
  intros x Hx. unfold cmWst in Hx. cbn [lib.Lib.Frame.outside] in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact I].
Qed.

(* cm_post_mb_K :3668-3782.  The four shadow stores 14..17 of each arm are checked against cmWst Sp fr (MUw3).  x1 is
   free at the start (the source fixes it to 0x8509c): the callee's world post at the return (TMB) gives only the
   callee-saved registers.  x1 is dead from the return 0x8509c on: the next write is the jal of the bcmp wrapper at
   0x850b4 (cmW_bc), which every path reaches first. *)
Lemma cmW_post_mb_K : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  bcmp_wrap_c_on.bcmp_wrap_contract_F_on ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  rng_bytes RNG -> lib.Lib.ExecF.rng RNG 65536 6217728 ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (k : nat), cm_gate len fb = true ->
  forall (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) (w4 w9 : word)
         (x1 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
  w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w9 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = 11)%nat -> (0 < k)%nat ->
  (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mc ->
  lib.Lib.Mem.bytes_at rsegs mc (fr + 112) (nth i DECLS []) -> addressable mc (fr + 112) 32 ->
  evtF rsegs RNG
    (fun ms => cm_exit_atW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn ms \/
       exists (k' : nat) (m0 : word -> option byte) (v4 v9 : word)
              (zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
         ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp zt0 zt1 zt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                      v4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) za3 za4 za5 za6 za7
                      (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) v4 (Z_to_bv 64 (fr + 112))
                      (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) v9 (Z_to_bv 64 1)
                      (Z_to_bv 64 (-8)) zt3 zt4 zt5 zt6)
                 F (Z_to_bv 64 0x865d8) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
         v4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat (Corelib.Init.Datatypes.S i)) /\ v9 = Z_to_bv 64 (Z.of_nat k') /\
         (Corelib.Init.Datatypes.S i + k' = 11)%nat /\ (0 < k')%nat /\
         (forall j, (j < Corelib.Init.Datatypes.S i)%nat -> nth j DECLS [] <> cm_blk fb) /\
         cmAtMBW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb (Corelib.Init.Datatypes.S i) fr sp2 jj nn m0)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 1) ya1 ya2 ya3 ya4 ya5 ya6 ya7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
        F (Z_to_bv 64 0x8509c) fc None mc (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    HBC Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU FP0 RB RIMG RWIN RWSH RFD RFW RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (cm_gate_len len fb) as cm_gate_len.
  pose proof (cm_shst_pre ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb SR AW FP0) as cm_shst_pre.
  pose proof (cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0) as cm_inv_step.
  pose proof (rd_mono_list f len Sp fb Rf Rlen Hfb) as rd_mono_list.
  pose proof (wv_store_ok f len Sp fb Rf Rlen Hfb) as cmW_wvs.
  pose proof (cmW_bc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
                HBC Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW AFU FP0 RB RIMG RWIN RWSH RFD RFW RFPW) as cm_bc.
  pose proof (cmW_tail_K ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
                Rf Rlen S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW) as cm_tail_K.
  pose proof (cmW_turn_head ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
                Rf Rlen RS S16 HK ST Hfb HF SR HHM HAE AW FP0 RWIN RWSH RFPW) as cm_turn_head.
  intros k G i fr sp2 jj nn mc w4 w9 x1 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
    E4 E9 Hik Hk Hnd INV2W BB2 AD2.
  pose proof INV2W as (INV2 & MUw2).
  destruct k as [|k]; [lia|].
  subst w4 w9.
  assert (Hi : (i < 11)%nat) by lia.
  pose proof INV2 as (FKl & _). pose proof (cm_fr_rng fr sp2 jj nn FKl) as (RFR & RFS & _). clear FKl.
  pose proof (cm_gate_len G) as L.
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  (* 0x8509c: the row is a declaration, so the test against s10 = 1 falls through *)
  step. if_false.
  (* 0x850a0, 0x850a4: the wrap test of the input pointer (not taken) *)
  step. step.
  rewrite cm_ltu_neg_l by lia.
  replace (-19 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  (* 0x850a8 .. 0x850b4: the call of the bcmp wrapper *)
  eapply (cm_bc _ i fr sp2 jj nn); [exact Hi | exact L | exact INV2W | exact BB2 | exact AD2 |].
  intros mc2 v zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 INV3W VR MM.
  pose proof INV3W as (INV3 & MUw3).
  (* 0x850b8: the result of the comparison *)
  step. rewrite cm_eqb0 by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - (* the match: 0x85240, the four shadow bytes := 0xf8, then the tail to the exit state *)
    destruct (cm_shst_pre _ _ _ _ _ INV3)
      as (_ & _ & _ & FAP3 & FSW3 & SHlo3 & SHhi3 & WM3 & MI3 & STW3 & STF3 & STS3).
    assert (MU3 : lib.Lib.Frame.munch (cmHF Sp fr) mc2 mc2) by apply lib.Lib.Frame.munch_refl.
    assert (WH3 : lib.Lib.Frame.wmono rsegs mc2 mc2) by apply lib.Lib.Frame.wmono_refl.
    unfold cmHF in MU3.
    unfold cmWst in MUw3.
    step.
    cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    step.
    match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
      assert (RM3 : rd_mono mc2 mf) by (cm_rdm MU3 STW3 STF3 STS3) end.
    eapply evtF_mono;
      [ apply (cm_tail_K fr sp2 jj nn _ (CM_T + 296 * Z.of_nat i));
        [ symmetry; apply cm_want_hit; [exact G | exact Hi | symmetry; exact (proj1 MM V0) | exact Hnd]
        | split; [eapply cm_inv_step; [exact INV3 | exact MU3 | exact WH3 | exact RM3 | exact MI3] | exact MUw3] ]
      | intros msx Hx; cbv beta; left; exact Hx ].
  - (* no match: 0x850bc, the four shadow bytes := 0xf8, then the next row's call or the tail with 0 *)
    assert (Hne : nth i DECLS [] <> cm_blk fb) by (intros Hq; apply V0; apply (proj2 MM); symmetry; exact Hq).
    destruct (cm_shst_pre _ _ _ _ _ INV3)
      as (_ & _ & _ & FAP3 & FSW3 & SHlo3 & SHhi3 & WM3 & MI3 & STW3 & STF3 & STS3).
    assert (MU3 : lib.Lib.Frame.munch (cmHF Sp fr) mc2 mc2) by apply lib.Lib.Frame.munch_refl.
    assert (WH3 : lib.Lib.Frame.wmono rsegs mc2 mc2) by apply lib.Lib.Frame.wmono_refl.
    unfold cmHF in MU3.
    unfold cmWst in MUw3.
    cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
      assert (RM3 : rd_mono mc2 mf) by (cm_rdm MU3 STW3 STF3 STS3);
      assert (INV4 : cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn mf)
        by (split; [eapply cm_inv_step; [exact INV3 | exact MU3 | exact WH3 | exact RM3 | exact MI3]
                   | exact MUw3])
    end.
    step. step. step.
    rewrite cm_eqb_lit by lia.
    match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ (if negb (?e =? 0) then _ else _) _ _ _ _) =>
      destruct (Z.eqb_spec e 0) as [K0|K0] end; cbn [negb]; cbv iota.
    + (* the 11th row was the last: s4 := 0, then the tail to the exit state *)
      assert (Ek : k = 0%nat) by lia. subst k.
      step.
      eapply evtF_mono;
        [ apply (cm_tail_K fr sp2 jj nn _ 0);
          [ symmetry; apply cm_want_none; intros j Hj;
            destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia]
          | exact INV4 ]
        | intros msx Hx; cbv beta; left; exact Hx ].
    + (* 0x8507c again: the next row's turn, up to its call of reac_box_model_block *)
      destruct k as [|k]; [lia|].
      eapply evtF_cut;
        [ eapply (cm_turn_head (Corelib.Init.Datatypes.S i) fr sp2 jj nn);
          [ exact G | lia | f_equal; unfold CM_T in *; lia | exact INV4 ]|].
      intros msx (m0 & -> & HAtMB).
      apply evtF_done. cbv beta. right.
      exists (Corelib.Init.Datatypes.S k). exists m0. do 14 eexists.
      split; [reflexivity|].
      split; [f_equal; unfold CM_T in *; lia|].
      split; [f_equal; lia|].
      split; [lia|].
      split; [lia|].
      split; [intros j Hj; destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia]|].
      exact HAtMB.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* cmPost :497 with the stretch's own write list: after the release store the run writes nothing, so the final
   memory equals the start memory m0 (munch []). *)
Definition cmPostW (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (m0 : word -> option byte) (ms' : machine_state)
    : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Lib.PropExec.seg_rom rsegs) /\
    lib.Lib.Frame.munch [] m0 m' /\
    lib.Lib.Frame.wmono rsegs m m' /\ lib.Lib.Mem.mem_inv rsegs m' /\ lib.Lib.Frame.stk rsegs m' (Sp - 9136) Sp /\
    asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (Sp - 9136) 9136 /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
      (reac_box_catalogue_match_D f len) /\
    reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (Sp - 9136) Sp.

(* cm_post_rel :972-1158.  The epilogue has no store: the post's write list is [] from the start memory (the
   release store's write over m1).  Beyond the write list: the F file's assertion SUB (:1064-1073), which only fed
   the replaced munch conjunct, and its unfold of aWc in Jmu are dropped. *)
Lemma cmW_post_rel : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp ->
  lib.Lib.Frame.stk rsegs m (Sp - 9136) Sp -> length fb = 50%nat ->
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m -> HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END -> addressable m (Sp - 9136) 9136 ->
  fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  lib.Lib.ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  forall (fr sp2 jj : Z) (mc m1 : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmAtRel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj mc m1 ->
  evtF rsegs RNG
    (cmPostW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb
       (write_to_mem m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))))
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x85198) fc None (write_to_mem m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))
        (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb RNG
    Rf Rlen RS S16 HK ST Hfb SR HHM HAE AW FP0 RWIN RWSH RHDR RFPW.
  pose proof (CA_facts f len Sp fb Rf Rlen S16 Hfb) as CA_facts.
  pose proof (fk_facts tp m f len Sp FS fb Rf Rlen S16 HK ST Hfb SR AW FP0) as fk_facts.
  pose proof (cm_fr_rng tp m f len Sp FS fb RNG Rf Rlen S16 HK Hfb HHM HAE FP0 RWIN RWSH RFPW) as cm_fr_rng.
  pose proof (acl_fs tp m f len Sp FS FP0) as acl_fs.
  pose proof (cm_sh_add8 f len Sp fb Rf Rlen Hfb) as cm_sh_add8.
  pose proof (cm_sh_div f len Sp fb Rf Rlen Hfb) as cm_sh_div.
  pose proof (rf_flag2 f len Sp FS fb RNG Rf Rlen Hfb RHDR) as rf_flag2.
  pose proof (wv_store_ok f len Sp fb Rf Rlen Hfb) as wv_store_ok.
  pose proof (cm_dj_in f len Sp fb Rf Rlen HK Hfb) as cm_dj_in.
  pose proof (addr_byte_keep f len Sp fb Rf Rlen Hfb) as addr_byte_keep.
  pose proof (fl_tls_cells f len Sp fb Rf Rlen Hfb) as fl_tls_cells.
  pose proof (cm_cls_keep f len Sp FS fb Rf Rlen HK Hfb) as cm_cls_keep.
  pose proof (cm_cls_rel f len Sp FS fb Rf Rlen HK Hfb) as cm_cls_rel.
  intros fr sp2 jj mc m1 r x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HAt.
  destruct HAt as (HJ & MUc & WMc & Jmicur & SRcur & STwcur & STfs1).
  destruct HJ as (HFK & Jmu & Jwm & Jmi & JRT & JAWX & JEXT & STw & STf & SAV & FLG).
  destruct JRT as (JAC & JSR & JFP & JTL).
  pose proof (fk_facts fr sp2 jj 1 HFK) as (Fm32 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof (cm_fr_rng fr sp2 jj 1 HFK) as (RFR & RFS & _).
  pose proof CA_facts as (CAm & CAlo & CAhi).
  assert (Fm8 : fr mod 8 = 0) by (clear -Fm32; Z.div_mod_to_equations; lia).
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - discriminate En.
  - clear En.
    destruct acl_fs as (AF1 & AF2 & AF3 & AF4 & AF5 & AF6).
    assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
    assert (FRhi : fr + 256 <= FS + FS_SIZE).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj.
      unfold FS_SIZE in *. lia. }
    assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply AF5.
      unfold FS_SIZE in *. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 40 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))); lia).
    specialize (FLG eq_refl).
    pose proof (rf_flag2 jj Hj) as RFL.
    pose proof JFP as JFPc.
    destruct JFPc as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & HPfs & _ & _ & _ & _ & _ & _ & _).
    destruct HPfs as (FSP1 & FSP2 & FSP3 & FSP4 & FSPstk).
    assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (SOKfl : store_ok rsegs m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) 1 = true)
      by (apply (wv_store_ok mc m1 (fs_flag FS 2 jj) 1%nat);
          [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
            apply (cm_stk_wv mc FS (FS + FS_SIZE) (fs_flag FS 2 jj) FSPstk); unfold FS_SIZE in *; lia
          | exact WMc | lia | unfold FS_SIZE in *; lia ]).
    change (Z_to_bv 64 (fs_flag FS 2 jj)) with (lib.Lib.Mem.wa (fs_flag FS 2 jj)).
    apply (lib.Lib.Frame.wmono_write rsegs mc m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in WMc.
    apply (cm_shadow_rw_write m m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in SRcur.
    apply (lib.Lib.Mem.mem_inv_store rsegs m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite lib.Lib.Mem.length_le1; exact SOKfl].
    apply (lib.Lib.Frame.stk_write rsegs m1 (Sp - 9136) Sp (fs_flag FS 2 jj) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in STwcur;
      [| unfold FS_SIZE in *; lia | rewrite lib.Lib.Mem.length_le1; lia].
    apply (lib.Lib.Frame.munch_write _ mc m1 (fs_flag FS 2 jj) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in MUc;
      [| unfold FS_SIZE in *; lia | rewrite lib.Lib.Mem.length_le1; lia
       | rewrite lib.Lib.Mem.length_le1; cbn [lib.Lib.Frame.inside]; right; right; left; split; lia].
    apply (lib.Lib.Frame.stk_write rsegs m1 FS (FS + FS_SIZE) (fs_flag FS 2 jj) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in STfs1;
      [| unfold FS_SIZE in *; lia | rewrite lib.Lib.Mem.length_le1; lia].
    assert (FRup : fr + 320 <= Sp) by lia.
    assert (SAFup : shadow_addr fr + 40 <= Sp - 104).
    { unfold shadow_addr, ASAN_K, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
    match goal with |- evtF _ _ _ (lib.Lib.MState.MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : lib.Lib.Step.rw_cells rsegs mf (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
        by (apply (lib.Lib.Frame.rw_cells_transport rsegs _ mc mf (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
                     SAV MUc WMc);
            cbn [lib.Lib.Frame.disjoint_from lib.Lib.Cells.cells_size lib.Lib.Cells.csize];
            split; [right; lia | split; [right; lia | split; [right; lia | exact I]]]) end.
    clear SAV. unfold cmSAVES in SAVf.
    do 18 step.
    apply evtF_done. unfold cmPostW. subst r.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
    assert (FRin : fs_frame FS 2 0 <= fr /\ fr + 256 <= fs_frame FS 2 (fs_M 2)).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (FLin : fs_flag FS 2 0 <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= fs_flag FS 2 0 + fs_M 2).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 12) with 4096 in Hj. lia. }
    assert (INframe : In (fs_frame FS 2 0, fs_frame FS 2 (fs_M 2)) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (INflag : In (fs_flag FS 2 0, fs_flag FS 2 0 + fs_M 2) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (INsh : In (shadow_addr (fs_frame FS 2 0), shadow_addr (fs_frame FS 2 (fs_M 2))) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (SG1f : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr) by (apply acl_sh_ge; destruct FRin; lia).
    assert (SG2f : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
    { pose proof (cm_sh_add8 fr 32 Fm8) as E. replace (fr + 8 * 32) with (fr + 256) in E by lia. rewrite <- E.
      apply acl_sh_ge. destruct FRin; lia. }
    split; [reflexivity|].
    match goal with |- lib.Lib.Frame.munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
    (* the stretch's own write list: none *)
    split; [apply lib.Lib.Frame.munch_refl |].
    split; [eapply (lib.Lib.Frame.wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
    split; [exact Jmicur |].
    split; [exact STwcur |].
    split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
             intros x Hx; unfold RT_LO, RT_HI, ASAN_GT, ASAN_K in *; cbn [lib.Lib.Frame.outside];
             split; [ clear -Hx AF3 FRlo; lia
                    | split; [ clear -Hx Fpos; unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia
                             | split; [ clear -Hx AF3 FLo; lia | exact I ] ] ] |].
    split; [exact SRcur |].
    assert (FLv : fs_flag FS 2 jj = FS + 28672 + jj)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 15) with 32768; change (2 ^ 13) with 8192; lia).
    assert (M2 : fs_M 2 = 4096) by reflexivity.
    pose proof FRin as (FRa & FRb). pose proof FLin as (FLa & FLb).
    assert (BELh : forall x, FS <= x < FS + 36864 -> x <> fs_flag FS 2 jj ->
              lib.Lib.Frame.outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x).
    { intros x Hx Hne. cbn [lib.Lib.Frame.outside]. split; [lia | split; [| split; [lia | exact I]]].
      intros [A B]. apply (acl_app_not_shadow x); [apply AF5; unfold FS_SIZE in *; lia |].
      pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS.
      replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia. exact HS. }
    assert (RDfl : lib.Lib.Mem.mrd rsegs M (lib.Lib.Mem.wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0)).
    { change (lib.Lib.Mem.mrd rsegs (write_to_mem m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) (lib.Lib.Mem.wa (fs_flag FS 2 jj))
              = Some (Z_to_bv 8 0)).
      pose proof (lib.Lib.Mem.bytes_at_write_same rsegs m1 (fs_flag FS 2 jj) (lib.Lib.Mem.le1 (Z_to_bv 64 0)) ltac:(lia)
                    ltac:(rewrite lib.Lib.Mem.length_le1; unfold FS_SIZE in *; lia)) as BW.
      destruct BW as (_ & _ & BW). specialize (BW 0%nat ltac:(rewrite lib.Lib.Mem.length_le1; lia)).
      replace (fs_flag FS 2 jj + Z.of_nat 0) with (fs_flag FS 2 jj) in BW by lia.
      rewrite BW. reflexivity. }
    assert (DJall : forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
              fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                    (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
    { intros DT TS C T DB kk HT. pose proof (JTL DT TS C T DB kk HT) as JTLi. unfold aXs in JTLi.
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - apply (cm_dj_in _ _ (fs_frame FS 2 0) (fs_frame FS 2 (fs_M 2)) fr (fr + 8) JTLi);
          [apply in_or_app; left; exact INframe | lia | lia].
      - apply (cm_dj_in _ _ (shadow_addr (fs_frame FS 2 0)) (shadow_addr (fs_frame FS 2 (fs_M 2)))
                 (shadow_addr fr) (shadow_addr fr + 32) JTLi); [apply in_or_app; left; exact INsh | lia | lia].
      - apply (cm_dj_in _ _ (fs_flag FS 2 0) (fs_flag FS 2 0 + fs_M 2) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) JTLi);
          [apply in_or_app; left; exact INflag | lia | lia]. }
    split.
    { split; [unfold HIGHMEM_BEG in *; lia | split; [lia | split; [clear -HAE; unfold APPMEM_END in *; lia |]]].
      intros i Hi.
      pose proof (JAWX (Sp - 9136 + i) ltac:(lia) ltac:(lia)) as AB.
      pose proof (rt_app_shadow (Sp - 9136 + i) (proj1 AB)) as HS.
      apply (addr_byte_keep _ mc M (Sp - 9136 + i) AB MUc).
      cbn [lib.Lib.Frame.outside]. split; [| split; [| split; [| exact I]]].
      - intros [A B]. apply (acl_app_not_shadow (shadow_addr (Sp - 9136 + i))); [apply AF5; lia | exact HS].
      - replace (shadow_addr fr + 32) with (shadow_addr (fr + 256))
          by (rewrite (cm_sh_div fr 256 Fm8); reflexivity).
        apply (acl_win_sh (Sp - 9136 + i) fr (fr + 256) Fm8). lia.
      - intros [A B]. apply (acl_app_not_shadow (shadow_addr (Sp - 9136 + i)));
          [apply AF5; unfold FS_SIZE in *; lia | exact HS]. }
    split.
    { destruct JFP as (DT & TS & C & T & DB & kk & HT & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
      pose proof (DJall DT TS C T DB kk HT) as DJ.
      exists DT, TS, C, T, DB, kk.
      split; [eapply fl_tls_cells; [exact HT | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite lib.Lib.Mem.length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4 | exact STfs1]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite lib.Lib.Mem.length_le8 in Hx; apply BELh; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BELh; lia]|].
      split.
      { apply Forall_cons_iff in HCL as [HC0 HCL]. apply Forall_cons_iff in HCL as [HC1 HCL].
        apply Forall_cons_iff in HCL as [HC2 _].
        constructor; [exact (cm_cls_keep _ mc M 0%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC0)|].
        constructor; [exact (cm_cls_keep _ mc M 1%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC1)|].
        constructor; [exact (cm_cls_rel _ mc M jj Hj BELh MUc RDfl HC2) | constructor]. }
      split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
    intros DT TS C T DB k HTM.
    destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _).
    pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
    pose proof (DJall DT0 TS0 C0 T0 DB0 k0 HT0) as DJ0.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                   lib.Lib.Frame.outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                            (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
    destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
Qed.

(* ============================================================================================================ *)
(* THE RE-BASED STRETCHES WITH THEIR OWN WRITE LISTS, in the shape of C_reac_box_catalogue_matchLib.v's cmRB_*: the
   run on MemNorm.normalize rsegs mb, back to mb through MemNormF.evtF_normalize_ro (stretch 6: evtF_rel_ro); posts
   relative to mb with ro_agree, never mem_inv.  cmBase and its helpers are the Lib file's. *)

(* cmRB_J with the stretch's write list cmWst Sp fr in place of aWc Sp FS. *)
Definition cmRBw_J (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  cmFK Sp FS fr sp2 jj nn /\ lib.Lib.Frame.munch (cmWst Sp fr) mb mc /\ lib.Lib.Frame.wmono rsegs mb mc /\ MemNorm.ro_agree rsegs mc /\
  RT tp mb f len Sp FS mc /\ AWX Sp fr mc /\ EXT f len fb mc /\
  lib.Lib.Frame.stk rsegs mc (Sp - 9136) Sp /\ lib.Lib.Frame.stk rsegs mc fr (fr + 192) /\
  lib.Lib.Step.rw_cells rsegs mc (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs mc (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))).

(* cmRB_exit_at with cmRBw_J, at a given frame (fr sp2 jj nn): the frame is a parameter, so the exit keeps the frame
   the stretch started with. *)
Definition cmRBw_exit_at (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  exists (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
    r = want CM_T len fb /\ cmRBw_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc /\
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp)) y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
                 (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x850fc) fc None mc (lib.Lib.PropExec.seg_rom rsegs).

(* cmRB_AtParse with cmRBw_J. *)
Definition cmRBw_AtParse (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  50 <= len /\
  bv_unsigned (nth 12 fb (Z_to_bv 8 0)) = 136 /\ bv_unsigned (nth 13 fb (Z_to_bv 8 0)) = 25 /\
  bv_unsigned (nth 16 fb (Z_to_bv 8 0)) = 205 /\ bv_unsigned (nth 17 fb (Z_to_bv 8 0)) = 234 /\
  cmRBw_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc /\
  addressable mc (fr + 32) 36.

(* cmRB_parse_at with cmRBw_AtParse, at a given frame (fr sp2 jj nn). *)
Definition cmRBw_parse_at (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  exists (mc : word -> option byte)
         (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                 rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x83e04) fc None mc (lib.Lib.PropExec.seg_rom rsegs) /\
    cmRBw_AtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc.

(* Stretch 2's end: the exit state or the reac_ctrl_parse call state (cmRB_gate), at the frame (fr sp2 jj nn) the
   stretch starts with (cmRBw_post_sm2_side: the request's frame). *)
Definition cmRBw_gate (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  cmRBw_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb fr sp2 jj nn ms \/
  cmRBw_parse_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb fr sp2 jj nn ms.

(* The same end on the normalized run (cmQ_gate over cmInvW), at a given frame. *)
Definition cmQw_gate (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  cm_exit_atW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb fr sp2 jj nn ms \/
  exists (m0 : word -> option byte)
         (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                 rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x83e04) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
    cmAtParseW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn m0.

(* cmRB_AtMB with cmRBw_J. *)
Definition cmRBw_AtMB (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  (i < 11)%nat /\ cmRBw_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc /\
  addressable mc (fr + 112) 32.

(* cmRB_mb_call with cmRBw_AtMB. *)
Definition cmRBw_mb_call (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (i k : nat) (fr sp2 jj nn : Z)
    (ms : machine_state) : Prop :=
  exists (m0 : word -> option byte) (zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp zt0 zt1 zt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) za3 za4 za5 za6 za7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
                 (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
                 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) zt3 zt4 zt5 zt6)
            F (Z_to_bv 64 0x865d8) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
    cmRBw_AtMB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb i fr sp2 jj nn m0.

(* Stretch 3's end (cmRB_parse_Q), both arms at the incoming frame (fr sp2 jj nn). *)
Definition cmRBw_parse_Q (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  cmRBw_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb fr sp2 jj nn ms \/
  (cm_gate len fb = true /\
   cmRBw_mb_call ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb 0 11 fr sp2 jj nn ms).

(* Stretch 4's end (cmRB_mb_Q), both arms at the incoming frame (fr sp2 jj nn). *)
Definition cmRBw_mb_Q (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (i : nat) (fr sp2 jj nn : Z)
    (ms : machine_state) : Prop :=
  cmRBw_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb fr sp2 jj nn ms \/
  exists k' : nat, (Corelib.Init.Datatypes.S i + k' = 11)%nat /\ (0 < k')%nat /\
    (forall j, (j < Corelib.Init.Datatypes.S i)%nat -> nth j DECLS [] <> cm_blk fb) /\
    cmRBw_mb_call ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb (Corelib.Init.Datatypes.S i) k' fr sp2 jj nn ms.

(* cmRB_Post with stretch 6's own write list: none, from the start memory m0 (the release store's write over mb). *)
Definition cmRBw_Post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (m0 : word -> option byte) (ms' : machine_state)
    : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Lib.PropExec.seg_rom rsegs) /\
    lib.Lib.Frame.munch [] m0 m' /\
    lib.Lib.Frame.wmono rsegs mb m' /\ MemNorm.ro_agree rsegs m' /\ lib.Lib.Frame.stk rsegs m' (Sp - 9136) Sp /\ asan_cells m' /\
    (forall P, shadow_rw_on P mb -> shadow_rw_on P m') /\ addressable m' (Sp - 9136) 9136 /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
      (reac_box_catalogue_match_D f len) /\
    reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (Sp - 9136) Sp.

(* An invariant of the normalized run carried back to the real memory (cmRB_J_of_rel, and MemNorm.munch_rel for the
   write list). *)
Lemma cmRBw_J_of_rel : forall (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc mc' : word -> option byte),
  MemNorm.mem_rel rsegs mb (MemNorm.normalize rsegs mb) -> MemNorm.mem_rel rsegs mc' mc ->
  MemNorm.ro_same rsegs mb mc' ->
  cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb fr sp2 jj nn mc ->
  cmRBw_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc'.
Proof.
  intros ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc mc' REL0 REL Hsm (HJ & MUw).
  destruct (C_reac_box_catalogue_matchLib.cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS
              fb fr sp2 jj nn mc mc' REL0 REL Hsm HJ) as (FK & _ & WM & RO & RTc & AX & EX & STW & STF & SAV & FLG).
  exact (conj FK (conj (MemNorm.munch_rel rsegs _ mb _ mc' mc REL0 REL Hsm MUw)
           (conj WM (conj RO (conj RTc (conj AX (conj EX (conj STW (conj STF (conj SAV FLG)))))))))).
Qed.

(* ---- stretch 2: the class-2 return (pc 544436, x1 free) -> the gate -> the reac_ctrl_parse call or the exit;
   cmW_post_sm2_side at m := m0 := m2 := normalize mb, with cmKBW's Q from cmW_pre_parse.  The post exports
   munch (cmWst Sp fr) mb mc, and both arms are at the request's frame j: fr = fs_frame FS 2 j, sp2 = CA Sp, jj = j,
   nn = 1. ---- *)
Lemma cmRBw_post_sm2_side : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  C_reac_box_catalogue_matchLib.cmBase mb tp f len Sp FS fb ->
  lib.Lib.Frame.stk rsegs mb (Sp - 9136) (CA Sp) ->
  forall m1 : word -> option byte,
  lib.Lib.Frame.stk rsegs m1 (CA Sp) Sp -> lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  C_reac_box_catalogue_matchLib.cmRB_win_kept m1 mb Sp ->
  forall j : Z, C_reac_box_catalogue_matchLib.cmRB_Fs2 mb FS j ->
  forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evtF rsegs RNG (cmRBw_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb
                    (fs_frame FS 2 j) (CA Sp) j 1)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 (CA Sp)) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fs_frame FS 2 j)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (lib.Lib.MState.ret_pc (Z_to_bv 64 544436)) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RWIN RWSH RFD RFW RFPW HB HSTlo m1 HST1 HSV1 HKP j HS2
    x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  (* the window at mb: below CA from the request's post, above CA kept from m1; the saves likewise kept *)
  pose proof (C_reac_box_catalogue_matchLib.cmRB_CA Sp S16) as CAb0.
  assert (STW : lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp)
    by exact (C_reac_box_catalogue_matchLib.cmRB_stk_join mb _ _ _ HSTlo
                (C_reac_box_catalogue_matchLib.cmRB_stk_keep m1 mb _ _ HKP HST1)).
  assert (SAV : lib.Lib.Step.rw_cells rsegs mb (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (C_reac_box_catalogue_matchLib.cmRB_rw_cells_keep m1 mb _ _); [|exact HSV1]. intros i Hi.
    change (lib.Lib.Cells.cells_size (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) with 104%nat in Hi.
    apply HKP. lia. }
  destruct (C_reac_box_catalogue_matchLib.cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  destruct CLn as (C1n & C2n & C3n & C4n & C5n).
  assert (HFn : 50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\
                (f + 50 <= Sp - 9136 \/ Sp <= f)).
  { intros L. destruct (HFp L) as (Q1 & Q2 & Q3). destruct (HFBn L) as (B1 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact B1 | exact Q3]. }
  assert (AFUn : 50 <= len -> addressable (MemNorm.normalize rsegs mb) f 50 /\ app_mem (f + 50)).
  { intros L. split; [exact (proj2 (HFBn L)) | exact (AFp L)]. }
  destruct HS2 as (Hj & Hm64 & HFL & HFW & HSH).
  pose proof (C_reac_box_catalogue_matchLib.cmRB_saves_n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp REL STn SAV)
    as SAVn.
  pose proof FPn as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & PSn) & _ & _ & HCn & HLO & _ & _ & _).
  pose proof (C_reac_box_catalogue_matchLib.cmRB_CA Sp S16) as CAb.
  pose proof (C_reac_box_catalogue_matchLib.cmRB_fr_in_fs FS j Hj) as (B1 & B2).
  (* the gate's continuation: cmW_pre_parse at the normalized base, for every gate state *)
  assert (K : cmKBW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb) f len Sp FS fb
                RNG (cmQw_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
                       f len Sp FS fb)).
  { intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INV.
    pose proof (cmW_pre_parse ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
      f len Sp FS fb RNG) as L.
    C_reac_box_catalogue_matchLib.cmRB_feed L.
    eapply evtF_mono;
      [exact (L fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INV)|].
    intros ms [EX|(m0 & E & HA)]; [left; exact EX|right].
    exists m0, rt0, rt1, rt2, ra3, ra4, ra5, ra6, ra7, rs6, rs9, rs10, rs11, rt3, rt4, rt5, rt6.
    split; [exact E | exact HA]. }
  assert (HAt : cmAtSM2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) Sp
                  (MemNorm.normalize rsegs mb)).
  { split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [exact MIn|]. split; [exact STn | exact SAVn]. }
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R ?F' ?pc ?fc' ?rv _ ?ro) =>
    assert (HN : evtF rsegs RNG (cmQw_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                                   (MemNorm.normalize rsegs mb) f len Sp FS fb (fs_frame FS 2 j) (CA Sp) j 1)
                   (lib.Lib.MState.MS R F' pc fc' rv (MemNorm.normalize rsegs mb) ro)) end.
  { pose proof (cmW_post_sm2_side ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
      f len Sp FS fb RNG) as L.
    C_reac_box_catalogue_matchLib.cmRB_feed L.
    apply (L _ (MemNorm.normalize rsegs mb) j _ K HAt); [|reflexivity].
    (* cmW_fs_post_2 at the normalized base: the request's post with m0 = m2 = normalize mb, x1 free *)
    exists x1, t0, t1, t2, (Z_to_bv 64 (fs_frame FS 2 j)), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6,
      (MemNorm.normalize rsegs mb).
    split; [reflexivity|].
    split; [apply lib.Lib.Frame.wmono_refl|].
    split; [exact MIn|].
    split; [apply (C_reac_box_catalogue_matchLib.cmRB_stk_sub _ _ _ _ _ STn); lia|].
    split; [exact PSn|].
    split; [destruct (proj1 (Forall_forall _ _) HCn 2%nat ltac:(right; right; left; reflexivity))
              as (_ & h & _ & Hh & _);
            exists h; exact Hh|].
    split; [exact Hj|]. split; [reflexivity|]. split; [exact Hm64|].
    split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HFL)|].
    split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HFW)|].
    split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HSH)|].
    split; [apply (C_reac_box_catalogue_matchLib.cmRB_stk_sub _ _ _ _ _ PSn); lia|].
    split; [intros a Ha; apply P4; lia|].
    split; [exact B1|]. split; [exact B2|]. split; [lia|].
    split; [unfold ASAN_STACK_MALLOC_K; lia|].
    split; [exact (C_reac_box_catalogue_matchLib.cmRB_fs2_disj FS j Hj)|].
    apply lib.Lib.Frame.munch_refl. }
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO HN) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HQ & Hrel & Hsm).
  destruct HQ as [EX|PA].
  - left.
    destruct EX as (mc & r & xr & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 &
                    z3 & z5 & z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJ & ->).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists (ms_mem st), r, xr, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9, z10, z11, u3, u4, u5, u6.
    split; [exact Er|]. split; [|exact Es].
    exact (cmRBw_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb (fs_frame FS 2 j) (CA Sp) j 1
             mc (ms_mem st) REL Hmr Hsm HJ).
  - right.
    destruct PA as (mc & rt0 & rt1 & rt2 & ra3 & ra4 & ra5 & ra6 & ra7 & rs6 & rs9 & rs10 & rs11 &
                    rt3 & rt4 & rt5 & rt6 & -> & (L50 & H12 & H13 & H16 & H17 & HJ & HAD)).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists (ms_mem st), rt0, rt1, rt2, ra3, ra4, ra5, ra6, ra7, rs6, rs9, rs10, rs11, rt3, rt4, rt5, rt6.
    split; [exact Es|].
    split; [exact L50|]. split; [exact H12|]. split; [exact H13|]. split; [exact H16|]. split; [exact H17|].
    split; [exact (cmRBw_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb (fs_frame FS 2 j)
                     (CA Sp) j 1 mc (ms_mem st) REL Hmr Hsm HJ)|].
    exact (C_reac_box_catalogue_matchLib.cmRB_addressable_of_rel _ _ _ _ Hmr HAD).
Qed.

(* ---- stretch 3: the reac_ctrl_parse return (pc 0x85058) -> the exit, or the reac_box_model_block call of row 0;
   cmW_post_parse_K at m := mc := mp := normalize mb.  The post exports munch (cmWst Sp fr) mb mc. ---- *)
Lemma cmRBw_post_parse : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  C_reac_box_catalogue_matchLib.cmBase mb tp f len Sp FS fb ->
  forall (fr sp2 jj nn : Z) (m1 : word -> option byte),
  (* the call memory m1 (stretch 2's end) *)
  cmFK Sp FS fr sp2 jj nn -> lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp ->
  lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs m1 (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) -> addressable m1 (fr + 32) 36 ->
  (* the return memory mb: reac_ctrl_parse's window and output, the caller's bytes kept *)
  lib.Lib.Frame.stk rsegs mb (sp2 - 8800) sp2 -> lib.Lib.Step.rw_cells rsegs mb (fr + 32) [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))] ->
  C_reac_box_catalogue_matchLib.cmRB_kept m1 mb
    (C_reac_box_catalogue_matchLib.cmRB_callee_kept Sp fr sp2 (sp2 - 8800) 32 36) ->
  (* the gate's checks *)
  50 <= len ->
  bv_unsigned (nth 12 fb (Z_to_bv 8 0)) = 136 -> bv_unsigned (nth 13 fb (Z_to_bv 8 0)) = 25 ->
  bv_unsigned (nth 16 fb (Z_to_bv 8 0)) = 205 -> bv_unsigned (nth 17 fb (Z_to_bv 8 0)) = 234 ->
  forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rs6 rs9 rs10 rs11 : word),
  evtF rsegs RNG (cmRBw_parse_Q ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb fr sp2 jj nn)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
             rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 t3 t4 t5 t6)
        F (lib.Lib.MState.ret_pc (Z_to_bv 64 0x85058)) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RWIN RWSH RFD RFW RFPW HB fr sp2 jj nn m1
    FK ST1 SV1 FL1 AD1 STc RWo KP L E12 E13 E16 E17
    x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rs6 rs9 rs10 rs11.
  destruct (C_reac_box_catalogue_matchLib.cmRB_callee_base ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 mb Sp FS fr
              sp2 jj nn (sp2 - 8800) 32 36 S16 FK ST1 SV1 FL1 AD1 STc KP) as (STW & HFr & ADb).
  pose proof (C_reac_box_catalogue_matchLib.cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb
                fr sp2 jj nn S16 HHM HB STW HFr) as HJ.
  destruct (C_reac_box_catalogue_matchLib.cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  assert (HFn : 50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\
                (f + 50 <= Sp - 9136 \/ Sp <= f)).
  { intros L'. destruct (HFp L') as (Q1 & Q2 & Q3). destruct (HFBn L') as (B1 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact B1 | exact Q3]. }
  assert (AFUn : 50 <= len -> addressable (MemNorm.normalize rsegs mb) f 50 /\ app_mem (f + 50)).
  { intros L'. split; [exact (proj2 (HFBn L')) | exact (AFp L')]. }
  pose proof (C_reac_box_catalogue_matchLib.cmRB_CA Sp S16) as CAb.
  assert (Hsp2 : Sp - 336 <= sp2 <= Sp - 128) by (destruct FK as [(_ & E & _ & _)|(_ & _ & E & _)]; lia).
  destruct (acl_fs tp (MemNorm.normalize rsegs mb) f len Sp FS FPn) as (FSpos & _ & _ & FShi & _ & FSdj).
  assert (FRpos : 0 < fr).
  { destruct FK as [(Ef & _ & _ & _)|(Hj & Ef & _ & _)]; [lia|].
    pose proof (C_reac_box_catalogue_matchLib.cmRB_fr_in_fs FS jj Hj) as (B1 & _). lia. }
  pose proof HJ as (_ & _ & _ & _ & (_ & _ & _ & TLJ) & _ & _ & _ & STFn & _ & _).
  (* cmAtParse at the normalized base *)
  assert (HAt : cmAtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
                  fr sp2 jj nn (MemNorm.normalize rsegs mb)).
  { exact (conj L (conj E12 (conj E13 (conj E16 (conj E17
             (conj HJ (MemNormTr.addressable_normalize mb _ _ RO ADb))))))). }
  (* the output buffer at the normalized base (in the frame, which is writable there: not read-only) *)
  assert (RWn : lib.Lib.Step.rw_cells rsegs (MemNorm.normalize rsegs mb) (fr + 32) [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))]).
  { apply MemNormTr.rw_cells_normalize; [exact RO | | exact RWo]. intros i Hi.
    change (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))]) with 36%nat in Hi.
    pose proof STFn as (_ & _ & HS).
    apply (MemNorm.ro_false_of_wview rsegs mb (MemNorm.normalize rsegs mb) _ REL).
    exact (proj1 (HS (fr + 32 + i) ltac:(lia))). }
  pose proof (cmW_post_parse_K ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as K.
  C_reac_box_catalogue_matchLib.cmRB_feed K.
  (* reac_ctrl_parse's post at the normalized base, the return memory being the base itself *)
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R ?F' ?pc ?fc' ?rv _ ?ro) =>
    assert (PP : cmW_parse_post gp tp F fc f len Sp FS fb fr sp2 nn rs6 rs9 rs10 rs11 (MemNorm.normalize rsegs mb)
                   (lib.Lib.MState.MS R F' pc fc' rv (MemNorm.normalize rsegs mb) ro)) end.
  { exists x1, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, (MemNorm.normalize rsegs mb).
    split; [reflexivity|].
    split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [exact MIn|].
    split; [unfold REAC_CTRL_PARSE_K; apply (C_reac_box_catalogue_matchLib.cmRB_stk_sub _ _ _ _ _ STn); lia|].
    split; [exact RWn|]. split; [exact (fun P H => H)|].
    split; [unfold REAC_CTRL_PARSE_K; apply (C_reac_box_catalogue_matchLib.cmRB_addressable_sub _ _ _ _ _ AWn); lia|].
    split.
    - unfold reac_ctrl_parse_W, reac_ctrl_parse_D, REAC_CTRL_PARSE_K.
      replace (fr + 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [app]. replace (fr + 32 + 36) with (fr + 68) by lia.
      apply (cm_fp_callee ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
               Rf Rlen S16 HK STn Hfb SRn AWn FPn fr sp2 jj nn (MemNorm.normalize rsegs mb) 1%nat (sp2 - 8800) 32 68
               _ HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      apply fl_dj_cons. split.
      + apply (fp_dj_incl _ (fp_w [0%nat; 1%nat; 2%nat] FS)); [apply fp_w_incl; cbn; tauto|].
        apply (fl_dj_sub f (f + 50)); [|lia|lia|lia].
        unfold aDf in FSdj. replace (len <? 50) with false in FSdj by (symmetry; apply Z.ltb_ge; lia).
        exact FSdj.
      + apply fl_dj_cons. split; [|constructor].
        exact (cm_dj_fr tp (MemNorm.normalize rsegs mb) f len Sp FS fb Rf Rlen S16 HK STn Hfb SRn AWn FPn
                 fr sp2 jj nn 32 68 1%nat FK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - unfold REAC_CTRL_PARSE_K.
      exact (cm_tls_callee tp f len Sp FS fb Rf Rlen HK Hfb (MemNorm.normalize rsegs mb) 1%nat (sp2 - 8800) sp2
               ltac:(lia) TLJ ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO
    (K fr sp2 jj nn _ rs6 rs9 rs10 rs11 _ HAt PP eq_refl)) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HQ & Hrel & Hsm).
  destruct HQ as [EX|(m0 & v4 & v9 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> &
                      G & E4 & E9 & (Hi & HJ0 & AD0))].
  - left.
    destruct EX as (mc & r & xe & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 &
                    z3 & z5 & z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJE & ->).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists (ms_mem st), r, xe, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9,
      z10, z11, u3, u4, u5, u6.
    split; [exact Er|]. split; [|exact Es].
    exact (cmRBw_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc
             (ms_mem st) REL Hmr Hsm HJE).
  - right. subst v4 v9.
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    split; [exact G|].
    exists (ms_mem st), zt0, zt1, zt2, za3, za4, za5, za6, za7, zt3, zt4, zt5, zt6.
    split; [exact Es|].
    split; [exact Hi|].
    split; [exact (cmRBw_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn m0
                     (ms_mem st) REL Hmr Hsm HJ0)|].
    exact (C_reac_box_catalogue_matchLib.cmRB_addressable_of_rel _ _ _ _ Hmr AD0).
Qed.

(* ---- stretch 4: a reac_box_model_block return (pc 0x8509c), row i -> the exit, or the call of row S i;
   cmW_post_mb_K at m := mc := normalize mb (the base: cmInvW with munch_refl).  The post exports
   munch (cmWst Sp fr) mb mc. ---- *)
Lemma cmRBw_post_mb : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  bcmp_wrap_c_on.bcmp_wrap_contract_F_on ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  rng_bytes RNG -> lib.Lib.ExecF.rng RNG 65536 6217728 ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  C_reac_box_catalogue_matchLib.cmBase mb tp f len Sp FS fb ->
  forall (k : nat), cm_gate len fb = true ->
  forall (i : nat) (fr sp2 jj nn : Z) (m1 : word -> option byte),
  (i + k = 11)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  (* the call memory m1 (the previous stretch's end) *)
  cmFK Sp FS fr sp2 jj nn -> lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp ->
  lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs m1 (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) -> addressable m1 (fr + 112) 32 ->
  (* the return memory mb: reac_box_model_block's window and output, the caller's bytes kept *)
  lib.Lib.Frame.stk rsegs mb (sp2 - 4272) sp2 -> lib.Lib.Mem.bytes_at rsegs mb (fr + 112) (nth i DECLS []) ->
  C_reac_box_catalogue_matchLib.cmRB_kept m1 mb
    (C_reac_box_catalogue_matchLib.cmRB_callee_kept Sp fr sp2 (sp2 - 4272) 112 32) ->
  forall (x1 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
  evtF rsegs RNG (cmRBw_mb_Q ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb i fr sp2 jj nn)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 1) ya1 ya2 ya3 ya4 ya5 ya6 ya7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
             (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
        F (Z_to_bv 64 0x8509c) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    HBC Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RB RIMG RWIN RWSH RFD RFW RFPW HB k G i fr sp2 jj nn m1
    Hik Hk Hnd FK ST1 SV1 FL1 AD1 STc BBo KP x1 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6.
  destruct (C_reac_box_catalogue_matchLib.cmRB_callee_base ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 mb Sp FS fr
              sp2 jj nn (sp2 - 4272) 112 32 S16 FK ST1 SV1 FL1 AD1 STc KP) as (STW & HFr & ADb).
  pose proof (C_reac_box_catalogue_matchLib.cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb
                fr sp2 jj nn S16 HHM HB STW HFr) as HJ.
  destruct (C_reac_box_catalogue_matchLib.cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  assert (HFn : 50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\
                (f + 50 <= Sp - 9136 \/ Sp <= f)).
  { intros L'. destruct (HFp L') as (Q1 & Q2 & Q3). destruct (HFBn L') as (B1 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact B1 | exact Q3]. }
  assert (AFUn : 50 <= len -> addressable (MemNorm.normalize rsegs mb) f 50 /\ app_mem (f + 50)).
  { intros L'. split; [exact (proj2 (HFBn L')) | exact (AFp L')]. }
  (* the invariant at the base carries an empty write list *)
  assert (HJW : cmInvW ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
                  fr sp2 jj nn (MemNorm.normalize rsegs mb)) by (split; [exact HJ | apply lib.Lib.Frame.munch_refl]).
  pose proof (cmW_post_mb_K ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as K.
  C_reac_box_catalogue_matchLib.cmRB_feed K.
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO
    (K k G i fr sp2 jj nn (MemNorm.normalize rsegs mb) _ _ x1 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
       eq_refl eq_refl Hik Hk Hnd HJW (MemNorm.bytes_at_normalize rsegs mb _ _ RO BBo)
       (MemNormTr.addressable_normalize mb _ _ RO ADb))) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HQ & Hrel & Hsm).
  destruct HQ as [EX|(k' & m0 & v4 & v9 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> &
                      E4 & E9 & Hik' & Hk' & Hnd' & (Hi & HJ0 & AD0))].
  - left.
    destruct EX as (mc & r & xe & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 &
                    z3 & z5 & z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJE & ->).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists (ms_mem st), r, xe, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9,
      z10, z11, u3, u4, u5, u6.
    split; [exact Er|]. split; [|exact Es].
    exact (cmRBw_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc
             (ms_mem st) REL Hmr Hsm HJE).
  - right. subst v4 v9.
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists k'. split; [exact Hik'|]. split; [exact Hk'|]. split; [exact Hnd'|].
    exists (ms_mem st), zt0, zt1, zt2, za3, za4, za5, za6, za7, zt3, zt4, zt5, zt6.
    split; [exact Es|].
    split; [exact Hi|].
    split; [exact (cmRBw_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn m0
                     (ms_mem st) REL Hmr Hsm HJ0)|].
    exact (C_reac_box_catalogue_matchLib.cmRB_addressable_of_rel _ _ _ _ Hmr AD0).
Qed.

(* ---- stretch 6: after the flag store (pc 0x85198) -> ret; cmW_post_rel at m := mc := m1 := normalize mb.  The base
   mb is the memory at the store (stretch 5's end); the start memory is the store's write of the flag byte 0 over mb,
   reached by MemNormF.evtF_rel_ro.  The post exports munch [] from that start memory: the stretch writes nothing.
   ---- *)
Lemma cmRBw_post_rel : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  lib.Lib.ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  C_reac_box_catalogue_matchLib.cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  forall (fr sp2 jj r : Z) (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  C_reac_box_catalogue_matchLib.cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp FS fr sp2 jj 1 ->
  evtF rsegs RNG
    (cmRBw_Post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb
       (write_to_mem mb (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))))
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x85198) fc None (write_to_mem mb (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))
        (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HHM HAE RWIN RWSH RHDR RFPW HB STW fr sp2 jj r
    x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HFr.
  pose proof (C_reac_box_catalogue_matchLib.cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb
                fr sp2 jj 1 S16 HHM HB STW HFr) as HJ.
  destruct (C_reac_box_catalogue_matchLib.cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  pose proof FPn as (DT & TS & C & T & DB & kk & _ & _ & (_ & _ & _ & _ & PSn) & _).
  destruct HFr as ([(_ & _ & _ & En)|(Hj & _ & _ & _)] & _ & _); [discriminate En|].
  pose proof (C_reac_box_catalogue_matchLib.cmRB_flag_in_fs FS jj Hj) as Gfl.
  assert (Hro : lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa (fs_flag FS 2 jj)) = false).
  { pose proof PSn as (_ & _ & HS).
    apply (MemNorm.ro_false_of_wview rsegs mb (MemNorm.normalize rsegs mb) _ REL).
    exact (proj1 (HS (fs_flag FS 2 jj) Gfl)). }
  assert (HW : MemNorm.all_rw rsegs (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (length (lib.Lib.Mem.le1 (Z_to_bv 64 0)))).
  { rewrite lib.Lib.Mem.length_le1. split; [exact Hro | exact I]. }
  assert (HMR : MemNorm.mem_rel rsegs (write_to_mem mb (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))
                  (write_to_mem (MemNorm.normalize rsegs mb) (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))).
  { split.
    - exact (MemNorm.write_rw rsegs _ mb (MemNorm.normalize rsegs mb) _ (fun x => eq_refl) HW).
    - intros a b Ha Hb. rewrite (MemNorm.write_ro_same rsegs _ mb _ a HW Ha) in Hb. exact (proj2 REL a b Ha Hb). }
  assert (HAt : cmAtRel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
                  fr sp2 jj (MemNorm.normalize rsegs mb) (MemNorm.normalize rsegs mb)).
  { split; [exact HJ|]. split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [exact MIn|].
    split; [exact (fun P H => H)|]. split; [exact STn | exact PSn]. }
  pose proof (cmW_post_rel ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as L.
  C_reac_box_catalogue_matchLib.cmRB_feed L.
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R ?F' ?pc ?fc' ?rv _ ?ro) =>
    pose proof (C_reac_box_catalogue_matchLib.cmRB_ms_rel_MS R F' pc fc' rv _ _ ro HMR) as HR end.
  pose proof (MemNormF.evtF_rel_ro _ _ _ _ HR
    (L fr sp2 jj (MemNorm.normalize rsegs mb) (MemNorm.normalize rsegs mb) r x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6
       z9 z10 z11 u3 u4 u5 u6 Er HAt)) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HP & Hrel & Hsame).
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  MU & WM & _ & STW' & AC' & SR' & AW' & FP' & TL').
  destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
  assert (Hsm : MemNorm.ro_same rsegs mb (ms_mem st)).
  { intros a Ha. rewrite (Hsame a Ha). exact (MemNorm.write_ro_same rsegs _ mb _ a HW Ha). }
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
  split; [exact Es|].
  split; [exact (MemNorm.munch_rel rsegs [] (write_to_mem mb (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) _
                   (ms_mem st) m' HMR Hmr Hsame MU)|].
  split; [exact (MemNorm.wmono_rel rsegs mb (MemNorm.normalize rsegs mb) (ms_mem st) m' REL Hmr Hsm WM)|].
  split; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ Hmr)|].
  split; [exact (MemNormTr.stk_of_rel _ _ _ _ Hmr STW')|].
  split; [exact (MemNormTr.asan_cells_of_rel _ _ Hmr AC')|].
  split; [intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_of_rel P _ _ Hmr
                                (SR' P (B.ShadowRwOnT.shadow_rw_on_rel P mb _ REL HP)))|].
  split; [exact (C_reac_box_catalogue_matchLib.cmRB_addressable_of_rel _ _ _ _ Hmr AW')|].
  split; [exact (MemNormTr.fp_transport m' (ms_mem st) _ _ _ _ _ _ _
                   (fun a bs Hb => proj2 (MemNorm.bytes_at_rel rsegs _ _ a bs Hmr) Hb)
                   (fun lo hi _ Hs => MemNormTr.stk_of_rel _ _ lo hi Hmr Hs) FP')|].
  intros DT0 TS0 C0 T0 DB0 k0 Hc. apply TL'.
  exact (MemNormTr.asan_tls_cells_transport (ms_mem st) m' _ _ _ _ _ _ _
           (fun a bs Hb => proj1 (MemNorm.bytes_at_rel rsegs _ _ a bs Hmr) Hb) Hc).
Qed.
