(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 617 of its 632 lines of code are new or changed and 233 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF: upd0_F, rom_at_F and join_app_F by the same script, addr_keep_app_F, four_bytes_F and shadow4_addr_F with `hide_sec.` only, cs_join_F, cs1_F, cs2_F and cs3_F with `hide_sec.` and footprint steps, and the new lemmas sh1_F, fk_sh4_F and fk_shadow4_sub.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes:
     JOIN_0013 = 0x21a20, 32 bytes (RcSynth.J13), file offset 0x11a20 (LOAD va 0x10000 off 0):
       04 03 00 13 00 02 00 fe 0e f0 41 0a 00 00 12 12 03 02 00 01 00 7a f7 00 00 00 00 00 00 00 00 02 - matches;
     JOIN_0014 = 0x21a60, 32 bytes (RcSynth.J14), file offset 0x11a60:
       04 03 00 14 00 02 00 fe 0f f0 41 0a 00 00 12 12 01 00 06 00 01 00 78 f7 00 00 00 00 00 00 00 00 - matches.
   (xxd -s <file offset> -l 32 fuzz_ctrl.debug.)

   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z):
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes (above).
   4. Every _F carries provenance in its header and goes to the auditor a Theorem Labs lane, who signs it against its
      proved run before it counts.
   5. A StepF "uncovered access" error means STOP: report it.  Do not widen the footprint to make it pass.

   This file is an S2 file: in the original four of the lemmas here conclude the fixed ret post Q0, so their twins
   generalize it (Variable Q, Hypothesis HKR : bmb_KR Q) and apply HKR where the original applies epi (here only
   through exit_r_F / fin1_F).  The pure Definitions of the proved files (FK, Wf, BI, SAVES, EB, EBW, RB) are
   kept by Notation; what mentions evt, and - after the route (C) narrowing - everything of the proved _binv.v
   that carried the universal shadow_rw, has an _F twin (BV_F, bv_jx_F, ... in reac_box_model_block_binvF.v).

   One cost note, because it decides the shape of the proofs below and of the access hook: the Section MainF
   hypotheses (HA with its division, HS16's mod, HP HN HO AP ANB AO AJ1 AJ2 NDJ) are dragged into zify, so an
   arithmetic goal that needs Z.div_mod_to_equations costs minutes in this section (measured here: 569.8 s for a
   one-line shadow-range goal, 1.5 s for the same goal after the proved file's own `hide_sec`).  So every changed proof
   below calls `hide_sec` first, each accessed shadow BYTE is put in the bare `rng RNG (x / 8 + ASAN_K) 1` form
   once per lemma by sh1_F, except cs3_F's three frame-shadow stores (:656, :753, :769), which the RSH fact of fk_rng_F covers (applied at :632), and the acc_hint does its one division step last (mb_accF :122). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2
  reac_box_model_block_cases.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  sh_word_on asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on
  asan_stack_malloc_c_on reac_box_model_block_c_on
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF
  reac_box_model_block_binv2F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* Last: StepF's step / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.
Module BCS := reac_box_model_block_cases.
Module BF := reac_box_model_block_baseF.
Module BEPIF := reac_box_model_block_epiF.
Module BINVF := reac_box_model_block_binvF.
Module BINV2F := reac_box_model_block_binv2F.
(* Route (C): the audited shadow region of this function and the restricted shadow_rw (a Theorem Labs lane's leaf
   reac_box_model_block_c_on.v:38, lib/A/ShadowRwOn.v:17).  The universal A.AsanRT.shadow_rw is FALSE at the
   allocator state (auditor a Theorem Labs lane, batch 75), so it is not a premise of this file any more. *)
Module SRON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

From Ltac2 Require Import Ltac2.

(* The section-closing generalization abstracts each lemma of Section Main over the section variables and hypotheses
   it uses, in declaration order, under their own names. inst c applies c to the hypotheses of the current context
   that carry the names of c's leading binders, and stops at the first binder whose name is not a hypothesis. *)
Ltac2 rec inst_go (c : constr) (t : constr) (acc : constr list) :=
  let fin () := match acc with
                | [] => c
                | _ => Constr.Unsafe.make (Constr.Unsafe.App c (Array.of_list (List.rev acc)))
                end in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod bnd body =>
      match Constr.Binder.name bnd with
      | Some id =>
          match Control.case (fun () => Control.hyp id) with
          | Val hv => let (h, _) := hv in inst_go c (Constr.Unsafe.substnl [h] 0 body) (h :: acc)
          | Err _ => fin ()
          end
      | None => fin ()
      end
  | _ => fin ()
  end.

Ltac2 inst (c : constr) := inst_go c (Constr.type c) [].

Ltac2 Notation "inst_exact" c(constr) := let r := inst c in exact $r.

Set Default Proof Mode "Classic".

(* The store hook of the evtF walk of this function (reac_box_model_blockF.v of 3c9fcc93205): it also transports
   rd_mono. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* An address the walk builds from a register holds [bv_unsigned (Z_to_bv 64 e)], which StepF's syntactic matching
   does not relate to the [rng] premise of its region (the box, the row, the frame words and the shadow bytes).
   Normalize the wrap, then close the bounds from any rng hypothesis; Z.div_mod_to_equations is needed where the
   address or the bound holds a division (a shadow byte is x / 8 + ASAN_K).
   The hook fires ONLY on that wrapped shape: StepF calls acc_hint FIRST in solve_acc1, so a wider pattern (every
   [wa a]) would shadow StepF's own cheap paths and run Z.div_mod_to_equations + lia over every rng hypothesis at
   every access of the run. *)
Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, ?n) =>
      lazymatch a with
      | context [bv_unsigned (Z_to_bv 64 _)] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
              cbv [wa]; rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit_wrap;
              Z.div_mod_to_equations; lia
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mb_accF.

(* The shadow-check tactics of reac_box_model_block_base.v:313-354 over evtF (an Ltac body binds the tactics in
   scope where it is written, so the evt forms of the proved file cannot serve here). *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RNGq ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNGq Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac pre_no X RX := idtac.
Ltac no_extra X := idtac.
Ltac add1 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.

Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* The callee contracts in their narrowed (_on) footprint form: a Theorem Labs lane's asan_memset_cF_on.v /
     asan_memcpy_cF_on.v and a Theorem Labs lane's build_dt1_single_c.v, the same three forms that
     reac_box_model_block_binv2F.v's cl_ms_F / cl_mc_F / cl_ms_loc_F / cl_bd_F take.  No lemma of this stretch
     takes the stack-malloc contract (the 0x85bb8 call is an event, cut in lane BASE). *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C): the shadow bytes of the audited region only.  The universal A.AsanRT.shadow_rw is FALSE at the
     allocator state (auditor a Theorem Labs lane, batch 75), so it is not a premise of this file. *)
  Hypothesis SR0 : SRON.shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
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

  (* The footprint and the nine regions of the run (reac_box_model_blockF.v of 3c9fcc93205, Section MainF). *)
  Variable RNG : footprint.
  Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
  Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rwsh : sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
  Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
  Hypothesis Rtls : reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
  Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
  Hypothesis RFSw : rng_ivls RNG (tl (fp_w [0%nat] FS)).
  Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).

  (* The data regions, as section hypotheses in every F file of this family (a Theorem Labs lane, interface decision B). *)
  Hypothesis Rby : rng_bytes RNG.
  Hypothesis Rwsw : sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis RP : p <> 0 -> rng RNG p 296.
  Hypothesis RPs : p <> 0 -> sh_cover RNG p 296.
  Hypothesis RO : o <> 0 -> rng RNG o 32.
  Hypothesis ROs : o <> 0 -> sh_cover RNG o 32.
  Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    rng RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    sh_cover RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RJ13s : b = 2 -> sh_cover RNG JOIN_0013 32.
  Hypothesis RJ14s : b = 1 -> sh_cover RNG JOIN_0014 32.

  (* The ret-post obligation of the epi half (reac_box_model_block_epiF.v): this file is an S2 file, so it
     generalizes the fixed Q0 of the proved run. *)
  Let bmb_KR := ltac2:(inst_exact @BEPIF.bmb_KR).
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The pure definitions of the proved files at this section's variables (interface decision A: kept by
     Notation, never redefined). *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  Let BV_F := ltac2:(inst_exact @BINVF.BV_F).
  Notation RB := (BINV.RB sp gp tp p o off A).

  (* The section facts of the proved files at this section's variables (the section-closing generalization
     abstracted each over the variables it used, so they cannot be applied by name). *)
  Let HA1 := ltac2:(inst_exact @B.HA1).
  Let fk_facts_F := ltac2:(inst_exact @BF.fk_facts_F).
  Let mrd_w1 := ltac2:(inst_exact @B.mrd_w1).
  Let mrd_wn_ne := ltac2:(inst_exact @B.mrd_wn_ne).
  (* Under the narrowed SR0 the Section facts of the proved _binv.v cannot be re-imported (every one of them
     carries the universal shadow_rw): they come from their _F twins in reac_box_model_block_binvF.v. *)
  Let djf_F := ltac2:(inst_exact @BINVF.djf_F).
  Let bv_jx_F := ltac2:(inst_exact @BINVF.bv_jx_F).
  Let bv_fstore_F := ltac2:(inst_exact @BINVF.bv_fstore_F).
  Let bv_sstore_F := ltac2:(inst_exact @BINVF.bv_sstore_F).
  Let call_facts_F := ltac2:(inst_exact @BINVF.call_facts_F).

  (* The footprint facts and run twins of the lanes below this one. *)
  Let fk_rng_F := ltac2:(inst_exact @BF.fk_rng_F).
  Let exit_r_F := ltac2:(inst_exact @BINVF.exit_r_F).
  Let fin1_F := ltac2:(inst_exact @BINVF.fin1_F).
  Let cl_mc_F := ltac2:(inst_exact @BINV2F.cl_mc_F).
  Let cl_bd_F := ltac2:(inst_exact @BINV2F.cl_bd_F).
  (* Route (C) membership helpers of reac_box_model_block_binv2F.v: a shadow word of the window / of the box is
     inside R, this function's audited shadow region. *)
  Let win_shadow_sub := ltac2:(inst_exact @BINV2F.win_shadow_sub).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (BCS.mb_hide T) in H.
  Ltac unhide H := unfold BCS.mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* The byte at a + i is writable in m: in the frame (FW), a shadow byte of the frame (SW) or in the window (ST0). *)
  Ltac wvF :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    match goal with
    | FW : forall i, 0 <= i < 64 -> wview rsegs m (wa (?fr + i)) <> None |- wview _ _ (wa ?x) <> None =>
        replace x with (fr + (x - fr)) by lia; apply FW; lia
    end.
  Ltac wvS :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    match goal with
    | SW : forall i, 0 <= i < 8 -> wview rsegs m (wa (?s + i)) <> None |- wview _ _ (wa ?x) <> None =>
        replace x with (s + (x - s)) by lia; apply SW; lia
    end.
  Ltac wvW :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii; apply (B.stk_wv m _ _ _ ST0); lia.

  (* wmono from m to the current memory: a carried fact and the stores since. *)
  Ltac wmo := first [ assumption | apply wmono_write; wmo ].

  (* store_ok of n bytes at a in the current memory, the bytes writable in m by wv. *)
  Ltac wst_with wv a n :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (apply (B.wv_store_ok m mm a n); [ wv | wmo | lia | lia ])
    end.
  Ltac wstF a n := wst_with ltac:(wvF) a n.
  Ltac wstS a n := wst_with ltac:(wvS) a n.
  Ltac wstW a n := wst_with ltac:(wvW) a n.

  (* Normalize a just-stored address to wa-form (as store_done's first step). *)
  Ltac norm_store :=
    lazymatch goal with
    | |- evtF ?segs ?RNGq ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
        let E := addr_expr a in
        lazymatch a with
        | wa _ => idtac
        | Z_to_bv 64 _ => change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
        | _ => replace (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs) by (f_equal; addr_eq_tac)
        end
    end.

  (* Branch conditions on literal-valued registers (as the plain proof's if_t/if_f). *)
  Ltac ulit := repeat match goal with
                      | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
                      end.
  Ltac cond_solve := unfold_cond; ulit; first [solve_cond_rec | solve_cond_base].
  Ltac if_t := lazymatch goal with
               | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; cond_solve]
               end.
  Ltac if_f := lazymatch goal with
               | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; cond_solve]
               end.

  (* A store into application memory keeps every addressable range (it writes no shadow byte). *)
  Lemma addr_keep_app_F : forall (mm : word -> option byte) (a : Z) (bs : list byte) (R nR : Z),
    addressable mm R nR -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> Z.of_nat (length bs) <= 4096 ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> app_mem (a + i)) ->
    addressable (write_to_mem mm (wa a) bs) R nR.
  Proof.
    intros mm a bs R nR HAx Ha Hl Hsz Happ. hide_sec.
    pose proof HAx as (R0 & Rn & Re & HAd).
    apply (B.addr_keep mm (write_to_mem mm (wa a) bs) R nR HAx).
    intros i Hi. destruct (HAd i Hi) as (Hap & bb & Hb & Hok).
    pose proof (rt_app_shadow (R + i) Hap) as Hsh.
    destruct (Z.eq_dec (Z.of_nat (length bs)) 0) as [E0|E0].
    - apply mrd_wn_ne; [exact Ha | exact Hl | | clear -E0; lia].
      pose proof (rt_shadow_bound _ Hsh) as HB. clear -HB; lia.
    - pose proof (Happ 0 ltac:(lia)) as A0. rewrite Z.add_0_r in A0.
      pose proof (Happ (Z.of_nat (length bs) - 1) ltac:(lia)) as A1.
      pose proof (rt_shadow_bound _ Hsh) as HB.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0, A1.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
      apply mrd_wn_ne; [exact Ha | exact Hl | clear -HB; lia | clear -A0 A1 Hsh HB E0 Hl Hsz; lia].
  Qed.

  (* --- the cases of the jump table at 0x219f4 --- *)

  Lemma upd0_F : forall (X Y : list byte), length X = length Y -> upd_bytes X 0 Y = Y.
  Proof.
    intros X Y L. unfold upd_bytes. cbn [firstn]. rewrite skipn_all2 by lia. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma rom_at_F : forall (mm : word -> option byte) (AA : Z) (bs : list byte), mem_inv rsegs mm ->
    (ro_bytes_b rsegs AA bs && (0 <=? AA) && (AA + Z.of_nat (length bs) <=? 2^64))%bool = true ->
    bytes_at rsegs mm AA bs.
  Proof.
    intros mm AA bs Hm H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply ro_bytes_at; [exact Hm | exact H2 | exact H3 |]. apply ro_bytes_b_sound. exact H1.
  Qed.

  (* The JOIN blocks are low application memory. *)
  Lemma join_app_F : forall x, JOIN_0013 <= x <= JOIN_0014 + 32 -> app_mem x.
  Proof.
    intros x Hx. unfold JOIN_0013, JOIN_0014 in Hx. unfold app_mem, LOWMEM_END. left. lia.
  Qed.
  (* One shadow BYTE of a covered range, in the bare rng form StepF's access solver matches cheaply (its own
     paths close an access with `lia` only, and the 8-aligned cover of sh_cover needs a division argument).  The
     division argument is made ONCE here, not at every access of the run. *)
  Lemma sh1_F : forall a n x, 0 <= a -> 0 < n -> a <= x -> x < a + n -> sh_cover RNG a n ->
    rng RNG (x / 8 + ASAN_K) 1.
  Proof.
    intros a n x Ha Hn Hx1 Hx2 H. hide_sec.
    unfold sh_cover, shadow_addr, ASAN_K in H. unfold ASAN_K.
    eapply rng_sub'; [exact H|]. Z.div_mod_to_equations. lia.
  Qed.


  (* 0x85ef4 (b = 1 and b = 2 join here): __asan_memcpy(o, JOIN, 32) and the result 1.
     Added premises: RJA / RJAs / RJAm, the JOIN block JA this lemma takes as a parameter - its range, its shadow
     cover and the membership of its shadow word in R (__asan_memcpy's _on contract asks for it).  JA is a lemma
     binder, not one of the section regions: cs1_F and cs2_F discharge the three from Rimg, from RJ14s / RJ13s
     and from R's b = 1 / b = 2 disjunct. *)
  Lemma cs_join_F : forall fr f spc j n w56 mc J (JA : Z) (JB : list byte) (a1 : word)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV_F fr j n w56 mc (zeros 32) J ->
    (JA = JOIN_0013 \/ JA = JOIN_0014) -> bytes_at rsegs mc JA JB -> length JB = 32%nat ->
    addressable mc JA 32 -> JB = synth row b nb -> rc row b = 1 -> bv_unsigned a1 = JA ->
    rng RNG JA 32 -> sh_cover RNG JA 32 ->
    (forall a, sh_word_on JA 32 a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 a1 x12 x13 x14 x15 x16 x17
                             x21 x22 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x85ef4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J JA JB a1 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 PI EJA HJB LJB AJB EX Er E1 RJA RJAs RJAm.
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (RO Ho0) as RObox. pose proof (ROs Ho0) as RObsh.
    pose proof (call_facts_F fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI)
      as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    assert (DOJ : o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)
      by (hide_sec; destruct (HO Ho0) as (_ & _ & H); exact H).
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold RB, BINV.RB. step. step. step.
    eapply (cl_mc_F fr f spc j n w56 mc (zeros 32) J 0x85f00 0 32 JA JB); try eassumption.
    - apply ret_pc_even; [lia | reflexivity].
    - lia.
    - lia.
    - lia.
    - cbn [Z.of_nat]. rewrite Z.add_0_r. apply unsigned_lit. lia.
    - cbn [Z.of_nat]. rewrite unsigned_lit by lia. reflexivity.
    - cbn [Z.of_nat]. apply join_app_F. unfold JOIN_0013, JOIN_0014 in *. clear -EJA; lia.
    - cbn [Z.of_nat]. apply join_app_F. unfold JOIN_0013, JOIN_0014 in *. clear -EJA; lia.
    - cbn [Z.of_nat]. rewrite Z.add_0_r. unfold JOIN_0013, JOIN_0014 in *. clear -DOJ EJA; lia.
    - cbn [Z.of_nat]. left. unfold JOIN_0013, JOIN_0014 in *. clear -EJA HHM'; lia.
    - intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc1 PI1.
      (* the state of a cl_*_F continuation is written with binvF's RB_F, the alias of BINV.RB *)
      unfold BINVF.RB_F, BINV.RB. step.
      eapply (fin1_F fr f spc j n w56 mc1 (upd_bytes (zeros 32) 0 JB) J); try eassumption.
      rewrite <- EX. apply (upd0_F (zeros 32) JB). unfold zeros. rewrite repeat_length. lia.
  Qed.

  (* b = 1 (0x85eec): the JOIN_0014 block. *)
  Lemma cs1_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 1 -> BV_F fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                             x21 x22 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x85eec) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    hide_sec.
    pose proof PI as ((_ & _ & _ & MIc & _) & _).
    destruct (bv_jx_F fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as (_ & _ & _ & _ & _ & _ & _ & JJ1 & _).
    pose proof (JJ1 Eb) as AJ.
    unfold RB, BINV.RB. step. step.
    eapply (cs_join_F fr f spc j n w56 mc J JOIN_0014 J14); try eassumption.
    - right. reflexivity.
    - apply rom_at_F; [exact MIc | vm_compute; reflexivity].
    - reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite unsigned_lit; [reflexivity | unfold JOIN_0014; lia].
    - (* the JOIN_0014 block is an image constant: inside [0x10000, 0x5ee000) *)
      apply (rng_sub' RNG 0x10000 0x5ee000); [exact Rimg | unfold JOIN_0014; lia].
    - exact (RJ14s Eb).
    - (* R's b = 1 disjunct: the JOIN_0014 block's shadow word *)
      intros a Ha. unfold C_ON.reac_box_model_block_shadow_R.
      right. right. right. right. right. left. split; [exact Eb | exact Ha].
  Qed.

  (* b = 2 (0x85eac): the JOIN_0013 block. *)
  Lemma cs2_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 2 -> BV_F fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                             x21 x22 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x85eac) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    hide_sec.
    pose proof PI as ((_ & _ & _ & MIc & _) & _).
    destruct (bv_jx_F fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as (_ & _ & _ & _ & _ & _ & _ & _ & JJ2).
    pose proof (JJ2 Eb) as AJ.
    unfold RB, BINV.RB. step. step. step.
    eapply (cs_join_F fr f spc j n w56 mc J JOIN_0013 J13); try eassumption.
    - left. reflexivity.
    - apply rom_at_F; [exact MIc | vm_compute; reflexivity].
    - reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite unsigned_lit; [reflexivity | unfold JOIN_0013; lia].
    - apply (rng_sub' RNG 0x10000 0x5ee000); [exact Rimg | unfold JOIN_0013; lia].
    - exact (RJ13s Eb).
    - (* R's b = 2 disjunct: the JOIN_0013 block's shadow word *)
      intros a Ha. unfold C_ON.reac_box_model_block_shadow_R.
      right. right. right. right. right. right. split; [exact Eb | exact Ha].
  Qed.

  (* The four digit bytes written into the ASan frame at fr + 32, read back. *)
  Lemma four_bytes_F : forall (mm : word -> option byte) (AA : Z) (l0 l1 l2 l3 : list byte),
    length l0 = 1%nat -> length l1 = 1%nat -> length l2 = 1%nat -> length l3 = 1%nat ->
    0 <= AA -> AA + 4 <= 2 ^ 64 ->
    bytes_at rsegs (write_to_mem (write_to_mem (write_to_mem (write_to_mem mm (wa AA) l0)
                                                  (wa (AA + 1)) l1) (wa (AA + 2)) l2) (wa (AA + 3)) l3)
      AA (l0 ++ l1 ++ l2 ++ l3).
  Proof.
    intros mm AA l0 l1 l2 l3 L0 L1 L2 L3 H0 H1. hide_sec.
    destruct l0 as [|c0 [|? ?]]; try discriminate. destruct l1 as [|c1 [|? ?]]; try discriminate.
    destruct l2 as [|c2 [|? ?]]; try discriminate. destruct l3 as [|c3 [|? ?]]; try discriminate.
    cbn [app].
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error]; simpl Z.of_nat; [| | | | lia];
      repeat (rewrite mrd_w1 by lia);
      repeat match goal with
             | |- context [?x =? ?y] =>
                 first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia)
                       | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
             end;
      reflexivity.
  Qed.

  (* After the shadow byte of [fr + 32, fr + 40) is set to 4, the four bytes at fr + 32 are addressable. *)
  Lemma shadow4_addr_F : forall fr f spc j n w56 (mc : word -> option byte) (v : byte),
    FK fr f spc j n w56 -> bv_signed v = 4 ->
    addressable (write_to_mem mc (wa (fr / 8 + off + 4)) [v]) (fr + 32) 4.
  Proof.
    intros fr f spc j n w56 mc v HK Hv. hide_sec.
    destruct (fk_facts_F fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (FAP 32 ltac:(lia)) as AF32. pose proof (FAP 35 ltac:(lia)) as AF35.
    pose proof AF32 as AF32'. pose proof AF35 as AF35'.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF32', AF35'.
    split; [clear -AF32'; lia|]. split; [lia|]. split; [unfold APPMEM_END; clear -AF35'; lia|].
    intros i Hi. split.
    - replace (fr + 32 + i) with (fr + (32 + i)) by lia. apply FAP. lia.
    - exists v.
      assert (Esh : shadow_addr (fr + 32 + i) = fr / 8 + off + 4).
      { unfold shadow_addr. rewrite Hoff. clear -FR8 Hi. Z.div_mod_to_equations. lia. }
      rewrite Esh. split.
      + rewrite mrd_w1 by (clear -SH1 SH2; lia). rewrite Z.eqb_refl. reflexivity.
      + unfold shadow_ok. right. rewrite Hv. split; [|lia].
        replace ((fr + 32 + i) mod 8) with i by (clear -FR8 Hi; Z.div_mod_to_equations; lia). lia.
  Qed.

  (* The 8-ALIGNED shadow word of the digit buffer [fr + 32, fr + 36), which build_dt1_single's quick check
     loads: in the real-stack arm the frame lies in the window, whose shadow cover Rwsh is 8-aligned at both
     ends; in the class-0 arm it lies in the class-0 frame area, whose shadow RFSsh runs from
     shadow_addr (FS + 36864) over 131072 bytes, and FS mod 4096 = 0 with ASAN_K mod 8 = 0 makes that start
     8-aligned too.  Same two cases as fk_rng_F (reac_box_model_block_baseF.v). *)
  Lemma fk_sh4_F : forall fr f spc j n w56, FK fr f spc j n w56 -> sh_cover RNG (fr + 32) 4.
  Proof.
    intros fr f spc j n w56 HK. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, P5.
    assert (EFR0 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (ESH0 : fs_M 0%nat * fs_B 0%nat / 8 = 131072) by reflexivity.
    (* copies: the section hypotheses themselves cannot be changed, the Let fk_rng_F uses them *)
    pose proof RFSsh as RFsh. rewrite ESH0, EFR0 in RFsh. unfold shadow_addr, ASAN_K in RFsh.
    pose proof Rwsh as Rwsh'.
    unfold sh_cover, shadow_addr, ASAN_K.
    unfold sh_cover, shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K in Rwsh'.
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
    - eapply rng_sub'; [exact Rwsh'|]. Z.div_mod_to_equations. lia.
    - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *.
      change (2 ^ (14 - 0)) with 16384 in Hj. change (2 ^ 0) with 1 in *.
      eapply rng_sub'; [exact RFsh|]. Z.div_mod_to_equations. lia.
  Qed.

  (* Route (C) membership for the digit buffer's shadow word: build_dt1_single's _on contract asks that the
     shadow its own region names lie inside R.  Same two FK arms as fk_sh4_F: the real-stack frame is in the
     window (R's first disjunct, win_shadow_sub), the class-0 frame is in the class-0 block
     (R's second disjunct, asan_stack_malloc_shadow_R FS 0). *)
  Lemma fk_shadow4_sub : forall fr f spc j n w56, FK fr f spc j n w56 ->
    forall a, sh_word_on (fr + 32) 4 a ->
      C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a.
  Proof.
    intros fr f spc j n w56 HK a Ha. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, P5.
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
    - exact (win_shadow_sub a (A - 64 + 32) 4 ltac:(unfold REAC_BOX_MODEL_BLOCK_K; lia) ltac:(lia)
               ltac:(lia) Ha).
    - unfold C_ON.reac_box_model_block_shadow_R. right. left.
      destruct Ha as (Hn0 & Hlo & Hhi).
      unfold asan_stack_malloc_shadow_R, fs_frame, fs_M, fs_B, sh_word_on,
        rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr, ASAN_K in *.
      change (Z.of_nat 0) with 0 in *. change (2 ^ 0) with 1 in *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 0)) with 16384 in Hj.
      Z.div_mod_to_equations; lia.
  Qed.

  (* b = 3 (0x85eb8): the four decimal digits of the 16-bit field at p + 266 through build_dt1_single. *)
  Lemma cs3_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 3 -> BV_F fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                             x21 x22 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x85eb8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'.
    (* the regions this run touches: the row and the box as bare rng facts, the shadow BYTE the instrumented
       read of p + 266 loads (sh1_F makes the division argument once), the frame and its shadow from FK. *)
    pose proof (RP Hp0) as RProw. pose proof (RO Ho0) as RObox.
    pose proof (sh1_F p 296 (p + 266) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (RPs Hp0)) as RShp.
    pose proof (sh1_F p 296 (p + 267) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (RPs Hp0)) as RShp2.
    destruct (fk_rng_F fr f spc j n w56 HK) as (RFR & RSH).
    assert (HPf : p mod 8 = 0 /\ length row = 296%nat)
      by (hide_sec; destruct (HP Hp0) as (H1 & H2 & _); split; assumption).
    destruct HPf as (Hp8 & Lrow).
    destruct (fk_facts_F fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof PI as ((MUc & WMc & RMc & MIc & SVc & HHc & F56c) & HO32 & HL & HRB & HNB).
    pose proof (rs_rd2 rsegs mc p row 266 HRB ltac:(lia)) as R1.
    change (Z.of_nat 266) with 266 in R1.
    pose proof (rs_rw16_range row 266) as RV.
    pose proof (bv_jx_F fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    assert (RX : 0 <= p + 266 < 2 ^ 64)
      by (pose proof JAP as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    pose proof (B.acl_shadow mc p 296 266 2 (p + 266) JAP ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH.
    pose proof (FAP 0 ltac:(lia)) as AF0. rewrite Z.add_0_r in AF0.
    pose proof (FAP 63 ltac:(lia)) as AF63.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF0, AF63.
    hide_sec.
    unfold RB, BINV.RB.
    step.
    chk_core (p + 266) RX (Z_to_bv 5 12) SH pre_sr add1.
    step. rewrite rs_zx16. step. step. step.
    (* the shadow byte of the digit buffer is set to 4 *)
    wstS (fr / 8 + off + 4) 1%nat. step. norm_store.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) => replace l with [Z_to_bv 8 4] by reflexivity
    end.
    pose proof (shadow4_addr_F fr f spc j n w56 mc (Z_to_bv 8 4) HK ltac:(reflexivity)) as AD4.
    pose proof (bv_sstore_F fr f spc j n w56 mc (zeros 32) J 4 (wa (fr / 8 + off + 4)) [Z_to_bv 8 4]
                  HK Hp0 Ho0 PI ltac:(lia) ltac:(cbn [length]; lia) eq_refl) as PI1.
    repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
    step.
    rewrite (unsigned_lit (rw16 row 266)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    assert (ES : synth row b nb = (if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32))
      by (rewrite Eb; reflexivity).
    assert (ER : rc row b = (if fwm row <=? 9999 then 1 else -1)) by (rewrite Eb; reflexivity).
    destruct (Z.leb_spec (fwm row) 9999) as [FW9|FW9]; unfold fwm in FW9.
    - (* the value fits in four digits: write them into the frame and call build_dt1_single *)
      if_t.
      do 30 step.
      (* the four digit bytes at fr + 32 *)
      wstF (fr + 32) 1%nat. step. norm_store.
      wstF (fr + 33) 1%nat. step. norm_store.
      wstF (fr + 34) 1%nat. step. norm_store.
      wstF (fr + 35) 1%nat. step. norm_store.
      repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem (write_to_mem (write_to_mem ?m0 _ ?l0) _ ?l1) _ ?l2) _ ?l3) _) =>
          pose proof (four_bytes_F m0 (fr + 32) l0 l1 l2 l3 ltac:(simpl_sizes; reflexivity)
                        ltac:(simpl_sizes; reflexivity) ltac:(simpl_sizes; reflexivity)
                        ltac:(simpl_sizes; reflexivity)
                        ltac:(clear -AF0 AF63; lia) ltac:(clear -AF0 AF63; lia)) as HD4;
          replace (fr + 32 + 1) with (fr + 33) in HD4 by lia;
          replace (fr + 32 + 2) with (fr + 34) in HD4 by lia;
          replace (fr + 32 + 3) with (fr + 35) in HD4 by lia
      end.
      (* the four bytes are the decimal digits of the field *)
      assert (Hv : 0 <= rw16 row 266 < 10000) by (clear -RV FW9; lia).
      lazymatch type of HD4 with
      | bytes_at _ _ _ ?DD =>
          assert (EDD : DD = digits (fwm row));
          [ unfold digits, fwm; rewrite !rc_le1_lit; cbn [app map];
            clear -Hv; revert Hv; generalize (rw16 row 266); intros v Hv;
            repeat apply rc_cons_eq; try reflexivity; unfold bz; rs_brute_tac v
          | rewrite EDD in HD4 ]
      end.
      (* the invariant across the four frame stores *)
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem (write_to_mem (write_to_mem ?m0 _ ?l0) _ ?l1) _ ?l2) _ ?l3) _) =>
          pose proof (bv_fstore_F fr f spc j n w56 m0 (zeros 32) J 32 (wa (fr + 32)) l0
                        HK Hp0 Ho0 PI1 ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIb;
          pose proof (bv_fstore_F fr f spc j n w56 _ (zeros 32) J 33 (wa (fr + 33)) l1
                        HK Hp0 Ho0 PIb ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIc;
          pose proof (bv_fstore_F fr f spc j n w56 _ (zeros 32) J 34 (wa (fr + 34)) l2
                        HK Hp0 Ho0 PIc ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PId;
          pose proof (bv_fstore_F fr f spc j n w56 _ (zeros 32) J 35 (wa (fr + 35)) l3
                        HK Hp0 Ho0 PId ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIe;
          assert (APFR : forall x, fr <= x < fr + 64 -> app_mem x)
            by (intros x Hx; replace x with (fr + (x - fr)) by lia; apply FAP; lia);
          pose proof (addr_keep_app_F _ (fr + 32) l0 (fr + 32) 4 AD4 ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADb;
          pose proof (addr_keep_app_F _ (fr + 33) l1 (fr + 32) 4 ADb ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADc;
          pose proof (addr_keep_app_F _ (fr + 34) l2 (fr + 32) 4 ADc ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADd;
          pose proof (addr_keep_app_F _ (fr + 35) l3 (fr + 32) 4 ADd ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADe
      end.
      do 4 step.
      eapply (cl_bd_F fr f spc j n w56 _ J 0x865fc 4 (fr + 32) 0 (digits (fwm row))).
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + exact PIe.
      + apply ret_pc_even; [lia | reflexivity].
      + lia.
      + lia.
      + reflexivity.
      + rewrite unsigned_lit; [reflexivity | clear -Ro'; lia].
      + rewrite unsigned_lit; [reflexivity | lia].
      + rewrite unsigned_lit; [reflexivity | clear -AF0 AF63; lia].
      + cbn [Z.of_nat]. rewrite unsigned_lit; [reflexivity | lia].
      + exact HD4.
      + cbn [Z.of_nat]. exact ADe.
      + replace (fr + 32 + 7) with (fr + 39) by lia. apply APFR. lia.
      + cbn [Z.of_nat]. replace (fr + 32 + 4) with (fr + 36) by lia. apply APFR. lia.
      + cbn [Z.of_nat]. pose proof (djf_F fr f spc j n w56 HK Hp0 Ho0) as (DJo & _). clear -DJo; lia.
      + cbn [Z.of_nat]. right. clear -FRlo FRhi; lia.
      (* the three footprint premises of cl_bd_F: the digit buffer in the ASan frame, its shadow word, and that
         shadow word's membership in R *)
      + cbn [Z.of_nat]. eapply rng_sub'; [exact RFR|]. clear -FRlo FRhi; lia.
      + cbn [Z.of_nat]. exact (fk_sh4_F fr f spc j n w56 HK).
      + cbn [Z.of_nat]. exact (fk_shadow4_sub fr f spc j n w56 HK).
      + intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mcf PIf.
        pose proof PIf as ((MUf & WMf & RMf & MIf & _) & _).
        unfold BINVF.RB_F, BINV.RB. step. step.
        wstS (fr / 8 + off + 4) 1%nat. step. norm_store.
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m0 (wa ?aw) ?lw) _) =>
            pose proof (bv_sstore_F fr f spc j n w56 m0 (dt1s 0 (digits (fwm row))) J 4 (wa aw) lw
                          HK Hp0 Ho0 PIf ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIg
        end.
        repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
        step.
        eapply (exit_r_F fr f spc j n w56 _ (dt1s 0 (digits (fwm row))) J 1); try eassumption.
        * rewrite ES. replace (fwm row <=? 9999) with true by (symmetry; apply Z.leb_le; unfold fwm; lia).
          reflexivity.
        * rewrite ER. replace (fwm row <=? 9999) with true by (symmetry; apply Z.leb_le; unfold fwm; lia).
          reflexivity.
    - (* the value does not fit: the box stays zero and the result is -1 *)
      if_f.
      step. step. step.
      wstS (fr / 8 + off + 4) 1%nat. step. norm_store.
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m0 (wa ?aw) ?lw) _) =>
          pose proof (bv_sstore_F fr f spc j n w56 m0 (zeros 32) J 4 (wa aw) lw
                        HK Hp0 Ho0 PI1 ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIg
      end.
      repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
      step.
      eapply (exit_r_F fr f spc j n w56 _ (zeros 32) J (-1)); try eassumption.
      + rewrite ES. replace (fwm row <=? 9999) with false by (symmetry; apply Z.leb_gt; unfold fwm; lia).
        reflexivity.
      + rewrite ER. replace (fwm row <=? 9999) with false by (symmetry; apply Z.leb_gt; unfold fwm; lia).
        reflexivity.
  Qed.

End MainF.
