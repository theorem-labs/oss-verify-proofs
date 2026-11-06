(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 343 of its 358 lines of code are new or changed and 233 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases0a.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF, from its proof scripts; the script edits include `hide_sec.` in all four, footprint steps in stchk0_F and osum0_F, and the new lemma sh1_F.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the two runs of this file, the 31-byte checksum
   loop at 0x866c0 and the check byte at 0x866f8, read the box [o, o + 32), its shadow bytes and the code; they
   read no image constant and no runtime cell with a fixed value).

   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z):
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes (none here).
   4. Every _F carries provenance in its header and goes to the auditor a Theorem Labs lane, who signs it against its
      proved run before it counts.
   5. A StepF "uncovered access" error means STOP: report it.  Do not widen the footprint to make it pass.

   This file is an S2 file: in the original both lemmas conclude the fixed ret post Q0, so the twins generalize it
   (Variable Q, Hypothesis HKR : bmb_KR Q) and reach it through fin1_F.  The pure Definitions of the proved files
   (FK, Wf, BI, SAVES, EB, EBW, RB, H8) are kept by Notation or by qualified name; what mentions evt, and - after
   the route (C) narrowing - everything of the proved _binv.v that carried the universal shadow_rw, has an _F
   twin (BV_F, bv_jx_F, bv_ok_F, bv_store_F, rw1_F in reac_box_model_block_binvF.v).

   One cost note, because it decides the shape of the proofs below and of the access hook: the Section MainF
   hypotheses (HA with its division, HS16's mod, HP HN HO AP ANB AO AJ1 AJ2 NDJ) are dragged into zify, so an
   arithmetic goal that needs Z.div_mod_to_equations costs minutes in this section (measured here: 569.8 s for a
   one-line shadow-range goal, 1.5 s for the same goal after the proved file's own `hide_sec`).  So every proof
   below calls `hide_sec` first, each accessed shadow BYTE is put in the bare `rng RNG (x / 8 + ASAN_K) 1` form
   once per lemma by sh1_F, and the acc_hint does no division reasoning. *)
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
  reac_box_model_block_cases0a.
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
Module BC0A := reac_box_model_block_cases0a.
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
   does not relate to the [rng] premise of its region (the box and its shadow bytes): normalize the wrap, then
   close the bounds from an rng hypothesis by lia alone.
   Two things keep this hook CHEAP, which the file needs because StepF calls acc_hint FIRST in solve_acc1, at
   every access of the run, under a backtracking match over every rng hypothesis: it fires only on the wrapped
   shape (a wider pattern would also shadow StepF's own paths), and it does no division reasoning.  The division
   argument of a shadow byte is made ONCE per lemma, by sh1_F below, which puts the accessed shadow byte in the
   bare `rng RNG (x / 8 + ASAN_K) 1` form. *)
Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, ?n) =>
      lazymatch a with
      | context [bv_unsigned (Z_to_bv 64 _)] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
              cbv [wa]; rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit_wrap; lia
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
  Let mrd_w1 := ltac2:(inst_exact @B.mrd_w1).
  Let mrd_wn_ne := ltac2:(inst_exact @B.mrd_wn_ne).
  (* Under the narrowed SR0 the Section facts of the proved _binv.v cannot be re-imported (every one of them
     carries the universal shadow_rw): they come from their _F twins in reac_box_model_block_binvF.v. *)
  Let rw1_F := ltac2:(inst_exact @BINVF.rw1_F).
  Let bv_jx_F := ltac2:(inst_exact @BINVF.bv_jx_F).
  Let bv_ok_F := ltac2:(inst_exact @BINVF.bv_ok_F).
  Let bv_store_F := ltac2:(inst_exact @BINVF.bv_store_F).

  (* The run twin of the lane below this one. *)
  Let fin1_F := ltac2:(inst_exact @BINVF.fin1_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (BC0A.mb_hide T) in H.
  Ltac unhide H := unfold BC0A.mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* A store into the box at o + k. *)
  Ltac ost k :=
    lazymatch goal with
    | PI : BV_F ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let HS := fresh "HS" in
        pose proof (bv_ok_F fr j n w56 mc X J k 1%nat PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (bv_store_F _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity
                                       | unfold wa; f_equal;
                                         repeat match goal with
                                                | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
                                                    rewrite (unsigned_lit z) by lia
                                                end; lia])) as PI';
            clear PI;
            let mc' := fresh "mc" in set (mc' := write_to_mem mc AA bs) in *; clearbody mc'
        end
    end.

  (* The shadow fact for an instrumented access of w bytes at o + k (the box). *)
  Ltac sho k w :=
    lazymatch goal with
    | PI : BV_F ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx_F _ _ _ _ _ _ mc X J HKt Hpt Hot PI) as JXf;
        let H := fresh "SH" in
        pose proof (B.acl_shadow mc o 32 k w (o + k)
                      (proj1 (proj2 (proj2 (proj2 JXf)))) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear; lia) eq_refl) as H;
        clear JXf
    end.

  (* Branch conditions on literal-valued registers (as the plain proof's if_t/if_f). *)
  Ltac ulit := repeat match goal with
                      | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
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

  (* --- b = 0 (0x85c88): the grammar block --- *)

  (* The 64-bit neg of the running sum, as the check byte. *)
  Lemma le1_neg_F : forall s, le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)].
  Proof.
    intros s. hide_sec. rewrite rc_le1_lit. f_equal. apply Z_to_bv8_mod. change (2 ^ 8) with 256.
    rewrite Z.mod_mod by lia. rewrite unsigned_lit_wrap.
    change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
  Qed.

  (* 0x866f8: the check byte at o + 31 (the store check joins 0x864b4 from both arms) and the release.
     Regions: the box [o, o + 32) and its shadow cover, both section hypotheses (RO, ROs at o <> 0). *)
  Lemma stchk0_F : forall fr f spc j n w56 mc J X (a1w : word)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV_F fr j n w56 mc X J ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 -> a1w = Z_to_bv 64 (psum X 31) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 a1w x12 x13 x14 x15 x16 x17
                             x21 x22 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x866f8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J X a1w x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 PI EX Er E1.
    hide_sec.
    pose proof Ro as Ro'. pose proof (psum_range X 31) as PR.
    pose proof (RO Ho0) as RObox.
    pose proof (sh1_F o 32 (o + 31) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (ROs Ho0)) as RSh31.
    pose proof (bv_jx_F fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (_ & _ & _ & JAO & _).
    assert (LX : length X = 32%nat)
      by (pose proof PI as (_ & [[[L _] _] _] & _); exact L).
    assert (RXo31 : 0 <= o + 31 < 2 ^ 64)
      by (pose proof JAO as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    pose proof (B.acl_shadow mc o 32 31 1 (o + 31) JAO ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear; lia) eq_refl) as SH.
    destruct SH as (kk & RK & OK & KR).
    subst a1w. unfold RB, BINV.RB.
    step.
    step. rewrite ?(unsigned_lit (o + 31)) by lia. rewrite ?rc_shr3.
    steps_until_if. clear RK.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR; lia).
    destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbn [negb]; cbv iota.
    - step. ost 31. rewrite le1_neg_F in PI0.
      eapply (fin1_F fr f spc j n w56 _ (upd_bytes X (Z.to_nat 31) [bz (- psum X 31 mod 256)]) J);
        try eassumption.
      rewrite <- EX. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by lia.
      change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by lia.
      rewrite app_nil_r. reflexivity.
    - step. rewrite ?(unsigned_lit (o + 31)) by lia. rewrite rc_land7.
      step.
      pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl) as MB.
      rewrite (rc_lts_signed ((o + 31) mod 8) (bv_signed kk)) by (clear -MB KR; lia).
      replace ((o + 31) mod 8 <? bv_signed kk) with true
        by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]).
      cbv iota.
      step. ost 31. rewrite le1_neg_F in PI0.
      eapply (fin1_F fr f spc j n w56 _ (upd_bytes X (Z.to_nat 31) [bz (- psum X 31 mod 256)]) J);
        try eassumption.
      rewrite <- EX. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by lia.
      change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by lia.
      rewrite app_nil_r. reflexivity.
  Qed.

  (* 0x866c0: the 31-byte checksum loop of the b = 0 path.
     Regions: the box [o, o + 32) and its shadow cover, both section hypotheses (RO, ROs at o <> 0). *)
  Lemma osum0_F : forall k i fr f spc j n w56 mc J X (a0w a2w a3w : word)
      (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    (i + k = 31)%nat -> (0 < k)%nat -> a0w = Z_to_bv 64 (o + Z.of_nat i) -> a3w = a0w ->
    a2w = Z_to_bv 64 (Z.of_nat k) ->
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV_F fr j n w56 mc X J ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 a0w (Z_to_bv 64 (psum X i))
                             a2w a3w x14 x15 x16 x17
                             x21 x22 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x866c0) fc None mc (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i fr f spc j n w56 mc J X a0w a2w a3w x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        Hik Hk E0 E3 E2 HK Hp0 Ho0 PI EX Er; [lia|].
    hide_sec.
    pose proof Ro as Ro'.
    pose proof (RO Ho0) as RObox.
    pose proof (sh1_F o 32 (o + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear -Hik; lia)
                  (ROs Ho0)) as RShi.
    assert (LX : length X = 32%nat) by (pose proof PI as (_ & [[[L _] _] _] & _); exact L).
    pose proof (bv_jx_F fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (_ & _ & _ & JAO & _).
    assert (RXoi : 0 <= o + Z.of_nat i < 2 ^ 64)
      by (pose proof JAO as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe Hik; lia).
    pose proof (rd_byte rsegs mc o X i (rw1_F mc o 32 X (proj1 (proj2 PI))) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    pose proof (B.acl_shadow mc o 32 (Z.of_nat i) 1 (o + Z.of_nat i) JAO ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear; lia) eq_refl) as SH.
    subst a0w a3w a2w. unfold RB, BINV.RB.
    chk_core (o + Z.of_nat i) RXoi (Z_to_bv 5 15) SH pre_sr no_extra.
    step. step. step. step. rewrite psum_S_zxb. step. step.
    ulit.
    destruct k as [|k].
    - match goal with |- context [bv_eqb (Z_to_bv 64 ?z) (Z_to_bv 64 0)] =>
        rewrite (rc_eqb_lit z 0) by lia; replace (z =? 0) with true by (symmetry; apply Z.eqb_eq; lia) end.
      cbn [negb]. cbv iota.
      step.
      eapply (stchk0_F fr f spc j n w56 mc J X); try eassumption.
      replace (S i) with 31%nat by lia. reflexivity.
    - match goal with |- context [bv_eqb (Z_to_bv 64 ?z) (Z_to_bv 64 0)] =>
        rewrite (rc_eqb_lit z 0) by lia; replace (z =? 0) with false by (symmetry; apply Z.eqb_neq; lia) end.
      cbn [negb]. cbv iota.
      eapply (IH (S i)); try eassumption; first [lia | f_equal; lia | reflexivity].
  Qed.

End MainF.
