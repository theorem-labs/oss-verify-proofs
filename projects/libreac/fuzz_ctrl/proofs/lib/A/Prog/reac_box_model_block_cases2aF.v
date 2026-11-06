(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1417 of its 1432 lines of code are new or changed and 233 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases2.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF: cs4_F, cs5_F and a4_cl_mc_loc_F follow their scripts, with four new helper lemmas, two OfF bounds, three corollaries of the runs and five Lets; the script edits include `hide_sec.` and footprint steps, and a4_cl_mc_loc_F also takes RSr, RSsh and SSsh.  Image: fuzz_ctrl.asan (libreac v1.9.0), ELF
   sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd.  FACTS ed6b6b7b0ab.  Const cells
   checked against the v1.9.0 image bytes: none read (these three runs read only the row at p, the box at o, the
   name at rname row and the function's own window; every other value they use is an instruction immediate).

   Part a of the two-file twin of reac_box_model_block_cases2.v (a Theorem Labs lane's bmbF inventory, section 6 (a working note, not in this delivery)):
   cs4_F (_cases2.v:328), cs5_F (:497) and a4_cl_mc_loc_F (:1078).  The five b = 6 lemmas (a4_cs6_name,
   a4_cs6_rsum, a4_cs6_bsum, a4_cs6_tail, cs6) are part b, reac_box_model_block_cases2bF.v, which imports this
   file.

   rule 24: no function is proved here.  Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z):
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header (image root, ELF sha256, tool version, which compare) and goes to
      the auditor a Theorem Labs lane, who signs it against its proved run before it counts.
   5. A StepF "uncovered access" error means STOP: report it.  Do not widen the footprint to make it pass.

   The three statements are _cases2.v's with `evt rsegs Q0` replaced by `evtF rsegs RNG Q` (the fixed ret-post Q0
   is generalized to the section variable Q, so the S2 stretch can stop at the flag release at 0x864f4; where the
   original applies `epi` the re-run applies HKR), and with the data regions carried by Section MainF's footprint
   hypotheses (the nine of 3c9fcc93205 reac_box_model_blockF.v:147-159 plus the ten of the lead's decision
   (B) of 2026-10-28 23:0xZ).  a4_cl_mc_loc_F alone adds three lemma-level premises: its source [SS, SS + nn) is an
   arbitrary address no section hypothesis covers.

   __asan_memcpy is applied in its shared footprint form (asan_memcpy_cF.v, a Theorem Labs lane), with named arguments.
   No lemma here takes the stack-malloc contract: the jal at 0x85bb8 is the glue's allocator event, outside this
   stretch.  `Import YK11` of the Seg-file form is not used: this unit is the lib.Lib engine, as
   3c9fcc93205 reac_box_model_blockF.v is. *)
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
  reac_box_model_block_cases2.
(* the shared footprint forms of the two runtime helpers, and the footprint statements of this family *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* route (C): the audited narrow shadow region of this function (a Theorem Labs lane), as a STATEMENT leaf. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan sh_word_on asan_stack_malloc_c_on
  asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on reac_box_model_block_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF
  reac_box_model_block_binv2F.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* lib.Lib is doubled under lib/A/Bz/Lib: name its modules by their full logical path (the lead,
   2026-10-29 05:20Z). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module SRON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.
Module BF := reac_box_model_block_baseF.
Module BEPIF := reac_box_model_block_epiF.
Module BINVF := reac_box_model_block_binvF.
Module BINV2F := reac_box_model_block_binv2F.

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

(* The store hook of reac_box_model_block.v, re-issued for the evtF walk: it also transports rd_mono
   (3c9fcc93205 reac_box_model_blockF.v:46-56). *)
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

(* An address the walk builds from a register holds [bv_unsigned (Z_to_bv 64 e)], which StepF's syntactic
   matching does not relate to the [rng] premise of its region.  Normalize the wrap, then close the bounds
   from an rng hypothesis by lia alone.  Text of reac_box_model_block_cases0aF.v:120-132 (a Theorem Labs lane's S1
   measurement, 18:24Z: a hook that does division reasoning costs 78-417 s per chk_core, this one 1.8-4.8 s).
   Two things keep it cheap: it fires only on the wrapped shape, and it does no division reasoning -- the
   division argument of a shadow byte is made ONCE per lemma by sh1_F below. *)
Local Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, ?n) =>
      lazymatch a with
      | context [bv_unsigned (Z_to_bv 64 _)] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
              cbv [wa]; rewrite ?LMS.unsigned_lit_wrap; lia
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mb_accF.

(* The shadow-check tactics of reac_box_model_block_base.v:313-354 over evtF (an Ltac body binds the tactics in
   scope where it is written, so the evt forms of the proved file cannot serve here).  Text of
   reac_box_model_block_casesF.v:128-169. *)
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

(* An opaque wrapper: a hypothesis of type mb_hide T is invisible to lia. *)
Definition mb_hide (P : Prop) : Prop := P.

Section MainF.
  (* reac_box_model_block_cases2.v:54-91 verbatim, except: the three callee contracts in their footprint forms
     (asan_memcpy_cF.v, asan_memset_cF.v, build_dt1_single_c.v), and no stack-malloc contract at all. *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* route (C): the callees' _on contracts (a Theorem Labs lane carried a Theorem Labs lane's leaves into the worktree;
     asan_memcpy_cF_on.v:20, asan_memset_cF_on.v, build_dt1_single_c.v). *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* route (C) (bmbF-narrow-brief.md): NOT A.AsanRT.shadow_rw (universal shadow, false at the allocator
     state) but the audited region of this function, reac_box_model_block_c_on.v:38. *)
  Hypothesis SR0 : SRON.shadow_rw_on
    (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
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

  (* The footprint and the regions these runs read or write.  The nine of 3c9fcc93205
     reac_box_model_blockF.v:147-159 (the side stack in two pieces: the header [FS, fs_frame FS 0 0) and the
     class-0 area fp_w [0%nat] FS), then the ten data-region facts of the lead's decision (B). *)
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
  Hypothesis Rby : rng_bytes RNG.
  Hypothesis Rwsw : sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis RP : p <> 0 -> rng RNG p 296.
  Hypothesis RPs : p <> 0 -> sh_cover RNG p 296.
  Hypothesis RO : o <> 0 -> rng RNG o 32.
  Hypothesis ROs : o <> 0 -> sh_cover RNG o 32.
  Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> rng RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> sh_cover RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RJ13s : b = 2 -> sh_cover RNG JOIN_0013 32.
  Hypothesis RJ14s : b = 1 -> sh_cover RNG JOIN_0014 32.

  (* The continuation obligation of the release at 0x864f4 (lane EPI), in place of the fixed ret-post Q0. *)
  Let bmb_KR := ltac2:(inst_exact @BEPIF.bmb_KR).
  (* The post is indexed by the FK data of the stretch (the lead, 2026-10-29): the glue can discharge the
     epi obligation only for the frame cgif allocated, on the fake arm. *)
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The definitions of reac_box_model_block_base.v and reac_box_model_block_binv.v at this section's variables
     (decision (A): the originals' pure Definitions are reused, never redefined; same text as
     reac_box_model_block_binvF.v:155-163). *)
  Notation FK := (B.FK FS A).
  (* route (C): BV over the NARROWED shadow premise (a Theorem Labs lane's BV_F = BINV.BV with JX's `shadow_rw mc`
     replaced by `shadow_rw_on (reac_box_model_block_shadow_R ...) mc`); same binders. *)
  Notation BV := (BINVF.BV_F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS A row nb).
  Notation RB := (BINVF.RB_F sp gp tp p o off A).

  (* The pure lemmas of the earlier layers at this section's variables and hypotheses. *)
  Let HA1 := ltac2:(inst_exact @B.HA1).
  Let fk_facts := ltac2:(inst_exact @BF.fk_facts_F).
  Let rw1 := ltac2:(inst_exact @BINVF.rw1_F).
  Let djw := ltac2:(inst_exact @BINVF.djw_F).
  Let bv_jx := ltac2:(inst_exact @BINVF.bv_jx_F).
  Let bv_ok := ltac2:(inst_exact @BINVF.bv_ok_F).
  Let bv_lok := ltac2:(inst_exact @BINVF.bv_lok_F).
  Let bv_store := ltac2:(inst_exact @BINVF.bv_store_F).
  Let bv_lstore := ltac2:(inst_exact @BINVF.bv_lstore_F).
  Let bv_fok := ltac2:(inst_exact @BINVF.bv_fok_F).
  Let bv_sok := ltac2:(inst_exact @BINVF.bv_sok_F).
  Let bv_fstore := ltac2:(inst_exact @BINVF.bv_fstore_F).
  Let bv_sstore := ltac2:(inst_exact @BINVF.bv_sstore_F).
  Let call_facts := ltac2:(inst_exact @BINVF.call_facts_F).
  Let rw_upd2 := ltac2:(inst_exact @BINV2F.rw_upd2_F).
  Let app_loc := ltac2:(inst_exact @BINV2F.app_loc_F).

  (* The run lemmas of the earlier layers, in their _F form (the only cross-lane names this file uses). *)
  Let exit_r := ltac2:(inst_exact @BINVF.exit_r_F).
  Let fin1 := ltac2:(inst_exact @BINVF.fin1_F).
  Let cl_mc := ltac2:(inst_exact @BINV2F.cl_mc_F).
  Let cl_ms_loc := ltac2:(inst_exact @BINV2F.cl_ms_loc_F).
  Let cl_bd := ltac2:(inst_exact @BINV2F.cl_bd_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* The window's shadow cover covers the shadow span of any sub-range of the window: the destination of the
     memcpy of a4_cl_mc_loc_F is the locals at A + dd, the source of the cl_bd_F / cl_mc_F calls of cs4_F / cs5_F
     is the locals at A + 19, and the helper's own frame [sp - 2224, sp) is a sub-range of the window
     [sp - 4272, sp). *)
  Lemma sh_cover_win : forall a n, 0 < n -> bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K <= a -> a + n <= bv_unsigned sp ->
    sh_cover RNG a n.
  Proof.
    intros a n Hn Hlo Hhi. hide_sec.
    pose proof Rwsh as W. unfold sh_cover in W |- *.
    eapply rng_sub'; [exact W|].
    unfold shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K in *.
    Z.div_mod_to_equations. lia.
  Qed.

  (* An aligned shadow word span of a sub-range is inside the span of the range (route (C): the memcpy's
     destination, the locals at A + dd, is inside the window). *)
  Lemma sh_word_on_sub : forall pp nn0 qq kk aa, 0 < kk -> pp <= qq -> qq + kk <= pp + nn0 ->
    sh_word_on qq kk aa -> sh_word_on pp nn0 aa.
  Proof.
    intros pp nn0 qq kk aa Hk Hlo Hhi (Hne & Hb). hide_sec.
    unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
    split; [lia|]. Z.div_mod_to_equations. lia.
  Qed.

  Lemma sh_word_win : forall a n, 0 < n -> bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K <= a -> a + n <= bv_unsigned sp ->
    sh_word_rng RNG a n.
  Proof.
    intros a n Hn Hlo Hhi. hide_sec. right.
    pose proof (sh_cover_win a n Hn Hlo Hhi) as HC. unfold sh_cover in HC.
    unfold sh_al8_lo, sh_al8_hi. exact HC.
  Qed.


  (* One shadow BYTE of a covered range, in the bare rng form StepF's access solver matches cheaply.  The
     division argument is made ONCE here, not at every access of the run (cases0aF.v:354). *)
  Lemma sh1_F : forall a n x, 0 <= a -> 0 < n -> a <= x -> x < a + n -> sh_cover RNG a n ->
    rng RNG (x / 8 + ASAN_K) 1.
  Proof.
    intros a n x Ha Hn Hx1 Hx2 H. hide_sec.
    unfold sh_cover, shadow_addr, ASAN_K in H. unfold ASAN_K.
    eapply rng_sub'; [exact H|]. clear -Ha Hn Hx1 Hx2. Z.div_mod_to_equations. lia.
  Qed.


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


  (* --- stepping tactics for the body --- *)

  (* A store into the locals at A + k. *)
  Ltac lst k :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let HS := fresh "HS" in
        pose proof (bv_lok fr j n w56 mc X J k 1%nat PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (bv_lstore _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity | unfold wa; f_equal; lia])
                        : BV fr j n w56 (write_to_mem mc AA bs) X (upd_bytes J (Z.to_nat k) bs)) as PI';
            clear PI;
            let mc' := fresh "mc" in set (mc' := write_to_mem mc AA bs) in *; clearbody mc'
        end
    end.

  (* A store into the box at o + k. *)
  Ltac ost k :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let HS := fresh "HS" in
        pose proof (bv_ok fr j n w56 mc X J k 1%nat PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (bv_store _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity | unfold wa; f_equal; lia])
                        : BV fr j n w56 (write_to_mem mc AA bs) (upd_bytes X (Z.to_nat k) bs) J) as PI';
            clear PI;
            let mc' := fresh "mc" in set (mc' := write_to_mem mc AA bs) in *; clearbody mc'
        end
    end.

  (* A store into the ASan frame at fr + k. *)
  Ltac fst_ k :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let HS := fresh "HS" in
        pose proof (bv_fok _ _ _ _ _ _ mc X J k 1%nat HKt PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (bv_fstore _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity | unfold wa; f_equal; lia])) as PI';
            clear PI;
            let mc' := fresh "mc" in set (mc' := write_to_mem mc AA bs) in *; clearbody mc'
        end
    end.

  (* A store into the frame's shadow byte k. *)
  Ltac sst_ k :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let HS := fresh "HS" in
        pose proof (bv_sok _ _ _ _ _ _ mc X J k 1%nat HKt PI ltac:(lia) ltac:(lia)) as HS;
        step; clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
            let PI' := fresh "PI" in
            pose proof (bv_sstore _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity | unfold wa; f_equal; lia])) as PI';
            clear PI;
            let mc' := fresh "mc" in set (mc' := write_to_mem mc AA bs) in *; clearbody mc'
        end
    end.

  (* The shadow fact for an instrumented access of w bytes at p + jj (the row). *)
  Ltac shp jj w :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mc X J HKt Hpt Hot PI) as JXf;
        let H := fresh "SH" in
        pose proof (B.acl_shadow mc p 296 jj w (p + jj)
                      (proj1 (proj2 (proj2 (proj2 (proj2 JXf))))) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear; lia) eq_refl) as H;
        clear JXf
    end.


  (* b = 4 (0x85e20): the two zero bytes and the three 16-bit row fields at p + 268, 270, 272 big-endian into the
     locals at A + 19 .. A + 26, then build_dt1_single(o, 1536, A + 19, 8) and the join at 0x864bc. *)
  Lemma cs4_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 4 -> BV fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85e20) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    hide_sec.
    (* The footprint facts in the form StepF's access paths match: the window with its length as a numeral, the
       box and the row as bare rng facts (each access closes by one lia), and each accessed shadow BYTE by sh1_F below.
       The shadow covers stay FOLDED (no lia call and no hook meets their division); they
       are kept in the context so that the lemma uses the same Section hypotheses as before. *)
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    pose proof Rwsh as Rwsh'.
    pose proof (RP Hp0) as RPm.
    pose proof (RPs Hp0) as RPsm.
    pose proof (RO Ho0) as ROm.
    pose proof (ROs Ho0) as ROsm.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    (* the 56 local bytes as a bare rng fact, so each store into them closes by one lia (StepF's leftmost path) *)
    assert (RAl : rng RNG A 56)
      by (eapply rng_sub'; [exact Rwin|]; unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; lia).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    unfold APPMEM_END in Boe, Bpe.
    assert (Hp8 : p mod 8 = 0) by (hide_sec; destruct (HP Hp0) as (H1 & _); exact H1).
    assert (LJ : length J = 56%nat) by (destruct PI as (_ & _ & [[[LJ0 _] _] _] & _); exact LJ0).
    (* the accessed shadow BYTES in the bare rng form the cheap acc_hint matches (sh1_F; a Theorem Labs lane S1). *)
    pose proof (sh1_F p 296 (p + 268) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (RPs Hp0)) as SHBp268.
    rewrite <- Hoff in SHBp268.
    pose proof (sh1_F p 296 (p + 270) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (RPs Hp0)) as SHBp270.
    rewrite <- Hoff in SHBp270.
    pose proof (sh1_F p 296 (p + 272) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (RPs Hp0)) as SHBp272.
    rewrite <- Hoff in SHBp272.
    assert (RX1 : 0 <= p + 268 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX2 : 0 <= p + 270 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX3 : 0 <= p + 272 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RA19 : 0 <= A + 19 < 2 ^ 64) by (clear -HAlo HAhi HHM' Rsp; lia).
    (* the 56 local bytes, so that the reads back of what the stores wrote compute *)
    do 56 (destruct J as [|? J]; [cbn in LJ; discriminate | cbn in LJ]).
    destruct J as [|? J]; [|cbn in LJ; discriminate].
    unfold RB, reac_box_model_block_binvF.RB_F.
    (* 0x85e20, 0x85e24: the two zero bytes at A + 19, A + 20 *)
    lst 19. lst 20.
    (* 0x85e28: a0 = p + 268 *)
    step.
    (* 0x85e2c .. 0x85e38: the checked 2-byte load of the row field at p + 268 *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
        destruct JXf as (_ & _ & _ & _ & JAP1 & _);
        pose proof (B.acl_shadow mm p 296 268 2 (p + 268) JAP1 ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH1;
        clear JAP1
    end.
    rewrite <- Hoff in SH1.
    chk_core (p + 268) RX1 (Z_to_bv 5 12) SH1 pre_sr add1.
    (* 0x85e3c: lh a1, 268(s4) *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let HRw := fresh "HRw" in
        assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
        pose proof (rs_rd2 rsegs mm p row 268 HRw ltac:(clear -Lrow; lia)) as RD1;
        change (Z.of_nat 268) with 268 in RD1; clear HRw
    end.
    step. clear RD1.
    (* 0x85e40: a0 = p + 270; 0x85e44: a2 = the high byte *)
    step. step.
    (* 0x85e48, 0x85e4c: the two bytes at A + 21, A + 22 *)
    lst 21. lst 22.
    (* 0x85e50 .. 0x85e5c: the checked 2-byte load of the row field at p + 270 *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
        destruct JXf as (_ & _ & _ & _ & JAP2 & _);
        pose proof (B.acl_shadow mm p 296 270 2 (p + 270) JAP2 ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH2;
        clear JAP2
    end.
    rewrite <- Hoff in SH2.
    chk_core (p + 270) RX2 (Z_to_bv 5 12) SH2 pre_sr add1.
    (* 0x85e60: lh a1, 270(s4) *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let HRw := fresh "HRw" in
        assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
        pose proof (rs_rd2 rsegs mm p row 270 HRw ltac:(clear -Lrow; lia)) as RD2;
        change (Z.of_nat 270) with 270 in RD2; clear HRw
    end.
    step. clear RD2.
    (* 0x85e64: a0 = p + 272; 0x85e68: a2 = (p + 272) / 8, the shadow address used at 0x85e78 *)
    step. step.
    rewrite (unsigned_lit (p + 272)) by (clear -RX3; lia). rewrite rc_shr3.
    (* 0x85e6c: a3 = the high byte; 0x85e70, 0x85e74: the two bytes at A + 23, A + 24 *)
    step. lst 23. lst 24.
    (* 0x85e78 .. 0x85e80: the checked 2-byte load of the row field at p + 272 *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
        destruct JXf as (_ & _ & _ & _ & JAP3 & _);
        pose proof (B.acl_shadow mm p 296 272 2 (p + 272) JAP3 ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH3;
        clear JAP3
    end.
    rewrite <- Hoff in SH3.
    chk_core (p + 272) RX3 (Z_to_bv 5 12) SH3 pre_no add1.
    (* 0x85e84: lh a0, 0(a0) *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let HRw := fresh "HRw" in
        assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
        pose proof (rs_rd2 rsegs mm p row 272 HRw ltac:(clear -Lrow; lia)) as RD3;
        change (Z.of_nat 272) with 272 in RD3; clear HRw
    end.
    step. clear RD3.
    (* 0x85e88: a1 = the high byte; 0x85e8c, 0x85e90: the two bytes at A + 25, A + 26 *)
    step. lst 25. lst 26.
    (* 0x85e94 .. 0x85ea4: the arguments and the call build_dt1_single (o, 1536, A + 19, 8) *)
    do 5 step.
    (* the eight bytes at A + 19 read back as the rvb row *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
        let HL := fresh "HL" in
        assert (HL : rw_cells rsegs mm A [CB 56 Jf]) by (destruct PI0 as (_ & _ & H & _); exact H);
        pose proof (rs_cell0_sub rsegs mm A 56 Jf [] 19 8 HL ltac:(lia)) as HD;
        change (Z.of_nat 19) with 19 in HD; clear HL;
        cbv [upd_bytes firstn skipn app length le1 Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in HD
    end.
    apply (bytes_at_ext rsegs _ _ _ (rvb row)) in HD;
      [| unfold rvb; rewrite !rs_hi16, !rs_lo16 by apply rs_rw16_range; reflexivity].
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
        eapply (cl_bd fr f spc j n w56 mm Jf 0x85ea8 8 (A + 19) 1536 (rvb row))
    end.
    - exact HK.
    - exact Hp0.
    - exact Ho0.
    - eassumption.
    - apply ret_pc_even; [lia | reflexivity].
    - lia.
    - lia.
    - reflexivity.
    - apply unsigned_lit. clear -Ro'; lia.
    - apply unsigned_lit. lia.
    - apply unsigned_lit. clear -RA19; lia.
    - apply unsigned_lit. lia.
    - exact HD.
    - match goal with
      | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
          let JXf := fresh "JXf" in
          pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
          destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
          apply (B.acl_addr_sub mm A 56); [exact JAL | lia | lia | lia]
      end.
    - match goal with
      | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
          let JXf := fresh "JXf" in
          pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
          destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
          replace (A + 19 + 7) with (A + 26) by lia; exact (B.acl_app_in mm A 56 26 JAL ltac:(lia))
      end.
    - match goal with
      | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
          let JXf := fresh "JXf" in
          pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
          destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
          replace (A + 19 + Z.of_nat 8) with (A + 27) by lia; exact (B.acl_app_in mm A 56 27 JAL ltac:(lia))
      end.
    - clear -Dow HAlo HAhi; lia.
    - left. lia.
    (* cl_bd_F's two footprint premises for the copy source: the eight local bytes at A + 19, in the window *)
    - eapply rng_sub'; [exact Rwin|]. unfold REAC_BOX_MODEL_BLOCK_K. clear -HAlo HAhi HHM' Rsp; cbn [Z.of_nat]; lia.
    - apply sh_cover_win; unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; cbn [Z.of_nat]; lia.
    - (* cl_bd_F's shadow membership for the source: the locals are inside the window (R's first disjunct) *)
      intros aa Haa. left. revert Haa. apply sh_word_on_sub;
        unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; cbn [Z.of_nat]; lia.
    (* 0x85ea8: j 0x864bc, the join with the result 1 *)
    - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mc' PI'.
      unfold RB, reac_box_model_block_binvF.RB_F. step.
      eapply (fin1 fr f spc j n w56 mc' (dt1s 1536 (rvb row)) _); try eassumption.
      + rewrite Eb. reflexivity.
      + rewrite Eb. reflexivity.
  Qed.


  (* b = 5 (0x85f04), IDENT_FIRST: the checked has field at p + 56 (zero: s5 = 0, release at 0x864c0); memset of the
     16 name bytes at A + 19; the checked rname at p + 280 and the checked name copy loop (a4_nl5); the 21 checked
     header bytes at o .. o + 20; memcpy of the first 10 name bytes to o + 21; the checked outer checksum loop, the
     checked check byte at o + 31 and the join 0x864bc (a4_ol5). *)
  Lemma cs5_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 5 -> BV fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85f04) fc None mc (seg_rom rsegs)).
  Proof.
    hide_sec.
    (* 0x8627c .. 0x864bc: the outer checksum loop, the checked check byte at o + 31, the join (fin1) *)
    assert (a4_ol5 : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (X J : list byte)
        (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
      FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
      withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
      BV fr j n w56 mc X J ->
      evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                           (Z_to_bv 64 (o + Z.of_nat i)) (Z_to_bv 64 (psum X i))
                           (Z_to_bv 64 (Z.of_nat kk)) (Z_to_bv 64 (o + Z.of_nat i)) x14 x15 x16 x17
                           x21 x22 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x8627c) fc None mc (seg_rom rsegs))).
    { hide_sec.
      (* the byte that neg a1, a1; sb a1, 0(a0) stores *)
      assert (NEG : forall s, le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)]).
      { intros s. rewrite rc_le1_lit. f_equal. apply Z_to_bv8_mod. change (2^8) with 256.
        rewrite Z.mod_mod by lia. rewrite unsigned_lit_wrap.
        change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
      induction kk as [|kk IH];
        intros i fr f spc j n w56 mc X J x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
          HK Hp0 Ho0 Hik Hk LX ES Er PI; [lia|].
      (* The footprint facts in the form StepF's access hook matches (`H : rng RNG ?lo ?len`, closed by
         Z.div_mod_to_equations + lia): the window with its length as a numeral, the box and the row, and
         their shadow covers at the walk's own shadow offset off (a Theorem Labs lane, 2026-10-29). *)
      pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
      pose proof Rwsh as Rwsh'. unfold sh_cover, shadow_addr, REAC_BOX_MODEL_BLOCK_K in Rwsh'. rewrite <- Hoff in Rwsh'.
      pose proof (RO Ho0) as ROm.
      pose proof (ROs Ho0) as ROsm. unfold sh_cover, shadow_addr in ROsm. rewrite <- Hoff in ROsm.
      pose proof Ro as Ro'.
      pose proof (sh1_F o 32 (o + Z.of_nat i) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Hik; lia) (ROs Ho0)) as SHBoi.
      rewrite <- Hoff in SHBoi.
      pose proof (sh1_F o 32 (o + 31) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHBo31.
      rewrite <- Hoff in SHBo31.
      destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (_ & _ & _ & _ & _ & _ & _ & Boe & _).
      unfold APPMEM_END in Boe.
      assert (RX : 0 <= o + Z.of_nat i < 2 ^ 64) by (clear -Ro' Boe Hik; lia).
      pose proof (rd_byte rsegs mc o X i (rw1 _ _ _ _ (proj1 (proj2 PI))) ltac:(lia)) as RD.
      pose proof (psum_range X i) as PR.
      pose proof (bv_jx _ _ _ _ _ _ mc _ _ HK Hp0 Ho0 PI) as JXf.
      destruct JXf as (_ & _ & _ & JAO & _).
      pose proof (B.acl_shadow mc o 32 (Z.of_nat i) 1 (o + Z.of_nat i) JAO ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(pose proof (Z.mod_pos_bound (o + Z.of_nat i) 8 eq_refl); lia) eq_refl) as SH.
      clear JAO.
      rewrite <- Hoff in SH.
      unfold RB, reac_box_model_block_binvF.RB_F.
      (* 0x8627c .. 0x86288, 0x862a8, 0x862ac: the shadow check of the byte at o + i *)
      chk_core (o + Z.of_nat i) RX (Z_to_bv 5 15) SH pre_sr no_extra.
      (* 0x8628c .. 0x86298: the byte, the count, the address and the sum *)
      step. step. step. step.
      rewrite psum_S_zxb.
      (* 0x8629c, 0x862a0: bnez a2, 0x8627c *)
      step. step.
      rewrite (rc_eqb_lit (Z.of_nat (S kk) + -1) 0) by lia.
      replace (Z.of_nat (S kk) + -1) with (Z.of_nat kk) by lia.
      replace (o + Z.of_nat i + 1) with (o + Z.of_nat (S i)) by lia.
      destruct kk as [|kk].
      2: {
        replace (Z.of_nat (S kk) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
        eapply (IH (S i)); first [eassumption | lia]. }
      (* the 31 bytes are summed: 0x862a4, j 0x86480 *)
      change (Z.of_nat 0 =? 0) with true. cbn [negb].
      replace (S i) with 31%nat by lia.
      step.
      (* 0x86480 .. 0x86498: the shadow check of the store at o + 31, in its beqz form (walked by hand: chk_core fits
         only the bnez form) *)
      assert (RX31 : 0 <= o + 31 < 2 ^ 64) by (clear -Ro' Boe; lia).
      pose proof (bv_jx _ _ _ _ _ _ mc _ _ HK Hp0 Ho0 PI) as JXf.
      destruct JXf as (_ & _ & _ & JAO & _).
      pose proof (B.acl_shadow mc o 32 31 1 (o + 31) JAO ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl); lia) eq_refl) as SH31.
      clear JAO.
      rewrite <- Hoff in SH31.
      step.
      destruct SH31 as (k31 & RK31 & OK31 & KR31).
      pre_sr (o + 31) RX31. steps_until_if. clear RK31.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k31)) by (clear -KR31; lia).
      (* the two paths (shadow byte 0, or (o + 31) mod 8 below it) join at 0x864b4 with a3 apart *)
      lazymatch goal with
      | |- evtF ?segs ?RNGq ?Q (MS ?R ?F (if _ then ?B else _) ?fc ?rv ?mm ?ro) =>
          enough (G : forall rr : word, evtF segs RNGq Q (MS (bvmap_set (Z_to_bv 5 13) rr R) F B fc rv mm ro));
          [ destruct (Z.eqb_spec (bv_signed k31) 0) as [K0|K0]; cbn [negb];
            [ bjoin G (Z_to_bv 5 13)
            | step; rewrite ?(unsigned_lit (o + 31)) by (clear -RX31; lia); rewrite rc_land7;
              step;
              let MB := fresh "MB" in pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl) as MB;
              rewrite (rc_lts_signed ((o + 31) mod 8) (bv_signed k31)) by (clear -MB KR31; lia);
              replace ((o + 31) mod 8 <? bv_signed k31) with true
                by (symmetry; apply Z.ltb_lt; destruct OK31 as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]);
              cbn [negb]; clear MB; bjoin G (Z_to_bv 5 13) ]
          | intros ?; simp_regs; clear OK31 KR31 ]
      end.
      (* 0x864b4, 0x864b8: neg a1, a1; sb a1, 0(a0): the check byte at o + 31 *)
      step. ost 31.
      (* 0x864bc: li s5, 1 and the release; the box is now withchk (firstn 31 X) *)
      match goal with H : BV _ _ _ _ _ _ _ |- _ => rewrite NEG in H end.
      match goal with
      | H : BV _ _ _ _ ?mm ?Xn _ |- _ =>
          apply (fin1 fr f spc j n w56 mm Xn J); [exact HK | exact Hp0 | exact Ho0 | exact H | | exact Er]
      end.
      rewrite <- ES. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by lia.
      change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by lia.
      rewrite app_nil_r. reflexivity. }
    (* 0x85f58 .. 0x85f90: the name copy loop, each byte with its shadow check, to the join at 0x86034 *)
    assert (a4_nl5 : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
        (J0 Y J2 : list byte)
        (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
      FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 5 -> has row <> 0 -> rname row <> 0 ->
      (i + kk = 16)%nat -> (0 < kk)%nat ->
      (forall t, (t < i)%nat -> bv_unsigned (nth t nb (Z_to_bv 8 0)) <> 0) ->
      length J0 = 19%nat -> length J2 = 21%nat ->
      Y = firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i) ->
      BV fr j n w56 mc (zeros 32) (J0 ++ Y ++ J2) ->
      (forall (mc' : word -> option byte) (y10 y11 y12 y13 y14 y15 : word),
         BV fr j n w56 mc' (zeros 32) (J0 ++ nmf nb ++ J2) ->
         evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 y10 y11 y12 y13 y14 y15 x16 x17
                              x21 x22 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x86034) fc None mc' (seg_rom rsegs))) ->
      evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                           (Z_to_bv 64 (rname row + Z.of_nat i)) (Z_to_bv 64 (rname row + Z.of_nat i))
                           (Z_to_bv 64 (Z.of_nat kk)) (Z_to_bv 64 (A + 19 + Z.of_nat i)) x14 x15 x16 x17
                           x21 x22 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x85f58) fc None mc (seg_rom rsegs))).
    { (* plain.v's mb_upd_app, mb_upd_pre and mb_upd_mid *)
      assert (qUAPP : forall (qb qd qc : list byte) qk, (qk + length qc <= length qb)%nat ->
        upd_bytes (qb ++ qd) qk qc = upd_bytes qb qk qc ++ qd).
      { clear. intros qb qd qc qk qH. unfold upd_bytes. rewrite firstn_app, skipn_app.
        replace (qk - length qb)%nat with 0%nat by lia. replace (qk + length qc - length qb)%nat with 0%nat by lia.
        rewrite firstn_O, skipn_O, app_nil_r, <- !app_assoc. reflexivity. }
      assert (qUPRE : forall (qa qb qc : list byte) qk, (qk + length qc <= length qb)%nat ->
        upd_bytes (qa ++ qb) (length qa + qk) qc = qa ++ upd_bytes qb qk qc).
      { clear. intros qa qb qc qk qH. unfold upd_bytes. rewrite firstn_app, skipn_app.
        replace (length qa + qk - length qa)%nat with qk by lia.
        replace (length qa + qk + length qc - length qa)%nat with (qk + length qc)%nat by lia.
        rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite <- !app_assoc. reflexivity. }
      assert (qUMID : forall (qa qb qd qc : list byte) qn qk, length qa = qn -> (qk + length qc <= length qb)%nat ->
        upd_bytes (qa ++ qb ++ qd) (qn + qk) qc = qa ++ upd_bytes qb qk qc ++ qd).
      { intros qa qb qd qc qn qk <- qH. rewrite qUPRE by (rewrite length_app; clear -qH; lia).
        rewrite qUAPP by exact qH. reflexivity. }
      clear qUPRE qUAPP.
      assert (qOKN : p <> 0 -> b = 5 -> has row <> 0 -> rname row <> 0 -> name_ok nb).
      { intros qHp0 qEb qH1 qH2. destruct (HN qHp0 (or_introl qEb) qH1 qH2) as (qOK & _). exact qOK. }
      hide_sec.
      intros qkk. induction qkk as [|qkk qIH];
        intros qi qfr qf qspc qj qn qw56 qmc qJ0 qY qJ2 qx1 qx5 qx6 qx7 qx14 qx15 qx16 qx17 qx21 qx22 qx26 qx27
          qx28 qx29 qx30 qx31 qHK qHp0 qHo0 qEb qH1 qH2 qHik qHk qHnz qLJ0 qLJ2 qEY qPI qK; [clear -qHk; lia|].
      subst qY.
      assert (qB56 : b = 5 \/ b = 6) by (left; exact qEb).
      pose proof (qOKN qHp0 qEb qH1 qH2) as qOK.
      (* The footprint facts in the form StepF's access paths match: the window with its length as a numeral, the
         box and the row as bare rng facts (each access closes by one lia), and each accessed shadow BYTE by sh1_F below.
         The shadow covers stay FOLDED (no lia call and no hook meets their division); they
         are kept in the context so that the lemma uses the same Section hypotheses as before. *)
      pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
      pose proof Rwsh as Rwsh'.
      pose proof (RN qHp0 qB56 qH1 qH2) as RNm.
      pose proof (RNs qHp0 qB56 qH1 qH2) as RNsm.
      pose proof (RP qHp0) as RPm.
      pose proof (RPs qHp0) as RPsm.
      pose proof (name_ok_lt nb qi qOK ltac:(clear -qHik; lia) qHnz) as qHi.
      assert (qHNB : bytes_at rsegs qmc (rname row) nb)
        by (destruct qPI as (_ & _ & _ & _ & qHn); exact (qHn qB56 qH1 qH2)).
      pose proof (bytes_at_bound _ _ _ _ qHNB) as qBN.
      pose proof (rd_byte rsegs qmc (rname row) nb qi qHNB qHi) as qRD.
      clear qHNB.
      assert (qRX : 0 <= rname row + Z.of_nat qi < 2 ^ 64) by (clear -qBN qHi; lia).
      (* the accessed name shadow BYTE in the bare rng form the cheap acc_hint matches (sh1_F). *)
      pose proof (sh1_F (rname row) (Z.of_nat (length nb)) (rname row + Z.of_nat qi)
                    ltac:(clear -qBN qHi; lia) ltac:(clear -qHi; lia) ltac:(clear; lia) ltac:(clear -qHi; lia)
                    (RNs qHp0 qB56 qH1 qH2)) as SHBn.
      rewrite <- Hoff in SHBn.
      (* 0x85f58 .. 0x85f90: the checked 1-byte access at a0 = rname row + i *)
      pose proof (bv_jx _ _ _ _ _ _ qmc _ _ qHK qHp0 qHo0 qPI) as qJX.
      destruct qJX as (_ & _ & _ & _ & _ & _ & qJAN & _).
      pose proof (qJAN qB56 qH1 qH2) as qJAN1. clear qJAN.
      pose proof (B.acl_shadow qmc (rname row) (Z.of_nat (length nb)) (Z.of_nat qi) 1 (rname row + Z.of_nat qi)
                    qJAN1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -qHi; lia)
                    ltac:(clear; Z.div_mod_to_equations; lia) eq_refl) as qSH.
      clear qJAN1.
      rewrite <- Hoff in qSH.
      unfold RB, reac_box_model_block_binvF.RB_F.
      chk_core (rname row + Z.of_nat qi) qRX (Z_to_bv 5 15) qSH pre_sr no_extra.
      (* 0x85f68: lbu a4, 0(a1); 0x85f6c: beqz a4, 0x86034 *)
      step. clear qRD. step.
      rewrite rc_zxb_eqb0.
      destruct (Z.eqb_spec (bv_unsigned (nth qi nb (Z_to_bv 8 0))) 0) as [qC0|qCNZ]; cbv iota.
      - (* the zero byte: the join with nmf nb *)
        apply qK. rewrite (nmf_stop nb qi qHi ltac:(clear -qHik; lia) qHnz qC0). exact qPI.
      - (* 0x85f70: sb a4, 0(a3) *)
        lst (19 + Z.of_nat qi).
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            match goal with qP : BV _ _ _ _ mm _ _ |- _ => rename qP into qPI1 end
        end.
        rewrite le1_zxb in qPI1.
        replace (Z.to_nat (19 + Z.of_nat qi)) with (19 + qi)%nat in qPI1 by (clear; lia).
        rewrite (qUMID qJ0 _ qJ2 _ 19%nat qi qLJ0) in qPI1.
        2:{ rewrite length_app, length_firstn, repeat_length. cbn [length]. clear -qHi qHik. lia. }
        rewrite upd_prefix in qPI1 by (clear -qHi qHik; lia).
        (* 0x85f74 .. 0x85f80: a2 - 1, a3 + 1, a0 + 1, a1 + 1; 0x85f84: bnez a2, 0x85f58 *)
        step. step. step. step. step.
        rewrite (rc_eqb_lit (Z.of_nat (S qkk) + -1) 0) by (clear -qHik; lia).
        destruct qkk as [|qkk].
        + (* the 16th byte: 0x85f88, j 0x86034 *)
          replace (Z.of_nat (S 0) + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; clear; lia).
          cbn [negb]. cbv iota.
          step.
          assert (qL16 : length nb = 16%nat) by (destruct qOK as (qOKl & _ & _); clear -qOKl qHi qHik; lia).
          replace (S qi) with 16%nat in qPI1 by (clear -qHik; lia).
          rewrite <- (nmf_full nb qL16) in qPI1.
          2:{ intros qt qHt. destruct (Nat.eq_dec qt qi) as [->|qNe];
              [exact qCNZ | apply qHnz; clear -qHt qNe qHik; lia]. }
          apply qK. exact qPI1.
        + (* the next byte: back to 0x85f58 *)
          replace (Z.of_nat (S (S qkk)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; clear; lia).
          cbn [negb]. cbv iota.
          replace (Z.of_nat (S (S qkk)) + -1) with (Z.of_nat (S qkk)) by (clear; lia).
          replace (rname row + Z.of_nat qi + 1) with (rname row + Z.of_nat (S qi)) by (clear; lia).
          replace (A + 19 + Z.of_nat qi + 1) with (A + 19 + Z.of_nat (S qi)) by (clear; lia).
          eapply (qIH (S qi) qfr qf qspc qj qn qw56 _ qJ0 (firstn (S qi) nb ++ repeat (Z_to_bv 8 0) (16 - S qi))
                    qJ2);
            [exact qHK | exact qHp0 | exact qHo0 | exact qEb | exact qH1 | exact qH2 | clear -qHik; lia
            | clear; lia | | exact qLJ0 | exact qLJ2 | reflexivity | exact qPI1 | exact qK].
          intros qt qHt. destruct (Nat.eq_dec qt qi) as [->|qNe]; [exact qCNZ | apply qHnz; clear -qHt qNe; lia]. }
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    hide_sec.
    (* The footprint facts in the form StepF's access paths match: the window with its length as a numeral, the
       box and the row as bare rng facts (each access closes by one lia), and each accessed shadow BYTE by sh1_F below.
       The shadow covers stay FOLDED (no lia call and no hook meets their division); they
       are kept in the context so that the lemma uses the same Section hypotheses as before. *)
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    pose proof Rwsh as Rwsh'.
    pose proof (RP Hp0) as RPm.
    pose proof (RPs Hp0) as RPsm.
    pose proof (RO Ho0) as ROm.
    pose proof (ROs Ho0) as ROsm.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    unfold APPMEM_END in Boe, Bpe.
    assert (B56 : b = 5 \/ b = 6) by (left; exact Eb).
    assert (Hp8 : p mod 8 = 0) by (hide_sec; destruct (HP Hp0) as (H1 & _); exact H1).
    assert (LJ : length J = 56%nat) by (destruct PI as (_ & _ & [[[LJ0 _] _] _] & _); exact LJ0).
    (* the accessed shadow BYTES in the bare rng form the cheap acc_hint matches (sh1_F; a Theorem Labs lane S1). *)
    pose proof (sh1_F p 296 (p + 56) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (RPs Hp0)) as SHBp56.
    rewrite <- Hoff in SHBp56.
    pose proof (sh1_F p 296 (p + 280) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (RPs Hp0)) as SHBp280.
    rewrite <- Hoff in SHBp280.
    assert (RX56 : 0 <= p + 56 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX280 : 0 <= p + 280 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RA19 : 0 <= A + 19 < 2 ^ 64) by (clear -HAlo HAhi HHM' Rsp; lia).
    (* RO0, not RO: RO is the section's guarded `o <> 0 -> rng RNG o 32` (a Theorem Labs lane S1, 18:11Z). *)
    assert (RO0 : 0 <= o < 2 ^ 64) by (clear -Ro'; lia).
    assert (RXo1 : 0 <= o + 1 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo2 : 0 <= o + 2 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo3 : 0 <= o + 3 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo4 : 0 <= o + 4 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo5 : 0 <= o + 5 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo6 : 0 <= o + 6 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo7 : 0 <= o + 7 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo8 : 0 <= o + 8 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo9 : 0 <= o + 9 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo10 : 0 <= o + 10 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo11 : 0 <= o + 11 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo12 : 0 <= o + 12 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo13 : 0 <= o + 13 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo14 : 0 <= o + 14 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo15 : 0 <= o + 15 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo16 : 0 <= o + 16 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo17 : 0 <= o + 17 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo18 : 0 <= o + 18 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo19 : 0 <= o + 19 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo20 : 0 <= o + 20 < 2 ^ 64) by (clear -Ro' Boe; lia).
    (* the shadow byte of a one-byte access at o + t, at any memory of the body *)
    assert (SHO : forall (mm : word -> option byte) (X0 J0 : list byte) (t : Z), 0 <= t < 32 ->
              BV fr j n w56 mm X0 J0 ->
              exists k : byte, ov_read_bytes rsegs mm (wa ((o + t) / 8 + off)) 1 = Some [k]
                /\ (bv_signed k = 0 \/ (o + t) mod 8 + (1 - 1) < bv_signed k) /\ -128 <= bv_signed k < 128).
    { intros mm X0 J0 t Ht PI0.
      pose proof (bv_jx fr f spc j n w56 mm X0 J0 HK Hp0 Ho0 PI0) as (_ & _ & _ & JAOx & _).
      rewrite Hoff.
      exact (B.acl_shadow mm o 32 t 1 (o + t) JAOx ltac:(clear -Ht; lia) ltac:(clear; lia) ltac:(clear -Ht; lia)
               ltac:(clear; Z.div_mod_to_equations; lia) eq_refl). }
    (* sx32 of a 32-bit value is 0 exactly when the value is 0 *)
    assert (SX0 : forall w, 0 <= w < 2 ^ 32 -> bv_eqb (sx32 (Z_to_bv 64 w)) (Z_to_bv 64 0) = (w =? 0)).
    { intros w Hw. destruct (Z.eqb_spec w 0) as [->|N]; [reflexivity|].
      unfold bv_eqb, sx32. apply Z.eqb_neq. rewrite (unsigned_lit w) by (clear -Hw; lia).
      rewrite unsigned_lit_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
      unfold bv_wrap. change (bv_modulus 32) with 4294967296. clear -Hw N. Z.div_mod_to_equations. lia. }
    unfold RB, reac_box_model_block_binvF.RB_F.
    (* 0x85f04: a0 = p + 56 *)
    step.
    (* 0x85f08 .. 0x85f14: the checked 4-byte load of the has field *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
        destruct JXf as (_ & _ & _ & _ & JAP1 & _);
        pose proof (B.acl_shadow mm p 296 56 4 (p + 56) JAP1 ltac:(clear; lia) ltac:(clear; lia)
                      ltac:(clear; lia) ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH1;
        clear JAP1
    end.
    rewrite <- Hoff in SH1.
    chk_core (p + 56) RX56 (Z_to_bv 5 12) SH1 pre_sr add1.
    (* 0x85f18: lw a0, 0(a0) *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let HRw := fresh "HRw" in
        assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
        pose proof (rs_rd4 rsegs mm p row 56 HRw ltac:(clear -Lrow; lia)) as RD56;
        change (Z.of_nat 56) with 56 in RD56; clear HRw
    end.
    step. clear RD56. step.
    (* 0x85f1c: beqz a0, 0x8602c — the row emits no identity record *)
    rewrite SX0 by (pose proof (rs_rw32_range row 56); clear -H; lia).
    change (rw32 row 56) with (has row).
    destruct (Z.eqb_spec (has row) 0) as [H0|H0]; cbv iota.
    - (* 0x8602c: s5 = 0, then the release at 0x864c0 *)
      step. step.
      match goal with
      | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
          eapply (exit_r fr f spc j n w56 mm (zeros 32) Jf 0)
      end.
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + eassumption.
      + rewrite Eb. change (synth row 5 nb) with (if has row =? 0 then zeros 32 else idf (nmr row nb)).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
      + rewrite Eb. change (rc row 5) with (if has row =? 0 then 0 else 1).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
    - (* 0x85f20 .. 0x85f2c: __asan_memset(A + 19, 0, 16) *)
      do 4 step.
      match goal with
      | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
          eapply (cl_ms_loc fr f spc j n w56 mm (zeros 32) Jf 0x85f30 19 16 0)
      end.
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + eassumption.
      + apply ret_pc_even; [clear; lia | reflexivity].
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + apply unsigned_lit. clear -RA19; cbn [Z.of_nat]; lia.
      + apply unsigned_lit. clear; lia.
      + apply unsigned_lit. clear; lia.
      + intros u0 u1 u2 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 mc1 PI1.
        assert (PI1b : BV fr j n w56 mc1 (zeros 32) (upd_bytes J 19 (repeat (Z_to_bv 8 0) 16))) by exact PI1.
        clear PI1. rename PI1b into PI1.
        set (JA := firstn 19 J) in *. set (JB := skipn 35 J) in *.
        assert (LJA : length JA = 19%nat) by (unfold JA; rewrite length_firstn; clear -LJ; lia).
        assert (LJB : length JB = 21%nat) by (unfold JB; rewrite length_skipn; clear -LJ; lia).
        assert (EJ : upd_bytes J 19 (repeat (Z_to_bv 8 0) 16) = JA ++ repeat (Z_to_bv 8 0) 16 ++ JB)
          by (unfold upd_bytes, JA, JB; rewrite repeat_length; reflexivity).
        rewrite EJ in PI1. clear EJ.
        assert (WIN : forall (P NM R : list byte) (nn : nat), length P = 19%nat -> (nn <= length NM)%nat ->
                  firstn nn (skipn 19 (P ++ NM ++ R)) = firstn nn NM).
        { intros P NM R nn LP H. rewrite skipn_app, skipn_all2 by (clear -LP; lia).
          replace (19 - length P)%nat with 0%nat by (clear -LP; lia).
          rewrite skipn_O, app_nil_l, firstn_app.
          replace (nn - length NM)%nat with 0%nat by (clear -H; lia).
          rewrite firstn_O, app_nil_r. reflexivity. }
        pose proof (rs_nmr_len row nb) as LNM.
        (* 0x85f30: a0 = p + 280 *)
        unfold RB, reac_box_model_block_binvF.RB_F. step.
        (* 0x85f34 .. 0x85f40: the checked 8-byte load of the rname field; its shadow byte is 0 *)
        match goal with
        | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
            let JXf := fresh "JXf" in
            pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
            destruct JXf as (_ & _ & _ & _ & JAP2 & _);
            pose proof (rt_shadow_rd mm p 296 [] JAP2 (fun _ _ => I)) as HSR2;
            pose proof (rt_addressable mm p 296 JAP2) as HAD2;
            pose proof (rt_rt3 mm p 296 JAP2) as HR32;
            destruct (asan_shadow_read_at rsegs mm ASAN_K p 296 [] 280 ((p + 280) / 8 + ASAN_K) HSR2
                        ltac:(clear; lia) eq_refl) as (kk8 & RK8 & BK8);
            pose proof (asan_check_8 rsegs mm ASAN_K p 296 280 kk8 HAD2 HR32 ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear -Hp8; Z.div_mod_to_equations; lia) BK8) as K80;
            clear JAP2 HSR2 HAD2 HR32 BK8
        end.
        rewrite <- Hoff in RK8.
        step. rewrite (unsigned_lit (p + 280)) by (clear -RX280; lia). rewrite rc_shr3.
        step. step. step.
        rewrite rc_zxb_eqb0. rewrite (rc_signed0_unsigned0 kk8 K80). cbn [Z.eqb negb]. cbv iota.
        clear RK8 K80.
        (* 0x85f44: ld a1, 0(a0) *)
        match goal with
        | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
            let HRw := fresh "HRw" in
            assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
            pose proof (rs_rd8 rsegs mm p row 280 HRw ltac:(clear -Lrow; lia)) as RD280;
            change (Z.of_nat 280) with 280 in RD280; change (rw64 row 280) with (rname row) in RD280; clear HRw
        end.
        step. clear RD280. step.
        (* 0x85f48: beqz a1, 0x86034 — the row has no name *)
        rewrite rc_eqb_lit by (first [clear; lia | pose proof (rs_rw64_range row 280) as RN0;
                                      change (rw64 row 280) with (rname row) in RN0; clear -RN0; lia]).
        (* 0x86034 .. 0x86278: the 21 header bytes, the 10 name bytes and the entry of the outer sum *)
        assert (TAIL : forall (mc2 : word -> option byte) (y10 y11 y12 y13 y14 y15 : word),
                  BV fr j n w56 mc2 (zeros 32) (JA ++ nmr row nb ++ JB) ->
                  evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 0x85f30) (Z_to_bv 64 spc) u0 u1 u2
                                       y10 y11 y12 y13 y14 y15 u16 u17 x21 x22 x26 x27 u28 u29 u30 u31)
                                   F (Z_to_bv 64 0x86034) fc None mc2 (seg_rom rsegs))).
        { intros mc2 y10 y11 y12 y13 y14 y15 PI2. unfold RB, reac_box_model_block_binvF.RB_F.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 0 ltac:(clear; lia) PI0) as SH end.
          rewrite Z.add_0_r in SH.
          pose proof (sh1_F o 32 o ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core o RO0 (Z_to_bv 5 11) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 0.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 1 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 1) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 1) RXo1 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 1.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 2 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 2) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 2) RXo2 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 2. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 3 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 3) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 3) RXo3 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 3.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 4 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 4) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 4) RXo4 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 4. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 5 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 5) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 5) RXo5 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 5.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 6 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 6) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 6) RXo6 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 6. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 7 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 7) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 7) RXo7 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 7.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 8 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 8) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 8) RXo8 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 8.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 9 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 9) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 9) RXo9 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 9.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 10 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 10) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 10) RXo10 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 10.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 11 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 11) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 11) RXo11 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 11.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 12 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 12) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 12) RXo12 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 12. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 13 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 13) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 13) RXo13 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 13. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 14 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 14) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 14) RXo14 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 14.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 15 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 15) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 15) RXo15 (Z_to_bv 5 13) SH pre_sr no_extra.
          clear SHB.
          ost 15. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 16 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 16) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 16) RXo16 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 16.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 17 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 17) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 17) RXo17 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 17. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 18 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 18) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 18) RXo18 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. step. ost 18.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 19 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 19) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 19) RXo19 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          ost 19. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 20 ltac:(clear; lia) PI0) as SH end.
          pose proof (sh1_F o 32 (o + 20) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (ROs Ho0)) as SHB.
          rewrite <- Hoff in SHB.
          chk_core (o + 20) RXo20 (Z_to_bv 5 12) SH pre_sr no_extra.
          clear SHB.
          step. ost 20.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            replace X0 with (map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1]
                             ++ [] ++ zeros 11) in PI0
              by (rewrite ?rc_le1_lit;
                  try replace (Z_to_bv 8 (-2)) with (bz 254) by (apply Z_to_bv8_mod; reflexivity);
                  try replace (Z_to_bv 8 (-16)) with (bz 240) by (apply Z_to_bv8_mod; reflexivity);
                  reflexivity)
          end.
          (* 0x8625c .. 0x86268: __asan_memcpy(o + 21, A + 19, 10) *)
          do 4 step.
          match goal with
          | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
              let HL := fresh "HL" in
              assert (HL : rw_cells rsegs mm A [CB 56 Jf]) by (destruct PI0 as (_ & _ & H & _); exact H);
              pose proof (rs_cell0_sub rsegs mm A 56 Jf [] 19 10 HL ltac:(clear; lia)) as HD;
              change (Z.of_nat 19) with 19 in HD; clear HL
          end.
          rewrite (WIN JA (nmr row nb) JB 10%nat LJA ltac:(clear -LNM; lia)) in HD.
          match goal with
          | PI0 : BV _ _ _ _ ?mm ?X0 ?Jf |- _ =>
              eapply (cl_mc fr f spc j n w56 mm X0 Jf 0x8626c 21 10 (A + 19) (firstn 10 (nmr row nb)))
          end.
          - exact HK.
          - exact Hp0.
          - exact Ho0.
          - eassumption.
          - apply ret_pc_even; [clear; lia | reflexivity].
          - clear; lia.
          - clear; lia.
          - clear; lia.
          - rewrite length_firstn. clear -LNM; lia.
          - apply unsigned_lit. clear -Ro' Boe; cbn [Z.of_nat]; lia.
          - apply unsigned_lit. clear -RA19; lia.
          - apply unsigned_lit. clear; lia.
          - exact HD.
          - match goal with
            | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
                let JXf := fresh "JXf" in
                pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
                destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
                apply (B.acl_addr_sub mm A 56); [exact JAL | clear; lia | clear; lia | clear; lia]
            end.
          - match goal with
            | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
                let JXf := fresh "JXf" in
                pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
                destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
                replace (A + 19 + 7) with (A + 26) by (clear; lia);
                exact (B.acl_app_in mm A 56 26 JAL ltac:(clear; lia))
            end.
          - match goal with
            | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
                let JXf := fresh "JXf" in
                pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
                destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
                replace (A + 19 + Z.of_nat 10) with (A + 29) by (clear; lia);
                exact (B.acl_app_in mm A 56 29 JAL ltac:(clear; lia))
            end.
          - clear -Dow HAlo HAhi; cbn [Z.of_nat]; lia.
          - right. clear -HAlo HAhi; lia.
          (* cl_mc_F's two footprint premises for the copy source: the ten local bytes at A + 19, in the window *)
          - eapply rng_sub'; [exact Rwin|]. unfold REAC_BOX_MODEL_BLOCK_K.
            clear -HAlo HAhi HHM' Rsp; cbn [Z.of_nat]; lia.
          - apply sh_cover_win; unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; cbn [Z.of_nat]; lia.
          - (* cl_mc_F's shadow membership for the source: the locals are inside the window *)
            intros aa Haa. left. revert Haa. apply sh_word_on_sub;
              unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; cbn [Z.of_nat]; lia.
          - intros v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 mcM PIM.
            rewrite (rs_upd_fill (map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1])
                       [] (firstn 10 (nmr row nb)) 11 21) in PIM
              by (first [reflexivity | rewrite length_firstn; clear -LNM; lia]).
            rewrite length_firstn in PIM.
            replace (11 - Nat.min 10 (length (nmr row nb)))%nat with 1%nat in PIM by (clear -LNM; lia).
            cbn [app] in PIM.
            assert (PIMb : BV fr j n w56 mcM
                             (map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1]
                              ++ firstn 10 (nmr row nb) ++ zeros 1) (JA ++ nmr row nb ++ JB)) by exact PIM.
            clear PIM. rename PIMb into PIM.
            (* 0x8626c .. 0x86278: the sum registers, then the outer sum loop *)
            unfold RB, reac_box_model_block_binvF.RB_F. do 4 step.
            pose proof (a4_ol5 31%nat 0%nat fr f spc j n w56 mcM
                          (map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1]
                           ++ firstn 10 (nmr row nb) ++ zeros 1) (JA ++ nmr row nb ++ JB)) as OL.
            change (Z.of_nat 0) with 0 in OL. rewrite Z.add_0_r in OL.
            eapply OL.
            + exact HK.
            + exact Hp0.
            + exact Ho0.
            + clear; lia.
            + clear; lia.
            + rewrite !length_app, length_firstn. cbn [length map zeros repeat]. clear -LNM; lia.
            + rewrite Eb. change (synth row 5 nb) with (if has row =? 0 then zeros 32 else idf (nmr row nb)).
              replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
              unfold idf, idf31. f_equal.
              rewrite app_assoc, firstn_app, length_app, length_firstn, length_map. cbn [length].
              replace (31 - (21 + Nat.min 10 (length (nmr row nb))))%nat with 0%nat by (clear -LNM; lia).
              rewrite firstn_O, app_nil_r, firstn_all2
                by (rewrite length_app, length_firstn, length_map; cbn [length]; clear -LNM; lia).
              reflexivity.
            + rewrite Eb. change (rc row 5) with (if has row =? 0 then 0 else 1).
              replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
            + exact PIM. }
        (* 0x85f48 taken: the row has no name, the sixteen zero bytes are nmr row nb *)
        destruct (Z.eqb_spec (rname row) 0) as [N0|N0]; cbv iota.
        * apply TAIL. unfold nmr. rewrite (proj2 (Z.eqb_eq _ _) N0). exact PI1.
        * (* 0x85f4c .. 0x85f54, then the name loop at 0x85f58 *)
          do 3 step.
          pose proof (a4_nl5 16%nat 0%nat fr f spc j n w56 mc1 JA (repeat (Z_to_bv 8 0) 16) JB) as NL.
          change (Z.of_nat 0) with 0 in NL. rewrite !Z.add_0_r in NL.
          eapply NL.
          -- exact HK.
          -- exact Hp0.
          -- exact Ho0.
          -- exact Eb.
          -- exact H0.
          -- exact N0.
          -- clear; lia.
          -- clear; lia.
          -- intros t Ht. clear -Ht; lia.
          -- exact LJA.
          -- exact LJB.
          -- reflexivity.
          -- exact PI1.
          -- intros mc2 y10 y11 y12 y13 y14 y15 PI2. apply TAIL.
             unfold nmr. rewrite (proj2 (Z.eqb_neq _ _) N0). exact PI2.
  Qed.


  (* __asan_memcpy(A + d, S, n): the local bytes [d, d + n) become src (cl_mc with the locals as destination, proved
     as cl_ms_loc and cl_mc). *)
  Lemma a4_cl_mc_loc_F : forall fr f spc j n w56 mc X J (ret : Z) (dd nn : nat) (SS : Z) (src : list byte)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    (* the only lemma-level footprint premises of this file: the source [SS, SS + nn) is an arbitrary address,
       which no Section MainF hypothesis covers (the destination, the locals at A + dd, is in the window). *)
    rng RNG SS (Z.of_nat nn) -> sh_cover RNG SS (Z.of_nat nn) ->
    (* route (C): the source's aligned shadow words are inside this function's audited shadow region. *)
    (forall a, sh_word_on SS (Z.of_nat nn) a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (dd + nn <= 56)%nat -> (1 <= nn)%nat -> (dd + 7 <= 56)%nat ->
    length src = nn ->
    bv_unsigned a0 = A + Z.of_nat dd -> bv_unsigned a1 = SS -> bv_unsigned a2 = Z.of_nat nn ->
    bytes_at rsegs mc SS src -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) -> app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= A + Z.of_nat dd \/ A + Z.of_nat dd + Z.of_nat nn <= SS) ->
    (SS + Z.of_nat nn <= bv_unsigned sp - 4272 \/ A <= SS) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' X (upd_bytes J dd src) ->
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret dd nn SS src a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI RSr RSsh SSsh Hret Hdn Hn Hd7 LS E0 E1 E2 HSb HAS HS7 HSN DSD DSW K.
    (* The footprint facts in the form StepF's access hook matches (`H : rng RNG ?lo ?len`, closed by
          Z.div_mod_to_equations + lia): the window with its length as a numeral, the box and the row, and
          their shadow covers at the walk's own shadow offset off (a Theorem Labs lane, 2026-10-29). *)
    hide_sec.
       pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
       pose proof Rwsh as Rwsh'. unfold sh_cover, shadow_addr, REAC_BOX_MODEL_BLOCK_K in Rwsh'. rewrite <- Hoff in Rwsh'.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI)
      as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof (app_loc fr f spc j n w56 mc X J) as APL.
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -CF1 CF3 HHM' Rsp; lia).
    pose proof (rs_rw_sub rsegs mc A 56 J dd nn HL Hdn) as HSub.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    unfold RB, reac_box_model_block_binvF.RB_F.
    eapply evtF_cut.
    { eapply HMCF with (RNG := RNG) (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn dd J)) (src := src);
        unfold ASAN_MEMCPY_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSb.
      - exact LS.
      - exact HSub.
      - right. exact DSD.
      - lia.
      - exact HAS.
      - apply (B.acl_addr_sub mc A 56); [exact JAL | lia | lia | lia].
      - unfold end_in_app. right. exact HSN.
      - unfold end_in_app. right. replace (A + Z.of_nat dd + Z.of_nat nn) with (A + Z.of_nat (dd + nn)) by lia.
        apply (APL (Z.of_nat (dd + nn))); [exact HK | exact Hp0 | exact Ho0 | exact PI | lia].
      - right. split; [exact HS7|].
        replace (A + Z.of_nat dd + 7) with (A + (Z.of_nat dd + 7)) by lia.
        apply (APL (Z.of_nat dd + 7)); [exact HK | exact Hp0 | exact Ho0 | exact PI | lia].
      - unfold RT_LO, RT_HI. clear -HHM' HAlo HAhi Hdn; lia.
      - right. clear -CF7 HAlo HAhi; lia.
      - clear -DSW CF1 CF3 CF7 HAlo HAhi; lia.
      - exact STlo.
      - clear -CF3; lia.
      - unfold HIGHMEM_BEG; clear -HHM'; lia.
      - exact CF5.
      - exact JAC.
      - (* route (C): the memcpy's region is the source and the destination; the destination is the locals
           at A + dd, inside the window (R's first disjunct); the source comes from the lemma's SSsh. *)
        unfold asan_memcpy_shadow_R. rewrite ?E0, ?E1, ?E2.
        apply (SRON.shadow_rw_on_mono
                 (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) _ mc); [| exact JSW].
        intros aa [Haa|Haa]; [exact (SSsh aa Haa)|].
        left. revert Haa. apply sh_word_on_sub;
          unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp Hdn Hn; lia.
      - exact MI.
      (* the footprint premises of asan_memcpy_contract_F (asan_memcpy_cF.v:80-85), in order *)
      - exact Rby.
      - eapply rng_sub'; [exact Rimg|]. unfold IMG_LO, IMG_HI. lia.
      - eapply rng_sub'; [exact Rwin|]. unfold REAC_BOX_MODEL_BLOCK_K. clear -CF1 CF3 HHM' Rsp; lia.
      - eapply rng_sub'; [exact Rwin|]. unfold REAC_BOX_MODEL_BLOCK_K.
        clear -HAlo HAhi HHM' Rsp Hdn; lia.
      - exact RSr.
      - apply sh_word_win; unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp Hdn Hn; lia.
      - right. unfold sh_al8_lo, sh_al8_hi. unfold sh_cover in RSsh. exact RSsh.
      - apply sh_word_win; unfold REAC_BOX_MODEL_BLOCK_K; clear -HHM' Rsp CF1 CF3; lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems & MU2 & WM2 & MI2
                    & ST2 & RW2 & SB2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E2, Nat2Z.id in RW2.
    rewrite E0, E2 in MU2. unfold ASAN_MEMCPY_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)). rewrite LS. clear -Hy; lia.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy CF1 CF3 HHM'; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw _].
      unfold B.Wf in Hw. cbn [outside] in Hw. destruct Hw as (Hwin & _).
      cbn [outside]. split; [clear -Hwin CF1 CF3 CF7 HAlo HAhi Hdn; lia|].
      split; [clear -Hwin CF1 CF3; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -CF6 CF7 HAlo HAhi Hdn; lia|]. split; [clear -CF1 CF3; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -HFSb HHM' CF1 CF3 CF7 HAlo HAhi P1 Hdn; lia|].
      split; [clear -HFSb HHM' CF1 CF3 P1; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -FRhi FRlo HAlo HAhi CF7 HFSb HHM' P1 Hdn; lia|].
      split; [clear -CF8 CF1 CF3 CF7 HAlo HAhi; lia | exact I].
    - split; [|split; [|split]].
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HO32 MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hdn; lia|]. split; [clear -Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
      + apply (rw_upd2 mc m2 A 56 dd nn J src
                 [(A + Z.of_nat dd, A + Z.of_nat dd + Z.of_nat nn); (spc - 2224, spc)] HL Hdn LS MU2 WM2).
        * intros x Hx Hx2. cbn [outside]. split; [clear -Hx2; lia|].
          split; [clear -Hx CF1 CF3 CF7 HAlo HAhi; lia | exact I].
        * exact (rw1 m2 _ _ _ RW2).
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpw CF1 CF3 CF7 HAlo HAhi Hdn; lia|]. split; [clear -Dpw CF1 CF3; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dnw CF1 CF3 CF7 HAlo HAhi Hdn; lia|]. split; [clear -Dnw CF1 CF3; lia | exact I].
  Qed.
End MainF.

(* --------------------------------------------------------------------------------------------------------- *)
(* The corollaries: the original Exec.evt statements of reac_box_model_block_cases2.v re-derived from the
   footprint forms with ExecF.RNG_all, the post Q := Q0 and the continuation HKR := bmb_KR_Q0
   (reac_box_model_block_epiF.v).  This is the check that each _F statement is the old one plus footprint
   premises, nothing weaker.  The callee contracts stay in their _F form (a run that calls __asan_memcpy,
   __asan_memset or build_dt1_single cannot be re-played without the callee's footprint contract), and so does
   a4_cl_mc_loc's own continuation premise, for the same reason.  Text of the section and of all_rng:
   reac_box_model_block_binv2F.v:739-816 (itself reac_box_model_block_epiF.v:879-950). *)
Section OfF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* route (C): the callees' _on contracts (a Theorem Labs lane carried a Theorem Labs lane's leaves into the worktree;
     asan_memcpy_cF_on.v:20, asan_memset_cF_on.v, build_dt1_single_c.v). *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* route (C) (bmbF-narrow-brief.md): NOT A.AsanRT.shadow_rw (universal shadow, false at the allocator
     state) but the audited region of this function, reac_box_model_block_c_on.v:38. *)
  Hypothesis SR0 : SRON.shadow_rw_on
    (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
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

  Notation FK := (B.FK FS A).
  (* route (C): the ret post in its _on form (reac_box_model_block_c_on.v:47); under the narrowed SR0 the
     universal `shadow_rw m'` of B.Q0 is not provable, so a Theorem Labs lane's bmb_KR_Q0 is at this constant. *)
  Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    F fc m p b o FS row nb).
  (* route (C): BV over the NARROWED shadow premise (a Theorem Labs lane's BV_F = BINV.BV with JX's `shadow_rw mc`
     replaced by `shadow_rw_on (reac_box_model_block_shadow_R ...) mc`); same binders. *)
  Notation BV := (BINVF.BV_F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS A row nb).
  Notation RB := (BINVF.RB_F sp gp tp p o off A).

  (* The footprint forms at this section's variables, still waiting for RNG, its region premises, Q and HKR. *)
  Let cs4_F0 := ltac2:(inst_exact @cs4_F).
  Let cs5_F0 := ltac2:(inst_exact @cs5_F).
  Let a4_cl_mc_loc_F0 := ltac2:(inst_exact @a4_cl_mc_loc_F).
  Let bmb_KR_Q00 := ltac2:(inst_exact @BEPIF.bmb_KR_Q0).

  (* Section MainF's hide_sec at this section's hypotheses, the first tactic of every proof below: the lia of
     all_rng then does not search their disjunctions, implications and HA's division (the same helpers as
     reac_box_model_block_binv2F.v's OfF, a Theorem Labs lane S2). *)
  Ltac hide_secO :=
    let hd H := let T := type of H in change (mb_hide T) in H in
    hd HP; hd HN; hd HO; hd AP; hd ANB; hd AO; hd AJ1; hd AJ2; hd NDJ; hd HA; hd HS16.

  (* The all-footprint meets every region premise of this family's runs. *)
  Let FShi : FS + FS_SIZE <= 2^64.
  Proof.
    hide_secO.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5).
    pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A2. lia.
  Qed.

  Let FSlo : 0 <= FS.
  Proof.
    hide_secO.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). lia.
  Qed.

  (* The region bounds the all-footprint needs (0 <= a and a + n <= APPMEM_END for each range), from the
     addressable premises and the section's AO / AP / ANB / AJ1 / AJ2, which hide_secO hides from lia. *)
  Ltac bounds0 :=
    repeat match goal with
    | H : addressable ?mm ?a ?n |- _ =>
        let AB := fresh "AB" in pose proof H as AB; destruct AB as (? & ? & ? & _);
        change (mb_hide (addressable mm a n)) in H
    end;
    repeat match goal with H : mb_hide (addressable _ _ _) |- _ => unfold mb_hide in H end;
    try (match goal with H : o <> 0 |- _ => destruct (AO H) as ((? & ? & ? & _) & ? & ?) end);
    try (match goal with H : p <> 0 |- _ => destruct (AP H) as (? & ? & ? & _) end);
    try (match goal with H1 : p <> 0, H2 : (b = 5 \/ b = 6), H3 : has row <> 0, H4 : rname row <> 0 |- _ =>
           destruct (ANB H1 H2 H3 H4) as (? & ? & ? & _) end);
    try (match goal with H : b = 1 |- _ => destruct (AJ1 H) as (? & ? & ? & _) end);
    try (match goal with H : b = 2 |- _ => destruct (AJ2 H) as (? & ? & ? & _) end);
    unfold HIGHMEM_BEG, APPMEM_END in *.

  Ltac all_rng :=
    (* No region goal needs the footprint forms or the epi continuation above, and the shadow covers in their
       types are divisions that Z.div_mod_to_equations below would generalize one by one. *)
    try clear cs4_F0; try clear cs5_F0; try clear a4_cl_mc_loc_F0; try clear bmb_KR_Q00;
    let HHM' := fresh in let HAE' := fresh in
    pose proof HHM as HHM'; pose proof HAE as HAE';
    unfold HIGHMEM_BEG, APPMEM_END in *;
    unfold sh_cover, rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi,
           rng_ivls, reac_box_model_block_tls_rng, rng_bytes,
           shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K, fs_frame, fs_flag, fs_hint, fs_M, fs_B, FS_SIZE in *;
    try (unfold fp_w, fp_w1 in *); cbn [tl flat_map app fst snd] in *;
    repeat (intros || split || apply Forall_cons || apply Forall_nil);
    try exact I;
    bounds0;
    try (apply ExecF.rng_all; cbn [Z.of_nat]; Z.div_mod_to_equations; lia);
    try (cbn [Z.of_nat]; Z.div_mod_to_equations; lia).

  (* reac_box_model_block_cases2.v:315 *)
  Lemma cs4_of_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 4 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85e20) fc None mc (seg_rom rsegs)).
  Proof.
    intros. hide_secO. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply cs4_F0 with (Q := fun _ _ _ _ _ _ => Q0) (j := j) (n := n) (w56 := w56) (J := J);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

  (* reac_box_model_block_cases2.v:484 *)
  Lemma cs5_of_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 5 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85f04) fc None mc (seg_rom rsegs)).
  Proof.
    intros. hide_secO. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply cs5_F0 with (Q := fun _ _ _ _ _ _ => Q0) (j := j) (n := n) (w56 := w56) (J := J);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

  (* reac_box_model_block_cases2.v:1065; the continuation premise stays in evtF form at ExecF.RNG_all (the
     lemma passes it on, so an old evt continuation cannot be re-played by a footprint run). *)
  Lemma a4_cl_mc_loc_of_F : forall fr f spc j n w56 mc X J (ret : Z) (dd nn : nat) (SS : Z) (src : list byte)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (dd + nn <= 56)%nat -> (1 <= nn)%nat -> (dd + 7 <= 56)%nat ->
    length src = nn ->
    bv_unsigned a0 = A + Z.of_nat dd -> bv_unsigned a1 = SS -> bv_unsigned a2 = Z.of_nat nn ->
    bytes_at rsegs mc SS src -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) -> app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= A + Z.of_nat dd \/ A + Z.of_nat dd + Z.of_nat nn <= SS) ->
    (SS + Z.of_nat nn <= bv_unsigned sp - 4272 \/ A <= SS) ->
    (* route (C): the source's shadow membership is a premise of the _on world, so it stays in the corollary
       (the all-footprint gives the rng premises, but no region membership). *)
    (forall a, sh_word_on SS (Z.of_nat nn) a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' X (upd_bytes J dd src) ->
       evtF rsegs ExecF.RNG_all Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    intros. hide_secO. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply a4_cl_mc_loc_F0 with (Q := fun _ _ _ _ _ _ => Q0) (j := j) (n := n) (w56 := w56) (X := X) (J := J)
      (dd := dd) (nn := nn) (SS := SS) (src := src);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

End OfF.
