(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 975 of its 992 lines of code are new or changed and 231 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases2.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF, from its proof scripts; the script edits include RFSh cleared, Rp / Rb / Ro hidden and footprint steps, and the new lemmas rng_sub_at, sh_cover_sub and sh1_F.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the five runs of this file read only the row at
   p, the name at rname row, the box at o and the function's own locals and frame; every image byte they touch is
   an instruction fetch, which is not an access).

   This is the second half of the _cases2.v twin (the first half, cs4_F / cs5_F / a4_cl_mc_loc_F, is
   reac_box_model_block_cases2aF.v): the b = 6 helpers a4_cs6_name, a4_cs6_rsum, a4_cs6_bsum, a4_cs6_tail and the
   case cs6 (0x85f98, the IDENT_LAST block).  Each statement is its original (_cases2.v:1179, :1270, :1310,
   :1392, :1652) with `evt rsegs Q0` replaced by `evtF rsegs RNG (Q fr f spc j n w56)` and, in a4_cs6_rsum_F, three more binders: these are S2 lemmas, so the fixed
   ret post Q0 becomes the section variable Q under HKR : bmb_KR Q (reac_box_model_block_epiF.v), and the ret-side
   frame release they used to reach through `epi` is reached through HKR.  The footprint premises are the nine of
   Section MainF (Rimg .. RFSsh) plus the data-region hypotheses Rby .. RJ14s, identical in every F file of the
   family (a Theorem Labs lane, interface decision (B)); no run lemma of this file adds a premise of its own.

   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z), obeyed here except condition 1:
   1. each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation;
   2. the _F output feeds ONLY the ported cgif-form walk: no W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim;
   3. the source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell; the re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes;
   4. this file carries its provenance above and goes to the auditor a Theorem Labs lane, who signs it against its proved
      run before it counts;
   5. a StepF "uncovered access" error means STOP and report: the footprint is never widened to make a step pass.

   rule 24: no function is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c asan_memset_cF asan_memcpy_cF build_dt1_single_c
  reac_box_model_block_c reac_box_model_block_cF
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2
  reac_box_model_block_cases2
  reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF reac_box_model_block_binv2F
  reac_box_model_block_cases2aF.
(* Route (C) (a Theorem Labs lane batch 75, a Theorem Labs lane's L3-recipe.md (a working note, not in this delivery)): the section's shadow premise is the region a Theorem Labs lane
   audited (reac_box_model_block_c_on.v:38), not the universal shadow_rw.  rng_asan is Required WITHOUT Import:
   it defines sh_word_rng, which asan_memcpy_cF.v defines too. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on
  asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_c_on rng_asan.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* the proved originals *)
Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.
Module C2 := reac_box_model_block_cases2.
(* their footprint twins *)
Module BF := reac_box_model_block_baseF.
Module BEPIF := reac_box_model_block_epiF.
Module BINVF := reac_box_model_block_binvF.
Module BINV2F := reac_box_model_block_binv2F.
Module C2AF := reac_box_model_block_cases2aF.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

From Ltac2 Require Import Ltac2.

(* The section-closing generalization abstracts each lemma of Section Main over the section variables and
   hypotheses it uses, in declaration order, under their own names. inst c applies c to the hypotheses of the
   current context that carry the names of c's leading binders, and stops at the first binder whose name is not a
   hypothesis.  (The text of reac_box_model_block_cases2.v:26-46.) *)
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

(* ------------------------------------------------------------------------------------------------------- *)
(* The footprint hooks of the walk (the text of 3c9fcc93205 reac_box_model_blockF.v, this function's own). *)

(* The store hook of reac_box_model_block_base.v, re-issued for the evtF walk: it also transports rd_mono. *)
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
   matching does not relate to the [rng] premise of its region.  Normalize the wrap, then close the bounds from
   an rng hypothesis by lia alone.
   Text of reac_box_model_block_cases0aF.v:112-133 (the narrow hook): StepF calls acc_hint FIRST in solve_acc1, at
   every access of the run, under a backtracking match over every rng hypothesis, so it fires only on the wrapped
   shape and does no division reasoning (each lia already turns the division of a shadow byte x / 8 + off into
   equations).  The division argument of an accessed shadow byte is made ONCE per lemma, by sh1_F below, which
   puts it in the bare rng form [rng RNG (x / 8 + ASAN_K) 1]. *)
Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, ?n) =>
      lazymatch a with
      | context [bv_unsigned (Z_to_bv 64 _)] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
              cbv [wa]; rewrite ?MState.unsigned_lit_wrap; lia
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mb_accF.

(* A sub-range of a covered range, and of its 8-aligned shadow word cover (sh_cover of
   reac_box_model_block_cF.v): the locals [A + d, A + d + n) lie in the window, so their footprint facts come
   from Rwin / Rwsh. *)
Lemma rng_sub_at : forall (R : footprint) lo len lo' len',
  rng R lo len -> lo <= lo' -> lo' + len' <= lo + len -> rng R lo' len'.
Proof. intros R lo len lo' len' H H1 H2. exact (rng_sub R lo len lo' len' H H1 H2). Qed.

Lemma sh_cover_sub : forall (R : footprint) a n a' n',
  sh_cover R a n -> 0 <= a -> a <= a' -> 1 <= n' -> a' + n' <= a + n -> sh_cover R a' n'.
Proof.
  intros R a n a' n' H Ha Haa Hn Hb. unfold sh_cover, shadow_addr, ASAN_K in *.
  apply (rng_sub' R _ _ _ _ H).
  pose proof (Z.div_le_mono a a' 8 ltac:(lia) Haa) as D1.
  pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
  split; Z.div_mod_to_equations; lia.
Qed.

(* ------------------------------------------------------------------------------------------------------- *)
(* The shadow-check tactics of the proved file over evtF (an Ltac body binds the tactics in scope where it is
   written, so the evt forms of reac_box_model_block_base.v cannot serve here).  Text of _base.v:313-354. *)

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
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG Q (MS (bvmap_set r rr R) F B fc rv mm ro));
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

(* ------------------------------------------------------------------------------------------------------- *)
Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* Route (C): the runtime helpers in their narrowed (_on) footprint contracts, the text _binv2F.v's
     Section MainF uses (a Theorem Labs lane, carried by a Theorem Labs lane from a working branch). *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  (* _cases2.v:60-91, verbatim *)
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C): the shadow region of this function (reac_box_model_block_c_on.v:38), not shadow_rw. *)
  Hypothesis SR0 : shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
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

  (* The footprint and the nine regions of the function's own run (3c9fcc93205 reac_box_model_blockF.v:147-159). *)
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
  (* The data regions, identical in every F file of the family (a Theorem Labs lane, interface decision (B)). *)
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

  (* The ret-side obligation of the S2 stretch: the fixed post Q0 of the proved file becomes a variable, and the
     frame release the proved lemmas reached through `epi` is reached through HKR. *)
  Let bmb_KR := ltac2:(inst_exact @BEPIF.bmb_KR).
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The definitions of reac_box_model_block_base.v and reac_box_model_block_binv.v at this section's variables
     (decision (A): the originals' pure Definitions are reused, never redefined).  Route (C): BV is the narrowed
     BINVF.BV_F (its JX conjunct is shadow_rw_on R mc, not shadow_rw mc), and every fact that goes through JX
     comes from its narrowed twin in _baseF.v / _binvF.v, never from the proved file. *)
  Notation FK := (B.FK FS A).
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
  (* BINV2.rw_upd2 is not instantiated here: its section binder SR0 is shadow_rw m, not the route (C) SR0 above,
     so its inst is an illegal application; no proof below uses it. *)
  Let app_loc := ltac2:(inst_exact @BINV2.app_loc).

  (* The run lemmas of the earlier layers, in their _F form (the only cross-lane names this file uses). *)
  Let exit_r := ltac2:(inst_exact @BINVF.exit_r_F).
  Let fin1 := ltac2:(inst_exact @BINVF.fin1_F).
  Let cl_mc := ltac2:(inst_exact @BINV2F.cl_mc_F).
  (* C2a's sub-range lemma for the shadow-word covers (reac_box_model_block_cases2aF.v, next to sh_word_win). *)
  Let sh_word_on_sub := ltac2:(inst_exact @C2AF.sh_word_on_sub).
  Let cl_ms_loc := ltac2:(inst_exact @BINV2F.cl_ms_loc_F).
  Let a4_cl_mc_loc := ltac2:(inst_exact @C2AF.a4_cl_mc_loc_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (C2.mb_hide T) in H.
  Ltac unhide H := unfold C2.mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* The byte at a + i is writable in m: in the frame (FW), a shadow byte of the frame (SW) or in the window. *)
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
    | |- evtF ?segs ?RNGq ?Qq (MS ?R ?Fq ?pc ?fcq ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
        let E := addr_expr a in
        lazymatch a with
        | wa _ => idtac
        | Z_to_bv 64 _ => change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
        | _ => replace (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs) by (f_equal; addr_eq_tac)
        end
    end.

  (* --- stepping tactics for the body --- *)

  (* A store into the locals at A + k.  bv_lok states store_ok at (wa (A + k)); the walk builds the address
     left-associated (A + 40 + i), so the hypothesis is re-associated before the step, as a Theorem Labs lane's wst does
     (the address must match the walk's expression syntactically). *)
  Ltac lst k :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let HS := fresh "HS" in
        pose proof (bv_lok fr j n w56 mc X J k 1%nat PI ltac:(lia) ltac:(lia)) as HS;
        rewrite ?Z.add_assoc in HS;
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
        rewrite ?Z.add_assoc in HS;
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

  (* One shadow BYTE of a covered range, in the bare rng form StepF's access solver matches cheaply (its own
     paths close an access with `lia` only, and the 8-aligned cover of sh_cover needs a division argument).  The
     division argument is made ONCE here, not at every access of the run.  Text of
     reac_box_model_block_cases0aF.v:351-360, with the context cleared before the division argument (the hidden
     section hypotheses still hold divisions, which Z.div_mod_to_equations would generalize). *)
  Lemma sh1_F : forall a n x, 0 <= a -> 0 < n -> a <= x -> x < a + n -> sh_cover RNG a n ->
    rng RNG (x / 8 + ASAN_K) 1.
  Proof.
    intros a n x Ha Hn Hx1 Hx2 H. hide_sec.
    unfold sh_cover, shadow_addr, ASAN_K in H. unfold ASAN_K.
    eapply rng_sub'; [exact H|]. clear -Ha Hn Hx1 Hx2. Z.div_mod_to_equations. lia.
  Qed.

  (* ----------------------------------------------------------------------------------------------------- *)
  (* b = 6, the name copy of 0x85fec .. 0x8601c (ASan slow path 0x86020): the NUL-terminated name at rname row,
     at most 16 bytes, into the locals at A + 40.  _cases2.v:1179, verbatim but for the post. *)
  Lemma a4_cs6_name_F : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (J0 Y : list byte) (ri ai : Z)
      (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 6 -> has row <> 0 -> rname row <> 0 ->
    (i + kk = 16)%nat -> (0 < kk)%nat ->
    (forall t, (t < i)%nat -> bv_unsigned (nth t nb (Z_to_bv 8 0)) <> 0) ->
    length J0 = 40%nat ->
    Y = firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i) ->
    ri = rname row + Z.of_nat i -> ai = A + 40 + Z.of_nat i ->
    BV fr j n w56 mc (zeros 32) (J0 ++ Y) ->
    (forall (mc' : word -> option byte) (y10 y11 y12 y13 y14 y15 : word),
       BV fr j n w56 mc' (zeros 32) (J0 ++ nmf nb) ->
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 y10 y11 y12 y13 y14 y15 x16 x17
                            x21 x22 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x862b4) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                         (Z_to_bv 64 ri) (Z_to_bv 64 ri) (Z_to_bv 64 (Z.of_nat kk)) (Z_to_bv 64 ai) x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85fec) fc None mc (seg_rom rsegs)).
  (* `using All`: the section-closed statement of the base text, whose old acc_hint (Z.div_mod_to_equations)
     generalized every section hypothesis into the proof; the faster proof uses fewer of them *)
  Proof using -(RFSh).
    (* RFSh (the side-stack header band, hint word included) is FALSE at the glue's footprint and no access of
       this run needs it: the flag byte it could match is covered by RFSw.  Keep it out of the closed type. *)
    clear RFSh.
    hide_sec.
    (* local copies of the section ranges, which LiaTwx2's lia (zify_split_ranges) otherwise destructs at every
       call in this lemma's large context; then the section ranges are hidden *)
    pose proof Rp as Rp'. pose proof Rb as Rb'. pose proof Ro as Ro'. hide Rp; hide Rb; hide Ro.
    assert (UPRE : forall (J0 Y bs : list byte) i, (i + length bs <= length Y)%nat ->
      upd_bytes (J0 ++ Y) (length J0 + i) bs = J0 ++ upd_bytes Y i bs).
    { clear. intros J0 Y bs i H. unfold upd_bytes. rewrite firstn_app, skipn_app.
      replace (length J0 + i - length J0)%nat with i by lia.
      replace (length J0 + i + length bs - length J0)%nat with (i + length bs)%nat by lia.
      rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite <- !app_assoc. reflexivity. }
    assert (OKN : p <> 0 -> b = 6 -> has row <> 0 -> rname row <> 0 -> name_ok nb).
    { intros Hp0 Eb H1 H2. destruct (HN Hp0 (or_intror Eb) H1 H2) as (OK & _). exact OK. }
    induction kk as [|kk IH];
      intros i fr f spc j n w56 mc J0 Y ri ai x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        HK Hp0 Ho0 Eb H1 H2 Hik Hk Hnz LJ0 EY Eri Eai PI K; [clear -Hk; lia|].
    subst Y ri ai.
    assert (B56 : b = 5 \/ b = 6) by (right; exact Eb).
    pose proof (OKN Hp0 Eb H1 H2) as OK.
    pose proof (name_ok_lt nb i OK ltac:(clear -Hik; lia) Hnz) as Hi.
    assert (HNB : bytes_at rsegs mc (rname row) nb) by (destruct PI as (_ & _ & _ & _ & H); exact (H B56 H1 H2)).
    pose proof (bytes_at_bound _ _ _ _ HNB) as BN.
    pose proof (rd_byte rsegs mc (rname row) nb i HNB Hi) as RD.
    clear HNB.
    assert (RX : 0 <= rname row + Z.of_nat i < 2 ^ 64) by (clear -BN Hi; lia).
    (* the name's footprint: the section hypotheses RN / RNs at this lemma's guards.  The accessed shadow BYTE is
       put in bare rng form by sh1_F, at the run's own shadow offset off (Hoff), so StepF's access hook can use it. *)
    pose proof (RN Hp0 B56 H1 H2) as RNm.
    pose proof (sh1_F (rname row) (Z.of_nat (length nb)) (rname row + Z.of_nat i) ltac:(clear -BN; lia)
                  ltac:(clear -Hi; lia) ltac:(clear; lia) ltac:(clear -Hi; lia) (RNs Hp0 B56 H1 H2)) as RNsm.
    rewrite <- Hoff in RNsm.
    (* the window, unguarded and with its size a numeral, for the store into the locals at A + 40 + i *)
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    (* 0x85fec .. 0x85ff8, 0x86020, 0x86024: the checked 1-byte access at a0 = rname row + i *)
    pose proof (bv_jx _ _ _ _ _ _ mc _ _ HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (_ & _ & _ & _ & _ & _ & JAN & _).
    pose proof (JAN B56 H1 H2) as JAN1. clear JAN.
    pose proof (B.acl_shadow mc (rname row) (Z.of_nat (length nb)) (Z.of_nat i) 1 (rname row + Z.of_nat i) JAN1
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Hi; lia)
                  ltac:(clear; Z.div_mod_to_equations; lia) eq_refl) as SH.
    clear JAN1.
    rewrite <- Hoff in SH.
    unfold RB, reac_box_model_block_binvF.RB_F.
    chk_core (rname row + Z.of_nat i) RX (Z_to_bv 5 15) SH pre_sr no_extra.
    (* 0x85ffc: lbu a4, 0(a1); 0x86000: beqz a4, 0x862b4 *)
    step. clear RD. step.
    rewrite rc_zxb_eqb0.
    destruct (Z.eqb_spec (bv_unsigned (nth i nb (Z_to_bv 8 0))) 0) as [C0|CNZ]; cbv iota.
    - (* the zero byte: the join with nmf nb *)
      apply K. rewrite (nmf_stop nb i Hi ltac:(clear -Hik; lia) Hnz C0). exact PI.
    - (* 0x86004: sb a4, 0(a3) *)
      lst (40 + Z.of_nat i).
      rewrite le1_zxb in PI0.
      replace (Z.to_nat (40 + Z.of_nat i)) with (length J0 + i)%nat in PI0 by (clear -LJ0; lia).
      rewrite (UPRE J0 _ _ i) in PI0.
      2:{ rewrite length_app, length_firstn, repeat_length. cbn [length]. clear -Hi Hik. lia. }
      rewrite upd_prefix in PI0 by (clear -Hi Hik; lia).
      (* 0x86008 .. 0x86014: a2 - 1, a3 + 1, a0 + 1, a1 + 1; 0x86018: bnez a2, 0x85fec *)
      step. step. step. step. step.
      rewrite (rc_eqb_lit (Z.of_nat (S kk) + -1) 0) by (clear -Hik; lia).
      destruct kk as [|kk].
      + (* the 16th byte: 0x8601c, j 0x862b4 *)
        replace (Z.of_nat (S 0) + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; clear; lia).
        cbn [negb]. cbv iota.
        step.
        assert (L16 : length nb = 16%nat) by (destruct OK as (OKl & _ & _); clear -OKl Hi Hik; lia).
        replace (S i) with 16%nat in PI0 by (clear -Hik; lia).
        rewrite <- (nmf_full nb L16) in PI0.
        2:{ intros t Ht. destruct (Nat.eq_dec t i) as [->|Ne]; [exact CNZ | apply Hnz; clear -Ht Ne Hik; lia]. }
        apply K. exact PI0.
      + (* the next byte: back to 0x85fec *)
        replace (Z.of_nat (S (S kk)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; clear; lia).
        cbn [negb]. cbv iota.
        replace (Z.of_nat (S (S kk)) + -1) with (Z.of_nat (S kk)) by (clear; lia).
        eapply (IH (S i) fr f spc j n w56 _ J0 (firstn (S i) nb ++ repeat (Z_to_bv 8 0) (16 - S i))
                  (rname row + Z.of_nat i + 1) (A + 40 + Z.of_nat i + 1));
          [exact HK | exact Hp0 | exact Ho0 | exact Eb | exact H1 | exact H2 | clear -Hik; lia | clear; lia
          | | exact LJ0 | reflexivity | clear; lia | clear; lia | exact PI0 | exact K].
        intros t Ht. destruct (Nat.eq_dec t i) as [->|Ne]; [exact CNZ | apply Hnz; clear -Ht Ne; lia].
  Qed.

  (* b = 6, 0x863ec .. 0x863f8: the inner sum of build_ident_last over the 21 record bytes at A + 19.  The record
     is in the frame's own locals, so its loads carry no shadow check and no region premise of their own (the
     locals are inside the window: Rwin).  _cases2.v:1270. *)
  Lemma a4_cs6_rsum_F : forall (kk i : nat) (REC : list byte) (f fr spc j n : Z) (w56 : word) (ai : Z)
      (mc : word -> option byte)
      (x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    (i + kk = 21)%nat -> (0 < kk)%nat -> length REC = 21%nat -> 0 <= A -> A + 56 < 2 ^ 64 ->
    ai = A + 19 + Z.of_nat i -> bytes_at rsegs mc (A + 19) REC ->
    (forall y10 y12 y13 : word,
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 y10 (Z_to_bv 64 (psum REC 21)) y12 y13
                            x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x863fc) fc None mc (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                         (Z_to_bv 64 ai) (Z_to_bv 64 (psum REC i)) (Z_to_bv 64 (A + 40)) x13
                         x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x863ec) fc None mc (seg_rom rsegs)).
  Proof using -(RFSh).
    clear RFSh.
    hide_sec.
    pose proof Rp as Rp'. pose proof Rb as Rb'. pose proof Ro as Ro'. hide Rp; hide Rb; hide Ro.
    induction kk as [|kk IH];
      intros i REC f fr spc j n w56 ai mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        Hik Hk LR HA0 HA56 Eai HREC K; [clear -Hk; lia|].
    subst ai.
    pose proof (rd_byte rsegs mc (A + 19) REC i HREC ltac:(clear -LR Hik; lia)) as RD.
    pose proof (psum_range REC i) as PR.
    (* the window, unguarded and with its size a numeral: the record bytes are the frame's own locals *)
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    unfold RB, reac_box_model_block_binvF.RB_F.
    (* 0x863ec: lbu a3, 0(a0); 0x863f0: a0 + 1; 0x863f4: a1 + a3 *)
    step. clear RD. step. step.
    rewrite psum_S_zxb.
    (* 0x863f8: bne a0, a2, 0x863ec *)
    step.
    rewrite (rc_eqb_lit (A + 19 + Z.of_nat i + 1) (A + 40)) by (clear -HA0 HA56 Hik; lia).
    destruct kk as [|kk].
    - replace (A + 19 + Z.of_nat i + 1 =? A + 40) with true by (symmetry; apply Z.eqb_eq; clear -Hik; lia).
      cbn [negb]. cbv iota. replace (S i) with 21%nat by (clear -Hik; lia).
      unfold RB, reac_box_model_block_binvF.RB_F in K. apply K.
    - replace (A + 19 + Z.of_nat i + 1 =? A + 40) with false by (symmetry; apply Z.eqb_neq; clear -Hik; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i) REC f fr spc j n w56 (A + 19 + Z.of_nat i + 1)); first [clear -Hik; lia | assumption].
  Qed.

  (* b = 6, 0x86448 .. 0x86470 (ASan slow path 0x86474): the outer checksum loop over the first 31 bytes of the
     box at o, each load with its 1-byte shadow check; then 0x864a0 .. 0x864b8 (slow path 0x86920): the checked
     store of the check byte at o + 31, and the join at 0x864bc (fin1).  _cases2.v:1310. *)
  Lemma a4_cs6_bsum_F : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (X J : list byte) (oi : Z)
      (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 -> oi = o + Z.of_nat i ->
    BV fr j n w56 mc X J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                         (Z_to_bv 64 oi) (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat kk)) (Z_to_bv 64 oi)
                         x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x86448) fc None mc (seg_rom rsegs)).
  Proof using -(RFSh).
    clear RFSh.
    hide_sec.
    pose proof Rp as Rp'. pose proof Rb as Rb'. pose proof Ro as Ro'. hide Rp; hide Rb; hide Ro.
    (* the byte that neg a1, a1; sb a1, 0(a0) stores *)
    assert (NEG : forall s, le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)]).
    { clear. intros s. rewrite rc_le1_lit. f_equal. apply Z_to_bv8_mod. change (2^8) with 256.
      rewrite Z.mod_mod by lia. rewrite unsigned_lit_wrap.
      change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
    assert (RW1 : forall mm AA N Xc, rw_cells rsegs mm AA [CB N Xc] -> bytes_at rsegs mm AA Xc).
    { clear. intros mm AA N Xc [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    induction kk as [|kk IH];
      intros i fr f spc j n w56 mc X J oi x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        HK Hp0 Ho0 Hik Hk LX ES Er Eoi PI; [clear -Hk; lia|].
    subst oi.
    (* the box, the shadow BYTE of o + i (sh1_F) in bare rng form at the run's shadow offset, and the window *)
    pose proof (RO Ho0) as ROm.
    pose proof (sh1_F o 32 (o + Z.of_nat i) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hik; lia) (ROs Ho0)) as ROsm.
    rewrite <- Hoff in ROsm.
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (_ & _ & _ & _ & _ & _ & _ & Boe & _).
    unfold APPMEM_END in Boe.
    assert (RX : 0 <= o + Z.of_nat i < 2 ^ 64) by (clear -Ro' Boe Hik; lia).
    pose proof (rd_byte rsegs mc o X i (RW1 _ _ _ _ (proj1 (proj2 PI))) ltac:(clear -LX Hik; lia)) as RD.
    pose proof (psum_range X i) as PR.
    pose proof (bv_jx _ _ _ _ _ _ mc _ _ HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (_ & _ & _ & JAO & _).
    pose proof (B.acl_shadow mc o 32 (Z.of_nat i) 1 (o + Z.of_nat i) JAO ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hik; lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + Z.of_nat i) 8 eq_refl) as MB; clear -MB; lia)
                  eq_refl) as SH.
    clear JAO.
    rewrite <- Hoff in SH.
    unfold RB, reac_box_model_block_binvF.RB_F.
    (* 0x86448 .. 0x86454, 0x86474, 0x86478: the shadow check of the byte at o + i *)
    chk_core (o + Z.of_nat i) RX (Z_to_bv 5 15) SH pre_sr no_extra.
    (* 0x86458 .. 0x86468: the byte, the count, the address, the sum and the second address *)
    step. clear RD. step. step. step.
    rewrite psum_S_zxb.
    (* 0x86468: a3 + 1; 0x8646c: bnez a2, 0x86448 *)
    step. step.
    rewrite (rc_eqb_lit (Z.of_nat (S kk) + -1) 0) by (clear -Hik; lia).
    replace (Z.of_nat (S kk) + -1) with (Z.of_nat kk) by (clear; lia).
    destruct kk as [|kk].
    2: {
      replace (Z.of_nat (S kk) =? 0) with false by (symmetry; apply Z.eqb_neq; clear; lia). cbn [negb]. cbv iota.
      eapply (IH (S i) fr f spc j n w56 mc X J (o + Z.of_nat i + 1));
        first [eassumption | clear -Hik; lia]. }
    (* the 31 bytes are summed: 0x86470, j 0x864a0 *)
    change (Z.of_nat 0 =? 0) with true. cbn [negb]. cbv iota.
    replace (S i) with 31%nat by (clear -Hik; lia).
    (* 0x864a0: a0 = o + 31, then its shadow check (bnez form, slow path 0x86920) *)
    step. step.
    assert (RX31 : 0 <= o + 31 < 2 ^ 64) by (clear -Ro' Boe; lia).
    pose proof (sh1_F o 32 (o + 31) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  (ROs Ho0)) as ROsm31.
    rewrite <- Hoff in ROsm31.
    pose proof (bv_jx _ _ _ _ _ _ mc _ _ HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (_ & _ & _ & JAO & _).
    pose proof (B.acl_shadow mc o 32 31 1 (o + 31) JAO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl) as MB; clear -MB; lia) eq_refl) as SH31.
    clear JAO.
    rewrite <- Hoff in SH31.
    chk_core (o + 31) RX31 (Z_to_bv 5 13) SH31 pre_sr no_extra.
    (* 0x864b4, 0x864b8: neg a1, a1; sb a1, 0(a0): the check byte at o + 31 *)
    step. ost 31.
    (* 0x864bc: li s5, 1 and the release; the box is now withchk (firstn 31 X) *)
    match goal with H : BV _ _ _ _ _ _ _ |- _ => rewrite NEG in H end.
    match goal with
    | H : BV _ _ _ _ ?mm ?Xn _ |- _ =>
        apply (fin1 fr f spc j n w56 mm Xn J); [exact HK | exact Hp0 | exact Ho0 | exact H | | exact Er]
    end.
    rewrite <- ES. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by (clear -LX; lia).
    change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by (clear -LX; lia).
    rewrite app_nil_r. reflexivity.
  Qed.

  (* b = 6, 0x862b4 .. 0x86444 (build_ident_last after the name field NM is in the locals at A + 40).
     _cases2.v:1392. *)
  Lemma a4_cs6_tail_F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (J0 NM : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 6 -> has row <> 0 ->
    length J0 = 40%nat -> length NM = 16%nat -> NM = nmr row nb ->
    BV fr j n w56 mc (zeros 32) (J0 ++ NM) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x862b4) fc None mc (seg_rom rsegs)).
  Proof.
    clear RFSh.
    intros fr f spc j n w56 mc J0 NM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb H0 LJ0 LNM ENM PI. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Rb as Rb'. pose proof Ro as Ro'. hide Rp; hide Rb; hide Ro.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    (* the box in bare rng form, and the window; the shadow BYTE of each checked access at o + t is put in bare
       rng form at the run's shadow offset by RSO (sh_cover through sh1_F) just before its check *)
    pose proof (RO Ho0) as ROm.
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    (* of djw's facts the run needs Boe, and Dow once (cl_mc's premise below); the four disjunctions it does not need
       are dropped and Dow is hidden, so the walk's lia calls do not case-split on them *)
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & _ & _ & _ & _ & _ & _ & Boe & _).
    unfold APPMEM_END in Boe. hide Dow.
    assert (RO0 : 0 <= o < 2 ^ 64) by (clear -Ro'; lia).
    assert (RXo1 : 0 <= o + 1 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo2 : 0 <= o + 2 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo3 : 0 <= o + 3 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo4 : 0 <= o + 4 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo5 : 0 <= o + 5 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo6 : 0 <= o + 6 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo7 : 0 <= o + 7 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo8 : 0 <= o + 8 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo15 : 0 <= o + 15 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RXo16 : 0 <= o + 16 < 2 ^ 64) by (clear -Ro' Boe; lia).
    assert (RA0 : 0 <= A) by (clear -HAlo HHM'; lia).
    assert (RA56 : A + 56 < 2 ^ 64) by (clear -HAhi Rsp; lia).
    (* the locals are application memory (as app_loc) *)
    assert (APL : forall t, 0 <= t <= 56 -> app_mem (A + t)).
    { intros t Ht. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right.
      clear -HHM' HAE' HAlo HAhi Ht Rsp; lia. }
    (* the locals' footprint: inside the window (Rwin) and its shadow cover (Rwsh) *)
    assert (RLOC : forall d nn, 0 <= d -> 1 <= nn -> d + nn <= 56 -> rng RNG (A + d) nn).
    { intros d nn Hd Hn Hdn.
      apply (rng_sub_at RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K);
        [exact Rwin | unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi Hd Hn Hdn; lia
        | unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi Hd Hn Hdn Rsp; lia]. }
    assert (SLOC : forall d nn, 0 <= d -> 1 <= nn -> d + nn <= 56 -> sh_cover RNG (A + d) nn).
    { intros d nn Hd Hn Hdn.
      apply (sh_cover_sub RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K);
        [exact Rwsh | unfold REAC_BOX_MODEL_BLOCK_K; clear -HHM'; lia
        | unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi Hd; lia | clear -Hn; lia
        | unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi Hd Hn Hdn Rsp; lia]. }
    (* the shadow byte of a one-byte access at o + t, at any memory of the body *)
    assert (SHO : forall (mm : word -> option byte) (X0 J1 : list byte) (t : Z), 0 <= t < 32 ->
              BV fr j n w56 mm X0 J1 ->
              exists k : byte, ov_read_bytes rsegs mm (wa ((o + t) / 8 + off)) 1 = Some [k]
                /\ (bv_signed k = 0 \/ (o + t) mod 8 + (1 - 1) < bv_signed k) /\ -128 <= bv_signed k < 128).
    { intros mm X0 J1 t Ht PI0.
      pose proof (bv_jx fr f spc j n w56 mm X0 J1 HK Hp0 Ho0 PI0) as (_ & _ & _ & JAOx & _).
      rewrite Hoff.
      exact (B.acl_shadow mm o 32 t 1 (o + t) JAOx ltac:(clear -Ht; lia) ltac:(clear; lia) ltac:(clear -Ht; lia)
               ltac:(clear; Z.div_mod_to_equations; lia) eq_refl). }
    (* the shadow byte of a one-byte access at o + t in bare rng form (sh1_F), at the run's shadow offset *)
    assert (RSO : forall t, 0 <= t < 32 -> rng RNG ((o + t) / 8 + off) 1).
    { intros t Ht. rewrite Hoff.
      exact (sh1_F o 32 (o + t) ltac:(clear -Ro'; lia) ltac:(clear; lia) ltac:(clear -Ht; lia) ltac:(clear -Ht; lia)
               (ROs Ho0)). }
    (* the 21 record bytes sum to 22 + the sum of the name *)
    assert (EPS : forall (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 : byte),
              psum [Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 1;
                    n0; n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15] 21
              = 22 + psum [n0; n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15] 16).
    { clear. intros. cbn [psum nth]. rewrite !rc_byte_lit by lia. lia. }
    (* concrete locals: 40 bytes, then the 16 name bytes *)
    do 40 (destruct J0 as [|? J0]; [cbn in LJ0; discriminate | cbn in LJ0]).
    destruct J0 as [|? J0]; [|cbn in LJ0; discriminate].
    destruct NM as [|n0 [|n1 [|n2 [|n3 [|n4 [|n5 [|n6 [|n7 [|n8 [|n9 [|n10 [|n11 [|n12 [|n13 [|n14 [|n15 NM]]]]]]]]]]]]]]]];
      try (cbn in LNM; discriminate).
    destruct NM as [|? NM]; [|cbn in LNM; discriminate].
    cbn [app] in PI. clear LJ0 LNM.
    unfold RB, reac_box_model_block_binvF.RB_F.
    (* 0x862b4 .. 0x862d0: the five record header bytes at A + 19 .. A + 23 *)
    step. step. step. lst 19. lst 20. lst 21. lst 22. lst 23.
    match goal with PI0 : BV _ _ _ _ _ _ _ |- _ =>
      rewrite ?rc_le1_lit in PI0; unfold upd_bytes in PI0;
      repeat match type of PI0 with context [Z.to_nat ?z] =>
        let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in PI0 end;
      cbn [firstn skipn app length Nat.add] in PI0 end.
    (* 0x862d4 .. 0x862e0: __asan_memcpy(A + 24, A + 40, 16) *)
    step. step. step. step.
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
        let HL := fresh "HL" in
        assert (HL : rw_cells rsegs mm A [CB 56 Jf]) by (destruct PI0 as (_ & _ & H & _); exact H);
        pose proof (rs_cell0_sub rsegs mm A 56 Jf [] 40 16 HL ltac:(clear; lia)) as HD;
        change (Z.of_nat 40) with 40 in HD; cbn [firstn skipn] in HD; clear HL
    end.
    match type of HD with bytes_at _ _ _ ?D =>
      match goal with
      | PI0 : BV _ _ _ _ ?mm ?X0 ?Jf |- _ =>
          eapply (a4_cl_mc_loc fr f spc j n w56 mm X0 Jf 0x862e4 24 16 (A + 40) D)
      end
    end.
    - exact HK.
    - exact Hp0.
    - exact Ho0.
    - eassumption.
    - (* NEW (a4_cl_mc_loc_F): the source range, inside the window *)
      change (Z.of_nat 16) with 16. apply RLOC; clear; lia.
    - (* NEW (a4_cl_mc_loc_F): its shadow word cover, inside the window's *)
      change (Z.of_nat 16) with 16. apply SLOC; clear; lia.
    - (* route (C): the source's shadow is R's window disjunct (the source is the locals at A + 40) *)
      change (Z.of_nat 16) with 16. intros aa Haa. left. revert Haa.
      apply sh_word_on_sub; unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; lia.
    - apply ret_pc_even; [clear; lia | reflexivity].
    - clear; lia.
    - clear; lia.
    - clear; lia.
    - reflexivity.
    - apply unsigned_lit. clear -RA0 RA56; cbn [Z.of_nat]; lia.
    - apply unsigned_lit. clear -RA0 RA56; lia.
    - apply unsigned_lit. clear; lia.
    - exact HD.
    - match goal with
      | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
          let JXf := fresh "JXf" in
          pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
          destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
          apply (B.acl_addr_sub mm A 56); [exact JAL | clear; lia | clear; lia | clear; lia]
      end.
    - replace (A + 40 + 7) with (A + 47) by (clear; lia). apply APL. clear; lia.
    - replace (A + 40 + Z.of_nat 16) with (A + 56) by (clear; lia). apply APL. clear; lia.
    - right. clear; lia.
    - right. clear; lia.
    - intros u0 u1 u2 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 mq1 PQ1.
      lazymatch type of PQ1 with ?h ?fr0 ?j0 ?n0 ?w0 ?mm ?X0 ?J0 => change (BV fr0 j0 n0 w0 mm X0 J0) in PQ1 end.
      unfold upd_bytes in PQ1. cbn [firstn skipn app length Nat.add] in PQ1.
      (* C2AF.a4_cl_mc_loc_F states this continuation over BINV.RB (reac_box_model_block_cases2aF.v:271), which
         BINVF.RB_F does not unfold *)
      unfold RB, reac_box_model_block_binvF.RB_F, reac_box_model_block_binv.RB.
      (* 0x862e4 .. 0x863c8: the nine checked header bytes 4 2 0 13 0 2 0 254 8 of the box *)
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 0 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 0 ltac:(clear; lia)) as RS.
      rewrite Z.add_0_r in SH, RS.
      chk_core o RO0 (Z_to_bv 5 11) SH pre_sr no_extra. clear RS.
      step. step. ost 0.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 1 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 1 ltac:(clear; lia)) as RS.
      chk_core (o + 1) RXo1 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      step. step. ost 1.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 2 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 2 ltac:(clear; lia)) as RS.
      chk_core (o + 2) RXo2 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      ost 2. step.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 3 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 3 ltac:(clear; lia)) as RS.
      chk_core (o + 3) RXo3 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      step. step. ost 3.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 4 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 4 ltac:(clear; lia)) as RS.
      chk_core (o + 4) RXo4 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      ost 4. step.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 5 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 5 ltac:(clear; lia)) as RS.
      chk_core (o + 5) RXo5 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      step. step. ost 5.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 6 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 6 ltac:(clear; lia)) as RS.
      chk_core (o + 6) RXo6 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      ost 6. step.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 7 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 7 ltac:(clear; lia)) as RS.
      chk_core (o + 7) RXo7 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      step. step. ost 7.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 8 ltac:(clear; lia) PI0) as SH end.
      pose proof (RSO 8 ltac:(clear; lia)) as RS.
      chk_core (o + 8) RXo8 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
      step. step. ost 8.
      match goal with PI0 : BV _ _ _ _ _ _ _ |- _ =>
        rewrite ?rc_le1_lit in PI0; unfold upd_bytes, zeros in PI0;
        repeat match type of PI0 with context [Z.to_nat ?z] =>
          let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in PI0 end;
        cbn [repeat firstn skipn app length Nat.add] in PI0 end.
      (* 0x863d4 .. 0x863dc: __asan_memcpy(o + 9, A + 50, 6) *)
      step. step. step.
      match goal with
      | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
          let HL := fresh "HL" in
          assert (HL : rw_cells rsegs mm A [CB 56 Jf]) by (destruct PI0 as (_ & _ & H & _); exact H);
          pose proof (rs_cell0_sub rsegs mm A 56 Jf [] 50 6 HL ltac:(clear; lia)) as HD2;
          change (Z.of_nat 50) with 50 in HD2; cbn [firstn skipn] in HD2; clear HL
      end.
      match type of HD2 with bytes_at _ _ _ ?D =>
        match goal with
        | PI0 : BV _ _ _ _ ?mm ?X0 ?Jf |- _ =>
            eapply (cl_mc fr f spc j n w56 mm X0 Jf 0x863e0 9 6 (A + 50) D)
        end
      end.
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + eassumption.
      + apply ret_pc_even; [clear; lia | reflexivity].
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + reflexivity.
      + apply unsigned_lit. clear -Ro' Boe; cbn [Z.of_nat]; lia.
      + apply unsigned_lit. clear -RA0 RA56; lia.
      + apply unsigned_lit. clear; lia.
      + exact HD2.
      + match goal with
        | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
            let JXf := fresh "JXf" in
            pose proof (bv_jx _ _ _ _ _ _ mm _ _ HK Hp0 Ho0 PI0) as JXf;
            destruct JXf as (_ & _ & _ & _ & _ & JAL & _);
            apply (B.acl_addr_sub mm A 56); [exact JAL | clear; lia | clear; lia | clear; lia]
        end.
      + unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right.
        clear -HHM' HAE' HAlo HAhi Rsp; lia.
      + replace (A + 50 + Z.of_nat 6) with (A + 56) by (clear; lia). apply APL. clear; lia.
      + unhide Dow. clear -Dow HAlo HAhi; cbn [Z.of_nat]; lia.
      + right. clear; lia.
      + (* cl_mc_F's two footprint premises: the source, the locals at A + 50, is inside the window *)
        change (Z.of_nat 6) with 6. apply RLOC; clear; lia.
      + change (Z.of_nat 6) with 6. apply SLOC; clear; lia.
      + (* route (C): the source's shadow is R's window disjunct (the locals at A + 50) *)
        change (Z.of_nat 6) with 6. intros aa Haa. left. revert Haa.
        apply sh_word_on_sub; unfold REAC_BOX_MODEL_BLOCK_K; clear -HAlo HAhi HHM' Rsp; lia.
      + intros v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 mq2 PQ2.
        lazymatch type of PQ2 with ?h ?fr0 ?j0 ?n0 ?w0 ?mm ?X0 ?J0 => change (BV fr0 j0 n0 w0 mm X0 J0) in PQ2 end.
        unfold upd_bytes in PQ2. cbn [firstn skipn app length Nat.add] in PQ2.
        (* 0x863e0 .. 0x863e8: the registers of the record sum, then its loop *)
        unfold RB, reac_box_model_block_binvF.RB_F. step. step. step.
        match goal with
        | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
            let HL := fresh "HL" in
            assert (HL : rw_cells rsegs mm A [CB 56 Jf]) by (destruct PI0 as (_ & _ & H & _); exact H);
            pose proof (rs_cell0_sub rsegs mm A 56 Jf [] 19 21 HL ltac:(clear; lia)) as HREC;
            change (Z.of_nat 19) with 19 in HREC; cbn [firstn skipn] in HREC; clear HL
        end.
        match type of HREC with bytes_at _ ?mm _ ?REC =>
          eapply (a4_cs6_rsum_F 21 0 REC f fr spc j n w56 (A + 19) mm)
        end.
        * clear; lia.
        * clear; lia.
        * reflexivity.
        * exact RA0.
        * exact RA56.
        * clear; lia.
        * exact HREC.
        * intros y10 y12 y13. unfold RB, reac_box_model_block_binvF.RB_F.
          rewrite EPS.
          (* 0x863fc .. 0x8640c, 0x86908: a0 = o + 15 and its shadow check *)
          step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
            pose proof (SHO mm X0 J1 15 ltac:(clear; lia) PI0) as SH end.
          pose proof (RSO 15 ltac:(clear; lia)) as RS.
          chk_core (o + 15) RXo15 (Z_to_bv 5 13) SH pre_sr no_extra. clear RS.
          (* 0x86410 .. 0x8641c: negw / andi 127, a0 = o + 16, the stamp byte at o + 15 *)
          step. step. step. ost 15.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
            pose proof (SHO mm X0 J1 16 ltac:(clear; lia) PI0) as SH end.
          pose proof (RSO 16 ltac:(clear; lia)) as RS.
          chk_core (o + 16) RXo16 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
          (* 0x86430 .. 0x86438: the 247 at o + 16 *)
          step. step. ost 16.
          (* 0x8643c .. 0x86444: a2 = 31, a3 = a0 = o, then the block sum loop *)
          step. step. step.
          match goal with PI0 : BV _ _ _ _ _ _ _ |- _ =>
            rewrite ?rc_le1_stamp, ?rc_le1_lit in PI0; unfold upd_bytes in PI0;
            repeat match type of PI0 with context [Z.to_nat ?z] =>
              let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in PI0 end;
            cbn [firstn skipn app length Nat.add] in PI0 end.
          match goal with
          | PI0 : BV _ _ _ _ ?mm ?X0 ?Jf |- _ =>
              eapply (a4_cs6_bsum_F 31 0 fr f spc j n w56 mm X0 Jf o)
          end.
          -- exact HK.
          -- exact Hp0.
          -- exact Ho0.
          -- clear; lia.
          -- clear; lia.
          -- reflexivity.
          -- rewrite Eb. change (synth row 6 nb) with (if has row =? 0 then zeros 32 else idl (nmr row nb)).
             replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
             rewrite <- ENM. unfold idl. apply (f_equal withchk).
             unfold idl31, idlc, zeros. cbn [firstn skipn map app repeat].
             replace (Z_to_bv 8 (-2)) with (bz 254) by (apply Z_to_bv8_mod; reflexivity).
             replace (Z_to_bv 8 (-9)) with (bz 247) by (apply Z_to_bv8_mod; reflexivity).
             unfold bz. reflexivity.
          -- rewrite Eb. change (rc row 6) with (if has row =? 0 then 0 else 1).
             replace (has row =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
          -- clear; lia.
          -- eassumption.
  Qed.

  (* b = 6 (0x85f98): the IDENT_LAST block (build_ident_last).  _cases2.v:1652. *)
  Lemma cs6_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 6 -> BV fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85f98) fc None mc (seg_rom rsegs)).
  Proof.
    clear RFSh.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Rb as Rb'. pose proof Ro as Ro'. hide Rp; hide Rb; hide Ro.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    (* the row and the box in bare rng form, the two shadow BYTES the row's checked loads read (of p + 56 and of
       p + 280, by sh1_F) in bare rng form at the run's shadow offset, and the window *)
    pose proof (RP Hp0) as RPm.
    pose proof (sh1_F p 296 (p + 56) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  (RPs Hp0)) as RPsm.
    pose proof (sh1_F p 296 (p + 280) ltac:(clear -Rp'; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  (RPs Hp0)) as RPsm2.
    rewrite <- Hoff in RPsm, RPsm2.
    pose proof (RO Ho0) as ROm. pose proof (ROs Ho0) as ROsm.
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (_ & _ & _ & _ & _ & _ & Lrow & _ & Bpe).
    unfold APPMEM_END in Bpe.
    assert (Hp8 : p mod 8 = 0) by (destruct (HP Hp0) as (H1 & _); exact H1).
    assert (LJ : length J = 56%nat) by (destruct PI as (_ & _ & [[[LJ0 _] _] _] & _); exact LJ0).
    assert (OKN : has row <> 0 -> rname row <> 0 -> name_ok nb)
      by (intros H1 H2; destruct (HN Hp0 (or_intror Eb) H1 H2) as (OK & _); exact OK).
    assert (RX56 : 0 <= p + 56 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX280 : 0 <= p + 280 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RA40 : 0 <= A + 40 < 2 ^ 64) by (clear -HAlo HAhi HHM' Rsp; lia).
    (* sx32 of a 32-bit value is 0 exactly when the value is 0 *)
    assert (SX0 : forall w, 0 <= w < 2 ^ 32 -> bv_eqb (sx32 (Z_to_bv 64 w)) (Z_to_bv 64 0) = (w =? 0)).
    { intros w Hw. destruct (Z.eqb_spec w 0) as [->|N]; [reflexivity|].
      unfold bv_eqb, sx32. apply Z.eqb_neq. rewrite (unsigned_lit w) by (clear -Hw; lia).
      rewrite unsigned_lit_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
      unfold bv_wrap. change (bv_modulus 32) with 4294967296. clear -Hw N. Z.div_mod_to_equations. lia. }
    unfold RB, reac_box_model_block_binvF.RB_F.
    (* 0x85f98: a0 = p + 56 *)
    step.
    (* 0x85f9c .. 0x85fa8, 0x86778 .. 0x86780: the checked 4-byte load of the has field *)
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
    (* 0x85fac: lw a0, 0(a0) *)
    match goal with
    | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
        let HRw := fresh "HRw" in
        assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
        pose proof (rs_rd4 rsegs mm p row 56 HRw ltac:(clear -Lrow; lia)) as RD56;
        change (Z.of_nat 56) with 56 in RD56; clear HRw
    end.
    step. clear RD56. step.
    (* 0x85fb0: beqz a0, 0x8602c — the row emits no identity record *)
    rewrite SX0 by (pose proof (rs_rw32_range row 56) as R; clear -R; lia).
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
      + rewrite Eb. change (synth row 6 nb) with (if has row =? 0 then zeros 32 else idl (nmr row nb)).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
      + rewrite Eb. change (rc row 6) with (if has row =? 0 then 0 else 1).
        rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
    - (* 0x85fb4 .. 0x85fc0: __asan_memset(A + 40, 0, 16), the name field's zero fill *)
      do 4 step.
      match goal with
      | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
          eapply (cl_ms_loc fr f spc j n w56 mm (zeros 32) Jf 0x85fc4 40 16 0)
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
      + apply unsigned_lit. clear -RA40; cbn [Z.of_nat]; lia.
      + apply unsigned_lit. clear; lia.
      + apply unsigned_lit. clear; lia.
      + intros u0 u1 u2 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 mc1 PI1.
        lazymatch type of PI1 with ?h ?fr0 ?j0 ?n0 ?w0 ?mm ?X0 ?J0 => change (BV fr0 j0 n0 w0 mm X0 J0) in PI1 end.
        set (JA := firstn 40 J) in *.
        assert (LJA : length JA = 40%nat) by (unfold JA; rewrite length_firstn; clear -LJ; lia).
        assert (EJ : upd_bytes J 40 (repeat (Z_to_bv 8 0) 16) = JA ++ repeat (Z_to_bv 8 0) 16).
        { unfold upd_bytes, JA. rewrite repeat_length. rewrite (skipn_all2 J) by (clear -LJ; lia).
          rewrite app_nil_r. reflexivity. }
        rewrite EJ in PI1. clear EJ.
        (* 0x85fc4: a0 = p + 280 *)
        unfold RB, reac_box_model_block_binvF.RB_F. step.
        (* 0x85fc8 .. 0x85fd4: the checked 8-byte load of the rname field; its shadow byte is 0 *)
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
        (* 0x85fd8: ld a1, 0(a0) *)
        match goal with
        | PI0 : BV _ _ _ _ ?mm _ _ |- _ =>
            let HRw := fresh "HRw" in
            assert (HRw : bytes_at rsegs mm p row) by (destruct PI0 as (_ & _ & _ & H & _); exact H);
            pose proof (rs_rd8 rsegs mm p row 280 HRw ltac:(clear -Lrow; lia)) as RD280;
            change (Z.of_nat 280) with 280 in RD280; change (rw64 row 280) with (rname row) in RD280; clear HRw
        end.
        step. clear RD280. step.
        (* 0x85fdc: beqz a1, 0x862b4 — the row has no name *)
        rewrite rc_eqb_lit by (first [clear; lia | pose proof (rs_rw64_range row 280) as RN0;
                                      change (rw64 row 280) with (rname row) in RN0; clear -RN0; lia]).
        destruct (Z.eqb_spec (rname row) 0) as [N0|N0]; cbv iota.
        * (* no name: the sixteen zero bytes are nmr row nb *)
          eapply (a4_cs6_tail_F fr f spc j n w56 mc1 JA (repeat (Z_to_bv 8 0) 16));
            [exact HK | exact Hp0 | exact Ho0 | exact Eb | exact H0 | exact LJA | reflexivity | | exact PI1].
          unfold nmr. rewrite (proj2 (Z.eqb_eq _ _) N0). reflexivity.
        * (* 0x85fe0 .. 0x85fe8: a2 = 16, a3 = A + 40, a0 = rname row, then the name copy loop at 0x85fec *)
          do 3 step.
          pose proof (OKN H0 N0) as OK.
          eapply (a4_cs6_name_F 16 0 fr f spc j n w56 mc1 JA (repeat (Z_to_bv 8 0) 16) (rname row) (A + 40)).
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
          -- reflexivity.
          -- clear; lia.
          -- clear; lia.
          -- exact PI1.
          -- intros mc2 y10 y11 y12 y13 y14 y15 PI2.
             eapply (a4_cs6_tail_F fr f spc j n w56 mc2 JA (nmf nb));
               [exact HK | exact Hp0 | exact Ho0 | exact Eb | exact H0 | exact LJA | | | exact PI2].
             ++ unfold nmf. rewrite length_app, repeat_length. pose proof (rs_takenz_len nb) as TL.
                destruct OK as ((_ & L16) & _). clear -TL L16. lia.
             ++ unfold nmr. rewrite (proj2 (Z.eqb_neq _ _) N0). reflexivity.
  Qed.

End MainF.
