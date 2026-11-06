(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v; 497 of its 510 lines of code are new or changed and 235 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases0.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF: cs0_F follows cs0's script and sfacts is a Lemma with its own proof; the script edits include `hide_sec.` first, footprint (rng, shadow-cover) steps, the R16 / R20 reorder with `clear R16`, RIr / ROr for RI / RO, two `clear - ... lia.` bullets, `unfold BCASES0A.H8` for `unfold H8` and `f_equal; lia` for `f_equal. lia`.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the run of this file reads the row fields at
   p + 16, p + 20, p + 252, p + 253, p + 290 and their shadow bytes, writes the eight header bytes of the out
   block [o, o + 8) and calls __asan_memset at 0x85e14 / 0x86624; it reads no image or runtime cell with a fixed
   value. The pcs 0x85c88, 0x85e14 / 0x85e18, 0x86624 / 0x86628, 0x86630, 0x86654 are of the v1.9.0 image).

   The run of reac_box_model_block_cases0.v (cs0 at 0x85c88) as an ExecF.evtF run under a universally quantified
   footprint RNG, following cs0's proof script, with the edits :2 lists. The ret post Q0 is generalized to the section variable Q with the
   obligation HKR : bmb_KR Q (brief "Fixed cross-lane interface", S2 files); Q is INDEXED by the run's FK data
   (fr f spc j n w56), the lead's S2 interface change of 03:20Z. The data-region footprint facts are
   the section hypotheses Rimg .. RFSsh, Rby, Rwsw, RP .. RJ14s; the run adds no footprint premise of its own. *)
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
  reac_box_model_block_cases0a reac_box_model_block_cases0b reac_box_model_block_cases0c
  reac_box_model_block_cases0.
(* The footprint twins of the files the original imports, and the shared _F callee contracts. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF
  reac_box_model_block_binv2F reac_box_model_block_cases0aF reac_box_model_block_cases0bF
  reac_box_model_block_cases0cF
  reac_box_model_block_c_on sh_word_on asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on
  rng_asan.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module BINV := reac_box_model_block_binv.
Module BCASES0A := reac_box_model_block_cases0a.
Module BCASES0C := reac_box_model_block_cases0c.
Module C0 := reac_box_model_block_cases0.
Module BF := reac_box_model_block_baseF.
Module BEPIF := reac_box_model_block_epiF.
Module BINVF := reac_box_model_block_binvF.
Module BINV2F := reac_box_model_block_binv2F.
Module BCASES0AF := reac_box_model_block_cases0aF.
Module BCASES0BF := reac_box_model_block_cases0bF.
Module BCASES0CF := reac_box_model_block_cases0cF.
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

(* An opaque wrapper: a hypothesis of type mb_hide T is invisible to lia. *)
Definition mb_hide (P : Prop) : Prop := P.

(* The store hook of the evtF walk of this function (reac_box_model_blockF.v of 3c9fcc93205, as
   reac_box_model_block_cases0aF.v re-issues it): it also transports rd_mono. *)
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
   does not relate to the [rng] premise of its region (the row, the box and their shadow bytes).  Normalize the
   wrap, then close the bounds from an rng hypothesis by lia alone.
   The hook fires ONLY on that wrapped shape: StepF calls acc_hint FIRST in solve_acc1, so a wider pattern (every
   [wa a]) would shadow StepF's own cheap paths and run lia over every rng hypothesis at every access of the run
   (a Theorem Labs lane, 06:4xZ: a 3 h compile of cases0aF).  It does no division reasoning (text of
   reac_box_model_block_cases0aF.v:120-132): cs0_F puts each shadow byte it reads in the bare form
   [rng RNG (x / 8 + off) 1] (the division argument made once per region, not at every access). *)
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

(* The shadow-check tactics of reac_box_model_block_base.v:313-358, over StepF's evtF goals (the evt forms of the
   proved file cannot fire on an evtF goal). Same text otherwise. *)
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
  (* Route (C): the callee contracts in their `_on` footprint form (asan_memset_cF_on.v / asan_memcpy_cF_on.v,
     build_dt1_single_c.v's _on block). *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C) narrowing (bmbF-narrow-brief.md (a working note, not in this delivery)): only the shadow region the function and its callees read or
     store (a Theorem Labs lane's audited R, reac_box_model_block_c_on.v:38); the name SR0 is kept. *)
  Hypothesis SR0 : A.ShadowRwOn.shadow_rw_on
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

  (* The footprint and the regions this run reads or writes. *)
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
  Hypothesis Rwsw : rng_asan.sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
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

  (* The post is a parameter: S2 of the cgif-form walk stops at the flag release 0x864f8, before the ret post Q0.
     bmb_KR Q is the statement of reac_box_model_block_epi.v's `epi` with Q0 replaced by Q and evt rsegs by
     evtF rsegs RNG (reac_box_model_block_epiF.v), taken at this section's variables. *)
  Let bmb_KR := ltac2:(inst_exact @BEPIF.bmb_KR).
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The pure definitions of the proved files, by Notation (interface decision (A)). *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  Notation Q0 := (B.Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  Notation BV := (BINVF.BV_F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS A row nb).
  Notation RB := (BINVF.RB_F sp gp tp p o off A).
  Notation H8 := (BCASES0A.H8 row).
  Notation nsi := (BCASES0C.nsi row).
  Notation nso := (BCASES0C.nso row).

  (* The pure facts of the proved files at this section's variables. Under the narrowed SR0 the facts that go
     through the universal shadow_rw come from the _F twins (reac_box_model_block_baseF.v / _binvF.v), bound to
     the proved file's own names so that the proof scripts below stay the proved scripts, word for word. *)
  Let HA1 := ltac2:(inst_exact @BF.HA1_F).
  Let STW0 := ltac2:(inst_exact @BF.STW0_F).
  Let fk_facts := ltac2:(inst_exact @BF.fk_facts_F).
  Let mrd_wn_ne := ltac2:(inst_exact @BF.mrd_wn_ne_F).
  Let rw1 := ltac2:(inst_exact @BINVF.rw1_F).
  Let djw := ltac2:(inst_exact @BINVF.djw_F).
  Let bv_ok := ltac2:(inst_exact @BINVF.bv_ok_F).
  Let bv_store := ltac2:(inst_exact @BINVF.bv_store_F).
  Let bv_jx := ltac2:(inst_exact @BINVF.bv_jx_F).
  Let app_o := ltac2:(inst_exact @BINVF.app_o_F).
  Let cell_bytes_pt := ltac2:(inst_exact @BINVF.cell_bytes_pt_F).
  Let le1_neg := ltac2:(inst_exact @BCASES0AF.le1_neg_F).

  (* sfacts of reac_box_model_block_cases0c.v is RE-PROVED here, by the proved file's own script, instead of
     re-imported: the section closing of the proved file generalized it over that file's callee contract
     hypotheses (HMS : asan_memset_contract is the binder inst stops at), which this section does not have - it
     carries the _F contracts instead. A pure fact, no run, no new proof obligation. *)
  Lemma sfacts : synok row = true -> Z.of_nat nsi = ic row / 4 /\ Z.of_nat nso = oc row / 4 /\
    (nsi + nso <= 12)%nat /\ (ic row = 0 -> nsi = 0%nat) /\ (ic row <> 0 -> 1 <= ic row / 4) /\
    (oc row = 0 -> nso = 0%nat) /\ (oc row <> 0 -> 1 <= oc row / 4) /\ 0 <= ic row < 2 ^ 31 /\
    0 <= oc row < 2 ^ 31.
  Proof.
    intros S. unfold synok in S. rewrite !andb_true_iff in S. destruct S as ((((S1 & S2) & S3) & S4) & S5).
    apply Z.leb_le in S1, S2, S5. apply Z.eqb_eq in S3, S4.
    pose proof (rs_ic_range row) as RIr. pose proof (rs_oc_range row) as ROr.
    unfold BCASES0C.nsi, BCASES0C.nso.
    assert (DI : 0 <= ic row / 4) by (clear -S1; apply Z.div_pos; lia).
    assert (DO : 0 <= oc row / 4) by (clear -S2; apply Z.div_pos; lia).
    clear -S1 S2 S3 S4 S5 RIr ROr DI DO.
    repeat split; try lia.
    all: intros E; first [rewrite E; reflexivity | Z.div_mod_to_equations; lia].
  Qed.

  (* The _F runs of the files below this one. *)
  Let cl_ms_F := ltac2:(inst_exact @BINV2F.cl_ms_F).
  Let cl_mc_F := ltac2:(inst_exact @BINV2F.cl_mc_F).
  Let exit_r_F := ltac2:(inst_exact @BINVF.exit_r_F).
  Let blk68_F := ltac2:(inst_exact @BCASES0CF.blk68_F).
  Let blk8c_F := ltac2:(inst_exact @BCASES0CF.blk8c_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  Ltac ulit := repeat match goal with
                      | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
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
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mc X J HKt Hpt Hot PI) as JXf;
        let H := fresh "SH" in
        pose proof (B.acl_shadow mc o 32 k w (o + k)
                      (proj1 (proj2 (proj2 (proj2 JXf)))) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear; lia) eq_refl) as H;
        clear JXf
    end.

  (* The shadow fact for an instrumented access of w bytes at p + k (the row), at the current memory. *)
  Ltac shp2 k w :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, HKt : FK _ _ _ _ _ _, Hpt : p <> 0, Hot : o <> 0 |- _ =>
        let JXf := fresh "JXf" in
        pose proof (bv_jx _ _ _ _ _ _ mc X J HKt Hpt Hot PI) as JXf;
        let H := fresh "SH" in
        pose proof (B.acl_shadow mc p 296 k w (p + k)
                      (proj1 (proj2 (proj2 (proj2 (proj2 JXf))))) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear; lia) eq_refl) as H;
        clear JXf
    end.

  (* The byte of the row at index k, as a read of the current memory. *)
  Ltac rrow k :=
    lazymatch goal with
    | PI : BV ?fr ?j ?n ?w56 ?mc ?X ?J, LR : length row = 296%nat |- _ =>
        let R := fresh "RD" in
        pose proof (rd_byte rsegs mc p row k (proj1 (proj2 (proj2 (proj2 PI)))) ltac:(rewrite LR; lia)) as R;
        let z := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with z in R
    end.

  (* 0x85c88: case b = 0, the grammar block. *)
  Lemma cs0_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 0 -> BV fr j n w56 mc (zeros 32) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (-1)) x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85c88) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    (* hide_sec FIRST (a Theorem Labs lane, measured 11:5xZ: the section's own HA / HS16 / HP .. NDJ make every
       Z.div_mod_to_equations + lia in this walk hundreds of times slower; the proved file calls it late). *)
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'.
    (* The regions this run reads or writes, as BARE rng hypotheses at the run's own address form: StepF's access
       hook matches `rng RNG lo len` only, so the guarded section facts are instantiated at p <> 0 / o <> 0.  The
       8-aligned shadow word covers are NOT left unfolded in the context (their nested divisions made every
       Z.div_mod_to_equations + lia of the walk pay for them): SHp / SHo make the division argument once, and each
       shadow byte the run reads is put in the bare form [rng RNG (x / 8 + off) 1] right before its check. *)
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    pose proof (RP Hp0) as RProw. pose proof (RO Ho0) as RObox.
    assert (SHp : forall x, p <= x < p + 296 -> rng RNG (x / 8 + off) 1).
    { pose proof (RPs Hp0) as RProwsh. clear - RProwsh Hoff Rp. intros x Hx.
      unfold sh_cover, shadow_addr in RProwsh. rewrite <- Hoff in RProwsh.
      eapply rng_sub'; [exact RProwsh|]. Z.div_mod_to_equations. lia. }
    assert (SHo : forall x, o <= x < o + 32 -> rng RNG (x / 8 + off) 1).
    { pose proof (ROs Ho0) as RObsh. clear - RObsh Hoff Ro. intros x Hx.
      unfold sh_cover, shadow_addr in RObsh. rewrite <- Hoff in RObsh.
      eapply rng_sub'; [exact RObsh|]. Z.div_mod_to_equations. lia. }
    assert (HPf : p mod 8 = 0 /\ length row = 296%nat)
      by (destruct (HP Hp0) as (H1 & H2 & _); split; assumption).
    destruct HPf as (Hp8 & Lrow).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    assert (RXp : forall k, 0 <= k <= 296 -> 0 <= p + k < 2 ^ 64)
      by (pose proof JAP as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; intros k Hk; lia).
    assert (RXo : forall k, 0 <= k <= 32 -> 0 <= o + k < 2 ^ 64)
      by (pose proof JAO as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; intros k Hk; lia).
    (* R20 before R16, and R16 cleared after its load: StepF's solve_load tries the read facts of the access width
       newest first, and a wrong one fails only through word_eq_tac's Z.div_mod_to_equations + lia (11 s). *)
    pose proof (rs_rd4 rsegs mc p row 20 (proj1 (proj2 (proj2 (proj2 PI)))) ltac:(lia)) as R20.
    pose proof (rs_rd4 rsegs mc p row 16 (proj1 (proj2 (proj2 (proj2 PI)))) ltac:(lia)) as R16.
    change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 20) with 20 in R20.
    pose proof (rs_ic_range row) as RIr. pose proof (rs_oc_range row) as ROr.
    assert (SYF : forall X, synok row = false -> X = synth row b nb -> X = zeros 32).
    { intros X S E. rewrite E, Eb. change (synth row 0 nb) with (if synok row then gram row else zeros 32).
      rewrite S. reflexivity. }
    assert (RCF : synok row = false -> -1 = rc row b).
    { intros S. rewrite Eb. change (rc row 0) with (if synok row then 1 else -1). rewrite S. reflexivity. }

    unfold RB, BINVF.RB_F.
    (* the input and output counts *)
    step.
    pose proof (RXp 16 ltac:(lia)) as RX16.
    pose proof (B.acl_shadow mc p 296 16 4 (p + 16) JAP ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH16.
    pose proof (SHp (p + 16) ltac:(clear; lia)) as RS.
    chk_core (p + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr add1. clear RS.
    step. clear R16. rewrite rs_sx32_ic. step.
    rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (ic row) 0) as [I0|I0]; cbv iota.
    { assert (S : synok row = false)
        by (unfold synok; replace (0 <=? ic row) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      eapply (exit_r_F fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption.
      - symmetry. exact (SYF _ S eq_refl).
      - exact (RCF S). }
    step.
    pose proof (RXp 20 ltac:(lia)) as RX20.
    pose proof (B.acl_shadow mc p 296 20 4 (p + 20) JAP ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH20.
    pose proof (SHp (p + 20) ltac:(clear; lia)) as RS.
    chk_core (p + 20) RX20 (Z_to_bv 5 12) SH20 pre_sr add1. clear RS.
    step. rewrite rs_sx32_oc. step.
    rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (oc row) 0) as [O0|O0]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (0 <=? oc row) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite !andb_false_r. reflexivity. }
      eapply (exit_r_F fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption.
      - symmetry. exact (SYF _ S eq_refl).
      - exact (RCF S). }
    step. step. step.
    rewrite (rs_or3 (ic row) (oc row)) by lia.
    destruct (Z.eqb_spec (ic row mod 4) 0) as [IM|IM]; [destruct (Z.eqb_spec (oc row mod 4) 0) as [OM|OM]|];
      cbn [andb negb]; cbv iota.
    2,3: assert (S : synok row = false) by
           (unfold synok; rewrite ?(proj2 (Z.eqb_neq _ _) IM), ?(proj2 (Z.eqb_neq _ _) OM), ?andb_false_r;
            reflexivity);
         eapply (exit_r_F fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption;
         [ symmetry; exact (SYF _ S eq_refl) | exact (RCF S) ].
    step. rewrite rs_srliw2 by lia. step. rewrite rs_srliw2 by lia. step. step.
    assert (RSI : 0 <= ic row / 4 <= 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (RSO : 0 <= oc row / 4 <= 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    step. rewrite rc_ltu_lit by lia.
    destruct (Z.ltb_spec 12 (oc row / 4 + ic row / 4)) as [G|G]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (ic row / 4 + oc row / 4 <=? 12) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r. reflexivity. }
      eapply (exit_r_F fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption.
      - symmetry. exact (SYF _ S eq_refl).
      - exact (RCF S). }
    assert (SOK : synok row = true)
      by (unfold synok; repeat (apply andb_true_iff; split); first [apply Z.leb_le | apply Z.eqb_eq]; lia).
    (* the eight header bytes of the grammar block *)
    pose proof (RXo 0 ltac:(lia)) as RXo0. rewrite Z.add_0_r in RXo0.
    pose proof (SHo o ltac:(clear; lia)) as RS.
    sho 0 1. chk_core o RXo0 (Z_to_bv 5 11) SH pre_sr no_extra. clear RS.
    step. step. ost 0.
    pose proof (RXo 1 ltac:(lia)) as RXo1.
    pose proof (SHo (o + 1) ltac:(clear; lia)) as RS.
    sho 1 1. chk_core (o + 1) RXo1 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    step. step. ost 1.
    pose proof (RXo 2 ltac:(lia)) as RXo2.
    pose proof (SHo (o + 2) ltac:(clear; lia)) as RS.
    sho 2 1. chk_core (o + 2) RXo2 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    ost 2.
    step.
    pose proof (RXo 3 ltac:(lia)) as RXo3.
    pose proof (SHo (o + 3) ltac:(clear; lia)) as RS.
    sho 3 1. chk_core (o + 3) RXo3 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    step. ost 3.
    (* the selector byte at p + 252 and the trap byte at p + 253 *)
    step.
    pose proof (RXp 252 ltac:(lia)) as RXp252.
    pose proof (SHp (p + 252) ltac:(clear; lia)) as RS.
    shp2 252 1.
    chk_core (p + 252) RXp252 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    step.
    rrow 252%nat.
    pose proof (RXo 4 ltac:(lia)) as RXo4.
    pose proof (SHo (o + 4) ltac:(clear; lia)) as RS.
    sho 4 1. chk_core (o + 4) RXo4 (Z_to_bv 5 13) SH pre_sr no_extra. clear RS.
    ost 4.
    step.
    pose proof (RXo 5 ltac:(lia)) as RXo5.
    pose proof (SHo (o + 5) ltac:(clear; lia)) as RS.
    sho 5 1. chk_core (o + 5) RXo5 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    ost 5.
    step.
    pose proof (RXo 6 ltac:(lia)) as RXo6.
    pose proof (SHo (o + 6) ltac:(clear; lia)) as RS.
    sho 6 1. chk_core (o + 6) RXo6 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    ost 6.
    step.
    pose proof (RXp 253 ltac:(lia)) as RXp253.
    pose proof (SHp (p + 253) ltac:(clear; lia)) as RS.
    shp2 253 1.
    chk_core (p + 253) RXp253 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    step.
    rrow 253%nat.
    pose proof (RXo 7 ltac:(lia)) as RXo7.
    pose proof (SHo (o + 7) ltac:(clear; lia)) as RS.
    sho 7 1. chk_core (o + 7) RXo7 (Z_to_bv 5 13) SH pre_sr no_extra. clear RS.
    ost 7.
    (* the layout byte at p + 290 *)
    step.
    pose proof (RXp 290 ltac:(lia)) as RXp290.
    pose proof (SHp (p + 290) ltac:(clear; lia)) as RS.
    shp2 290 1.
    chk_core (p + 290) RXp290 (Z_to_bv 5 12) SH pre_sr no_extra. clear RS.
    rrow 290%nat.
    step. step.
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RI2 & RO2).
    pose proof (RXo 32 ltac:(lia)) as RO32.
    lazymatch goal with
    | PIc : BV _ _ _ _ _ ?X _ |- _ =>
        replace X with (H8 ++ [] ++ zeros 24) in PIc by (rewrite ?le1_zxb, ?rc_le1_lit; reflexivity)
    end.
    step.
    rewrite rs_zxb_eqb by lia. change (bv_unsigned (nth 290 row (Z_to_bv 8 0))) with (lay row).
    destruct (Z.eqb_spec (lay row) 1) as [L1|L1]; cbn [negb]; cbv iota.
    - (* layout 1: the output slots (value 1) first *)
      step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (oc row) 0) as [OZ|OZ]; cbv iota.
      + step.
        lazymatch goal with
        | PIc : BV _ _ _ _ _ ?X _ |- _ =>
            replace X with (H8 ++ repeat (bz 1) nso ++ zeros (24 - nso)) in PIc
              by (rewrite (ZO OZ); reflexivity)
        end.
        eapply (blk68_F fr f spc j n w56 _ J); try eassumption.
        rewrite (ZO OZ). reflexivity.
      + do 6 step. rewrite ?(rs_seqz (oc row / 4)) by lia. step.
        eapply (cl_ms_F fr f spc j n w56 _ (H8 ++ [] ++ zeros 24) J 0x85e18 8 nso 1).
        * exact HK.
        * exact Hp0.
        * exact Ho0.
        * eassumption.
        * apply ret_pc_even; [lia | reflexivity].
        * lia.
        * clear - FO NO OZ. lia.
        * lia.
        * lia.
        * ulit. lia.
        * ulit. lia.
        * ulit. lia.
        * intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mcm PIm.
          change (Z_to_bv 8 1) with (bz 1) in PIm.
          rewrite (rs_upd_fill H8 [] (repeat (bz 1) nso) 24 8) in PIm
            by (unfold BCASES0A.H8; cbn [length]; rewrite ?repeat_length; lia).
          rewrite repeat_length in PIm. cbn [app] in PIm.
          unfold RB, BINVF.RB_F. step. step.
          eapply (blk68_F fr f spc j n w56 mcm J); try eassumption.
          ulit. f_equal; lia.
    - (* layout 2: the input slots (value 2) first *)
      step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (ic row) 0) as [IZ|IZ]; cbv iota.
      + step.
        lazymatch goal with
        | PIc : BV _ _ _ _ _ ?X _ |- _ =>
            replace X with (H8 ++ repeat (bz 2) nsi ++ zeros (24 - nsi)) in PIc
              by (rewrite (ZI IZ); reflexivity)
        end.
        eapply (blk8c_F fr f spc j n w56 _ J); try eassumption.
        rewrite (ZI IZ). reflexivity.
      + do 5 step. rewrite ?(rs_seqz (ic row / 4)) by lia. step.
        eapply (cl_ms_F fr f spc j n w56 _ (H8 ++ [] ++ zeros 24) J 0x86628 8 nsi 2).
        * exact HK.
        * exact Hp0.
        * exact Ho0.
        * eassumption.
        * apply ret_pc_even; [lia | reflexivity].
        * lia.
        * clear - FI NI IZ. lia.
        * lia.
        * lia.
        * ulit. lia.
        * ulit. lia.
        * ulit. lia.
        * intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mcm PIm.
          change (Z_to_bv 8 2) with (bz 2) in PIm.
          rewrite (rs_upd_fill H8 [] (repeat (bz 2) nsi) 24 8) in PIm
            by (unfold BCASES0A.H8; cbn [length]; rewrite ?repeat_length; lia).
          rewrite repeat_length in PIm. cbn [app] in PIm.
          unfold RB, BINVF.RB_F. step.
          eapply (blk8c_F fr f spc j n w56 mcm J); try eassumption.
          ulit. f_equal; lia.
  Qed.

End MainF.
