(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v; 288 of its 301 lines of code are new or changed and 235 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases0c.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF, from its proof scripts with RIr / ROr for RI / RO, C0C.nsi / C0C.nso for nsi / nso, `hide_sec.` moved first in blk68_F and blk8c_F, `unfold BCASES0A.H8` for `unfold H8`, and `f_equal; lia` for `f_equal. lia` in blk68_F's last step.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the two runs of this file write the out block
   [o, o + 32) through __asan_memset at 0x86674 and read the row fields ic / oc already in registers; they read no
   image or runtime cell with a fixed value. The pcs 0x86630, 0x86654, 0x86674 / 0x86678 are of the v1.9.0 image).

   The two runs of reac_box_model_block_cases0c.v (blk68 at 0x86630 and blk8c at 0x86654) as ExecF.evtF runs under
   a universally quantified footprint RNG, by the source scripts with the edits :2 lists. The ret post Q0 is generalized to the
   section variable Q with the obligation HKR : bmb_KR Q (brief "Fixed cross-lane interface", S2 files); Q is
   INDEXED by the run's FK data (fr f spc j n w56), the lead's S2 interface change of 03:20Z. The
   data-region footprint facts are the section hypotheses Rimg .. RFSsh, Rby, Rwsw, RP .. RJ14s; no run lemma of
   this file adds a footprint premise of its own. *)
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
  reac_box_model_block_cases0a reac_box_model_block_cases0b reac_box_model_block_cases0c.
(* The footprint twins of the files the original imports, and the shared _F callee contracts. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF
  reac_box_model_block_binv2F reac_box_model_block_cases0aF reac_box_model_block_cases0bF
  reac_box_model_block_c_on sh_word_on asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on
  rng_asan.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module BINV := reac_box_model_block_binv.
Module BCASES0A := reac_box_model_block_cases0a.
Module C0C := reac_box_model_block_cases0c.
Module BF := reac_box_model_block_baseF.
Module BEPIF := reac_box_model_block_epiF.
Module BINVF := reac_box_model_block_binvF.
Module BINV2F := reac_box_model_block_binv2F.
Module BCASES0AF := reac_box_model_block_cases0aF.
Module BCASES0BF := reac_box_model_block_cases0bF.
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
   does not relate to the [rng] premise of its region (the box and its shadow bytes).  Normalize the wrap, then
   close the bounds from any rng hypothesis; Z.div_mod_to_equations is needed where the address or the bound holds
   a division (a shadow byte is x / 8 + ASAN_K).
   The hook fires ONLY on that wrapped shape: StepF calls acc_hint FIRST in solve_acc1, so a wider pattern (every
   [wa a]) would shadow StepF's own cheap paths and run Z.div_mod_to_equations + lia over every rng hypothesis at
   every access of the run (a Theorem Labs lane, 06:4xZ: a 3 h compile of cases0aF). *)
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

  (* The footprint and the regions these runs read or write. *)
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
  Notation nsi := (C0C.nsi row).
  Notation nso := (C0C.nso row).

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
    pose proof (rs_ic_range row) as RIr. pose proof (rs_oc_range row) as ROr. unfold C0C.nsi, C0C.nso.
    assert (DI : 0 <= ic row / 4) by (clear -S1; apply Z.div_pos; lia).
    assert (DO : 0 <= oc row / 4) by (clear -S2; apply Z.div_pos; lia).
    clear -S1 S2 S3 S4 S5 RIr ROr DI DO.
    repeat split; try lia.
    all: intros E; first [rewrite E; reflexivity | Z.div_mod_to_equations; lia].
  Qed.

  (* The _F runs of the files below this one. *)
  Let cl_ms_F := ltac2:(inst_exact @BINV2F.cl_ms_F).
  Let cl_mc_F := ltac2:(inst_exact @BINV2F.cl_mc_F).
  Let mc0A_F := ltac2:(inst_exact @BCASES0BF.mc0A_F).
  Let tail0A_F := ltac2:(inst_exact @BCASES0BF.tail0A_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  Ltac ulit := repeat match goal with
                      | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
                      end.

  (* 0x86630 (layout 1, the output slots written): the input slots (value 0), then 0x8667c. *)
  Lemma blk68_F : forall fr f spc j n w56 mc J (s5w : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 0 -> synok row = true -> lay row = 1 ->
    s5w = Z_to_bv 64 (Z.of_nat nso) ->
    BV fr j n w56 mc (H8 ++ repeat (bz 1) nso ++ zeros (24 - nso)) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 (ic row / 4)) x15 x16 x17
                         s5w (Z_to_bv 64 (ic row)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x86630) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J s5w x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb SOK L E5 PI.
    (* hide_sec FIRST (a Theorem Labs lane, measured 11:5xZ: the section's own HA / HS16 / HP .. NDJ make every
       Z.div_mod_to_equations + lia hundreds of times slower). *)
    hide_sec.
    pose proof Ro as Ro'.
    pose proof (bv_jx fr f spc j n w56 mc _ J HK Hp0 Ho0 PI) as (_ & _ & _ & JAOx & _).
    assert (RO32 : 0 <= o /\ o + 32 <= 2 ^ 64)
      by (destruct JAOx as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RIr & ROr).
    pose proof (rs_slots_1 row L) as SL. fold (C0C.nsi row) (C0C.nso row) in SL.
    subst s5w.
    unfold RB, BINVF.RB_F. step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - eapply (tail0A_F nso (repeat (bz 1) nso) _ fr f spc j n w56 mc J); try eassumption.
      + lia.
      + apply repeat_length.
      + rewrite SL, (ZI I0). reflexivity.
      + reflexivity.
    - do 8 step.
      rewrite ?(rs_seqz (ic row / 4)) by lia.
      step.
      eapply (cl_ms_F fr f spc j n w56 mc _ J 0x86678 (8 + nso) nsi 0).
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + exact PI.
      + apply ret_pc_even; [lia | reflexivity].
      + lia.
      + lia.
      + lia.
      + lia.
      + ulit. rewrite ?rc_swrap_small by lia. ulit. lia.
      + ulit. lia.
      + ulit. lia.
      + intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc2 PI2.
        change (Z_to_bv 8 0) with (bz 0) in PI2.
        rewrite (rs_upd_fill H8 (repeat (bz 1) nso) (repeat (bz 0) nsi) (24 - nso) (8 + nso)) in PI2
          by (unfold BCASES0A.H8; cbn [length]; rewrite ?repeat_length; lia).
        rewrite repeat_length in PI2. replace (24 - nso - nsi)%nat with (24 - (nso + nsi))%nat in PI2 by lia.
        unfold RB, BINVF.RB_F. step.
        eapply (tail0A_F (nso + nsi) (repeat (bz 1) nso ++ repeat (bz 0) nsi) _ fr f spc j n w56 mc2 J);
          try eassumption.
        * lia.
        * rewrite length_app, !repeat_length. lia.
        * rewrite SL, <- app_assoc. do 2 f_equal. f_equal. lia.
        * ulit. f_equal; lia.
  Qed.

  (* 0x86654 (layout 2, the input slots written): the output slots (value 1), then 0x8667c. *)
  Lemma blk8c_F : forall fr f spc j n w56 mc J (s5w : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 0 -> synok row = true -> lay row <> 1 ->
    s5w = Z_to_bv 64 (Z.of_nat nsi) ->
    BV fr j n w56 mc (H8 ++ repeat (bz 2) nsi ++ zeros (24 - nsi)) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         s5w x22 (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x86654) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J s5w x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      HK Hp0 Ho0 Eb SOK L E5 PI.
    hide_sec.    (* first: see blk68_F *)
    pose proof Ro as Ro'.
    pose proof (bv_jx fr f spc j n w56 mc _ J HK Hp0 Ho0 PI) as (_ & _ & _ & JAOx & _).
    assert (RO32 : 0 <= o /\ o + 32 <= 2 ^ 64)
      by (destruct JAOx as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    destruct (sfacts SOK) as (FI & FO & F12 & ZI & NI & ZO & NO & RIr & ROr).
    pose proof (rs_slots_2 row L) as SL. fold (C0C.nsi row) (C0C.nso row) in SL.
    subst s5w.
    unfold RB, BINVF.RB_F. step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - eapply (tail0A_F nsi (repeat (bz 2) nsi ++ repeat (bz 1) nso) _ fr f spc j n w56 mc J); try eassumption.
      + lia.
      + rewrite length_app, !repeat_length, (ZO O0). lia.
      + rewrite SL, <- app_assoc, (ZO O0), Nat.sub_0_r. reflexivity.
      + reflexivity.
      + rewrite (ZO O0). cbn [repeat]. rewrite app_nil_r. exact PI.
    - do 7 step.
      rewrite ?(rs_seqz (oc row / 4)) by lia.
      step.
      eapply (cl_ms_F fr f spc j n w56 mc _ J 0x86678 (8 + nsi) nso 1).
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + exact PI.
      + apply ret_pc_even; [lia | reflexivity].
      + lia.
      + lia.
      + lia.
      + lia.
      + ulit. rewrite ?rc_swrap_small by lia. ulit. lia.
      + ulit. lia.
      + ulit. lia.
      + intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc2 PI2.
        change (Z_to_bv 8 1) with (bz 1) in PI2.
        rewrite (rs_upd_fill H8 (repeat (bz 2) nsi) (repeat (bz 1) nso) (24 - nsi) (8 + nsi)) in PI2
          by (unfold BCASES0A.H8; cbn [length]; rewrite ?repeat_length; lia).
        rewrite repeat_length in PI2. replace (24 - nsi - nso)%nat with (24 - (nsi + nso))%nat in PI2 by lia.
        unfold RB, BINVF.RB_F. step.
        eapply (tail0A_F (nsi + nso) (repeat (bz 2) nsi ++ repeat (bz 1) nso) _ fr f spc j n w56 mc2 J);
          try eassumption;
          first [ lia
                | rewrite length_app, !repeat_length; lia
                | rewrite SL, <- app_assoc, Nat.sub_add_distr; reflexivity
                | ulit; f_equal; lia ].
  Qed.

End MainF.
