(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 776 of its 791 lines of code are new or changed and 233 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_base.v at a working branch d69f7c708f6 (proved v1.9 run
   of record) over lib/Lib/StepF, from its proof scripts; the script edits include `hide_sec.` and footprint steps, the entry run is split at the jal (entry_pre_F / entry_post_F), and RFSf_F, fk_rng_F, bmb_at_call_refl and bmb_at_ret_of are new.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: GOT_CELL_K 0x9fad0 (file offset 0x8dad0, 8 bytes
   78 88 0a 00 00 00 00 00 = 0xa8878 = CELL_K) and GOT_UAR 0x9fb28 (file offset 0x8db28, 8 bytes
   80 88 0a 00 00 00 00 00 = 0xa8880 = UAR); the prologue reads both through auipc + ld at 0x85b94 .. 0x85ba0.
   CELL_K and UAR themselves are .bss cells: the run reads their VALUES from asan_cells (AC0), not from the image.

   The runs: `fwords` (0x85bec -> 0x85c48, then KB), and `entry` (0x85b44 -> Q0) SPLIT at the allocator call
   `jal __asan_stack_malloc_0` at 0x85bb8, the first of the two events the cgif glue cuts at:
     - entry_pre_F runs [0x85b44 .. 0x85bb8) and ends in a continuation at the state of the jal, whose memory
       facts are bmb_at_call (exactly the facts the proved run holds at reac_box_model_block_base.v:599, before
       `eapply evt_cut`);
     - entry_post_F runs [0x85bbc .. 0x85bec) on the FAKE-frame arm from bmb_at_ret (the side-stack arm of
       asan_stack_malloc_post, as the proved run uses it at reac_box_model_block_base.v:672-711) and continues
       through fwords_F with KB_F Q.  The real-stack arm is dead under cgif's allocator invariant and is not
       re-run here.
   No lemma of this file takes the stack-malloc contract: the call is an event, not a contract (the lead
   a Theorem Labs lane, 2026-10-28).  td_tail and epi_close are re-run by lane EPI, in reac_box_model_block_epiF.v.
   The pure Definitions (SAVES, Wf, FK, BI) and the pure section facts of the proved file are reused by Notation
   and by inst_exact; only KB, which mentions evt, gets an F twin. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_box_model_block_cF asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* Route (C) (a Theorem Labs lane batch 75, a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery) / L3-recipe.md (a working note, not in this delivery)): the section's shadow premise is the region
   a Theorem Labs lane audited, not the universal shadow_rw.  rng_asan is Required WITHOUT Import: it defines sh_word_rng,
   which asan_memcpy_cF.v defines too. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_c_on rng_asan.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
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

(* The store hook of reac_box_model_block_base.v (its line 215), re-issued for the evtF walk.  LOCAL: the
   redefinition must not escape this file (the coordinating lane, 2026-10-29); each F file carries its own copy. *)
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
   matching does not relate to the [rng] premise of its region (the GOT words of the prologue, the frame words
   and the shadow bytes of the frame).  Normalize the wrap, then close the bounds from any rng hypothesis;
   Z.div_mod_to_equations is needed where the address or the bound holds a division (a shadow byte is
   x / 8 + ASAN_K).  Only such addresses reach this hook: a literal or a plain variable address goes to
   StepF's own paths. *)
Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (wa ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len (wa E) n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?MState.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  | |- acc_in ?RNG (?a, ?n) =>
      lazymatch a with
      | context [bv_unsigned (Z_to_bv 64 _)] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
              cbv [wa]; rewrite ?MState.unsigned_lit_wrap; Z.div_mod_to_equations; lia
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mb_accF.

(* ------------------------------------------------------------------------------------------------------- *)
Section MainF.
  (* reac_box_model_block_base.v Section Main, verbatim, without HSM (no lemma of this file takes the
     stack-malloc contract: the call is an event). *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
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

  (* The footprint and the regions the runs of this family read or write.  The side stack in two pieces (not
     [FS, FS + FS_SIZE)): the header [FS, fs_frame FS 0 0) and the class-0 area fp_w [0%nat] FS. *)
  Variable RNG : footprint.
  Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
  Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rwsh : sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
  Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
  Hypothesis Rtls : reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
  Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
  (* The class-0 area WITHOUT its first range, the hint word [FS, FS + 8): this run does not read the hint
     itself (the allocator does, inside the call), and the header premise RFSh covers it anyway. *)
  Hypothesis RFSw : rng_ivls RNG (tl (fp_w [0%nat] FS)).
  Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
  (* The data-region footprint facts, as every F file of this family states them (seven write Rwsw's sh_word_rng as rng_asan.sh_word_rng) (the coordinating lane). *)
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

  (* The remaining premises of the contract (reac_box_model_block_base.v:749-769, verbatim); ebw_sub, br_ac and
     br_fp, which epi_state_F re-imports, are generalized over them. *)
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

  (* a Theorem Labs lane's speed fix (the coordinating lane, 2026-10-29): the second hypothesis block is full of
     disjunctions and implications, which zify drags into every lia call.  mb_hide is the device of
     reac_box_model_block_epi.v:50; hide_sec is its hide list. *)
  Definition mb_hide (P : Prop) : Prop := P.
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ.

  (* The pure definitions of reac_box_model_block_base.v at this section's variables. *)
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation Wf := (B.Wf sp FS).
  Notation FK := (B.FK FS A).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EBW := (B.EBW sp p o FS).

  (* The section facts of reac_box_model_block_base.v applied to this section's variables (inst applies a base
     lemma to the hypotheses that carry the names of its leading binders: those are exactly the section
     hypotheses it used).  Only the facts that go through SR0 cannot be re-imported: _base.v uses SR0 exactly at
     :475 (fk_facts), :606 (entry), :724 (JR_m) and :1051 (epi_state), and `clear`s it at :787, :957 and :1342;
     those get `_F` twins below. *)
  Let STW0 := ltac2:(inst_exact @B.STW0).
  Let HA1 := ltac2:(inst_exact @B.HA1).
  Let app_range := ltac2:(inst_exact @B.app_range).
  Let ebw_sub := ltac2:(inst_exact @B.ebw_sub).
  Let br_ac := ltac2:(inst_exact @B.br_ac).
  Let br_fp := ltac2:(inst_exact @B.br_fp).
  Let mrd_w1 := ltac2:(inst_exact @B.mrd_w1).
  Let mrd_wn_ne := ltac2:(inst_exact @B.mrd_wn_ne).
  Let bytes_keep_out := ltac2:(inst_exact @B.bytes_keep_out).
  Let inside_appl := ltac2:(inst_exact @B.inside_appl).
  Let zeqb_addcancel := ltac2:(inst_exact @B.zeqb_addcancel).
  Let win_shadow0 := ltac2:(inst_exact @B.win_shadow0).
  Let epi_addr := ltac2:(inst_exact @B.epi_addr).
  Let ebw_sub0 := ltac2:(inst_exact @B.ebw_sub0).

  (* The facts that do NOT go through SR0, under `_F` names so that every lane takes ONE source for the whole
     family (the coordinating lane, naming decision 2).  Each is the proved file's lemma at this section's
     variables, nothing re-proved. *)
  Definition STW0_F := STW0.
  Definition HA1_F := HA1.
  Definition app_range_F := app_range.
  Definition mrd_w1_F := mrd_w1.
  Definition mrd_wn_ne_F := mrd_wn_ne.
  Definition bytes_keep_out_F := bytes_keep_out.
  Definition inside_appl_F := inside_appl.
  Definition zeqb_addcancel_F := zeqb_addcancel.
  Definition epi_addr_F := epi_addr.
  Definition ebw_sub0_F := ebw_sub0.
  Definition win_shadow0_F := win_shadow0.

  (* reac_box_model_block_base.v:441 fk_facts, RE-PROVED here: its text uses SR0, which route (C) narrowed, so
     the proved file's lemma cannot be re-imported by inst_exact.  The script is the proved one; only the last
     bullet changes, where the writability of the frame's eight shadow bytes now needs, besides
     rt_app_shadow, the MEMBERSHIP of each byte in R: the real-stack frame [A - 64, A) lies in the window, so its
     shadow is in R's first disjunct (sh_word_on (S - K) K); the class-0 frame lies in the class-0 block, so its
     shadow is in R's second disjunct (asan_stack_malloc_shadow_R FS 0).  Nothing else of R is touched. *)
  Lemma fk_facts_F : forall fr f spc j n w56, FK fr f spc j n w56 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 64 -> app_mem (fr + i)) /\
    (fr + 64 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 8 -> wview rsegs m (wa (fr / 8 + off + i)) <> None) /\
    2147450880 <= fr / 8 + off /\ fr / 8 + off + 8 <= 17594333495296.
  Proof.
    hide_sec.
    intros fr f spc j n w56 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & HFS & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
                (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
                (forall i, 0 <= i < 64 -> app_mem (fr + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. pose proof AW0 as AW0'. destruct AW0' as (_ & _ & _ & AW).
        pose proof (proj1 (AW (A - 64 + i - (bv_unsigned sp - 4272)) ltac:(lia))) as APw.
        replace (bv_unsigned sp - 4272 + (A - 64 + i - (bv_unsigned sp - 4272))) with (A - 64 + i) in APw by lia.
        exact APw.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
        change (2 ^ 0) with 1 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr 64 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 8 -> fr / 8 + off + i = shadow_addr (fr + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. rewrite Hoff. lia. }
    (* the membership of the frame's shadow bytes in R, per FK arm *)
    assert (RMEM : forall i, 0 <= i < 8 ->
              C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb (shadow_addr (fr + 8 * i))).
    { intros i Hi. unfold C_ON.reac_box_model_block_shadow_R.
      destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
      - left. unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr, ASAN_K,
          REAC_BOX_MODEL_BLOCK_K. subst fr. split; [lia|]. Z.div_mod_to_equations. lia.
      - right. left. unfold asan_stack_malloc_shadow_R, shadow_addr, ASAN_K. subst fr.
        unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
        change (2 ^ 0) with 1 in *. Z.div_mod_to_equations. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi.
      exact (proj1 (SR0 _ (RMEM i Hi) (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - rewrite Hoff. unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  (* reac_box_model_block_base.v:1037 epi_state, RE-PROVED under the narrowed SR0 (it used SR0 at :1051).  ONE
     conjunct changes, the second: `shadow_rw m''` becomes the region transport
     `forall P, shadow_rw_on P m -> shadow_rw_on P m''`, which is shadow_rw_mono's own proof carried through the
     guard P and needs no shadow premise at all (wmono + rd_mono suffice).  The order of the four conjuncts is
     the proved file's, so a caller destructs it as (ACm & SWm & FPm & TLm).  br_ac and br_fp do not use SR0 and
     stay re-imported from the proved file. *)
  Lemma epi_state_F : forall fr f spc j n w56 (m'' : word -> option byte) (h'' : word) (flags'' : list byte),
    FK fr f spc j n w56 ->
    munch (EBW fr j n) m m'' -> wmono rsegs m m'' -> rd_mono m m'' ->
    bytes_at rsegs m'' (fs_hint FS 0%nat) (le8 h'') ->
    bytes_at rsegs m'' (fs_flag FS 0%nat 0) flags'' -> Z.of_nat (length flags'') = fs_M 0%nat ->
    Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'' ->
    asan_cells m'' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m'') /\
    fp [0%nat] m'' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) /\
    reac_box_model_block_tls m'' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Proof.
    hide_sec.
    intros fr f spc j n w56 m'' h'' flags'' HK MU WM RM Hint Hflags Hlen HF01.
    pose proof (ebw_sub fr f spc j n w56 HK) as SUB.
    split; [exact (br_ac (EBW fr j n) m'' MU SUB)|].
    split; [intros P HPp a Ha Hin; destruct (HPp a Ha Hin) as [Hv Hb];
            split; [exact (WM _ Hv) | exact (RM _ Hb)]|].
    split.
    - exact (br_fp (EBW fr j n) m'' h'' flags'' MU WM RM SUB Hint Hflags Hlen HF01).
    - unfold reac_box_model_block_tls, REAC_BOX_MODEL_BLOCK_K. intros DT TS C T DB k HT.
      unfold reac_box_model_block_X in SUB.
      exact (acl_tls_ret [0%nat] m m'' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o)
               [(shadow_addr (bv_unsigned sp - 4272), shadow_addr (bv_unsigned sp))] (EBW fr j n)
               FP0 TLS0 MU SUB DT TS C T DB k HT).
  Qed.


  (* reac_box_model_block_base.v:1077 win_sh_out, :1127 epi_shadow0 and :1162 epi_flags, RE-PROVED: their scripts
     apply fk_facts, so the proved versions are generalized over the universal SR0 and cannot be re-imported.
     The statements are the proved ones VERBATIM and the scripts are the proved ones with `fk_facts` replaced by
     `fk_facts_F`; nothing else changes, and none of the three uses the shadow premise itself. *)
  Lemma win_sh_out_F : forall fr f spc j n w56 x, FK fr f spc j n w56 ->
    bv_unsigned sp - 4272 <= x < bv_unsigned sp -> ~ (fr <= x < fr + 64) ->
    outside (EBW fr j n) (shadow_addr x).
  Proof.
    hide_sec. clear ebw_sub br_ac br_fp epi_addr ebw_sub0 win_shadow0 bytes_keep_out.
    intros fr f spc j n w56 x HK Hxw Hxfr.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hapx : app_mem x).
    { pose proof (acl_app_in m (bv_unsigned sp - 4272) 4272 (x - (bv_unsigned sp - 4272)) AW0 ltac:(lia)) as H.
      replace (bv_unsigned sp - 4272 + (x - (bv_unsigned sp - 4272))) with x in H by lia. exact H. }
    pose proof (rt_app_shadow x Hapx) as Hsh.
    assert (Hylo : LOWMEM_END <= shadow_addr x).
    { clear -Hsh. unfold in_shadow in Hsh. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    assert (Hyhi : shadow_addr x < HIGHMEM_BEG).
    { clear -Hsh. unfold in_shadow in Hsh. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    unfold LOWMEM_END in Hylo. unfold HIGHMEM_BEG in Hyhi.
    destruct (fk_facts_F fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Hn : 0 <= n <= 1) by (destruct HK as [(_ & _ & _ & _ & En) | (_ & _ & _ & _ & _ & En)]; lia).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & _ & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4.
    pose proof (P4 FS ltac:(lia)) as AFS. pose proof (P4 (FS + 7) ltac:(lia)) as AFS7.
    assert (Efl : fs_flag FS 0 j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (Aflag : app_mem (fs_flag FS 0 j)).
    { rewrite Efl. apply P4. destruct HK as [(_ & _ & _ & Ej & _) | (Hj & _)].
      - subst j; lia.
      - unfold fs_M in Hj; cbn [Z.of_nat] in Hj; change (2 ^ (14 - 0)) with 16384 in Hj; lia. }
    pose proof (FAP 0%Z ltac:(lia)) as AFr. rewrite Z.add_0_r in AFr.
    pose proof (FAP 63 ltac:(lia)) as AFr63.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AFS, AFS7, Aflag, AFr, AFr63.
    unfold B.EBW, B.Wf. apply fl_out_app.
    - cbn [outside]. split; [clear -Hyhi HHM'; lia|].
      split; [clear -Hylo Hyhi AFS AFS7; lia|].
      split; [clear -Hylo Hyhi Aflag Hn; lia|].
      split; [clear -Hylo Hyhi AFr AFr63; lia|].
      split; [|exact I].
      pose proof (acl_win_sh x fr (fr + 64) FR8 Hxfr) as HW.
      pose proof (sh_add8 fr 8 FR8) as E. replace (fr + 8 * 8) with (fr + 64) in E by lia.
      rewrite E in HW. exact HW.
    - remember ((p =? 0) || (o =? 0)) as bb eqn:Eo. destruct bb; [exact I|].
      symmetry in Eo. apply orb_false_iff in Eo. destruct Eo as [_ Eo].
      apply Z.eqb_neq in Eo.
      unhide AO. destruct (AO Eo) as (AOa & _ & _).
      pose proof (acl_app_in m o 32 0 AOa ltac:(lia)) as Ao0. rewrite Z.add_0_r in Ao0.
      pose proof (acl_app_in m o 32 31 AOa ltac:(lia)) as Ao31.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ao0, Ao31.
      cbn [outside]. split; [clear -Hylo Hyhi Ao0 Ao31; lia | exact I].
  Qed.

  Lemma epi_shadow0_F : forall fr f spc j n w56 (m'' : word -> option byte),
    FK fr f spc j n w56 ->
    munch (EBW fr j n) m m'' ->
    (f = 0 -> forall x, A - 64 <= x < A -> mrd rsegs m'' (wa (shadow_addr x)) = Some (Z_to_bv 8 0)) ->
    forall i, 0 <= i < 4272 ->
      mrd rsegs m'' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0).
  Proof.
    hide_sec.
    intros fr f spc j n w56 m'' HK MU FR0sh i Hi.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    set (x := bv_unsigned sp - 4272 + i).
    assert (Hax : app_mem x) by (exact (acl_app_in m (bv_unsigned sp - 4272) 4272 i AW0 Hi)).
    assert (Hxb : 0 <= shadow_addr x < 2 ^ 64)
      by (pose proof (rt_shadow_bound (shadow_addr x) (rt_app_shadow x Hax)) as HB; clear -HB; lia).
    assert (DEC : (f = 0 /\ A - 64 <= x < A) \/ ~ (fr <= x < fr + 64)).
    { destruct HK as [(Ef & Efr & _) | (Hj & Efr & Ef & _)].
      - destruct (Z_le_dec (A - 64) x) as [D1|D1]; destruct (Z_lt_dec x A) as [D2|D2];
          [left; split; [exact Ef | lia] | right; subst fr; lia | right; subst fr; lia | right; subst fr; lia].
      - right. subst fr.
        pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & HFS & _). unfold FS_SIZE in HFS.
        unfold fs_frame, fs_B, fs_M in *; cbn [Z.of_nat] in *.
        change (2 ^ (14 - 0)) with 16384 in Hj. change (2 ^ 0) with 1 in *.
        unfold x; clear -HFS Hj Hi; lia. }
    destruct DEC as [[Ef Hxf] | Hnf].
    - exact (FR0sh Ef x Hxf).
    - assert (OUT : outside (EBW fr j n) (shadow_addr x))
        by (apply (win_sh_out_F fr f spc j n w56); [exact HK | unfold x; lia | exact Hnf]).
      pose proof (MU (wa (shadow_addr x))) as Heq.
      rewrite wa_unsigned in Heq by exact Hxb. specialize (Heq OUT).
      replace (mrd rsegs m'' (wa (shadow_addr x))) with (mrd rsegs m (wa (shadow_addr x)))
        by (unfold mrd; rewrite Heq; reflexivity).
      unfold x. exact (win_shadow0 i Hi).
  Qed.

  Lemma epi_flags_F : forall fr f spc j n w56 (m'' : word -> option byte),
    FK fr f spc j n w56 ->
    munch (EBW fr j n) m m'' ->
    (n = 1 -> mrd rsegs m'' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    exists flags'', bytes_at rsegs m'' (fs_flag FS 0 0) flags'' /\
      Z.of_nat (length flags'') = fs_M 0 /\
      Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags''.
  Proof.
    hide_sec. clear ebw_sub br_ac br_fp epi_addr ebw_sub0 win_shadow0 bytes_keep_out.
    intros fr f spc j n w56 m'' HK MU Hrel.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & HT & HTP & HPl & H88 & H96 & HCL & HFS & HApp & HWd & HDd).
    unfold FS_SIZE in HFS. pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4.
    apply Forall_inv in HCL. destruct HCL as (_ & hm & flags_m & _ & Hflm & Hlen & Hforall).
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (Ef0 : fs_flag FS 0 0 = FS + 4096) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (Efl : fs_flag FS 0 j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    destruct (fk_facts_F fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Hn : 0 <= n <= 1) by (destruct HK as [(_ & _ & _ & _ & En) | (_ & _ & _ & _ & _ & En)]; lia).
    assert (FOUT : forall x, fs_flag FS 0 0 <= x < fs_flag FS 0 0 + fs_M 0 ->
              ~ (fs_flag FS 0 j <= x < fs_flag FS 0 j + n) -> outside (EBW fr j n) x).
    { intros x Hx Hxj. rewrite Ef0, EM in Hx.
      assert (Hxapp : app_mem x) by (apply P4; lia).
      assert (OW : outside (reac_box_model_block_W o (bv_unsigned sp)) x).
      { apply (fl_dj_out (reac_box_model_block_W o (bv_unsigned sp))
                 (fp_tls (bv_unsigned tp) DT TS C T DB k0 ++ [(FS, fs_frame FS 0 0)]) FS (fs_frame FS 0 0) x HWd).
        - apply in_or_app; right; left; reflexivity.
        - rewrite EFR0; lia. }
      unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in OW. cbn [outside] in OW. destruct OW as [OWwin OWo].
      unfold B.EBW, B.Wf. apply fl_out_app.
      - cbn [outside]. split; [exact OWwin|].
        split; [clear -Hx; lia|].
        split; [exact Hxj|].
        split; [clear -Hx FRlo; lia|].
        split; [|exact I].
        pose proof (FAP 0%Z ltac:(lia)) as AFr. rewrite Z.add_0_r in AFr.
        pose proof (rt_app_shadow fr AFr) as Hfrsh.
        pose proof (FAP 56 ltac:(lia)) as AFr56.
        pose proof (rt_app_shadow (fr + 56) AFr56) as Hfrsh2.
        pose proof (sh_add8 fr 7 FR8) as E7. replace (fr + 8 * 7) with (fr + 56) in E7 by lia.
        rewrite E7 in Hfrsh2.
        assert (Hfrlo : LOWMEM_END <= shadow_addr fr)
          by (clear -Hfrsh; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia).
        assert (Hfrhi : shadow_addr fr + 7 < HIGHMEM_BEG)
          by (clear -Hfrsh2; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia).
        unfold LOWMEM_END in Hfrlo. unfold HIGHMEM_BEG in Hfrhi.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxapp.
        clear -Hfrlo Hfrhi Hxapp. lia.
      - remember ((p =? 0) || (o =? 0)) as bq eqn:Eq. destruct bq; [exact I|].
        symmetry in Eq. apply orb_false_iff in Eq. destruct Eq as [_ Eq]. rewrite Eq in OWo. exact OWo. }
    assert (MRDeq : forall x, fs_flag FS 0 0 <= x < fs_flag FS 0 0 + fs_M 0 ->
              ~ (fs_flag FS 0 j <= x < fs_flag FS 0 j + n) -> mrd rsegs m'' (wa x) = mrd rsegs m (wa x)).
    { intros x Hx Hxj. pose proof (MU (wa x)) as Heq.
      rewrite wa_unsigned in Heq by (rewrite Ef0, EM in Hx; clear -Hx P1 HFS HAE'; lia).
      specialize (Heq (FOUT x Hx Hxj)). unfold mrd. rewrite Heq. reflexivity. }
    assert (Hlenn : length flags_m = Z.to_nat (fs_M 0)) by (rewrite <- Hlen; rewrite Nat2Z.id; reflexivity).
    rewrite EM in Hlenn.
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
    - subst n. exists flags_m. split; [|split; [exact Hlen | exact Hforall]].
      apply (B.bytes_keep m m'' _ flags_m Hflm). intros x Hx. rewrite Hlen in Hx.
      apply MRDeq; [exact Hx | clear; lia].
    - subst n.
      assert (Hjlt : (Z.to_nat j < length flags_m)%nat).
      { rewrite Hlenn. unfold fs_M in Hj; cbn [Z.of_nat] in Hj.
        change (2 ^ (14 - 0)) with 16384 in Hj. lia. }
      exists (upd_bytes flags_m (Z.to_nat j) [Z_to_bv 8 0]).
      destruct Hflm as (Ha & Hl & Hh).
      split; [|split].
      + split; [exact Ha|]. split; [rewrite upd_bytes_length by (cbn [length]; lia); exact Hl|].
        intros k Hk. rewrite upd_bytes_length in Hk by (cbn [length]; lia).
        rewrite upd_bytes_nth by (cbn [length]; lia).
        change (@length byte [Z_to_bv 8 0]) with 1%nat.
        destruct ((Z.to_nat j <=? k)%nat && (k <? Z.to_nat j + 1)%nat)%bool eqn:Ec.
        * apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec2].
          apply Nat.leb_le in Ec1. apply Nat.ltb_lt in Ec2.
          assert (Ekj : k = Z.to_nat j) by lia. subst k. rewrite Nat.sub_diag. cbn [nth_error].
          replace (fs_flag FS 0 0 + Z.of_nat (Z.to_nat j)) with (fs_flag FS 0 j)
            by (rewrite Z2Nat.id by lia; rewrite Ef0, Efl; lia).
          exact (Hrel eq_refl).
        * rewrite <- (Hh k Hk). apply MRDeq.
          { rewrite Ef0, EM. rewrite Hlenn in Hk. clear -Hk. lia. }
          { rewrite Ef0, Efl. apply andb_false_iff in Ec.
            assert (k <> Z.to_nat j).
            { destruct Ec as [E|E]; [apply Nat.leb_nle in E | apply Nat.ltb_nlt in E]; lia. }
            assert (Z.of_nat k <> j) by (rewrite <- (Z2Nat.id j) by lia; clear -H; lia).
            clear -H0. lia. }
      + rewrite upd_bytes_length by (cbn [length]; lia). exact Hlen.
      + apply Forall_forall. intros y Hy. apply In_nth_error in Hy. destruct Hy as [i Hi].
        assert (Hib : (i < length flags_m)%nat).
        { rewrite <- (upd_bytes_length flags_m (Z.to_nat j) [Z_to_bv 8 0]) by (cbn [length]; lia).
          apply nth_error_Some. rewrite Hi; discriminate. }
        rewrite upd_bytes_nth in Hi by (cbn [length]; lia).
        change (@length byte [Z_to_bv 8 0]) with 1%nat in Hi.
        destruct ((Z.to_nat j <=? i)%nat && (i <? Z.to_nat j + 1)%nat)%bool.
        * destruct (i - Z.to_nat j)%nat as [|nn]; cbn [nth_error] in Hi;
            [injection Hi as <-; left; reflexivity | destruct nn; discriminate].
        * rewrite Forall_forall in Hforall. apply Hforall. apply nth_error_In in Hi. exact Hi.
  Qed.

  (* reac_box_model_block_base.v:716 JR and its two lemmas (JR_m used SR0 at :724; jr_win's premise JR carries
     the universal shadow_rw, which route (C) forbids), with the same change: the shadow conjunct is the region
     transport from the section memory m. *)
  Definition JR_F (m' : word -> option byte) : Prop :=
    asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\
    addressable m' (bv_unsigned sp - 4272) 4272 /\
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) /\
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp).

  Lemma JR_m_F : JR_F m.
  Proof.
    hide_sec.
    split; [exact AC0|]. split; [intros P HPp; exact HPp|]. split; [exact AW0|].
    split; [exact FP0 | exact TLS0].
  Qed.

  Lemma jr_win_F : forall W' m1 m2, JR_F m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 ->
    sub_fp W' [(bv_unsigned sp - 4272, bv_unsigned sp)] -> JR_F m2.
  Proof.
    hide_sec.
    intros W' m1 m2 (AC & SW & AW & FP & TL) MU WM Hs.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' (bv_unsigned sp - 4272) (bv_unsigned sp) x Hs HHM Hx)).
    unfold JR_F, reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in *.
    split; [|split; [|split; [|split]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' (bv_unsigned sp - 4272) (bv_unsigned sp) x Hs).
      left. clear -Hx HHM'. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - (* the region transport across the window write: a shadow byte is outside W' (SHo) *)
      intros P HPp a Ha Hin. destruct (SW P HPp a Ha Hin) as [Hv Hb]. split; [exact (WM _ Hv)|].
      destruct Hb as (bb & Hbb). exists bb. unfold mrd in *.
      assert (Hb64 : bv_unsigned (wa a) = a).
      { unfold wa. apply unsigned_lit.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. lia. }
      rewrite (MU (wa a) ltac:(rewrite Hb64; exact (SHo _ Hin))). exact Hbb.
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_fp [0%nat] m1 m2 (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (if o =? 0 then [] else [(o, o + 32)]) (reac_box_model_block_D p o) W' FP MU WM Hs).
    - exact (fl_tls [0%nat] m1 m2 (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (if o =? 0 then [] else [(o, o + 32)]) (reac_box_model_block_D p o) W'
               (fp_w [0%nat] FS ++ [(shadow_addr (bv_unsigned sp - 4272), shadow_addr (bv_unsigned sp))]) FP MU Hs TL).
  Qed.

  (* The class-0 frame area [fs_frame FS 0 0, + 2^20) in rng form: the third range of fp_w [0%nat] FS, so the
     second of tl (fp_w [0%nat] FS) (RFSw); its bounds from fs_place. *)
  Lemma RFSf_F : rng RNG (fs_frame FS 0%nat 0) 1048576.
  Proof.
    hide_sec.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5).
    assert (FShi : FS + FS_SIZE <= 2^64).
    { pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A2. lia. }
    pose proof RFSw as RW. unfold rng_ivls, fp_w, fp_w1 in RW. cbn [flat_map app tl] in RW.
    apply Forall_cons_iff in RW as [_ RW].
    apply Forall_cons_iff in RW as [R3 _]. cbn [fst snd] in R3.
    assert (E0 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (E1 : fs_frame FS 0%nat (fs_M 0%nat) = FS + 36864 + 1048576) by (unfold fs_frame, fs_M, fs_B; cbn; lia).
    rewrite E0, E1 in R3. rewrite E0. unfold FS_SIZE in FShi.
    split; [lia|]. split; [lia|]. intros b0 j0 Hb Hj. apply R3; lia.
  Qed.

  (* The frame and its eight shadow bytes are in the footprint: the real-stack frame and its shadow lie in the
     window and in the window's shadow cover, the class-0 frame and its shadow in the class-0 frame area and in the
     shadow of the class-0 frames. *)
  Lemma fk_rng_F : forall fr f spc j n w56, FK fr f spc j n w56 ->
    rng RNG fr 64 /\ rng RNG (fr / 8 + off) 8.
  Proof.
    hide_sec.
    intros fr f spc j n w56 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & HFS & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    unfold sh_cover, shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K in Rwsh.
    unfold REAC_BOX_MODEL_BLOCK_K in Rwin.
    assert (ESH0 : fs_M 0%nat * fs_B 0%nat / 8 = 131072) by reflexivity.
    assert (EFR0 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    rewrite ESH0, EFR0 in RFSsh. unfold shadow_addr, ASAN_K in RFSsh.
    pose proof RFSf_F as RFf. rewrite EFR0 in RFf.
    rewrite Hoff. unfold ASAN_K.
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
    - split.
      + eapply rng_sub'; [exact Rwin|]. lia.
      + eapply rng_sub'; [exact Rwsh|]. Z.div_mod_to_equations. lia.
    - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
      change (2 ^ 0) with 1 in *.
      split.
      + eapply rng_sub'; [exact RFf|]. lia.
      + eapply rng_sub'; [exact RFSsh|]. Z.div_mod_to_equations. lia.
  Qed.

  (* reac_box_model_block_base.v's KB, the body obligation at 0x85c48, over StepF, with two changes the cgif glue
     needs (the coordinating lane, 2026-10-29):
     - the ra slot is QUANTIFIED (ra'): x1 is not callee-saved, so cgif's allocator rule does not fix it after the
       call, and no instruction of [0x85bbc .. the epilogue reload of ra] reads it (the proved run passes it on as
       the x1 binder of reac_box_model_block_binv.v:567 exit_r);
     - the post Q is INDEXED by the FK data of the run (fr f spc j n w56), so that a caller may conclude it for
       the frame cgif allocated only.  Q := fun _ _ _ _ _ _ => Q0 gives the proved run's form back. *)
  Definition KB_F (Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc ->
      evtF rsegs RNG (Q fr f spc j n w56)
        (MS (mkR ra' (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                 (Z_to_bv 64 b) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x85c48) fc None mc (seg_rom rsegs)).

  (* The facts the proved run holds at reac_box_model_block_base.v:599, before `eapply evt_cut`: the memory m1 at
     the call `jal __asan_stack_malloc_0` (0x85bb8).  asan_cells and shadow_rw are the two the proof derives there
     for the allocator (fl_asan_cells, shadow_rw_mono); fp carries the side-stack and thread-cell facts. *)
  Definition bmb_at_call (m1 : word -> option byte) : Prop :=
    munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\
    mem_inv rsegs m1 /\ asan_cells m1 /\
    (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m1) /\
    stk rsegs m1 (bv_unsigned sp - 4272) (bv_unsigned sp + -104) /\
    rw_cells rsegs m1 (bv_unsigned sp + -104) SAVES /\
    fp [0%nat] m1 (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).

  (* The glue instantiates the Section memory m at the normalized post-call memory and applies entry_post_F with
     m1 = m2 = m: bmb_at_call is then the Section's own facts plus the saved registers in the frame (the three
     relations are reflexive).  Nothing else of bmb_at_call has to be supplied. *)
  Lemma bmb_at_call_refl : rw_cells rsegs m (bv_unsigned sp + -104) (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    bmb_at_call m.
  Proof.
    hide_sec.
    intros SV. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    unfold bmb_at_call.
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply rd_mono_refl|].
    split; [exact MI0|]. split; [exact AC0|]. split; [intros P HPp; exact HPp|].
    split; [exact (proj1 (stk_split rsegs m _ (bv_unsigned sp + -104) _ ST0 ltac:(lia)))|].
    split; [exact SV | exact FP0].
  Qed.

  (* The side-stack (fake-frame) arm of asan_stack_malloc_post at the return 0x85bbc, as the proved run uses it at
     reac_box_model_block_base.v:672-711: the class-0 frame index jj, the allocator's post facts at m2 and the
     conjuncts of asan_stack_malloc_frame (asan_stack_malloc_c.v:53-66) at c = 0, K = ASAN_STACK_MALLOC_K,
     sp = Z_to_bv 64 A, L = 64 (so B = fs_B 0 = 64 and n = fs_shadow_n 0 64 = 8), j = jj, a0 = Z_to_bv 64 fr.
     DIFF to asan_stack_malloc_frame, and the only one: the conjunct `bytes_at rsegs m2 (fr + 24) (le8 sp)` is
     DROPPED (cgif's aj_stack_malloc_atS does not give that frame word; the re-run uses it nowhere, the
     readability of [fr + 24, fr + 32) comes from the frame's own stk, STF below).  The `(6 <= c)%nat -> ...`
     conjunct is dropped as vacuous at c = 0.  The real-stack arm is dead under cgif's allocator invariant. *)
  Definition bmb_at_ret (jj : Z) (m1 m2 : word -> option byte) : Prop :=
    0 <= jj < fs_M 0%nat /\
    wmono rsegs m1 m2 /\ mem_inv rsegs m2 /\ stk rsegs m2 (bv_unsigned sp - 4272) A /\
    fs_place m2 FS /\ (exists h2, bytes_at rsegs m2 (fs_hint FS 0%nat) (le8 h2)) /\
    fs_frame FS 0%nat jj mod 64 = 0 /\
    bytes_at rsegs m2 (fs_flag FS 0%nat jj) [Z_to_bv 8 1] /\
    bytes_at rsegs m2 (fs_frame FS 0%nat jj + 64 - 8) (le8 (Z_to_bv 64 (fs_flag FS 0%nat jj))) /\
    bytes_at rsegs m2 (shadow_addr (fs_frame FS 0%nat jj)) (repeat (Z_to_bv 8 0) (Z.to_nat 8)) /\
    addressable m2 (fs_frame FS 0%nat jj) 64 /\
    stk rsegs m2 (fs_frame FS 0%nat jj) (fs_frame FS 0%nat jj + 64) /\
    (forall a, fs_frame FS 0%nat jj <= a < fs_frame FS 0%nat jj + 64 -> app_mem a) /\
    FS <= fs_frame FS 0%nat jj /\ fs_frame FS 0%nat jj + 64 <= FS + FS_SIZE /\
    ASAN_GT <= fs_frame FS 0%nat jj /\ fs_frame FS 0%nat jj + 64 <= A - ASAN_STACK_MALLOC_K /\
    (forall (c' : nat) (j' : Z), (c' <= 10)%nat -> 0 <= j' < fs_M c' -> (c' <> 0%nat \/ j' <> jj) ->
       fs_frame FS c' j' + fs_B c' <= fs_frame FS 0%nat jj \/
       fs_frame FS 0%nat jj + 64 <= fs_frame FS c' j') /\
    munch [(fs_hint FS 0%nat, fs_hint FS 0%nat + 8); (fs_flag FS 0%nat jj, fs_flag FS 0%nat jj + 1);
           (fs_frame FS 0%nat jj + 24, fs_frame FS 0%nat jj + 32);
           (fs_frame FS 0%nat jj + 64 - 8, fs_frame FS 0%nat jj + 64);
           (shadow_addr (fs_frame FS 0%nat jj), shadow_addr (fs_frame FS 0%nat jj) + 8);
           (A - ASAN_STACK_MALLOC_K, A)] m1 m2.

  (* bmb_at_ret at m1 = m2 = m (the glue instantiates the Section memory at the normalized post-call memory)
     from the glue's own premises only: the frame index, the flag byte, the flag-pointer word at fr + 56, the
     frame's zero shadow, addressable and stk.  Every other conjunct comes from the Section facts: mem_inv MI0,
     ST0, and FP0 (fs_place: FS's alignment, ASAN_GT <= FS, app_mem and stk over the side stack; the class list:
     the hint word; HFS: FS + FS_SIZE <= sp - 4272). *)
  Lemma bmb_at_ret_of : forall jj,
    0 <= jj < fs_M 0%nat ->
    bytes_at rsegs m (fs_flag FS 0%nat jj) [Z_to_bv 8 1] ->
    bytes_at rsegs m (fs_frame FS 0%nat jj + 56) (le8 (Z_to_bv 64 (fs_flag FS 0%nat jj))) ->
    bytes_at rsegs m (shadow_addr (fs_frame FS 0%nat jj)) (repeat (Z_to_bv 8 0) 8%nat) ->
    addressable m (fs_frame FS 0%nat jj) 64 ->
    stk rsegs m (fs_frame FS 0%nat jj) (fs_frame FS 0%nat jj + 64) ->
    bmb_at_ret jj m m.
  Proof.
    hide_sec.
    intros jj Hjj HFL H56 HSH HADD STF.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & HT & HTP & HPl & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0.
    destruct HCL0 as [(_ & h & flags & HH & HF & HFl & HFb) _].
    assert (EM0 : fs_M 0%nat = 16384) by reflexivity. rewrite EM0 in Hjj.
    assert (Efr : fs_frame FS 0%nat jj = FS + 36864 + 64 * jj)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    unfold bmb_at_ret, ASAN_STACK_MALLOC_K, ASAN_GT, FS_SIZE.
    split; [rewrite EM0; exact Hjj|]. split; [apply wmono_refl|]. split; [exact MI0|].
    split; [exact (proj1 (stk_split rsegs m _ A _ ST0 ltac:(lia)))|].
    split; [exact HPl|]. split; [exists h; exact HH|].
    split; [rewrite Efr; Z.div_mod_to_equations; lia|].
    split; [exact HFL|].
    split; [replace (fs_frame FS 0%nat jj + 64 - 8) with (fs_frame FS 0%nat jj + 56) by lia; exact H56|].
    split; [exact HSH|]. split; [exact HADD|]. split; [exact STF|].
    split; [intros a Ha; apply P4; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split.
    - intros c' j' Hc' Hj' Hne.
      destruct (Nat.eq_dec c' 0%nat) as [Ec|Ec].
      + subst c'. rewrite EM0 in Hj'.
        assert (Ej : fs_frame FS 0%nat j' = FS + 36864 + 64 * j')
          by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        assert (Hjne : j' <> jj) by (destruct Hne as [Hc|Hj]; [exfalso; apply Hc; reflexivity | exact Hj]).
        rewrite Ej, Efr. replace (fs_B 0%nat) with 64 by reflexivity. lia.
      + right.
        assert (Hc1 : 1 <= Z.of_nat c') by lia.
        assert (Ej : fs_frame FS c' j' = FS + 36864 + Z.of_nat c' * 2 ^ 20 + j' * fs_B c')
          by reflexivity.
        assert (HB0 : 0 <= fs_B c') by (unfold fs_B; apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]).
        assert (Hj0 : 0 <= j' * fs_B c') by (apply Z.mul_nonneg_nonneg; lia).
        rewrite Ej, Efr. change (2 ^ 20) with 1048576.
        assert (Hc20 : 1048576 <= Z.of_nat c' * 1048576) by nia.
        lia.
    - apply munch_refl.
  Qed.

  Ltac bi_intro H :=
    let MU := fresh "MU" in let WM := fresh "WM" in let RM := fresh "RM" in let MI := fresh "MI" in
    let SV := fresh "SV" in let HH := fresh "HH" in let hh := fresh "h" in let F56 := fresh "F56" in
    destruct H as (MU & WM & RM & MI & SV & (hh & HH) & F56).

  Ltac wv_tac :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first [ match goal with
            | STW : forall a, bv_unsigned sp - 4272 <= a < bv_unsigned sp -> wview rsegs m (wa a) <> None |- _ =>
                apply STW; lia
            end
          | apply STW0; lia
          | match goal with
            | FW : forall i, 0 <= i < 64 -> wview rsegs m (wa (?fr + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (fr + (x - fr)) by lia; apply FW; lia
            end
          | match goal with
            | SW : forall i, 0 <= i < 8 -> wview rsegs m (wa (?s + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (s + (x - s)) by lia; apply SW; lia
            end ].

  Ltac wst a n :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ wv_tac | eassumption | lia | lia ])
    end.

  (* +0xa8 .. +0x100: the frame words and the frame's shadow. *)
  Lemma fwords_F : forall fr f spc j n w56 mc
      (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop),
    FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc -> KB_F Q ->
    evtF rsegs RNG (Q fr f spc j n w56)
      (MS (mkR ra' (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
               a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
               (Z_to_bv 64 b) (Z_to_bv 64 fr) s8 (wa off) s10 s11
               t3' t4' t5' t6') F (Z_to_bv 64 0x85bec) fc None mc (seg_rom rsegs)).
  Proof.
    hide_sec.
    intros fr f spc j n w56 mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HK HB K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts_F fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (fk_rng_F fr f spc j n w56 HK) as (RFR & RSH).
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & HFS & _).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'. pose proof HPl as (P1 & P2 & P3 & P4 & P5).
    unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    pose proof (app_range FS 8 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    pose proof HB as HB'. bi_intro HB'. unfold B.Wf, shadow_addr in MU.
    assert (Hspc : 0 <= spc < 2 ^ 64) by lia.
    assert (HS1 : store_ok rsegs mc (wa (A + 8)) 8 = true)
      by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia | exact WM | lia | lia]).
    step. store_done.
    do 8 step.
    wst fr 8%nat. step. store_done.
    wst (fr + 8) 8%nat. step. store_done.
    wst (fr + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
    wst (fr / 8 + off + 4) 1%nat. step. store_done.
    wst (fr / 8 + off + 5) 1%nat. step. store_done.
    wst (fr / 8 + off + 6) 1%nat. step. store_done.
    wst (fr / 8 + off + 7) 1%nat. step. store_done.
    step.
    wst (fr / 8 + off) 1%nat. step. store_done.
    wst (fr / 8 + off + 1) 1%nat. step. store_done.
    wst (fr / 8 + off + 2) 1%nat. step. store_done.
    wst (fr / 8 + off + 3) 1%nat. step. store_done.
    eapply K; [exact HK|].
    split; [unfold B.Wf, shadow_addr; exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  (* S1: [0x85b44 .. 0x85bb8), the prologue, the frame carve, the GOT reads (CELL_K, UAR) and the argument of the
     allocator call; it ends in the continuation KC at the state of the jal. *)
  Lemma entry_pre_F : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m ->
    (forall (a1' a2' : word) (m1 : word -> option byte), bmb_at_call m1 ->
       evtF rsegs RNG Q (MS (mkR ra (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A)
                          (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                          (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x85bb8) fc None m1 (seg_rom rsegs))) ->
    evtF rsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    hide_sec.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 KC.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof STW0 as STW.
    unfold REAC_BOX_MODEL_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    assert (MU : munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    rewrite <- Hoff in CK.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (bv_unsigned sp - 160) _ ST0c ltac:(lia)) as [STa STb].
    clear ST0c.
    carve_frame 104%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (bv_unsigned sp + -160)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (bv_unsigned sp - 160) (bv_unsigned sp + -104)); [exact STb | lia]. }
    step. store_done.
    do 13 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; rewrite HA; f_equal; f_equal; lia).
    rewrite EA.
    do 11 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* the side-stack state at m1 *)
    pose proof (fl_fp [0%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    pose proof (stk_merge rsegs m1 _ _ _ STa STb ltac:(lia)) as STc.
    eapply KC. unfold bmb_at_call.
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|].
    split; [exact (fl_asan_cells _ m m1 AC0 MU
      ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I]))|].
    split; [intros P HPp a Ha Hs; destruct (HPp a Ha Hs) as (Hv & Hb);
             split; [apply WM, Hv | apply RM, Hb]|].
    split; [exact STc|]. split; [exact FR | exact FP1].
  Qed.

  (* S2's head: [0x85bbc .. 0x85bec) on the side-stack (fake-frame) arm, then fwords_F and the body obligation. *)
  Lemma entry_post_F : forall jj (m1 m2 : word -> option byte)
      (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop),
    bmb_at_call m1 -> bmb_at_ret jj m1 m2 -> KB_F Q ->
    evtF rsegs RNG (Q (fs_frame FS 0%nat jj) (fs_frame FS 0%nat jj) A jj 1
                      (Z_to_bv 64 (fs_flag FS 0%nat jj)))
      (MS (mkR ra' (Z_to_bv 64 A) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
               (Z_to_bv 64 (fs_frame FS 0%nat jj)) a1' a2' a3' a4' a5' a6' a7' s2
               (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa off) s10 s11
               t3' t4' t5' t6') F (Z_to_bv 64 0x85bbc) fc None m2 (seg_rom rsegs)).
  Proof.
    hide_sec.
    intros jj m1 m2 ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HC HR K.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold bmb_at_call in HC. unfold bmb_at_ret in HR.
    destruct HC as (MU & WM & RM & MI & AC1 & SR1 & STc & FR & FP1).
    destruct HR as (Hjj & WM2 & MI2 & ST2 & HP2 & (h2 & HH2) & Hm64 & HFL & H56 & HSH & HADD & STF & APF
                    & FSlo & FShi & GT & FRA' & DIS & MU2).
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm.
    pose proof FPm as (DT' & TS' & C' & T' & DB' & k' & _ & _ & HPm & _ & _ & _ & HFS & _).
    pose proof HPm as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2. rewrite Z.add_0_r in HH2.
    unfold ASAN_STACK_MALLOC_K in *.
    remember (fs_frame FS 0%nat jj) as fr eqn:Efr.
    unfold fs_hint in MU2. cbn [Z.of_nat] in MU2. rewrite Z.add_0_r in MU2.
    unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
    assert (EFl : fs_flag FS 0%nat jj = FS + 4096 + jj) by (unfold fs_flag; cbn; lia).
    assert (EM0 : fs_M 0%nat = 16384) by reflexivity.
    rewrite EM0 in Hjj.
    assert (SHb : shadow_addr fr + 8 <= bv_unsigned sp - 4272)
      by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
    assert (RM2 : rd_mono m1 m2).
    { apply (rd_mono_list _ _ _ MU2).
      repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
      - apply (rd_of_bytes _ _ _ HFL). cbn. lia.
      - apply (rd_of_stk _ _ _ STF). lia.
      - apply (rd_of_bytes _ _ _ H56). rewrite length_le8. cbn. lia.
      - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    assert (MU3 : munch (Wf fr jj 1) m m2).
    { apply (munch_trans _ m m1 m2).
      - eapply munch_weaken; [|exact MU]. unfold sub_fp, B.Wf. cbn [outside]. intros. repeat split; try exact I; lia.
      - eapply munch_weaken; [|exact MU2]. unfold sub_fp, B.Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
      ltac:(rewrite EFl; cbn [disjoint_from cells_size csize Nat.add B.SAVES]; lia)) as FR2.
    clear MU MU2 WM WM2 RM RM2 FR STc MI.
    step. step. step. step.
    rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
    eapply (fwords_F fr fr A jj 1 (Z_to_bv 64 (fs_flag FS 0%nat jj))); [right; repeat split; lia | | exact K].
    split; [exact MU3|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
    replace (fr + 56) with (fr + 64 - 8) by lia. assumption.
  Qed.
End MainF.
(* Audit rebuild 2026-10-29 (evidence rule, the coordinating lane 04:39Z). *)
