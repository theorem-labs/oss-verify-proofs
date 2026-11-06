(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 897 of its 911 lines of code are new or changed and 234 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_epi.v at a working branch d69f7c708f6 (proved v1.9 run of
   record) over lib/Lib/StepF: the script edits include `hide_sec.` in est, rd8_at, td_tail_F and epi_close_F, and footprint steps and a new closing in td_tail_F; the run lemma epi is re-proved in stretches split at the release (epi_pre_F, epi_post_F, bmb_KR_Q0) through new lemmas.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the epilogue 0x864c0 -> ret 0x86560 reads no
   image or runtime cell: it writes the release magic word at the ASan frame, the frame's eight shadow bytes and,
   on the side-stack arm, the class-0 flag byte, then restores the saved registers from its own window and
   returns; instruction fetch is not an access).

   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z):
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk. No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell. The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header (image root, ELF sha256, tool version, which compare) and goes to
      the auditor a Theorem Labs lane, who signs it against its proved run before it counts.
   5. A StepF "uncovered access" error means STOP: report it. Do not widen the footprint to make it pass.

   What is here (lane EPI of the 8-lane split):
   - bmb_KR Q / bmb_KR_Q0: the statement of reac_box_model_block_epi.epi (_epi.v:237-246) with Q0 generalized to
     a post INDEXED by the lemma's FK data, Q fr f spc j n w56, and evt rsegs replaced by evtF rsegs RNG;
     bmb_KR_Q0 : bmb_KR (fun _ _ _ _ _ _ => Q0) is epi_F, the whole original epi (both arms) over StepF.
     Every S2 file takes `Hypothesis HKR : bmb_KR Q` and applies HKR where the original applies epi; every _of_F
     corollary instantiates it with bmb_KR_Q0.
   - the release split at the allocator event `sb zero,0(a0)` at 0x864f8 (the fake-frame arm; cgif's allocator
     invariant fixes the UAR flag at 1, so the real-stack arm is dead and is excluded by the premise n = 1):
     epi_pre_F runs [0x864c0 .. 0x864f8) and ends in a continuation at the state before the store (bmb_at_rel,
     a0 = the flag pointer read by `ld a0,56(s2)` at 0x864f4), epi_post_F runs [0x864fc .. ret] from bmb_after_rel.
     bmb_rel_step is the store itself, for the composition in bmb_KR_Q0.
   - td_tail_F and epi_close_F: the F twins of reac_box_model_block_base.v:888 and :1450 (they are in _base.v but
     belong to this stretch, S3). S3 hands the final memory back: td_tail_F, epi_close_F and epi_post_F conclude
     `evtF rsegs RNG (fun s => Q0 s /\ ms_mem s = <the lemma's final memory>) (...)` (the coordinating lane,
     2026-10-29, option (a)); the extra conjunct is discharged at evtF_done, where the memory is still that one
     because [0x864fc .. ret] stores nothing. The _of_F corollaries project the first conjunct (ExecF.evtF_mono),
     and so does bmb_KR_Q0, whose post is Q0.
   - td_tail_of_F / epi_close_of_F / epi_of_F: the corollaries that re-derive the original Exec.evt statements
     with ExecF.RNG_all (the check that the _F statements are the old ones plus footprint premises, nothing
     weaker).

   Section MainF is reac_box_model_block_epi.v's Section Main except for the narrowed SR0 (:160) and no HSM (no lemma of this file
   takes the stack-malloc contract: the 0x85bb8 call is an allocator event of lane BASE's stretch, the lead
   22:5xZ), and plus the footprint Variable RNG and the region hypotheses (the nine Rimg..RFSsh of
   reac_box_model_block_cF.v's list, then the data-region set Rby..RJ14s that every F file carries). The pure
   section facts of _base.v are re-imported from its _F twins by `Let x := ltac2:(inst_exact @BF.x_F)` (:233-244), as
   _epi.v:98-128 does, so every goal mentions B.FK / B.EB / B.EBW and no second copy of them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF sh_word_on asan_stack_malloc_c_on.
(* rng_asan and reac_box_model_block_c_on are Required WITHOUT Import: rng_asan defines sh_word_rng, which
   asan_memcpy_cF defines too, and a Theorem Labs lane's region is cited by its full name through C_ON. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_c_on rng_asan.
(* reac_box_model_block_baseF.v is imported as the F twin of the original this file's original imports; no lemma
   below uses one of its F twins: td_tail_F and epi_close_F (the F twins of _base.v:888 and :1450) are proved
   here, and the pure section facts of _base.v are re-proved or re-imported from the PROVED file by inst_exact. *)
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module E := reac_box_model_block_epi.
(* a Theorem Labs lane's audited shadow region and _on post, cited by name, never copied (route (C), brief
   bmbF-narrow-brief.md (a working note, not in this delivery)). *)
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.
(* The F twins of the _base.v facts that go through the shadow premise (the lead's decision (2), 2026-10-29):
   they cannot be re-imported from the proved file any more, because it proves them under the UNIVERSAL
   shadow_rw; a Theorem Labs lane proves them in _baseF.v under the narrowed SR0. *)
Module BF := reac_box_model_block_baseF.

(* The store hook of the proved file, re-issued for the evtF walk: it also transports rd_mono
   (text of 3c9fcc93205 reac_box_model_blockF.v:46-57).  Local: this redefinition must not escape the file
   (the coordinating lane, 2026-10-29). *)
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
   does not relate to the [rng] premise of its region (the frame words and the shadow bytes of the frame, the flag
   byte). Normalize the wrap, then close the bounds from an rng hypothesis by lia alone.
   Text of reac_box_model_block_cases0aF.v (at head lib/A/Prog/reac_box_model_block_cases0aF.v:120-132) (the narrow hook, a Theorem Labs lane's S3 speed patch; from a working branch 9d19e850454): StepF
   calls acc_hint FIRST in solve_acc1, at every access of the run, under a backtracking match over every rng
   hypothesis, so it fires only on the wrapped shape and does no division reasoning (each lia already turns the
   division of a shadow byte x / 8 + off into equations).  The division argument of the frame's shadow bytes is
   made ONCE, by epi_fk_rng_F below, which puts them in the bare rng form [rng RNG (fr / 8 + off) 8]. *)
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

From Ltac2 Require Import Ltac2.

(* The section-closing generalization abstracts each lemma of Section Main over the section variables and
   hypotheses it used, in declaration order, under their own names (text of _epi.v:22-48). *)
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

Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C) (brief bmbF-narrow-brief.md (a working note, not in this delivery)): the universal shadow_rw is FALSE at the allocator state, so the
     premise names only a Theorem Labs lane's audited region. The name SR0 is kept, so inst_exact still instantiates it. *)
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

  (* The footprint and the regions this unit's runs read or write: the nine of reac_box_model_block_cF.v's list
     (text of 3c9fcc93205 reac_box_model_blockF.v:147-159), then the data-region set every F file of this family
     carries (the lead, interface decision (B)). The epilogue uses only Rwin, Rwsh, RFSw and RFSsh. *)
  Variable RNG : footprint.
  Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
  Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rwsh : sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
  Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
  Hypothesis Rtls : reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
  Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
  (* The class-0 area WITHOUT the hint word [FS, FS + 8): no lemma of this file reads or writes it (the lead
     a Theorem Labs lane, 2026-10-29); the glue keeps the hint word unchanged across S2 from the footprint. *)
  Hypothesis RFSw : rng_ivls RNG (tl (fp_w [0%nat] FS)).
  Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
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

  (* The definitions of reac_box_model_block_base.v at this section's variables (text of _epi.v:88-96). *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  (* Route (C): the post's `shadow_rw m'` is a Theorem Labs lane's region transport (reac_box_model_block_post_on). *)
  Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    F fc m p b o FS row nb).

  (* The pure lemmas of reac_box_model_block_base.v at this section's variables and hypotheses (_epi.v:98-128
     without the run lemmas entry / fwords / td_tail / epi_close: those have F twins). *)
  (* Every one of these comes from reac_box_model_block_baseF.v, not from the proved _base.v: under the narrowed
   SR0 an inst_exact of a proved-file lemma whose binders carry the universal `shadow_rw m` is an illegal
   application (the lead's narrowing check, 2026-10-29).  In _baseF.v fk_facts_F, epi_state_F, epi_shadow0_F,
   epi_addr_F, epi_flags_F and ebw_sub0_F are the narrowed twins; HA1_F, mrd_w1_F, mrd_wn_ne_F, bytes_keep_out_F,
   inside_appl_F and zeqb_addcancel_F are plain aliases of the proved lemmas at that section's variables. *)
  Let HA1 := ltac2:(inst_exact @BF.HA1_F).
  Let fk_facts := ltac2:(inst_exact @BF.fk_facts_F).
  Let ebw_sub0 := ltac2:(inst_exact @BF.ebw_sub0_F).
  Let epi_state := ltac2:(inst_exact @BF.epi_state_F).
  Let epi_addr := ltac2:(inst_exact @BF.epi_addr_F).
  Let epi_shadow0 := ltac2:(inst_exact @BF.epi_shadow0_F).
  Let epi_flags := ltac2:(inst_exact @BF.epi_flags_F).
  Let mrd_w1 := ltac2:(inst_exact @BF.mrd_w1_F).
  Let mrd_wn_ne := ltac2:(inst_exact @BF.mrd_wn_ne_F).
  Let bytes_keep_out := ltac2:(inst_exact @BF.bytes_keep_out_F).
  Let inside_appl := ltac2:(inst_exact @BF.inside_appl_F).
  Let zeqb_addcancel := ltac2:(inst_exact @BF.zeqb_addcancel_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* The byte at a + i is writable in m: in the frame (FW), a shadow byte of the frame (SW) or in the window
     (ST0) (text of _epi.v:139-152). *)
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

  (* store_ok of n bytes at a in the current memory, the bytes writable in m by wv (the evtF goal shape). *)
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
    | |- evtF ?segs ?RG ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
        let E := addr_expr a in
        lazymatch a with
        | wa _ => idtac
        | Z_to_bv 64 _ => change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
        | _ => replace (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs) by (f_equal; addr_eq_tac)
        end
    end.

  (* A store of bs at a inside the body footprint W, carried across the four facts the body keeps (_epi.v:187-198). *)
  Lemma est : forall (W : list ivl) (mc : word -> option byte) (a : Z) (bs : list byte),
    munch W m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> inside W a (Z.of_nat (length bs)) ->
    store_ok rsegs mc (wa a) (length bs) = true ->
    munch W m (write_to_mem mc (wa a) bs) /\ wmono rsegs m (write_to_mem mc (wa a) bs) /\
    rd_mono m (write_to_mem mc (wa a) bs) /\ mem_inv rsegs (write_to_mem mc (wa a) bs).
  Proof.
    intros W mc a bs MU WM RM MI Ha Hl Hin HS. hide_sec.
    split; [exact (munch_write W m mc a bs MU Ha Hl Hin)|].
    split; [exact (wmono_write rsegs m mc (wa a) bs WM)|].
    split; [exact (B.rd_mono_write m mc (wa a) bs RM) | exact (mem_inv_store rsegs mc (wa a) bs MI HS)].
  Qed.

  (* After a store step whose write_to_mem is left visible, carry the four facts across it. *)
  Ltac estep :=
    norm_store;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?pm (wa ?A0) ?bb) _) =>
        match goal with
        | MU : munch ?W m pm, WM : wmono rsegs m pm, RM : rd_mono m pm, MI : mem_inv rsegs pm |- _ =>
            let T := fresh "T" in
            let MU' := fresh "MUc" in let WM' := fresh "WMc" in
            let RM' := fresh "RMc" in let MI' := fresh "MIc" in
            pose proof (est W pm A0 bb MU WM RM MI ltac:(lia) ltac:(simpl_sizes; lia)
                          ltac:(unfold B.EBW, B.Wf, shadow_addr; rewrite ?Hoff; apply inside_appl;
                                simpl_sizes; cbn [inside]; lia)
                          ltac:(simpl_sizes;
                                match goal with HS : store_ok rsegs pm _ _ = true |- _ => exact HS end)) as T;
            clear MU WM RM MI;
            destruct T as (MU' & WM' & RM' & MI')
        end
    end.

  (* One inline store of a single byte at a, the stored byte normalized to [Z_to_bv 8 v] when it is a literal. *)
  Ltac sst a :=
    wstS a 1%nat; step;
    (lazymatch goal with
     | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) =>
         try (replace l with [Z_to_bv 8 0] by reflexivity)
     end);
    estep;
    repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.

  (* An 8-byte read of a word written in memory (_epi.v:224-232). *)
  Lemma rd8_at : forall (mm : word -> option byte) (AA : Z) (v : word),
    bytes_at rsegs mm AA (le8 v) -> ov_read_bytes rsegs mm (wa AA) 8 = Some (le8 v).
  Proof.
    intros mm AA v H. hide_sec.
    pose proof (bytes_at_read rsegs mm AA (le8 v) 0 8 H ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as HR.
    rewrite Z.add_0_r in HR. rewrite skipn_O in HR.
    assert (E : firstn 8 (le8 v) = le8 v) by (apply firstn_all2; rewrite length_le8; lia).
    rewrite E in HR. exact HR.
  Qed.

  (* ------------------------------------------------------------------------------------------------------- *)
  (* The regions of the epilogue in rng form. *)

  (* The class-0 frame area [fs_frame FS 0 0, + 2^20): the second range of tl (fp_w [0%nat] FS) (RFSw), its
     bounds from fs_place (text of 3c9fcc93205 reac_box_model_blockF.v RFSf_F). *)
  Lemma epi_RFSf_F : rng RNG (fs_frame FS 0%nat 0) 1048576.
  Proof.
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

  (* The class-0 flag byte j: the first range of tl (fp_w [0%nat] FS). *)
  Lemma epi_RFSfl_F : forall j, 0 <= j < fs_M 0%nat -> rng RNG (fs_flag FS 0%nat j) 1.
  Proof.
    intros j Hj. hide_sec.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5).
    assert (FShi : FS + FS_SIZE <= 2^64).
    { pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A2. lia. }
    pose proof RFSw as RW. unfold rng_ivls, fp_w, fp_w1 in RW. cbn [flat_map app tl] in RW.
    apply Forall_cons_iff in RW as [R2 _]. cbn [fst snd] in R2.
    assert (EM : fs_M 0%nat = 16384) by reflexivity.
    assert (EF0 : fs_flag FS 0%nat 0 = FS + 4096) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (EFj : fs_flag FS 0%nat j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    rewrite EM in Hj. rewrite EF0, EM in R2. rewrite EFj. unfold FS_SIZE in FShi.
    split; [lia|]. split; [lia|]. intros b0 j0 Hb Hj0. apply R2; lia.
  Qed.

  (* The frame and its eight shadow bytes are in the footprint: the real-stack frame and its shadow lie in the
     window and in the window's shadow cover, the class-0 frame and its shadow in the class-0 frame area and in
     the shadow of the class-0 frames (text of 3c9fcc93205 reac_box_model_blockF.v fk_rng_F, at B.FK). *)
  Lemma epi_fk_rng_F : forall fr f spc j n w56, FK fr f spc j n w56 ->
    rng RNG fr 64 /\ rng RNG (fr / 8 + off) 8.
  Proof.
    intros fr f spc j n w56 HK. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & HFS & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    unfold sh_cover, shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K in Rwsh.
    unfold REAC_BOX_MODEL_BLOCK_K in Rwin.
    assert (ESH0 : fs_M 0%nat * fs_B 0%nat / 8 = 131072) by reflexivity.
    assert (EFR0 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    pose proof RFSsh as RFSsh'. rewrite ESH0, EFR0 in RFSsh'. unfold shadow_addr, ASAN_K in RFSsh'.
    pose proof epi_RFSf_F as RFf. rewrite EFR0 in RFf.
    rewrite Hoff. unfold ASAN_K.
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
    - split.
      + eapply rng_sub'; [exact Rwin|]. lia.
      + eapply rng_sub'; [exact Rwsh|]. Z.div_mod_to_equations. lia.
    - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
      change (2 ^ 0) with 1 in *.
      split.
      + eapply rng_sub'; [exact RFf|]. lia.
      + eapply rng_sub'; [exact RFSsh'|]. Z.div_mod_to_equations. lia.
  Qed.

  (* ------------------------------------------------------------------------------------------------------- *)
  (* S3: 0x86520 -> ret 0x86560. The F twins of reac_box_model_block_base.v:888 and :1450. *)

  (* 0x86520: a0 = s5, the saved registers restored and the frame popped, ret (_base.v:888). *)
  Lemma td_tail_F : forall (r : Z) (m' : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word) (spc fr f : Z),
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    rw_cells rsegs m' (bv_unsigned sp + -104) SAVES ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells m' -> (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') ->
    addressable m' (bv_unsigned sp - 4272) 4272 ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m'
     else bytes_at rsegs m' o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m') ->
    evtF rsegs RNG (fun s => Q0 s /\ ms_mem s = m')
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86520) fc None m' (seg_rom rsegs)).
  Proof.
    intros r m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 spc fr f
      Er FR WM MI ST AC SW AW FP TL POSTMU. hide_sec.
    subst r. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp. unfold B.SAVES in FR.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
    do 17 step.
    apply evtF_done. cbv beta. split; [| reflexivity].
    unfold C_ON.reac_box_model_block_post_on. cbv beta.
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact POSTMU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP | exact TL].
  Qed.

  (* The 0x86520 restore/return, from the body facts carried to the final memory (_base.v:1450). *)
  Lemma epi_close_F : forall (fr f spc j n : Z) (w56 : word) (mfin : word -> option byte) (hfin : word) (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    munch (EBW fr j n) m mfin -> wmono rsegs m mfin -> rd_mono m mfin -> mem_inv rsegs mfin ->
    rw_cells rsegs mfin (bv_unsigned sp + -104) SAVES ->
    bytes_at rsegs mfin (fs_hint FS 0) (le8 hfin) ->
    (f = 0 -> forall x, A - 64 <= x < A -> mrd rsegs mfin (wa (shadow_addr x)) = Some (Z_to_bv 8 0)) ->
    (n = 1 -> mrd rsegs mfin (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m mfin
     else bytes_at rsegs mfin o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m mfin) ->
    evtF rsegs RNG (fun s => Q0 s /\ ms_mem s = mfin)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86520) fc None mfin (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mfin hfin r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK Hr MUf WMf RMf MIf SVf HHf SHRB FLRB POSTMU. hide_sec.
    destruct (epi_flags fr f spc j n w56 mfin HK MUf FLRB) as (flags'' & Hfl & Hflen & Hf01).
    pose proof (epi_state fr f spc j n w56 mfin hfin flags'' HK MUf WMf RMf HHf Hfl Hflen Hf01)
      as (ACm & SWm & FPm & TLm).
    eapply td_tail_F.
    - exact Hr.
    - exact SVf.
    - exact WMf.
    - exact MIf.
    - exact (B.stk_mono m mfin _ _ ST0 WMf RMf).
    - exact ACm.
    - exact SWm.
    - apply epi_addr. exact (epi_shadow0 fr f spc j n w56 mfin HK MUf SHRB).
    - exact FPm.
    - exact TLm.
    - exact POSTMU.
  Qed.

  (* ------------------------------------------------------------------------------------------------------- *)
  (* The epilogue obligation: the statement of _epi.v:237-246 with Q0 generalized and evt replaced by evtF.
     The post is INDEXED by the lemma's own FK data (fr f spc j n w56), so that an S2 caller can stop at a
     continuation that mentions the frame it allocated (the coordinating lane, 2026-10-29). *)

  Definition bmb_KR (Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop) : Prop :=
    forall (r : Z) (mc : word -> option byte)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word)
        (spc fr f j n : Z) (w56 : word),
      FK fr f spc j n w56 -> EB fr f j n w56 mc ->
      r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
      evtF rsegs RNG (Q fr f spc j n w56)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
                 (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x864c0) fc None mc (seg_rom rsegs)).

  (* The state at the allocator event: the facts the proof holds at _epi.v:379, before the 15th step
     (`sb zero,0(a0)` at 0x864f8), with a0 = the flag pointer read by `ld a0,56(s2)` at 0x864f4. mc is the
     body-end memory of EB, mld the memory after the magic word and the eight shadow bytes. *)
  Definition bmb_at_rel (fr j : Z) (mc mld : word -> option byte) : Prop :=
    munch [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mld /\ wmono rsegs mc mld /\
    munch (EBW fr j 1) m mld /\ wmono rsegs m mld /\ rd_mono m mld /\ mem_inv rsegs mld /\
    store_ok rsegs mld (wa (fs_flag FS 0 j)) 1 = true.

  (* The same with the flag byte released (0) in memory; the state of epi_post_F at 0x864fc. *)
  Definition bmb_after_rel (fr j : Z) (mc mfin : word -> option byte) : Prop :=
    munch [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8); (fs_flag FS 0 j, fs_flag FS 0 j + 1)] mc mfin /\
    wmono rsegs mc mfin /\
    munch (EBW fr j 1) m mfin /\ wmono rsegs m mfin /\ rd_mono m mfin /\ mem_inv rsegs mfin /\
    mrd rsegs mfin (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0).

  (* The release store itself (the event the cgif glue replaces by astack_free_law / frame_flag_lawP): the
     bookkeeping of _epi.v:380-415 at the store. *)
  Lemma bmb_rel_step : forall (fr j : Z) (mc mld : word -> option byte),
    0 <= j < fs_M 0%nat -> fr = fs_frame FS 0%nat j -> bmb_at_rel fr j mc mld ->
    bmb_after_rel fr j mc (write_to_mem mld (wa (fs_flag FS 0 j)) [Z_to_bv 8 0]).
  Proof.
    intros fr j mc mld Hj Efr (MUr6 & WM6 & MUe & WMe & RMe & MIe & HSflag). hide_sec.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, P5.
    assert (EM : fs_M 0%nat = 16384) by reflexivity.
    assert (EFl : fs_flag FS 0 j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity;
       rewrite EM in Hj; lia).
    assert (Hfl0 : 0 <= fs_flag FS 0 j) by (rewrite EFl; rewrite EM in Hj; lia).
    assert (Hfl1 : fs_flag FS 0 j + 1 <= 2^64).
    { pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A2. unfold FS_SIZE in A2.
      rewrite EFl; rewrite EM in Hj; lia. }
    split.
    { apply (munch_write [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8);
                          (fs_flag FS 0 j, fs_flag FS 0 j + 1)] mc mld (fs_flag FS 0 j) [Z_to_bv 8 0]);
        [ apply (munch_weaken [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)]
                   [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8); (fs_flag FS 0 j, fs_flag FS 0 j + 1)]
                   mc mld); [ | exact MUr6 ]
        | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; lia ].
      intros x Hout. cbn [outside] in Hout. destruct Hout as (H1 & H2 & _). cbn [outside]. tauto. }
    split; [apply wmono_write; exact WM6|].
    split; [| split; [| split]].
    - apply (munch_write (EBW fr j 1) m mld (fs_flag FS 0 j) [Z_to_bv 8 0]); [exact MUe | lia
        | cbn [length Z.of_nat]; lia
        | unfold B.EBW, B.Wf; apply inside_appl; cbn [inside length Z.of_nat]; lia].
    - apply wmono_write; exact WMe.
    - apply (B.rd_mono_write m mld (wa (fs_flag FS 0 j)) [Z_to_bv 8 0]); exact RMe.
    - split.
      + exact (mem_inv_store rsegs mld (wa (fs_flag FS 0 j)) [Z_to_bv 8 0] MIe HSflag).
      + rewrite mrd_w1 by lia. rewrite Z.eqb_refl. reflexivity.
  Qed.

  (* S2's tail: [0x864c0 .. 0x864f8) on the fake-frame arm, ending at the release (_epi.v:349-378). *)
  Lemma epi_pre_F : forall (Q : machine_state -> Prop) (r : Z) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word)
      (spc fr f j n : Z) (w56 : word),
    FK fr f spc j n w56 -> EB fr f j n w56 mc ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    n = 1 ->
    (forall (mld : word -> option byte)
            (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 : word),
       bmb_at_rel fr j mc mld ->
       evtF rsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (fs_flag FS 0 j)) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) y22 (Z_to_bv 64 fr)
                  (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) y26 y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x864f8) fc None mld (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x864c0) fc None mc (seg_rom rsegs)).
  Proof.
    intros Q r mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      spc fr f j n w56 HK HEB Hr Hn1 K.
    hide_sec.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HK as HKd.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (epi_fk_rng_F fr f spc j n w56 HK) as (RFR & RSH).
    destruct HEB as (MUe & WMe & RMe & MIe & SVe & (hh & HHe) & F56e & BOXe).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & HDd0).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb. unfold ASAN_GT in P3.
    assert (EA8 : fr / 8 + off = shadow_addr fr) by (unfold shadow_addr; rewrite Hoff; reflexivity).
    assert (SHOUT : forall x, app_mem x -> ~ (shadow_addr fr <= x < shadow_addr fr + 8)).
    { intros x Hax. pose proof (B.sh_add8 fr 8 FR8) as E8. replace (fr + 8 * 8) with (fr + 64) in E8 by lia.
      rewrite <- E8. apply (B.acl_sh_out x fr (fr + 64) Hax).
      - clear -FRlo P1; lia.
      - unfold APPMEM_END; clear -FRhi HAhi HAE'; lia. }
    assert (APPFR : forall x, fr <= x < fr + 64 -> app_mem x).
    { intros x Hx. replace x with (fr + (x - fr)) by lia. apply FAP. lia. }
    assert (OUTWR2 : forall x, app_mem x -> (x < fr \/ fr + 8 <= x) ->
              outside [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] x).
    { intros x Hax Hfrx. cbn [outside]. split; [lia|]. split; [|exact I].
      assert (~ (fr / 8 + off <= x < fr / 8 + off + 8)) by (rewrite EA8; apply SHOUT; exact Hax). lia. }
    (* the magic word at [fr, fr + 8) *)
    step. step. wstF fr 8%nat. step. estep.
    repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
    destruct HKd as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
    - (* the real-stack frame is excluded on this arm *)
      exfalso. clear -Hn1 En. lia.
    - (* a side-stack frame: fr = fs_frame FS 0 j, f = fr, spc = A, n = 1 (_epi.v:349-378) *)
      subst f spc w56 n.
      assert (Hfrpos : 0 < fr < 2 ^ 64) by (clear -FRlo P1 FRhi HAhi HAE'; lia).
      assert (EM : fs_M 0 = 16384) by reflexivity. rewrite EM in Hj.
      assert (EFl : fs_flag FS 0 j = FS + 4096 + j) by
        (unfold fs_flag; cbn [Z.of_nat];
         replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
      assert (EFj : fs_frame FS 0 j = FS + 36864 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      pose proof (epi_RFSfl_F j ltac:(rewrite EM; lia)) as RFL.
      step.
      replace (bv_eqb (Z_to_bv 64 fr) (Z_to_bv 64 0)) with false by (symmetry; apply rc_neq0_64; exact Hfrpos).
      cbv iota. step.
      sst (fr / 8 + off + 4). sst (fr / 8 + off + 5). sst (fr / 8 + off + 6). sst (fr / 8 + off + 7).
      sst (fr / 8 + off + 0). sst (fr / 8 + off + 1). sst (fr / 8 + off + 2). sst (fr / 8 + off + 3).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (mld := mm) in * end.
      assert (MUr6 : munch [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mld).
      { unfold mld. repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
        apply munch_refl. }
      assert (WM6 : wmono rsegs mc mld).
      { unfold mld. repeat apply wmono_write. apply wmono_refl. }
      assert (Hb56 : bytes_at rsegs mld (fr + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 j)))).
      { apply (bytes_keep_out [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mld (fr + 56)
                 (le8 (Z_to_bv 64 (fs_flag FS 0 j))) F56e MUr6).
        intros x Hx. rewrite length_le8 in Hx. apply OUTWR2; [apply APPFR; clear -Hx; lia | right; clear -Hx; lia]. }
      pose proof (rd8_at mld (fr + 56) (Z_to_bv 64 (fs_flag FS 0 j)) Hb56) as HR0.
      step.
      assert (HSflag : store_ok rsegs mld (wa (fs_flag FS 0 j)) 1 = true).
      { apply (B.wv_store_ok m mld (fs_flag FS 0 j) 1).
        - intros i Hi. apply (B.stk_wv m FS (FS + FS_SIZE) (fs_flag FS 0 j + i) P5).
          rewrite EFl. unfold FS_SIZE. clear -Hj Hi; lia.
        - assumption.
        - rewrite EFl; clear -P1 Hj; lia.
        - rewrite EFl; clear -P1 Hj HFSb HAE'; lia. }
      (* the cut: the allocator event sb zero,0(a0) at 0x864f8 is not stepped here *)
      apply K.
      unfold bmb_at_rel.
      split; [exact MUr6|]. split; [exact WM6|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      exact HSflag.
  Qed.

  (* S3's head: [0x864fc .. ret] from the released state (_epi.v:385-457 + epi_close + td_tail). *)
  Lemma epi_post_F : forall (r : Z) (mc mfin : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word)
      (spc fr f j n : Z) (w56 : word),
    FK fr f spc j n w56 -> EB fr f j n w56 mc -> n = 1 ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    bmb_after_rel fr j mc mfin ->
    evtF rsegs RNG (fun s => Q0 s /\ ms_mem s = mfin)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x864fc) fc None mfin (seg_rom rsegs)).
  Proof.
    intros r mc mfin x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      spc fr f j n w56 HK HEB Hn1 Hr HREL.
    hide_sec.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HK as HKd.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct HEB as (MUe & WMe & RMe & MIe & SVe & (hh & HHe) & F56e & BOXe).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & HDd0).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb. unfold ASAN_GT in P3.
    assert (EA8 : fr / 8 + off = shadow_addr fr) by (unfold shadow_addr; rewrite Hoff; reflexivity).
    assert (SHOUT : forall x, app_mem x -> ~ (shadow_addr fr <= x < shadow_addr fr + 8)).
    { intros x Hax. pose proof (B.sh_add8 fr 8 FR8) as E8. replace (fr + 8 * 8) with (fr + 64) in E8 by lia.
      rewrite <- E8. apply (B.acl_sh_out x fr (fr + 64) Hax).
      - clear -FRlo P1; lia.
      - unfold APPMEM_END; clear -FRhi HAhi HAE'; lia. }
    assert (EHint : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (APPFR : forall x, fr <= x < fr + 64 -> app_mem x).
    { intros x Hx. replace x with (fr + (x - fr)) by lia. apply FAP. lia. }
    assert (BOXF : (p =? 0) || (o =? 0) = false ->
              length (synth row b nb) = 32%nat /\ (forall x, o <= x < o + 32 -> app_mem x) /\
              (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272)).
    { intros Ebx. unhide HP. unhide AO. unhide HO.
      apply orb_false_iff in Ebx. destruct Ebx as [Ep Eo]. apply Z.eqb_neq in Ep. apply Z.eqb_neq in Eo.
      destruct (HP Ep) as (_ & Hl & _). destruct (AO Eo) as (AOa & _ & _). destruct (HO Eo) as (_ & Hdw & _).
      split; [exact (rs_synth_len row b nb Hl)|]. split; [|exact Hdw].
      intros x Hx. pose proof (B.acl_app_in m o 32 (x - o) AOa ltac:(clear -Hx; lia)) as H.
      replace (o + (x - o)) with x in H by ring. exact H. }
    destruct HKd as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
    - exfalso. clear -Hn1 En. lia.
    - subst f spc w56 n.
      assert (Hfrpos : 0 < fr < 2 ^ 64) by (clear -FRlo P1 FRhi HAhi HAE'; lia).
      assert (EM : fs_M 0 = 16384) by reflexivity. rewrite EM in Hj.
      assert (EFl : fs_flag FS 0 j = FS + 4096 + j) by
        (unfold fs_flag; cbn [Z.of_nat];
         replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
      assert (EFj : fs_frame FS 0 j = FS + 36864 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      destruct HREL as (MUr & WMr & MUc & WMc & RMc & MIc & FLRB).
      pose proof Rwin as Rwin'. unfold REAC_BOX_MODEL_BLOCK_K in Rwin'.
      (* 0x864fc: the jump to the restore block at 0x86520 *)
      step.
      assert (OUTWRS : forall x, app_mem x -> (x < fr \/ fr + 8 <= x) ->
                (x < fs_flag FS 0 j \/ fs_flag FS 0 j + 1 <= x) ->
                outside [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8);
                         (fs_flag FS 0 j, fs_flag FS 0 j + 1)] x).
      { intros x Hax Hfrx Hflx. cbn [outside]. split; [lia|]. split; [|split; [lia|exact I]].
        assert (~ (fr / 8 + off <= x < fr / 8 + off + 8)) by (rewrite EA8; apply SHOUT; exact Hax). lia. }
      assert (SVf : rw_cells rsegs mfin (bv_unsigned sp + -104) SAVES).
      { apply (B.acl_rw _ mc mfin (bv_unsigned sp + -104) SAVES SVe MUr WMr).
        intros x Hx. cbn [cells_size csize Nat.add B.SAVES] in Hx. apply OUTWRS.
        - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. clear -Hx HHM' HAE'; lia.
        - right. clear -Hx FRhi HAhi; lia.
        - right. rewrite EFl. clear -Hx HHM' HFSb HAE' P1 Hj; lia. }
      assert (HHf : bytes_at rsegs mfin (fs_hint FS 0) (le8 hh)).
      { rewrite EHint.
        apply (bytes_keep_out _ mc mfin FS (le8 hh) HHe MUr).
        intros x Hx. rewrite length_le8 in Hx. apply OUTWRS.
        - apply P4. clear -Hx; lia.
        - left. clear -Hx FRlo P1; lia.
        - left. rewrite EFl. clear -Hx Hj; lia. }
      eapply epi_close_F.
      + exact HK.
      + exact Hr.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + exact SVf.
      + exact HHf.
      + intros Hf0. exfalso. clear -Hf0 FRlo P1; lia.
      + intros _. exact FLRB.
      + pose proof (ebw_sub0 fr fr A j 1 (Z_to_bv 64 (fs_flag FS 0 j)) HK) as SUB.
        destruct (Bool.bool_dec ((p =? 0) || (o =? 0)) true) as [Ebox|Ebox];
          [| apply Bool.not_true_is_false in Ebox];
          rewrite Ebox in SUB, BOXe |- *; cbv iota.
        * unfold REAC_BOX_MODEL_BLOCK_K.
          apply (munch_weaken _ _ m mfin SUB). eassumption.
        * split.
          --
             apply (bytes_keep_out _ mc mfin o (synth row b nb) BOXe MUr).
             intros x Hx.
             destruct (BOXF Ebox) as (Hlen32 & Happ & _).
             rewrite Hlen32 in Hx.
             apply orb_false_iff in Ebox. destruct Ebox as [Ep' Eo'].
             assert (OF : outside (fp_w [0%nat] FS) x).
             { apply (fl_dj_out_r (reac_box_model_block_D p o) (fp_w [0%nat] FS) o (o + 32) x HDd0);
                 [|clear -Hx; lia].
               unfold reac_box_model_block_D. apply in_or_app. right. rewrite Eo'. left. reflexivity. }
             unfold fp_w, fp_w1 in OF. cbn [flat_map app outside] in OF.
             destruct OF as (_ & Ofl & Ofr & _).
             assert (EFM0 : fs_frame FS 0 (fs_M 0) = FS + 36864 + 1048576).
             { unfold fs_frame, fs_B, fs_M.
               replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
               replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
             assert (EFR00 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
             assert (EF00 : fs_flag FS 0 0 = FS + 4096) by
               (unfold fs_flag; cbn [Z.of_nat];
                replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
             apply OUTWRS; [apply Happ; exact Hx | | ].
             ++ rewrite EFR00, EFM0 in Ofr. rewrite Efr, EFj. clear -Ofr Hj; lia.
             ++ rewrite EF00, EM in Ofl. rewrite EFl. clear -Ofl Hj; lia.
          -- unfold REAC_BOX_MODEL_BLOCK_K. apply (munch_weaken _ _ m mfin SUB). eassumption.
  Qed.

  (* The whole original epi over StepF: the real-stack arm by its own script (_epi.v:285-348), the side-stack arm
     as epi_pre_F + the release store + epi_post_F. *)
  Lemma bmb_KR_Q0 : bmb_KR (fun _ _ _ _ _ _ => Q0).
  Proof.
    unfold bmb_KR.
    intros r mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      spc fr f j n w56 HK HEB Hr. hide_sec.
    cbv beta.
    pose proof HK as HKd0.
    destruct HKd0 as [(Ef0 & Efr0 & Esp0 & Ej0 & En0) | (Hj0 & Efr0 & Ef0 & Esp0 & Ew0 & En0)].
    - (* the real-stack frame: f = 0, fr = A - 64, spc = A - 64, j = 0, n = 0; the shadow is zeroed *)
      pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
      pose proof HA1 as (HA32 & HAlo & HAhi).
      pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
      destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
      destruct (epi_fk_rng_F fr f spc j n w56 HK) as (RFR & RSH).
      destruct HEB as (MUe & WMe & RMe & MIe & SVe & (hh & HHe) & F56e & BOXe).
      pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & HDd0).
      pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb. unfold ASAN_GT in P3.
      assert (EA8 : fr / 8 + off = shadow_addr fr) by (unfold shadow_addr; rewrite Hoff; reflexivity).
      assert (SHOUT : forall x, app_mem x -> ~ (shadow_addr fr <= x < shadow_addr fr + 8)).
      { intros x Hax. pose proof (B.sh_add8 fr 8 FR8) as E8. replace (fr + 8 * 8) with (fr + 64) in E8 by lia.
        rewrite <- E8. apply (B.acl_sh_out x fr (fr + 64) Hax).
        - clear -FRlo P1; lia.
        - unfold APPMEM_END; clear -FRhi HAhi HAE'; lia. }
      assert (EHint : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
      assert (OUTWR2 : forall x, app_mem x -> (x < fr \/ fr + 8 <= x) ->
                outside [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] x).
      { intros x Hax Hfrx. cbn [outside]. split; [lia|]. split; [|exact I].
        assert (~ (fr / 8 + off <= x < fr / 8 + off + 8)) by (rewrite EA8; apply SHOUT; exact Hax). lia. }
      assert (BOXF : (p =? 0) || (o =? 0) = false ->
                length (synth row b nb) = 32%nat /\ (forall x, o <= x < o + 32 -> app_mem x) /\
                (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272)).
      { intros Ebx. unhide HP. unhide AO. unhide HO.
        apply orb_false_iff in Ebx. destruct Ebx as [Ep Eo]. apply Z.eqb_neq in Ep. apply Z.eqb_neq in Eo.
        destruct (HP Ep) as (_ & Hl & _). destruct (AO Eo) as (AOa & _ & _). destruct (HO Eo) as (_ & Hdw & _).
        split; [exact (rs_synth_len row b nb Hl)|]. split; [|exact Hdw].
        intros x Hx. pose proof (B.acl_app_in m o 32 (x - o) AOa ltac:(clear -Hx; lia)) as H.
        replace (o + (x - o)) with x in H by ring. exact H. }
      (* the magic word at [fr, fr + 8) *)
      step. step. wstF fr 8%nat. step. estep.
      repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
      subst f j n spc.
      step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
      sst (fr / 8 + off + 4). sst (fr / 8 + off + 5). sst (fr / 8 + off + 6). sst (fr / 8 + off + 7).
      sst (fr / 8 + off + 0). sst (fr / 8 + off + 1). sst (fr / 8 + off + 2). sst (fr / 8 + off + 3).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (mfin := mm) in * end.
      assert (MUr : munch [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mfin).
      { unfold mfin. repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
        apply munch_refl. }
      assert (WMr : wmono rsegs mc mfin).
      { unfold mfin. repeat apply wmono_write. apply wmono_refl. }
      assert (SVf : rw_cells rsegs mfin (bv_unsigned sp + -104) SAVES).
      { apply (B.acl_rw [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mfin
                 (bv_unsigned sp + -104) SAVES SVe MUr WMr).
        intros x Hx. cbn [cells_size csize Nat.add B.SAVES] in Hx. apply OUTWR2.
        - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. clear -Hx HHM' HAE'; lia.
        - right. clear -Hx FRhi HAhi; lia. }
      assert (HHf : bytes_at rsegs mfin (fs_hint FS 0) (le8 hh)).
      { rewrite EHint.
        apply (bytes_keep_out [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mfin FS (le8 hh) HHe MUr).
        intros x Hx. rewrite length_le8 in Hx. apply OUTWR2.
        - apply P4. clear -Hx; lia.
        - left. clear -Hx FRlo P1; lia. }
      assert (SHRB : forall x, A - 64 <= x < A -> mrd rsegs mfin (wa (shadow_addr x)) = Some (Z_to_bv 8 0)).
      { intros x Hx.
        assert (Exsh : shadow_addr x = fr / 8 + off + (x - fr) / 8).
        { unfold shadow_addr. rewrite Hoff. rewrite Efr0.
          assert (Hm : (A - 64) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
          Z.div_mod_to_equations; lia. }
        assert (Hk : 0 <= (x - fr) / 8 < 8) by (rewrite Efr0; clear -Hx HA32; Z.div_mod_to_equations; lia).
        rewrite Exsh. set (kk := (x - fr) / 8) in *. unfold mfin.
        rewrite !mrd_w1 by (clear -SH1 SH2 Hk; lia). rewrite !zeqb_addcancel.
        destruct Hk as [Hk0 Hk8].
        assert (Ek : kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5 \/ kk = 6 \/ kk = 7) by lia.
        destruct Ek as [Ek'|[Ek'|[Ek'|[Ek'|[Ek'|[Ek'|[Ek'|Ek']]]]]]]; rewrite Ek'; reflexivity. }
      (* S3 now also hands the final memory back; bmb_KR's post is Q0, so project it *)
      apply (ExecF.evtF_mono rsegs RNG (fun s => Q0 s /\ ms_mem s = mfin) Q0);
        [| intros ms' Hms'; exact (proj1 Hms')].
      eapply epi_close_F.
      + exact HK.
      + exact Hr.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + exact SVf.
      + exact HHf.
      + intros _. exact SHRB.
      + intros Hn1; discriminate Hn1.
      + pose proof (ebw_sub0 fr 0 (A - 64) 0 0 w56 HK) as SUB.
        destruct (Bool.bool_dec ((p =? 0) || (o =? 0)) true) as [Ebox|Ebox];
          [| apply Bool.not_true_is_false in Ebox];
          rewrite Ebox in SUB, BOXe |- *; cbv iota.
        * unfold REAC_BOX_MODEL_BLOCK_K.
          apply (munch_weaken _ _ m mfin SUB). eassumption.
        * split.
          --
             apply (bytes_keep_out [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mfin o
                      (synth row b nb) BOXe MUr).
             intros x Hx.
             destruct (BOXF Ebox) as (Hlen32 & Happ & Hdw).
             rewrite Hlen32 in Hx.
             apply OUTWR2; [apply Happ; exact Hx|].
             clear -Hx Hdw HAlo HAhi Efr0; lia.
          -- unfold REAC_BOX_MODEL_BLOCK_K. apply (munch_weaken _ _ m mfin SUB). eassumption.
    - (* the side-stack frame: the split at the release *)
      eapply epi_pre_F; [exact HK | exact HEB | exact Hr | exact En0 |].
      intros mld y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 HREL.
      pose proof HREL as HRELd.
      destruct HRELd as (MUr6 & WM6 & MUld & WMld & RMld & MIld & HSflag).
      (* the release store sb zero,0(a0) at 0x864f8: its byte is the class-0 flag byte j *)
      pose proof (epi_RFSfl_F j Hj0) as RFL.
      step.
      (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) => try (replace l with [Z_to_bv 8 0] by reflexivity)
       end).
      norm_store.
      (* S3 now also hands the final memory back; bmb_KR's post is Q0, so project it *)
      apply (ExecF.evtF_mono rsegs RNG
               (fun s => Q0 s /\ ms_mem s = write_to_mem mld (wa (fs_flag FS 0 j)) [Z_to_bv 8 0]) Q0);
        [| intros ms' Hms'; exact (proj1 Hms')].
      eapply epi_post_F; [exact HK | exact HEB | exact En0 | exact Hr |].
      apply bmb_rel_step; [ | exact Efr0 | exact HREL].
      exact Hj0.
  Qed.

End MainF.

(* --------------------------------------------------------------------------------------------------------- *)
(* The corollaries: the original Exec.evt statements re-derived from the footprint forms with ExecF.RNG_all.
   This is the check that each _F statement is the old one plus footprint premises, nothing weaker. *)
Section OfF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* The corollaries re-derive the ORIGINAL statements, so this section keeps the WIDE premise and hands the
     narrowed one to the _F lemmas (ShadowRwOn.shadow_rw_on_of_shadow_rw); the name SR0 carries the narrowed
     form, so inst_exact instantiates the _F lemmas with it. *)
  Hypothesis SRW : shadow_rw m.
  Let SR0 : shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m :=
    shadow_rw_on_of_shadow_rw _ m SRW.
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
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  Notation Q0 := (B.Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  Notation Q0on := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      F fc m p b o FS row nb).

  (* The _on post gives the original post back at the wide premise (the bridge of
     reac_box_model_block_cF_on.v:110-115). *)
  Let post_of_on : forall ms', Q0on ms' -> Q0 ms'.
  Proof.
    intros ms' Hq. unfold C_ON.reac_box_model_block_post_on in Hq. unfold B.Q0, reac_box_model_block_post.
    destruct Hq as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    Ems & MU & WM & MI' & ST' & AC' & SW' & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI' (conj ST' (conj AC' (conj _ Rest))))))).
    exact (shadow_rw_of_on_all m' (SW' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m SRW))).
  Qed.

  (* The footprint forms at this section's variables, still waiting for RNG and its region premises. *)
  Let td_tail_F0 := ltac2:(inst_exact @td_tail_F).
  Let epi_close_F0 := ltac2:(inst_exact @epi_close_F).
  Let bmb_KR_Q0_0 := ltac2:(inst_exact @bmb_KR_Q0).

  (* The all-footprint meets every region premise of this file's runs: it is put in the context under the
     hypotheses' own shape, so that `try assumption` closes whichever subset the section closing kept. *)
  Ltac all_rng :=
    let HHM' := fresh "HHMa" in let HAE' := fresh "HAEa" in
    let FSlo := fresh "FSlo" in let FShi := fresh "FShi" in
    let R1 := fresh "Ra" in let R2 := fresh "Ra" in let R3 := fresh "Ra" in
    let R7 := fresh "Ra" in let R8 := fresh "Ra" in let R9 := fresh "Ra" in
    pose proof HHM as HHM'; pose proof HAE as HAE';
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE';
    assert (FSlo : 0 <= FS) by
      (pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _);
       pose proof HPl as (P1 & P2 & P3 & P4 & P5); lia);
    assert (FShi : FS + 11571200 <= 2^64) by
      (pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _);
       pose proof HPl as (P1 & P2 & P3 & P4 & P5);
       pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2;
       unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, FS_SIZE in A2; lia);
    assert (R1 : ExecF.rng ExecF.RNG_all 0x10000 0x5ee000) by (apply ExecF.rng_all; lia);
    assert (R2 : ExecF.rng ExecF.RNG_all (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K) by
      (apply ExecF.rng_all; unfold REAC_BOX_MODEL_BLOCK_K; lia);
    assert (R3 : sh_cover ExecF.RNG_all (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K) by
      (unfold sh_cover, shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K; apply ExecF.rng_all;
       Z.div_mod_to_equations; lia);
    assert (R7 : ExecF.rng ExecF.RNG_all FS (fs_frame FS 0%nat 0 - FS)) by
      (unfold fs_frame, fs_B; cbn [Z.of_nat]; apply ExecF.rng_all; lia);
    assert (R8 : rng_ivls ExecF.RNG_all (tl (fp_w [0%nat] FS))) by
      (unfold rng_ivls, fp_w, fp_w1; cbn [flat_map app tl]; repeat constructor; intros; exact I);
    assert (R9 : ExecF.rng ExecF.RNG_all (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8)) by
      (unfold shadow_addr, ASAN_K, fs_frame, fs_M, fs_B; cbn [Z.of_nat]; apply ExecF.rng_all;
       Z.div_mod_to_equations; lia);
    try assumption.

  Lemma td_tail_of_F : forall (r : Z) (m' : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word) (spc fr f : Z),
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    rw_cells rsegs m' (bv_unsigned sp + -104) SAVES ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' -> addressable m' (bv_unsigned sp - 4272) 4272 ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m'
     else bytes_at rsegs m' o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m') ->
    evt rsegs Q0
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86520) fc None m' (seg_rom rsegs)).
  Proof.
    intros.
    (* MainF's hide_sec, inline (an Ltac of a section does not survive its End) *)
    let hide H := let T := type of H in change (mb_hide T) in H in
    hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ; hide HA; hide HS16.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply ExecF.evtF_mono;
      [ eapply td_tail_F0;
        try (intros P _; apply shadow_rw_on_of_shadow_rw; assumption);
        try eassumption; try assumption; all_rng
      | intros ms' Hms'; exact (post_of_on ms' (proj1 Hms')) ].
  Qed.

  Lemma epi_close_of_F : forall (fr f spc j n : Z) (w56 : word) (mfin : word -> option byte) (hfin : word) (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    munch (EBW fr j n) m mfin -> wmono rsegs m mfin -> rd_mono m mfin -> mem_inv rsegs mfin ->
    rw_cells rsegs mfin (bv_unsigned sp + -104) SAVES ->
    bytes_at rsegs mfin (fs_hint FS 0) (le8 hfin) ->
    (f = 0 -> forall x, A - 64 <= x < A -> mrd rsegs mfin (wa (shadow_addr x)) = Some (Z_to_bv 8 0)) ->
    (n = 1 -> mrd rsegs mfin (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m mfin
     else bytes_at rsegs mfin o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m mfin) ->
    evt rsegs Q0
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86520) fc None mfin (seg_rom rsegs)).
  Proof.
    intros.
    (* MainF's hide_sec, inline (an Ltac of a section does not survive its End) *)
    let hide H := let T := type of H in change (mb_hide T) in H in
    hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ; hide HA; hide HS16.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply ExecF.evtF_mono;
      [ eapply epi_close_F0; try eassumption; try assumption; all_rng
      | intros ms' Hms'; exact (post_of_on ms' (proj1 Hms')) ].
  Qed.

  (* The original epi (_epi.v:237): the whole epilogue, both arms. *)
  Lemma epi_of_F : forall (r : Z) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word)
      (spc fr f j n : Z) (w56 : word),
    FK fr f spc j n w56 -> EB fr f j n w56 mc ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    evt rsegs Q0
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x864c0) fc None mc (seg_rom rsegs)).
  Proof.
    intros.
    (* MainF's hide_sec, inline (an Ltac of a section does not survive its End) *)
    let hide H := let T := type of H in change (mb_hide T) in H in
    hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ; hide HA; hide HS16.
    pose proof bmb_KR_Q0_0 as HKR. unfold bmb_KR in HKR.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply ExecF.evtF_mono;
      [ eapply HKR; try eassumption; try assumption; all_rng
      | intros ms' Hms'; exact (post_of_on ms' Hms') ].
  Qed.

End OfF.
