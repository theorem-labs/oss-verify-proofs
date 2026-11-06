(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v; 296 of its 313 lines of code are new or changed and 231 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_cases0b.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF: gram_eq by the same script, mc0A_F and tail0A_F with `hide_sec.` moved first and footprint steps added, and the new lemmas sh_cover_sub and sh_word_on_sub.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the two runs of this file read the row
   [p + 254, p + 265), the out block [o, o + 32) and their shadow; they read no image or runtime cell with a fixed
   value. The pcs 0x8667c, 0x8669c / 0x866a0, 0x866ac / 0x866b0 are of the v1.9.0 image).

   The two runs of reac_box_model_block_cases0b.v (mc0A at 0x866a0 and tail0A at 0x8667c) as ExecF.evtF runs under
   a universally quantified footprint RNG, with the source's proof script, `hide_sec.` moved first and footprint steps added. The ret post Q0 is generalized to the
   section variable Q with the obligation HKR : bmb_KR Q (brief "Fixed cross-lane interface", S2 files), so the
   stretch can stop at the flag release 0x864f8. Q is INDEXED by the run's FK data (fr f spc j n w56), the
   the lead's S2 interface change of 03:20Z: the glue discharges the epi obligation only for the frame cgif
   allocated, on the fake arm. The data-region footprint facts are the section hypotheses
   Rimg .. RFSsh, Rby, Rwsw, RP .. RJ14s; no run lemma of this file adds a footprint premise of its own. *)
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
  reac_box_model_block_cases0a reac_box_model_block_cases0b.
(* The footprint twins of the files the original imports, and the shared _F callee contracts. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF
  reac_box_model_block_binv2F reac_box_model_block_cases0aF reac_box_model_block_c_on sh_word_on
  asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on rng_asan.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module BINV := reac_box_model_block_binv.
Module BCASES0A := reac_box_model_block_cases0a.
Module C0B := reac_box_model_block_cases0b.
Module BF := reac_box_model_block_baseF.
Module BEPIF := reac_box_model_block_epiF.
Module BINVF := reac_box_model_block_binvF.
Module BINV2F := reac_box_model_block_binv2F.
Module BCASES0AF := reac_box_model_block_cases0aF.
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

(* A sub-range of a region whose 8-aligned shadow word cover is in RNG has its own cover in RNG: the two bounds of
   sh_cover are monotone in the range.  Used for the __asan_memcpy SOURCE [p + 254, p + 265) inside the row
   [p, p + 296) of the section's RP / RPs; footprint bookkeeping only, no proof obligation about the run.
   It is stated OUTSIDE Section MainF on purpose: inside, `lia` drags the section's own HA / HS16 / HP .. NDJ into
   this division goal and the sentence then needs more than 64 GB (measured: the 12:54Z build of this file died at
   66.9 GB, signal 9, inside this one `lia`). *)
Lemma sh_cover_sub : forall RNG a n a' n', sh_cover RNG a n -> 0 <= a -> 0 < n -> 0 < n' ->
  a <= a' -> a' + n' <= a + n -> sh_cover RNG a' n'.
Proof.
  intros RNG a n a' n' H Ha Hn Hn' Hlo Hhi. unfold sh_cover, shadow_addr in *.
  pose proof (Z.div_le_mono a a' 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.div_le_mono (a / 8 + ASAN_K) (a' / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_le_mono ((a' + n' - 1) / 8 + ASAN_K) ((a + n - 1) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D4.
  eapply rng_sub'; [exact H | lia].
Qed.

(* A sub-range's 8-aligned shadow WORDS are shadow words of the enclosing range: the membership side of
   sh_cover_sub, for the `_on` region R.  Same text as reac_box_model_block_cases2aF.v:319 (a Theorem Labs lane), restated
   here at top level so that `lia` does not see the Section's own division facts. *)
Lemma sh_word_on_sub : forall pp nn0 qq kk aa, 0 < kk -> pp <= qq -> qq + kk <= pp + nn0 ->
  sh_word_on qq kk aa -> sh_word_on pp nn0 aa.
Proof.
  intros pp nn0 qq kk aa Hk Hlo Hhi (Hne & Hb).
  unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
  split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* Route (C): the callee contracts in their `_on` footprint form (a Theorem Labs lane's asan_memset_cF_on.v /
     asan_memcpy_cF_on.v, build_dt1_single_c.v's _on block), carried into the worktree by a Theorem Labs lane. *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C) narrowing (brief bmbF-narrow-brief.md (a working note, not in this delivery), the coordinating lane 18:0xZ): the universal shadow_rw of the proved
     file is FALSE at the allocator state, so this stretch takes only the shadow region the function and its
     callees read or store (a Theorem Labs lane's audited R, reac_box_model_block_c_on.v:38). The name SR0 is kept, so
     inst_exact of the upstream _F facts still instantiates it. *)
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

  (* The footprint and the regions these runs read or write (text of 3c9fcc93205 reac_box_model_blockF.v:147-159
     for the nine, then the data-region facts fixed for every F file of this family). *)
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

  (* The definitions of reac_box_model_block_base.v at this section's variables (interface decision (A): the pure
     definitions of the proved files are kept by Notation; only evt-bearing ones have an _F twin). *)
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

  (* The pure facts of reac_box_model_block_base.v / _binv.v / _cases0a.v at this section's variables. Under the
     narrowed SR0 the facts of the PROVED files that go through the universal shadow_rw cannot be re-imported:
     those come from the _F twins (reac_box_model_block_baseF.v, reac_box_model_block_binvF.v), bound here to the
     proved file's own names so that the proof scripts below stay the proved scripts, word for word. *)
  Let HA1 := ltac2:(inst_exact @BF.HA1_F).
  Let STW0 := ltac2:(inst_exact @BF.STW0_F).
  Let fk_facts := ltac2:(inst_exact @BF.fk_facts_F).
  Let mrd_w1 := ltac2:(inst_exact @BF.mrd_w1_F).
  Let mrd_wn_ne := ltac2:(inst_exact @BF.mrd_wn_ne_F).
  Let bytes_keep_out := ltac2:(inst_exact @BF.bytes_keep_out_F).
  Let inside_appl := ltac2:(inst_exact @BF.inside_appl_F).
  Let zeqb_addcancel := ltac2:(inst_exact @BF.zeqb_addcancel_F).
  Let rw1 := ltac2:(inst_exact @BINVF.rw1_F).
  Let djw := ltac2:(inst_exact @BINVF.djw_F).
  Let bv_ok := ltac2:(inst_exact @BINVF.bv_ok_F).
  Let bv_store := ltac2:(inst_exact @BINVF.bv_store_F).
  Let bv_jx := ltac2:(inst_exact @BINVF.bv_jx_F).
  Let cell_bytes_pt := ltac2:(inst_exact @BINVF.cell_bytes_pt_F).
  Let app_o := ltac2:(inst_exact @BINVF.app_o_F).
  Let le1_neg := ltac2:(inst_exact @BCASES0AF.le1_neg_F).
  (* gram_eq of reac_box_model_block_cases0b.v is RE-PROVED here, by the proved file's own script, instead of
     re-imported: the section closing of the proved file generalized it over that file's callee contract
     hypotheses (HMS : asan_memset_contract is the binder inst stops at), which this section does not have - it
     carries the _F contracts instead. A pure fact, no run, no new proof obligation. *)
  Lemma gram_eq : length row = 296%nat -> synok row = true ->
    withchk (firstn 31 (H8 ++ (slots row ++ tail row) ++ zeros 1)) = gram row.
  Proof.
    intros Hlen SOK. pose proof (rs_gram31_len row Hlen SOK) as G.
    replace (firstn 31 (H8 ++ (slots row ++ tail row) ++ zeros 1)) with (gram31 row).
    - unfold withchk, chk, gram. rewrite rs_gram_chk. reflexivity.
    - assert (L31 : length (H8 ++ slots row ++ tail row) = 31%nat) by (unfold gram31 in G; exact G).
      rewrite app_assoc, firstn_app, L31, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
  Qed.

  (* The _F runs of the files below this one. *)
  Let cl_ms_F := ltac2:(inst_exact @BINV2F.cl_ms_F).
  Let cl_mc_F := ltac2:(inst_exact @BINV2F.cl_mc_F).
  Let stchk0_F := ltac2:(inst_exact @BCASES0AF.stchk0_F).
  Let osum0_F := ltac2:(inst_exact @BCASES0AF.osum0_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* Branch conditions on literal-valued registers (as the plain proof's if_t/if_f). *)
  Ltac ulit := repeat match goal with
                      | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
                      end.

  (* 0x866a0: __asan_memcpy(o + 20, p + 254, 11), then the checksum loop. *)
  Lemma mc0A_F : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 0 -> synok row = true ->
    BV fr j n w56 mc (H8 ++ slots row ++ zeros 12) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x866a0) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb SOK PI.
    (* hide_sec FIRST (a Theorem Labs lane, measured 11:5xZ: the section's own HA / HS16 / HP .. NDJ make every
       Z.div_mod_to_equations + lia in this file hundreds of times slower). *)
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    unfold APPMEM_END in Boe, Bpe.
    pose proof (bv_jx fr f spc j n w56 mc _ J HK Hp0 Ho0 PI) as (_ & _ & _ & JAO & JAP & _).
    assert (APp : forall t, 0 <= t < 296 -> app_mem (p + t))
      by (intros t Ht; destruct JAP as (_ & _ & _ & PA); exact (proj1 (PA t Ht))).
    pose proof (rs_slots_len row SOK) as LS.
    assert (LT : length (tail row) = 11%nat) by (unfold tail; rewrite length_firstn, length_skipn; lia).
    pose proof (bytes_at_sub rsegs mc p row 254 11 (proj1 (proj2 (proj2 (proj2 PI)))) ltac:(lia)) as HT.
    change (firstn 11 (skipn 254 row)) with (tail row) in HT. change (Z.of_nat 254) with 254 in HT.

    unfold RB, BINVF.RB_F. step. step. step. step.
    eapply (cl_mc_F fr f spc j n w56 mc _ J 0x866b0 20 11 (p + 254) (tail row)).
    - exact HK.
    - exact Hp0.
    - exact Ho0.
    - exact PI.
    - apply ret_pc_even; [lia | reflexivity].
    - lia.
    - lia.
    - lia.
    - exact LT.
    - ulit. cbn [Z.of_nat]. lia.
    - ulit. lia.
    - ulit. cbn [Z.of_nat]. lia.
    - exact HT.
    - apply (B.acl_addr_sub mc p 296); [exact JAP | lia | lia | lia].
    - replace (p + 254 + 7) with (p + 261) by lia. apply APp. lia.
    - change (Z.of_nat 11) with 11. replace (p + 254 + 11) with (p + 265) by lia.
      apply APp. lia.
    - cbn [Z.of_nat]. clear -Dpo. lia.
    - cbn [Z.of_nat]. clear -Dpw HAlo HAhi Rsp. lia.
    - change (Z.of_nat 11) with 11. eapply rng_sub'; [exact (RP Hp0) | lia].
    - change (Z.of_nat 11) with 11.
      apply (sh_cover_sub RNG p 296 (p + 254) 11); [exact (RPs Hp0) | lia | lia | lia | lia | lia].
    - (* route (C): the memcpy SOURCE's shadow words are R's row disjunct (p <> 0 /\ sh_word_on p 296 a); the
         source [p + 254, p + 265) lies inside the row [p, p + 296). *)
      change (Z.of_nat 11) with 11. intros aa Haa.
      right. right. left. split; [exact Hp0|].
      apply (sh_word_on_sub p 296 (p + 254) 11 aa); [clear; lia | clear; lia | clear; lia | exact Haa].
    - intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc2 PI2.
      rewrite (rs_upd_fill H8 (slots row) (tail row) 12 20) in PI2 by (unfold BCASES0A.H8; cbn [length]; lia).
      rewrite LT in PI2. change (12 - 11)%nat with 1%nat in PI2.
      unfold RB, BINVF.RB_F. step. step. step. step.
      eapply (osum0_F 31 0 fr f spc j n w56 mc2 J); try eassumption.
      + lia.
      + lia.
      + cbn [Z.of_nat]. f_equal. lia.
      + reflexivity.
      + reflexivity.
      + rewrite (gram_eq Lrow SOK). rewrite Eb. symmetry. exact (proj2 (rs_synth_gram row nb SOK)).
      + rewrite Eb. exact (proj1 (rs_synth_gram row nb SOK)).
  Qed.

  (* 0x8667c: the 3-fill of the slots not yet written (when k < 12), then 0x866a0. *)
  Lemma tail0A_F : forall (k : nat) P (s5w : word) fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 0 -> synok row = true -> (k <= 12)%nat -> length P = k ->
    P ++ repeat (bz 3) (12 - k) = slots row -> s5w = Z_to_bv 64 (Z.of_nat k) ->
    BV fr j n w56 mc (H8 ++ P ++ zeros (24 - k)) J ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         s5w x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x8667c) fc None mc (seg_rom rsegs)).
  Proof.
    intros k P s5w fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb SOK Hk LP EP E5 PI.
    hide_sec.    (* first: see mc0A_F *)
    pose proof Ro as Ro'.
    pose proof (bv_jx fr f spc j n w56 mc _ J HK Hp0 Ho0 PI) as (_ & _ & _ & JAOx & _).
    assert (RO32 : 0 <= o /\ o + 32 <= 2 ^ 64)
      by (destruct JAOx as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    subst s5w.
    unfold RB, BINVF.RB_F. step. step. step.
    ulit. rewrite ?rc_swrap_small by lia. rewrite rc_ltu_lit by lia. rewrite ?Z.add_0_r.
    destruct (Z.ltb_spec 11 (Z.of_nat k)) as [K12|K11]; cbv iota.
    - assert (E12 : k = 12%nat) by lia. rewrite E12 in EP, PI.
      replace (P ++ repeat (bz 3) (12 - 12)) with P in EP
        by (rewrite Nat.sub_diag; cbn [repeat]; rewrite app_nil_r; reflexivity).
      rewrite EP in PI. change (24 - 12)%nat with 12%nat in PI.
      eapply (mc0A_F fr f spc j n w56 mc J); eassumption.
    - step. step. step. step. step. step.
      eapply (cl_ms_F fr f spc j n w56 mc _ J 0x866a0 (8 + k) (12 - k) 3).
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
      + ulit. rewrite ?rc_swrap_small by lia. ulit. lia.
      + intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc2 PI2.
        change (Z_to_bv 8 3) with (bz 3) in PI2.
        rewrite (rs_upd_fill H8 P (repeat (bz 3) (12 - k)) (24 - k) (8 + k)) in PI2
          by (unfold BCASES0A.H8; cbn [length]; rewrite ?repeat_length; lia).
        rewrite EP, repeat_length in PI2. replace (24 - k - (12 - k))%nat with 12%nat in PI2 by lia.
        eapply (mc0A_F fr f spc j n w56 mc2 J); eassumption.
  Qed.

End MainF.
