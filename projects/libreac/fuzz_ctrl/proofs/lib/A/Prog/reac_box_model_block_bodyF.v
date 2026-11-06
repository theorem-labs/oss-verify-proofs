(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 461 of its 476 lines of code are new or changed and 233 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_body.v at a working branch d69f7c708f6 (proved v1.9 run
   of record) over lib/Lib/StepF: addr_keep_app, bv_init and upd0z by the same proof script, out_wf and dj_wf with `hide_sec.` moved first, body_none_F and body_F with changed steps (the epi obligation through bmb_KR, KB's extra ra').
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: the jump table at 0x219f4, 28 bytes (file offset 0x119f4 from
   the LOAD vaddr 0x10000 off 0x0 of fuzz_ctrl.debug):
     94 42 06 00 | f8 44 06 00 | b8 44 06 00 | c4 44 06 00 | 2c 44 06 00 | 10 45 06 00 | a4 45 06 00
   i.e. the seven entries 0x64294 0x644f8 0x644b8 0x644c4 0x6442c 0x64510 0x645a4, which the dispatch adds to the
   table address 0x219f4: the case entries 0x85c88 (cs0), 0x85eec (cs1), 0x85eac (cs2), 0x85eb8 (cs3), 0x85e20
   (cs4), 0x85f04 (cs5), 0x85f98 (cs6).  The table lies inside the image range Rimg, so it needs no premise of its
   own.  No other const cell is read by these two runs.

   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z), obeyed here except condition 1:
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and no
      new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header (image root, ELF sha256, tool version, which compare) and goes to
      the auditor a Theorem Labs lane, who signs it against its proved run before it counts.
   5. A StepF "uncovered access" error means STOP: report it.  Do not widen the footprint to make it pass.

   The two runs of reac_box_model_block_body.v (body_none, body) are S2 runs: in the original they conclude the
   fixed ret-post Q0 through `epi`.  Here the post is the section variable Q and the epi obligation is the section
   hypothesis HKR : bmb_KR Q (reac_box_model_block_epiF.v), so the stretch can stop at the flag release 0x864f8.
   reac_box_model_block_body.v's code is unchanged since release c5e779efe8c (comments edited); it keeps every code line of the source above and adds 11; its pure section facts (addr_keep_app, out_wf, dj_wf, bv_init, upd0z)
   are re-proved below by their own script, not re-imported by inst_exact. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2 reac_box_model_block_cases reac_box_model_block_cases0a reac_box_model_block_cases0b reac_box_model_block_cases0c reac_box_model_block_cases0 reac_box_model_block_cases2 reac_box_model_block_body.
(* The footprint twins this file chains: the callee contracts (a Theorem Labs lane's shared text) and the F files of the
   originals above. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF
  reac_box_model_block_binv2F reac_box_model_block_casesF reac_box_model_block_cases0aF
  reac_box_model_block_cases0bF reac_box_model_block_cases0cF reac_box_model_block_cases0F
  reac_box_model_block_cases2aF reac_box_model_block_cases2bF.
(* Route (C): the narrowed shadow premise, the region it names, and the callees' `_on` contracts (a Theorem Labs lane's
   text, carried by a Theorem Labs lane from a working branch f4423e55886 and a working branch). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan sh_word_on asan_memset_c_on
  asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on reac_box_model_block_c_on.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* reac_box_model_block, image A (asan), part 10 in footprint form: the body 0x85c48 .. 0x864c0 - the p = 0 and
   o = 0 exits, the box zeroed by __asan_memset, the b > 6 exit, and the jump table at 0x219f4 dispatching to the
   seven cases. *)

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.
Module BCASES := reac_box_model_block_cases.
Module BCASES0A := reac_box_model_block_cases0a.
Module BCASES0B := reac_box_model_block_cases0b.
Module BCASES0C := reac_box_model_block_cases0c.
Module BCASES0 := reac_box_model_block_cases0.
Module BCASES2 := reac_box_model_block_cases2.
Module BBODY := reac_box_model_block_body.
Module SRON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

Module BaseF := reac_box_model_block_baseF.
Module EpiF := reac_box_model_block_epiF.
Module BinvF := reac_box_model_block_binvF.
Module Binv2F := reac_box_model_block_binv2F.
Module CasesF := reac_box_model_block_casesF.
Module Cases0F := reac_box_model_block_cases0F.
Module Cases2aF := reac_box_model_block_cases2aF.
Module Cases2bF := reac_box_model_block_cases2bF.

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

(* The store hook of the evt walk, re-issued for the evtF walk: it also transports rd_mono. *)
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
   does not relate to the [rng] premise of its region.  Normalize the wrap, then close the bounds from any rng
   hypothesis; Z.div_mod_to_equations is needed where the address or the bound holds a division. *)
Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (wa ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len (wa E) n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit_wrap;
          Z.div_mod_to_equations; lia
      end
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
  (* The callee contracts in footprint form (a Theorem Labs lane's shared text).  No lemma of this file takes the stack
     malloc contract: S2 starts after the 0x85bb8 call has returned. *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C) narrowing (a Theorem Labs lane batch 75): not the universal A.AsanRT.shadow_rw, which is false at the allocator
     state, but the shadow region this function and its callees read or write (a Theorem Labs lane's audited region,
     reac_box_model_block_c_on.v:38). *)
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

  (* The footprint and the regions these runs read or write (reac_box_model_block_cF.v, the nine of the Section
     plus the runtime words; then the data regions, which every F file of the family carries). *)
  Variable RNG : footprint.
  Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
  Hypothesis Rrt : rng RNG RT_LO (RT_HI - RT_LO).
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

  (* The definitions of reac_box_model_block_base.v at this section's variables (unchanged: only KB, which names
     evt, has an F twin). *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  (* Route (C): the ret post is a Theorem Labs lane's _on form (reac_box_model_block_c_on.v:47), whose shadow conjunct is
     the region transport `forall P, shadow_rw_on P m -> shadow_rw_on P m'`; under the narrowed SR0 the universal
     `shadow_rw m'` of B.Q0 is not provable (a Theorem Labs lane). *)
  Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  (* The box invariant in its narrowed form: BINV.BV with the `shadow_rw mc` conjunct of JX replaced by
     shadow_rw_on over the audited region (route (C), reac_box_model_block_binvF.v's BV_F). *)
  Let BV := ltac2:(inst_exact @BinvF.BV_F).
  Let RB := ltac2:(inst_exact @BinvF.RB_F).

  (* The KB obligation in footprint form (reac_box_model_block_baseF.v). *)
  Let KB_F := ltac2:(inst_exact @BaseF.KB_F).

  (* The post of this stretch: the S2 lemmas of the family conclude the section variable Q, and reach it through
     the epi obligation bmb_KR (reac_box_model_block_epiF.v) where the original applies epi. *)
  Let bmb_KR := ltac2:(inst_exact @EpiF.bmb_KR).
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The pure section facts this file's two runs use.  A fact of a Theorem Labs lane's ORIGINAL files that goes through the
     universal shadow_rw is taken from its F twin instead (route (C), the lead's naming decision (2)):
     fk_facts_F (reac_box_model_block_baseF.v) and bv_jx_F (reac_box_model_block_binvF.v).  The facts of
     reac_box_model_block_body.v itself are RE-PROVED below by their own script, because the closing of its
     Section Main generalized them over the ORIGINAL callee contracts (HMS, HMC, HBD), which an _F section does
     not carry. *)
  Let HA1 := ltac2:(inst_exact @BaseF.HA1_F).
  Let fk_facts := ltac2:(inst_exact @BaseF.fk_facts_F).
  Let mrd_wn_ne := ltac2:(inst_exact @BaseF.mrd_wn_ne_F).
  Let bv_jx := ltac2:(inst_exact @BinvF.bv_jx_F).
  Let djf := ltac2:(inst_exact @BinvF.djf_F).
  Let dj_pair := ltac2:(inst_exact @BinvF.dj_pair_F).
  Let app_o := ltac2:(inst_exact @BinvF.app_o_F).

  (* The runs this file chains, in footprint form. *)
  Let cl_ms_F := ltac2:(inst_exact @Binv2F.cl_ms_F).
  Let exit_r_F := ltac2:(inst_exact @BinvF.exit_r_F).
  Let cs0_F := ltac2:(inst_exact @Cases0F.cs0_F).
  Let cs1_F := ltac2:(inst_exact @CasesF.cs1_F).
  Let cs2_F := ltac2:(inst_exact @CasesF.cs2_F).
  Let cs3_F := ltac2:(inst_exact @CasesF.cs3_F).
  Let cs4_F := ltac2:(inst_exact @Cases2aF.cs4_F).
  Let cs5_F := ltac2:(inst_exact @Cases2aF.cs5_F).
  Let cs6_F := ltac2:(inst_exact @Cases2bF.cs6_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.

  (* --- the pure facts of reac_box_model_block_body.v, by its own script (see the note above) --- *)

  (* A store into application memory keeps every addressable range (it writes no shadow byte).
     reac_box_model_block_body.v:360-379, verbatim. *)
  Lemma addr_keep_app : forall (mm : word -> option byte) (a : Z) (bs : list byte) (R nR : Z),
    addressable mm R nR -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> Z.of_nat (length bs) <= 4096 ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> app_mem (a + i)) ->
    addressable (write_to_mem mm (wa a) bs) R nR.
  Proof.
    intros mm a bs R nR HAx Ha Hl Hsz Happ.
    pose proof HAx as (R0 & Rn & Re & HAd).
    apply (B.addr_keep mm (write_to_mem mm (wa a) bs) R nR HAx).
    intros i Hi. destruct (HAd i Hi) as (Hap & bb & Hb & Hok).
    pose proof (rt_app_shadow (R + i) Hap) as Hsh.
    destruct (Z.eq_dec (Z.of_nat (length bs)) 0) as [E0|E0].
    - apply mrd_wn_ne; [exact Ha | exact Hl | | clear -E0; lia].
      pose proof (rt_shadow_bound _ Hsh) as HB. clear -HB; lia.
    - pose proof (Happ 0 ltac:(clear -E0; lia)) as A0. rewrite Z.add_0_r in A0.
      pose proof (Happ (Z.of_nat (length bs) - 1) ltac:(clear -E0; lia)) as A1.
      pose proof (rt_shadow_bound _ Hsh) as HB.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0, A1.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
      apply mrd_wn_ne; [exact Ha | exact Hl | clear -HB; lia | clear -A0 A1 Hsh HB E0 Hl Hsz; lia].
  Qed.

  (* An application byte apart from the window, from the class-0 side-stack bytes and from the frame is outside
     the frame footprint Wf.  reac_box_model_block_body.v:386-421, verbatim. *)
  Lemma out_wf : forall fr f spc j n w56 x, FK fr f spc j n w56 -> app_mem x ->
    (x < bv_unsigned sp - 4272 \/ bv_unsigned sp <= x) -> outside (fp_w [0%nat] FS) x ->
    ~ (fr <= x < fr + 64) -> outside (Wf fr j n) x.
  Proof.
    intros fr f spc j n w56 x HK Hap Hwin Hfpw Hfr.
    (* speed (a Theorem Labs lane): hide the Section's / and mod facts from zify BEFORE anything else *)
    hide_sec.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold fp_w, fp_w1 in Hfpw. cbn [flat_map app outside] in Hfpw.
    destruct Hfpw as (Hhint & Hflag & Hframe & _).
    assert (EH : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (EFl : fs_flag FS 0 j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    assert (Hjn : (j = 0 /\ n = 0) \/ (0 <= j < 16384 /\ n = 1)).
    { destruct HK as [(_ & _ & _ & Ej & En) | (Hj & _ & _ & _ & _ & En)];
        [left; split; assumption | right; rewrite EM in Hj; split; assumption]. }
    rewrite EH in Hhint. rewrite EF0, EM in Hflag.
    unfold B.Wf. cbn [outside].
    split; [clear -Hwin; lia|].
    split; [exact Hhint|].
    split; [rewrite EFl; clear -Hflag Hjn; lia|].
    split; [exact Hfr|].
    split; [|exact I].
    pose proof (B.acl_sh_out x fr (fr + 64) Hap) as HS.
    pose proof (B.sh_add8 fr 8 FR8) as E8. replace (fr + 8 * 8) with (fr + 64) in E8 by lia.
    rewrite E8 in HS. apply HS.
    - pose proof (FAP 0 ltac:(lia)) as AF0. rewrite Z.add_0_r in AF0.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF0. clear -AF0; lia.
    - pose proof (FAP 63 ltac:(lia)) as AF63.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF63. unfold APPMEM_END. clear -AF63; lia.
  Qed.

  (* A range of application memory apart from the window, the side-stack header ranges and the frame is apart
     from the frame footprint Wf.  reac_box_model_block_body.v:425-452, verbatim. *)
  Lemma dj_wf : forall fr f spc j n w56 (R nR : Z), FK fr f spc j n w56 -> 0 < nR -> nR <= 4096 ->
    (R + nR <= bv_unsigned sp - 4272 \/ bv_unsigned sp <= R) ->
    (forall x, R <= x < R + nR -> app_mem x) ->
    (R + nR <= fs_hint FS 0 \/ fs_hint FS 0 + 8 <= R) ->
    (R + nR <= fs_flag FS 0 0 \/ fs_flag FS 0 0 + fs_M 0 <= R) ->
    (R + nR <= fr \/ fr + 64 <= R) ->
    disjoint_from (Wf fr j n) R nR.
  Proof.
    intros fr f spc j n w56 R nR HK HnR HnR' Dwin Dapp Dhint Dflag Dfr.
    (* speed (a Theorem Labs lane): hide_sec first *)
    hide_sec.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (EFl : fs_flag FS 0 j = fs_flag FS 0 0 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    assert (Hjn : (j = 0 /\ n = 0) \/ (0 <= j < 16384 /\ n = 1)).
    { destruct HK as [(_ & _ & _ & Ej & En) | (Hj & _ & _ & _ & _ & En)];
        [left; split; assumption | right; rewrite EM in Hj; split; assumption]. }
    rewrite EM in Dflag.
    unfold B.Wf. cbn [disjoint_from].
    split; [clear -Dwin; lia|].
    split; [unfold fs_hint in Dhint; cbn [Z.of_nat] in Dhint; clear -Dhint; lia|].
    split; [rewrite EFl; clear -Dflag Hjn HnR; lia|].
    split; [clear -Dfr; lia|].
    split; [|exact I].
    pose proof (Dapp R ltac:(lia)) as AR. pose proof (Dapp (R + nR - 1) ltac:(lia)) as AR1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AR, AR1.
    clear -AR AR1 SH1 SH2 HnR HnR' Hoff. unfold shadow_addr in *. lia.
  Qed.

  (* The box cell, the row and the name bytes at a memory the frame set-up reached.
     reac_box_model_block_body.v:455-545, verbatim. *)
  Lemma bv_init : forall fr f spc j n w56 mc, FK fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BI (Wf fr j n) fr w56 mc -> exists J, BV fr j n w56 mc ob J.
  Proof.
    intros fr f spc j n w56 mc HK Hp0 Ho0 HB.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    destruct (djf fr f spc j n w56 HK Hp0 Ho0) as (DJo & DJp & DJn & _).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct HB as (MU & WM & RM & MI & SV & HH & F56).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & HDd0).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    assert (HOc : rw_cells rsegs m o [CB 32 ob] /\ (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272))
      by (hide_sec; destruct (HO Ho0) as (H1 & H2 & _); split; assumption).
    destruct HOc as (HOC & Dow).
    assert (HPf : length row = 296%nat /\ bytes_at rsegs m p row /\
                  (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272))
      by (hide_sec; destruct (HP Hp0) as (_ & H1 & H2 & H3 & _); split; [exact H1|]; split; assumption).
    destruct HPf as (Lrow & HRB0 & Dpw).
    assert (HNf : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
              bytes_at rsegs m (rname row) nb /\
              (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
              fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS))
      by (hide_sec; intros B5 H1 H2; destruct (HN Hp0 B5 H1 H2) as (_ & N2 & N3 & _);
          split; [exact N2|]; split; [exact N3 | exact (NDJ Hp0 B5 H1 H2)]).
    assert (APo : forall t, 0 <= t <= 32 -> app_mem (o + t)) by (apply app_o; exact Ho0).
    assert (APp : forall t, 0 <= t < 296 -> app_mem (p + t))
      by (hide_sec; intros t Ht; destruct (AP Hp0) as (_ & _ & _ & PA); exact (proj1 (PA t Ht))).
    assert (APn : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
              forall t, 0 <= t < Z.of_nat (length nb) -> app_mem (rname row + t))
      by (hide_sec; intros B5 H1 H2 t Ht; destruct (ANB Hp0 B5 H1 H2) as (_ & _ & _ & PA);
          exact (proj1 (PA t Ht))).
    (* the box cell and the row and name bytes survive the frame set-up *)
    assert (INO : In (o, o + 32) (reac_box_model_block_D p o)).
    { unfold reac_box_model_block_D. apply in_or_app. right.
      replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0). left. reflexivity. }
    assert (INP : In (p, p + 296) (reac_box_model_block_D p o)).
    { unfold reac_box_model_block_D. apply in_or_app. left.
      replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0). left. reflexivity. }
    assert (OUTo : forall x, o <= x < o + 32 -> outside (Wf fr j n) x).
    { intros x Hx. apply (out_wf fr f spc j n w56 x HK).
      - replace x with (o + (x - o)) by lia. apply APo. lia.
      - clear -Dow Hx; lia.
      - exact (fl_dj_out_r (reac_box_model_block_D p o) (fp_w [0%nat] FS) o (o + 32) x HDd0 INO Hx).
      - clear -DJo Hx; lia. }
    assert (OUTp : forall x, p <= x < p + 296 -> outside (Wf fr j n) x).
    { intros x Hx. apply (out_wf fr f spc j n w56 x HK).
      - replace x with (p + (x - p)) by lia. apply APp. lia.
      - clear -Dpw Hx; lia.
      - exact (fl_dj_out_r (reac_box_model_block_D p o) (fp_w [0%nat] FS) p (p + 296) x HDd0 INP Hx).
      - clear -DJp Hx; lia. }
    (* the locals cell is carved out of the window *)
    pose proof (B.stk_mono m mc _ _ ST0 WM RM) as STm.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) (A + 56) (bv_unsigned sp) STm ltac:(lia)) as [STl _].
    destruct (stk_carve rsegs mc (bv_unsigned sp - 4272) (A + 56) 56 STl ltac:(lia)) as [_ [junk FRl]].
    change (Z.of_nat 56) with 56 in FRl. replace (A + 56 - 56) with A in FRl by lia.
    exists junk.
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - eapply munch_weaken; [|exact MU]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx. apply B.out_appinv in Hx. exact (proj1 Hx).
    - exact WM.
    - exact RM.
    - exact MI.
    - exact SV.
    - exact HH.
    - exact F56.
    - split; [|split; [|split]].
      + apply (rw_cells_transport rsegs (Wf fr j n) m mc o [CB 32 ob] HOC MU WM).
        cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
        apply (dj_wf fr f spc j n w56 o 32 HK ltac:(lia) ltac:(lia)).
        * clear -Dow; lia.
        * intros x Hx. replace x with (o + (x - o)) by lia. apply APo. lia.
        * pose proof (dj_pair (reac_box_model_block_D p o) (fp_w [0%nat] FS) o (o + 32)
                        (fs_hint FS 0) (fs_hint FS 0 + 8) HDd0 INO
                        ltac:(unfold fp_w, fp_w1; cbn [flat_map app]; left; reflexivity)) as Hdj.
          unfold ly_dj in Hdj. clear -Hdj; lia.
        * pose proof (dj_pair (reac_box_model_block_D p o) (fp_w [0%nat] FS) o (o + 32)
                        (fs_flag FS 0 0) (fs_flag FS 0 0 + fs_M 0) HDd0 INO
                        ltac:(unfold fp_w, fp_w1; cbn [flat_map app]; right; left; reflexivity)) as Hdj.
          unfold ly_dj in Hdj. clear -Hdj; lia.
        * clear -DJo; lia.
      + exact FRl.
      + apply (fl_bytes (Wf fr j n) m mc p row HRB0 MU). rewrite Lrow. exact OUTp.
      + intros B5 H1 H2. destruct (HNf B5 H1 H2) as (HNB0 & Dnw & Dnj).
        apply (fl_bytes (Wf fr j n) m mc (rname row) nb HNB0 MU).
        intros x Hx. apply (out_wf fr f spc j n w56 x HK).
        * replace x with (rname row + (x - rname row)) by lia. apply (APn B5 H1 H2). lia.
        * clear -Dnw Hx; lia.
        * exact (fl_dj_out_r [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)
                   (rname row) (rname row + Z.of_nat (length nb)) x Dnj ltac:(left; reflexivity) Hx).
        * pose proof (DJn B5 H1 H2) as DN. clear -DN Hx; lia.
  Qed.

  (* reac_box_model_block_body.v:550-554, verbatim. *)
  Lemma upd0z : forall (X : list byte), length X = 32%nat -> upd_bytes X 0 (repeat (Z_to_bv 8 0) 32) = zeros 32.
  Proof.
    intros X L. unfold upd_bytes. cbn [firstn]. rewrite skipn_all2 by (rewrite repeat_length; lia).
    rewrite app_nil_r. reflexivity.
  Qed.

  (* --- the body: 0x85c48 .. 0x864c0 --- *)

  (* The box result is not written (p = 0 or o = 0): the release with the result -1. *)
  Lemma body_none_F : forall fr f spc j n w56 mc
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc -> (p =? 0) || (o =? 0) = true ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
                              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x864c0) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK HB Etrue.
    destruct HB as (MU & WM & RM & MI & SV & HH & F56).
    pose proof HKR as HR. unfold bmb_KR, EpiF.bmb_KR in HR.
    eapply HR.
    - exact HK.
    - unfold B.EB, B.EBW. rewrite Etrue. rewrite app_nil_r.
      split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|].
      split; [exact SV|]. split; [exact HH|]. split; [exact F56 | exact I].
    - rewrite Etrue. reflexivity.
  Qed.

  (* The body from the frame set-up (KB_F's state at 0x85c48) to the frame release. *)
  Lemma body_F : KB_F Q.
  Proof.
    unfold KB_F, BaseF.KB_F.
    intros fr f spc j n w56 mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HK HB.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'. pose proof Rb as Rb'.
    (* 0x85c48: li s5, -1 *)
    step.
    destruct (Z.eq_dec p 0) as [P0|P0].
    { step.
      replace (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) with true
        by (symmetry; rewrite (rc_eqb_lit p 0) by lia; apply Z.eqb_eq; exact P0).
      cbv iota.
      eapply (body_none_F fr f spc j n w56 mc); [exact HK | exact HB | rewrite P0; reflexivity]. }
    step.
    replace (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) with false
      by (symmetry; rewrite (rc_eqb_lit p 0) by lia; apply Z.eqb_neq; exact P0).
    cbv iota.
    destruct (Z.eq_dec o 0) as [O0|O0].
    { step.
      replace (bv_eqb (Z_to_bv 64 o) (Z_to_bv 64 0)) with true
        by (symmetry; rewrite (rc_eqb_lit o 0) by lia; apply Z.eqb_eq; exact O0).
      cbv iota.
      eapply (body_none_F fr f spc j n w56 mc); [exact HK | exact HB | rewrite O0; apply orb_true_r]. }
    step.
    replace (bv_eqb (Z_to_bv 64 o) (Z_to_bv 64 0)) with false
      by (symmetry; rewrite (rc_eqb_lit o 0) by lia; apply Z.eqb_neq; exact O0).
    cbv iota.
    rename P0 into Hp0. rename O0 into Ho0.
    (* the box zeroed: __asan_memset(o, 0, 32) *)
    destruct (bv_init fr f spc j n w56 mc HK Hp0 Ho0 HB) as (J0 & PI).
    pose proof PI as (_ & HO32 & _).
    pose proof HO32 as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lob _].
    assert (RO32 : 0 <= o /\ o + 32 <= 2 ^ 64).
    { pose proof (bv_jx fr f spc j n w56 mc ob J0 HK Hp0 Ho0 PI) as (_ & _ & _ & JAO & _).
      destruct JAO as (Pa & _ & Pe & _). unfold APPMEM_END in Pe. clear -Pa Pe; lia. }
    hide_sec.
    step. step. step. step.
    eapply (cl_ms_F fr f spc j n w56 mc ob J0 0x85c64 0 32 0).
    - exact HK.
    - exact Hp0.
    - exact Ho0.
    - exact PI.
    - apply ret_pc_even; [lia | reflexivity].
    - lia.
    - lia.
    - lia.
    - lia.
    - cbn [Z.of_nat]. rewrite Z.add_0_r. apply unsigned_lit. lia.
    - apply unsigned_lit. lia.
    - apply unsigned_lit. lia.
    - intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc1 PI1.
      rewrite (upd0z ob Lob) in PI1.
      pose proof PI1 as ((_ & _ & _ & MI1 & _) & _).
      unfold RB, BinvF.RB_F.
      step. step.
      destruct (Z.ltb_spec 6 b) as [B6|B6].
      + (* b > 6: the box stays zero and the result is -1 *)
        replace (bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 b)) with true
          by (symmetry; rewrite (rc_ltu_lit 6 b) by lia; apply Z.ltb_lt; exact B6).
        cbv iota.
        eapply (exit_r_F fr f spc j n w56 mc1 (zeros 32) J0 (-1)); try eassumption.
        * unfold synth. replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        * unfold rc. replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + replace (bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 b)) with false
          by (symmetry; rewrite (rc_ltu_lit 6 b) by lia; apply Z.ltb_ge; exact B6).
        cbv iota.
        assert (EBc : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6) by lia.
        (* the post keeps b; only the register that selects the jump-table entry is rewritten *)
        set (QQ := Q) in *.
        destruct EBc as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb; do 7 step; unfold QQ.
        * pose proof (cs0_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
        * pose proof (cs1_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
        * pose proof (cs2_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
        * pose proof (cs3_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
        * pose proof (cs4_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
        * pose proof (cs5_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
        * pose proof (cs6_F fr f spc j n w56 mc1 J0) as C; unfold RB, BinvF.RB_F, mkR in C.
          eapply C; eassumption.
  Qed.

End MainF.
