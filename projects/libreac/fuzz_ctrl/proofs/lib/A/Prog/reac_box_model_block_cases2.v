(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1645 of its 1659 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of reac_box_model_block_base.v:215's store hook: the base made it Local (a Theorem Labs lane, approved by a Theorem Labs lane, 2026-10-30). *)
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

(* reac_box_model_block, image A (asan), part 5b: the cases of the jump table at 0x219f4 that this unit proves - b = 4 (0x85e20), the three 16-bit row fields into the locals and build_dt1_single; b = 5 (0x85f04), the IDENT_FIRST block; b = 6 (0x85f98), the IDENT_LAST block. Each ends at the join 0x864bc or 0x864c0. *)

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.

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

Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HSM : asan_stack_malloc_0_contract.
  Hypothesis HMS : asan_memset_contract.
  Hypothesis HMC : asan_memcpy_contract.
  Hypothesis HBD : build_dt1_single_contract.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
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

  (* The definitions of reac_box_model_block_base.v at this section's variables. *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation KB := (B.KB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  Notation Q0 := (B.Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).

  (* The lemmas of reac_box_model_block_base.v applied to this section's variables and hypotheses (inst applies a
     base lemma to the hypotheses that carry the names of its leading binders: those are exactly the section
     variables and hypotheses the section-closing generalization abstracted it over). *)
  Let HA1 := ltac2:(inst_exact @B.HA1).
  Let STW0 := ltac2:(inst_exact @B.STW0).
  Let fk_facts := ltac2:(inst_exact @B.fk_facts).
  Let entry := ltac2:(inst_exact @B.entry).
  Let fwords := ltac2:(inst_exact @B.fwords).
  Let jr_win := ltac2:(inst_exact @B.jr_win).
  Let br_fp := ltac2:(inst_exact @B.br_fp).
  Let br_out_rt := ltac2:(inst_exact @B.br_out_rt).
  Let br_ac := ltac2:(inst_exact @B.br_ac).
  Let td_tail := ltac2:(inst_exact @B.td_tail).
  Let win_shadow0 := ltac2:(inst_exact @B.win_shadow0).
  Let wf_sub := ltac2:(inst_exact @B.wf_sub).
  Let ebw_sub := ltac2:(inst_exact @B.ebw_sub).
  Let wf_sub0 := ltac2:(inst_exact @B.wf_sub0).
  Let ebw_sub0 := ltac2:(inst_exact @B.ebw_sub0).
  Let epi_state := ltac2:(inst_exact @B.epi_state).
  Let epi_addr := ltac2:(inst_exact @B.epi_addr).
  Let win_sh_out := ltac2:(inst_exact @B.win_sh_out).
  Let epi_shadow0 := ltac2:(inst_exact @B.epi_shadow0).
  Let epi_flags := ltac2:(inst_exact @B.epi_flags).
  Let epi_close := ltac2:(inst_exact @B.epi_close).
  Let mrd_w1 := ltac2:(inst_exact @B.mrd_w1).
  Let mrd_wn_ne := ltac2:(inst_exact @B.mrd_wn_ne).
  Let bytes_keep_out := ltac2:(inst_exact @B.bytes_keep_out).
  Let inside_appl := ltac2:(inst_exact @B.inside_appl).
  Let zeqb_addcancel := ltac2:(inst_exact @B.zeqb_addcancel).


  Let epi := ltac2:(inst_exact @BEPI.epi).

  (* The definitions and lemmas of reac_box_model_block_binv.v at this section's variables. *)
  Let BF := ltac2:(inst_exact @BINV.BF).
  Let BV := ltac2:(inst_exact @BINV.BV).
  Let DJF := ltac2:(inst_exact @BINV.DJF).
  Let DJW := ltac2:(inst_exact @BINV.DJW).
  Let JX := ltac2:(inst_exact @BINV.JX).
  Let RB := ltac2:(inst_exact @BINV.RB).
  Let rw1 := ltac2:(inst_exact @BINV.rw1).
  Let inside_appr := ltac2:(inst_exact @BINV.inside_appr).
  Let dj_pair := ltac2:(inst_exact @BINV.dj_pair).
  Let djf := ltac2:(inst_exact @BINV.djf).
  Let djw := ltac2:(inst_exact @BINV.djw).
  Let sh_out := ltac2:(inst_exact @BINV.sh_out).
  Let addr_keep := ltac2:(inst_exact @BINV.addr_keep).
  Let bv_jx := ltac2:(inst_exact @BINV.bv_jx).
  Let upd_app := ltac2:(inst_exact @BINV.upd_app).
  Let rw_cb0 := ltac2:(inst_exact @BINV.rw_cb0).
  Let bv_ok := ltac2:(inst_exact @BINV.bv_ok).
  Let bv_lok := ltac2:(inst_exact @BINV.bv_lok).
  Let bv_store := ltac2:(inst_exact @BINV.bv_store).
  Let bv_lstore := ltac2:(inst_exact @BINV.bv_lstore).
  Let cell_bytes_pt := ltac2:(inst_exact @BINV.cell_bytes_pt).
  Let app_o := ltac2:(inst_exact @BINV.app_o).
  Let spc_bounds := ltac2:(inst_exact @BINV.spc_bounds).
  Let exit_r := ltac2:(inst_exact @BINV.exit_r).
  Let fin1 := ltac2:(inst_exact @BINV.fin1).
  Let bv_fok := ltac2:(inst_exact @BINV.bv_fok).
  Let bv_sok := ltac2:(inst_exact @BINV.bv_sok).
  Let bv_frame_dj := ltac2:(inst_exact @BINV.bv_frame_dj).
  Let bv_fstore := ltac2:(inst_exact @BINV.bv_fstore).
  Let bv_sstore := ltac2:(inst_exact @BINV.bv_sstore).
  Let call_facts := ltac2:(inst_exact @BINV.call_facts).

  Let rw_upd2 := ltac2:(inst_exact @BINV2.rw_upd2).
  Let cl_ms := ltac2:(inst_exact @BINV2.cl_ms).
  Let cl_mc := ltac2:(inst_exact @BINV2.cl_mc).
  Let app_loc := ltac2:(inst_exact @BINV2.app_loc).
  Let cl_ms_loc := ltac2:(inst_exact @BINV2.cl_ms_loc).
  Let cl_bd := ltac2:(inst_exact @BINV2.cl_bd).


  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
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
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
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
    | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
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
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
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
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
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
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
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
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?AA ?bs) _) =>
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
  Lemma cs4 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 4 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85e20) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    unfold APPMEM_END in Boe, Bpe.
    assert (Hp8 : p mod 8 = 0) by (hide_sec; destruct (HP Hp0) as (H1 & _); exact H1).
    assert (LJ : length J = 56%nat) by (destruct PI as (_ & _ & [[[LJ0 _] _] _] & _); exact LJ0).
    hide_sec.
    assert (RX1 : 0 <= p + 268 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX2 : 0 <= p + 270 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX3 : 0 <= p + 272 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RA19 : 0 <= A + 19 < 2 ^ 64) by (clear -HAlo HAhi HHM' Rsp; lia).
    (* the 56 local bytes, so that the reads back of what the stores wrote compute *)
    do 56 (destruct J as [|? J]; [cbn in LJ; discriminate | cbn in LJ]).
    destruct J as [|? J]; [|cbn in LJ; discriminate].
    unfold RB, reac_box_model_block_binv.RB.
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
    (* 0x85ea8: j 0x864bc, the join with the result 1 *)
    - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mc' PI'.
      unfold RB, reac_box_model_block_binv.RB. step.
      eapply (fin1 fr f spc j n w56 mc' (dt1s 1536 (rvb row)) _); try eassumption.
      + rewrite Eb. reflexivity.
      + rewrite Eb. reflexivity.
  Qed.


  (* b = 5 (0x85f04), IDENT_FIRST: the checked has field at p + 56 (zero: s5 = 0, release at 0x864c0); memset of the
     16 name bytes at A + 19; the checked rname at p + 280 and the checked name copy loop (a4_nl5); the 21 checked
     header bytes at o .. o + 20; memcpy of the first 10 name bytes to o + 21; the checked outer checksum loop, the
     checked check byte at o + 31 and the join 0x864bc (a4_ol5). *)
  Lemma cs5 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 5 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85f04) fc None mc (seg_rom rsegs)).
  Proof.
    (* 0x8627c .. 0x864bc: the outer checksum loop, the checked check byte at o + 31, the join (fin1) *)
    assert (a4_ol5 : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (X J : list byte)
        (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
      FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
      withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
      BV fr j n w56 mc X J ->
      evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
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
      pose proof Ro as Ro'.
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
      unfold RB, reac_box_model_block_binv.RB.
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
      | |- evt ?segs ?Q (MS ?R ?F (if _ then ?B else _) ?fc ?rv ?mm ?ro) =>
          enough (G : forall rr : word, evt segs Q (MS (bvmap_set (Z_to_bv 5 13) rr R) F B fc rv mm ro));
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
         evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 y10 y11 y12 y13 y14 y15 x16 x17
                              x21 x22 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x86034) fc None mc' (seg_rom rsegs))) ->
      evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
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
      pose proof (name_ok_lt nb qi qOK ltac:(clear -qHik; lia) qHnz) as qHi.
      assert (qHNB : bytes_at rsegs qmc (rname row) nb)
        by (destruct qPI as (_ & _ & _ & _ & qHn); exact (qHn qB56 qH1 qH2)).
      pose proof (bytes_at_bound _ _ _ _ qHNB) as qBN.
      pose proof (rd_byte rsegs qmc (rname row) nb qi qHNB qHi) as qRD.
      clear qHNB.
      assert (qRX : 0 <= rname row + Z.of_nat qi < 2 ^ 64) by (clear -qBN qHi; lia).
      (* 0x85f58 .. 0x85f90: the checked 1-byte access at a0 = rname row + i *)
      pose proof (bv_jx _ _ _ _ _ _ qmc _ _ qHK qHp0 qHo0 qPI) as qJX.
      destruct qJX as (_ & _ & _ & _ & _ & _ & qJAN & _).
      pose proof (qJAN qB56 qH1 qH2) as qJAN1. clear qJAN.
      pose proof (B.acl_shadow qmc (rname row) (Z.of_nat (length nb)) (Z.of_nat qi) 1 (rname row + Z.of_nat qi)
                    qJAN1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -qHi; lia)
                    ltac:(clear; Z.div_mod_to_equations; lia) eq_refl) as qSH.
      clear qJAN1.
      rewrite <- Hoff in qSH.
      unfold RB, reac_box_model_block_binv.RB.
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
        | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
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
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    unfold APPMEM_END in Boe, Bpe.
    assert (B56 : b = 5 \/ b = 6) by (left; exact Eb).
    assert (Hp8 : p mod 8 = 0) by (hide_sec; destruct (HP Hp0) as (H1 & _); exact H1).
    assert (LJ : length J = 56%nat) by (destruct PI as (_ & _ & [[[LJ0 _] _] _] & _); exact LJ0).
    hide_sec.
    assert (RX56 : 0 <= p + 56 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RX280 : 0 <= p + 280 < 2 ^ 64) by (clear -Rp' Bpe; lia).
    assert (RA19 : 0 <= A + 19 < 2 ^ 64) by (clear -HAlo HAhi HHM' Rsp; lia).
    assert (RO : 0 <= o < 2 ^ 64) by (clear -Ro'; lia).
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
    unfold RB, reac_box_model_block_binv.RB.
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
        unfold RB, reac_box_model_block_binv.RB. step.
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
        rewrite rc_eqb_lit by (first [clear; lia | pose proof (rs_rw64_range row 280) as RN;
                                      change (rw64 row 280) with (rname row) in RN; clear -RN; lia]).
        (* 0x86034 .. 0x86278: the 21 header bytes, the 10 name bytes and the entry of the outer sum *)
        assert (TAIL : forall (mc2 : word -> option byte) (y10 y11 y12 y13 y14 y15 : word),
                  BV fr j n w56 mc2 (zeros 32) (JA ++ nmr row nb ++ JB) ->
                  evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 0x85f30) (Z_to_bv 64 spc) u0 u1 u2
                                       y10 y11 y12 y13 y14 y15 u16 u17 x21 x22 x26 x27 u28 u29 u30 u31)
                                   F (Z_to_bv 64 0x86034) fc None mc2 (seg_rom rsegs))).
        { intros mc2 y10 y11 y12 y13 y14 y15 PI2. unfold RB, reac_box_model_block_binv.RB.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 0 ltac:(clear; lia) PI0) as SH end.
          rewrite Z.add_0_r in SH.
          chk_core o RO (Z_to_bv 5 11) SH pre_sr no_extra.
          step. step. ost 0.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 1 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 1) RXo1 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 1.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 2 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 2) RXo2 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 2. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 3 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 3) RXo3 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 3.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 4 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 4) RXo4 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 4. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 5 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 5) RXo5 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 5.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 6 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 6) RXo6 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 6. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 7 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 7) RXo7 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 7.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 8 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 8) RXo8 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 8.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 9 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 9) RXo9 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 9.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 10 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 10) RXo10 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 10.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 11 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 11) RXo11 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 11.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 12 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 12) RXo12 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 12. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 13 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 13) RXo13 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 13. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 14 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 14) RXo14 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 14.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 15 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 15) RXo15 (Z_to_bv 5 13) SH pre_sr no_extra.
          ost 15. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 16 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 16) RXo16 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 16.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 17 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 17) RXo17 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 17. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 18 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 18) RXo18 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. step. ost 18.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 19 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 19) RXo19 (Z_to_bv 5 12) SH pre_sr no_extra.
          ost 19. step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            pose proof (SHO mm X0 J0 20 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 20) RXo20 (Z_to_bv 5 12) SH pre_sr no_extra.
          step. ost 20.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J0 |- _ =>
            replace X0 with (map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1]
                             ++ [] ++ zeros 11) in PI0
              by (rewrite !rc_le1_lit;
                  replace (Z_to_bv 8 (-2)) with (bz 254) by (apply Z_to_bv8_mod; reflexivity);
                  replace (Z_to_bv 8 (-16)) with (bz 240) by (apply Z_to_bv8_mod; reflexivity);
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
            unfold RB, reac_box_model_block_binv.RB. do 4 step.
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
  Lemma a4_cl_mc_loc : forall fr f spc j n w56 mc X J (ret : Z) (dd nn : nat) (SS : Z) (src : list byte)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (dd + nn <= 56)%nat -> (1 <= nn)%nat -> (dd + 7 <= 56)%nat ->
    length src = nn ->
    bv_unsigned a0 = A + Z.of_nat dd -> bv_unsigned a1 = SS -> bv_unsigned a2 = Z.of_nat nn ->
    bytes_at rsegs mc SS src -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) -> app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= A + Z.of_nat dd \/ A + Z.of_nat dd + Z.of_nat nn <= SS) ->
    (SS + Z.of_nat nn <= bv_unsigned sp - 4272 \/ A <= SS) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' X (upd_bytes J dd src) ->
       evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret dd nn SS src a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hdn Hn Hd7 LS E0 E1 E2 HSb HAS HS7 HSN DSD DSW K.
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
    unfold RB, reac_box_model_block_binv.RB.
    eapply evt_cut.
    { eapply HMC with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn dd J)) (src := src);
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
      - exact JSW.
      - exact MI. }
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

  (* b = 6, the name copy of 0x85fec .. 0x8601c (ASan slow path 0x86020): the NUL-terminated name at rname row, at
     most 16 bytes, into the local bytes at A + 40; a0 = a1 = rname row + i, a2 = the count left, a3 = A + 40 + i.
     The exit is the join 0x862b4 with nmf nb in the 16 bytes (a0 .. a5 changed). *)
  Lemma a4_cs6_name : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
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
       evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 y10 y11 y12 y13 y14 y15 x16 x17
                            x21 x22 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x862b4) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                         (Z_to_bv 64 ri) (Z_to_bv 64 ri) (Z_to_bv 64 (Z.of_nat kk)) (Z_to_bv 64 ai) x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85fec) fc None mc (seg_rom rsegs)).
  Proof.
    assert (UPRE : forall (J0 Y bs : list byte) i, (i + length bs <= length Y)%nat ->
      upd_bytes (J0 ++ Y) (length J0 + i) bs = J0 ++ upd_bytes Y i bs).
    { clear. intros J0 Y bs i H. unfold upd_bytes. rewrite firstn_app, skipn_app.
      replace (length J0 + i - length J0)%nat with i by lia.
      replace (length J0 + i + length bs - length J0)%nat with (i + length bs)%nat by lia.
      rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite <- !app_assoc. reflexivity. }
    assert (OKN : p <> 0 -> b = 6 -> has row <> 0 -> rname row <> 0 -> name_ok nb).
    { intros Hp0 Eb H1 H2. destruct (HN Hp0 (or_intror Eb) H1 H2) as (OK & _). exact OK. }
    hide_sec.
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
    (* 0x85fec .. 0x85ff8, 0x86020, 0x86024: the checked 1-byte access at a0 = rname row + i *)
    pose proof (bv_jx _ _ _ _ _ _ mc _ _ HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (_ & _ & _ & _ & _ & _ & JAN & _).
    pose proof (JAN B56 H1 H2) as JAN1. clear JAN.
    pose proof (B.acl_shadow mc (rname row) (Z.of_nat (length nb)) (Z.of_nat i) 1 (rname row + Z.of_nat i) JAN1
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Hi; lia)
                  ltac:(clear; Z.div_mod_to_equations; lia) eq_refl) as SH.
    clear JAN1.
    rewrite <- Hoff in SH.
    unfold RB, reac_box_model_block_binv.RB.
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

  (* b = 6, 0x863ec .. 0x863f8: the inner sum of build_ident_last over the 21 record bytes at A + 19; a0 = A + 19 + i,
     a1 = psum REC i, a2 = A + 40. The record is in the frame's own locals, so its loads carry no shadow check. *)
  Lemma a4_cs6_rsum : forall (kk i : nat) (REC : list byte) (f fr spc ai : Z) (mc : word -> option byte)
      (x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    (i + kk = 21)%nat -> (0 < kk)%nat -> length REC = 21%nat -> 0 <= A -> A + 56 < 2 ^ 64 ->
    ai = A + 19 + Z.of_nat i -> bytes_at rsegs mc (A + 19) REC ->
    (forall y10 y12 y13 : word,
       evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 y10 (Z_to_bv 64 (psum REC 21)) y12 y13
                            x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x863fc) fc None mc (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                         (Z_to_bv 64 ai) (Z_to_bv 64 (psum REC i)) (Z_to_bv 64 (A + 40)) x13
                         x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x863ec) fc None mc (seg_rom rsegs)).
  Proof.
    hide_sec.
    induction kk as [|kk IH];
      intros i REC f fr spc ai mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        Hik Hk LR HA0 HA56 Eai HREC K; [clear -Hk; lia|].
    subst ai.
    pose proof (rd_byte rsegs mc (A + 19) REC i HREC ltac:(clear -LR Hik; lia)) as RD.
    pose proof (psum_range REC i) as PR.
    unfold RB, reac_box_model_block_binv.RB.
    (* 0x863ec: lbu a3, 0(a0); 0x863f0: a0 + 1; 0x863f4: a1 + a3 *)
    step. clear RD. step. step.
    rewrite psum_S_zxb.
    (* 0x863f8: bne a0, a2, 0x863ec *)
    step.
    rewrite (rc_eqb_lit (A + 19 + Z.of_nat i + 1) (A + 40)) by (clear -HA0 HA56 Hik; lia).
    destruct kk as [|kk].
    - replace (A + 19 + Z.of_nat i + 1 =? A + 40) with true by (symmetry; apply Z.eqb_eq; clear -Hik; lia).
      cbn [negb]. cbv iota. replace (S i) with 21%nat by (clear -Hik; lia).
      unfold RB, reac_box_model_block_binv.RB in K. apply K.
    - replace (A + 19 + Z.of_nat i + 1 =? A + 40) with false by (symmetry; apply Z.eqb_neq; clear -Hik; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i) REC f fr spc (A + 19 + Z.of_nat i + 1)); first [clear -Hik; lia | assumption].
  Qed.

  (* b = 6, 0x86448 .. 0x86470 (ASan slow path 0x86474): the outer checksum loop over the first 31 bytes of the box
     at o (a0 = a3 = o + i, a1 = psum X i, a2 = the count kk left), each load with its 1-byte shadow check; then
     0x864a0 .. 0x864b8 (slow path 0x86920): the checked store of the check byte (- psum X 31) mod 256 at o + 31, and
     the join at 0x864bc (fin1). *)
  Lemma a4_cs6_bsum : forall (kk i : nat) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (X J : list byte) (oi : Z)
      (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 -> oi = o + Z.of_nat i ->
    BV fr j n w56 mc X J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7
                         (Z_to_bv 64 oi) (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat kk)) (Z_to_bv 64 oi)
                         x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x86448) fc None mc (seg_rom rsegs)).
  Proof.
    (* the byte that neg a1, a1; sb a1, 0(a0) stores *)
    assert (NEG : forall s, le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)]).
    { clear. intros s. rewrite rc_le1_lit. f_equal. apply Z_to_bv8_mod. change (2^8) with 256.
      rewrite Z.mod_mod by lia. rewrite unsigned_lit_wrap.
      change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
    assert (RW1 : forall mm AA N Xc, rw_cells rsegs mm AA [CB N Xc] -> bytes_at rsegs mm AA Xc).
    { clear. intros mm AA N Xc [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    hide_sec.
    induction kk as [|kk IH];
      intros i fr f spc j n w56 mc X J oi x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        HK Hp0 Ho0 Hik Hk LX ES Er Eoi PI; [clear -Hk; lia|].
    subst oi.
    pose proof Ro as Ro'.
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
    unfold RB, reac_box_model_block_binv.RB.
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

  (* b = 6, 0x862b4 .. 0x86444 (build_ident_last after the name field NM is in the locals at A + 40): the five record
     header bytes 5 0 16 0 1 at A + 19, __asan_memcpy(A + 24, A + 40, 16) (the record's copy of the name), the nine
     checked header bytes of the box, __asan_memcpy(o + 9, A + 50, 6) (the last six name bytes), the record sum, the
     checked stamp byte (- psum) mod 128 at o + 15 and the 247 at o + 16, then the block sum loop. *)
  Lemma a4_cs6_tail : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (J0 NM : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 6 -> has row <> 0 ->
    length J0 = 40%nat -> length NM = 16%nat -> NM = nmr row nb ->
    BV fr j n w56 mc (zeros 32) (J0 ++ NM) ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x862b4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J0 NM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb H0 LJ0 LNM ENM PI.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Ro as Ro'. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    unfold APPMEM_END in Boe, Bpe.
    hide_sec.
    assert (RO : 0 <= o < 2 ^ 64) by (clear -Ro'; lia).
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
    unfold RB, reac_box_model_block_binv.RB.
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
      unfold RB, reac_box_model_block_binv.RB.
      (* 0x862e4 .. 0x863c8: the nine checked header bytes 4 2 0 13 0 2 0 254 8 of the box *)
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 0 ltac:(clear; lia) PI0) as SH end.
      rewrite Z.add_0_r in SH.
      chk_core o RO (Z_to_bv 5 11) SH pre_sr no_extra.
      step. step. ost 0.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 1 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 1) RXo1 (Z_to_bv 5 12) SH pre_sr no_extra.
      step. step. ost 1.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 2 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 2) RXo2 (Z_to_bv 5 12) SH pre_sr no_extra.
      ost 2. step.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 3 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 3) RXo3 (Z_to_bv 5 12) SH pre_sr no_extra.
      step. step. ost 3.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 4 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 4) RXo4 (Z_to_bv 5 12) SH pre_sr no_extra.
      ost 4. step.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 5 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 5) RXo5 (Z_to_bv 5 12) SH pre_sr no_extra.
      step. step. ost 5.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 6 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 6) RXo6 (Z_to_bv 5 12) SH pre_sr no_extra.
      ost 6. step.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 7 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 7) RXo7 (Z_to_bv 5 12) SH pre_sr no_extra.
      step. step. ost 7.
      match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
        pose proof (SHO mm X0 J1 8 ltac:(clear; lia) PI0) as SH end.
      chk_core (o + 8) RXo8 (Z_to_bv 5 12) SH pre_sr no_extra.
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
      + clear -Dow HAlo HAhi; cbn [Z.of_nat]; lia.
      + right. clear; lia.
      + intros v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 mq2 PQ2.
        lazymatch type of PQ2 with ?h ?fr0 ?j0 ?n0 ?w0 ?mm ?X0 ?J0 => change (BV fr0 j0 n0 w0 mm X0 J0) in PQ2 end.
        unfold upd_bytes in PQ2. cbn [firstn skipn app length Nat.add] in PQ2.
        (* 0x863e0 .. 0x863e8: the registers of the record sum, then its loop *)
        unfold RB, reac_box_model_block_binv.RB. step. step. step.
        match goal with
        | PI0 : BV _ _ _ _ ?mm _ ?Jf |- _ =>
            let HL := fresh "HL" in
            assert (HL : rw_cells rsegs mm A [CB 56 Jf]) by (destruct PI0 as (_ & _ & H & _); exact H);
            pose proof (rs_cell0_sub rsegs mm A 56 Jf [] 19 21 HL ltac:(clear; lia)) as HREC;
            change (Z.of_nat 19) with 19 in HREC; cbn [firstn skipn] in HREC; clear HL
        end.
        match type of HREC with bytes_at _ ?mm _ ?REC =>
          eapply (a4_cs6_rsum 21 0 REC f fr spc (A + 19) mm)
        end.
        * clear; lia.
        * clear; lia.
        * reflexivity.
        * exact RA0.
        * exact RA56.
        * clear; lia.
        * exact HREC.
        * intros y10 y12 y13. unfold RB, reac_box_model_block_binv.RB.
          rewrite EPS.
          (* 0x863fc .. 0x8640c, 0x86908: a0 = o + 15 and its shadow check *)
          step.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
            pose proof (SHO mm X0 J1 15 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 15) RXo15 (Z_to_bv 5 13) SH pre_sr no_extra.
          (* 0x86410 .. 0x8641c: negw / andi 127, a0 = o + 16, the stamp byte at o + 15 *)
          step. step. step. ost 15.
          match goal with PI0 : BV _ _ _ _ ?mm ?X0 ?J1 |- _ =>
            pose proof (SHO mm X0 J1 16 ltac:(clear; lia) PI0) as SH end.
          chk_core (o + 16) RXo16 (Z_to_bv 5 12) SH pre_sr no_extra.
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
              eapply (a4_cs6_bsum 31 0 fr f spc j n w56 mm X0 Jf o)
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

  (* b = 6 (0x85f98): the IDENT_LAST block (build_ident_last). The checked has field at p + 56 (0: the box stays zero
     and the result is 0, exit 0x864c0); else the name field at A + 40 (memset, the checked rname at p + 280, the
     name copy loop), then the tail at 0x862b4 and the join at 0x864bc. *)
  Lemma cs6 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 6 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85f98) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (_ & _ & _ & _ & _ & _ & Lrow & _ & Bpe).
    unfold APPMEM_END in Bpe.
    assert (Hp8 : p mod 8 = 0) by (hide_sec; destruct (HP Hp0) as (H1 & _); exact H1).
    assert (LJ : length J = 56%nat) by (destruct PI as (_ & _ & [[[LJ0 _] _] _] & _); exact LJ0).
    assert (OKN : has row <> 0 -> rname row <> 0 -> name_ok nb)
      by (intros H1 H2; hide_sec; destruct (HN Hp0 (or_intror Eb) H1 H2) as (OK & _); exact OK).
    hide_sec.
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
    unfold RB, reac_box_model_block_binv.RB.
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
        unfold RB, reac_box_model_block_binv.RB. step.
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
        rewrite rc_eqb_lit by (first [clear; lia | pose proof (rs_rw64_range row 280) as RN;
                                      change (rw64 row 280) with (rname row) in RN; clear -RN; lia]).
        destruct (Z.eqb_spec (rname row) 0) as [N0|N0]; cbv iota.
        * (* no name: the sixteen zero bytes are nmr row nb *)
          eapply (a4_cs6_tail fr f spc j n w56 mc1 JA (repeat (Z_to_bv 8 0) 16));
            [exact HK | exact Hp0 | exact Ho0 | exact Eb | exact H0 | exact LJA | reflexivity | | exact PI1].
          unfold nmr. rewrite (proj2 (Z.eqb_eq _ _) N0). reflexivity.
        * (* 0x85fe0 .. 0x85fe8: a2 = 16, a3 = A + 40, a0 = rname row, then the name copy loop at 0x85fec *)
          do 3 step.
          pose proof (OKN H0 N0) as OK.
          eapply (a4_cs6_name 16 0 fr f spc j n w56 mc1 JA (repeat (Z_to_bv 8 0) 16) (rname row) (A + 40)).
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
             eapply (a4_cs6_tail fr f spc j n w56 mc2 JA (nmf nb));
               [exact HK | exact Hp0 | exact Ho0 | exact Eb | exact H0 | exact LJA | | | exact PI2].
             ++ unfold nmf. rewrite length_app, repeat_length. pose proof (rs_takenz_len nb) as TL.
                destruct OK as ((_ & L16) & _). clear -TL L16. lia.
             ++ unfold nmr. rewrite (proj2 (Z.eqb_neq _ _) N0). reflexivity.
  Qed.

End Main.
