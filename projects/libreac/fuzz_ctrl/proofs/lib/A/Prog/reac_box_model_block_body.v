(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 579 of its 593 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2 reac_box_model_block_cases reac_box_model_block_cases0a reac_box_model_block_cases0b reac_box_model_block_cases0c reac_box_model_block_cases0 reac_box_model_block_cases2.
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

(* reac_box_model_block, image A (asan), part 10: the body 0x85c48 .. 0x864c0 - the p = 0 and o = 0 exits, the box zeroed by __asan_memset, the b > 6 exit, and the jump table at 0x219f4 dispatching to the seven cases. *)

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
  Notation BV := (BINV.BV ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS A row nb).
  Let DJF := ltac2:(inst_exact @BINV.DJF).
  Let DJW := ltac2:(inst_exact @BINV.DJW).
  Let JX := ltac2:(inst_exact @BINV.JX).
  Notation RB := (BINV.RB sp gp tp p o off A).
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

  (* The cases of the jump table at 0x219f4, from reac_box_model_block_cases0.v (b = 0), reac_box_model_block_cases.v
     (b = 1, 2, 3) and reac_box_model_block_cases2.v (b = 4, 5, 6). *)
  Let cs0 := ltac2:(inst_exact @BCASES0.cs0).
  Let cs1 := ltac2:(inst_exact @BCASES.cs1).
  Let cs2 := ltac2:(inst_exact @BCASES.cs2).
  Let cs3 := ltac2:(inst_exact @BCASES.cs3).
  Let cs4 := ltac2:(inst_exact @BCASES2.cs4).
  Let cs5 := ltac2:(inst_exact @BCASES2.cs5).
  Let cs6 := ltac2:(inst_exact @BCASES2.cs6).


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


  (* Branch conditions on literal-valued registers (as the plain proof's if_t/if_f). *)
  Ltac ulit := repeat match goal with
                      | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
                      end.
  Ltac cond_solve := unfold_cond; ulit; first [solve_cond_rec | solve_cond_base].
  Ltac if_t := lazymatch goal with
               | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; cond_solve]
               end.
  Ltac if_f := lazymatch goal with
               | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; cond_solve]
               end.

  (* A store into application memory keeps every addressable range (it writes no shadow byte). *)
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


  (* --- the invariant at the body's entry --- *)

  (* An application byte apart from the window, from the class-0 side-stack bytes and from the frame is outside the
     frame footprint Wf. *)
  Lemma out_wf : forall fr f spc j n w56 x, FK fr f spc j n w56 -> app_mem x ->
    (x < bv_unsigned sp - 4272 \/ bv_unsigned sp <= x) -> outside (fp_w [0%nat] FS) x ->
    ~ (fr <= x < fr + 64) -> outside (Wf fr j n) x.
  Proof.
    intros fr f spc j n w56 x HK Hap Hwin Hfpw Hfr.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HHM as HHM'. pose proof HAE as HAE'. hide_sec.
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

  (* A range of application memory apart from the window, the side-stack header ranges and the frame is apart from
     the frame footprint Wf. *)
  Lemma dj_wf : forall fr f spc j n w56 (R nR : Z), FK fr f spc j n w56 -> 0 < nR -> nR <= 4096 ->
    (R + nR <= bv_unsigned sp - 4272 \/ bv_unsigned sp <= R) ->
    (forall x, R <= x < R + nR -> app_mem x) ->
    (R + nR <= fs_hint FS 0 \/ fs_hint FS 0 + 8 <= R) ->
    (R + nR <= fs_flag FS 0 0 \/ fs_flag FS 0 0 + fs_M 0 <= R) ->
    (R + nR <= fr \/ fr + 64 <= R) ->
    disjoint_from (Wf fr j n) R nR.
  Proof.
    intros fr f spc j n w56 R nR HK HnR HnR' Dwin Dapp Dhint Dflag Dfr.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HHM as HHM'. pose proof HAE as HAE'. hide_sec.
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

  (* The box cell, the row and the name bytes at a memory the frame set-up reached. *)
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


  (* --- the body: 0x85c48 .. 0x864c0 --- *)

  Lemma upd0z : forall (X : list byte), length X = 32%nat -> upd_bytes X 0 (repeat (Z_to_bv 8 0) 32) = zeros 32.
  Proof.
    intros X L. unfold upd_bytes. cbn [firstn]. rewrite skipn_all2 by (rewrite repeat_length; lia).
    rewrite app_nil_r. reflexivity.
  Qed.

  (* The box result is not written (p = 0 or o = 0): the release with the result -1. *)
  Lemma body_none : forall fr f spc j n w56 mc
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc -> (p =? 0) || (o =? 0) = true ->
    evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
                          (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x864c0) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK HB Etrue.
    destruct HB as (MU & WM & RM & MI & SV & HH & F56).
    eapply epi.
    - exact HK.
    - unfold B.EB, B.EBW. rewrite Etrue. rewrite app_nil_r.
      split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|].
      split; [exact SV|]. split; [exact HH|]. split; [exact F56 | exact I].
    - rewrite Etrue. reflexivity.
  Qed.

  (* The body from the frame set-up (KB's state at 0x85c48) to the frame release. *)
  Lemma body : KB Q0.
  Proof.
    unfold B.KB.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HK HB.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'. pose proof Rb as Rb'.
    (* 0x85c48: li s5, -1 *)
    step.
    destruct (Z.eq_dec p 0) as [P0|P0].
    { step.
      replace (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) with true
        by (symmetry; rewrite (rc_eqb_lit p 0) by lia; apply Z.eqb_eq; exact P0).
      cbv iota.
      eapply (body_none fr f spc j n w56 mc); [exact HK | exact HB | rewrite P0; reflexivity]. }
    step.
    replace (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) with false
      by (symmetry; rewrite (rc_eqb_lit p 0) by lia; apply Z.eqb_neq; exact P0).
    cbv iota.
    destruct (Z.eq_dec o 0) as [O0|O0].
    { step.
      replace (bv_eqb (Z_to_bv 64 o) (Z_to_bv 64 0)) with true
        by (symmetry; rewrite (rc_eqb_lit o 0) by lia; apply Z.eqb_eq; exact O0).
      cbv iota.
      eapply (body_none fr f spc j n w56 mc); [exact HK | exact HB | rewrite O0; apply orb_true_r]. }
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
    eapply (cl_ms fr f spc j n w56 mc ob J0 0x85c64 0 32 0).
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
      unfold RB, BINV.RB.
      step. step.
      destruct (Z.ltb_spec 6 b) as [B6|B6].
      + (* b > 6: the box stays zero and the result is -1 *)
        replace (bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 b)) with true
          by (symmetry; rewrite (rc_ltu_lit 6 b) by lia; apply Z.ltb_lt; exact B6).
        cbv iota.
        eapply (exit_r fr f spc j n w56 mc1 (zeros 32) J0 (-1)); try eassumption.
        * unfold synth. replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        * unfold rc. replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + replace (bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 b)) with false
          by (symmetry; rewrite (rc_ltu_lit 6 b) by lia; apply Z.ltb_ge; exact B6).
        cbv iota.
        assert (EBc : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6) by lia.
        (* the post keeps b; only the register that selects the jump-table entry is rewritten *)
        set (QQ := Q0) in *.
        destruct EBc as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb; do 7 step; unfold QQ.
        * pose proof (cs0 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
        * pose proof (cs1 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
        * pose proof (cs2 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
        * pose proof (cs3 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
        * pose proof (cs4 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
        * pose proof (cs5 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
        * pose proof (cs6 fr f spc j n w56 mc1 J0) as C; unfold RB, BINV.RB, mkR in C.
          eapply C; eassumption.
  Qed.

End Main.
