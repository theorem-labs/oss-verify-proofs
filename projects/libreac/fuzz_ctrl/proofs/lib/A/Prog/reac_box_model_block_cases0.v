(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 553 of its 567 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2 reac_box_model_block_cases0a reac_box_model_block_cases0b reac_box_model_block_cases0c.
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

(* reac_box_model_block, image A (asan), part 9: case b = 0 (0x85c88) - the input and output counts of the row with their shadow checks and the four synok exits, the eight header bytes of the grammar block (each store checked), the layout byte at p + 290, and the first slot fill of each layout (__asan_memset at 0x85e14 for layout 1, 0x86624 for layout 2), joining the blocks of reac_box_model_block_cases0c.v. *)

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.
Module BCASES0A := reac_box_model_block_cases0a.
Module BCASES0B := reac_box_model_block_cases0b.
Module BCASES0C := reac_box_model_block_cases0c.

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

  (* The lemmas of reac_box_model_block_cases0a.v at this section's variables. *)
  Notation H8 := (BCASES0A.H8 row).
  Let le1_neg := ltac2:(inst_exact @BCASES0A.le1_neg).
  Let stchk0 := ltac2:(inst_exact @BCASES0A.stchk0).
  Let osum0 := ltac2:(inst_exact @BCASES0A.osum0).

  (* The lemmas of reac_box_model_block_cases0b.v at this section's variables. *)
  Let gram_eq := ltac2:(inst_exact @BCASES0B.gram_eq).
  Let mc0A := ltac2:(inst_exact @BCASES0B.mc0A).
  Let tail0A := ltac2:(inst_exact @BCASES0B.tail0A).

  (* The lemmas of reac_box_model_block_cases0c.v at this section's variables. *)
  Notation nsi := (BCASES0C.nsi row).
  Notation nso := (BCASES0C.nso row).
  Let sfacts := ltac2:(inst_exact @BCASES0C.sfacts).
  Let blk68 := ltac2:(inst_exact @BCASES0C.blk68).
  Let blk8c := ltac2:(inst_exact @BCASES0C.blk8c).


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
                      ltac:(Z.div_mod_to_equations; lia) eq_refl) as H;
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


  Lemma cs0 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 0 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (-1)) x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85c88) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'.
    assert (HPf : p mod 8 = 0 /\ length row = 296%nat)
      by (hide_sec; destruct (HP Hp0) as (H1 & H2 & _); split; assumption).
    destruct HPf as (Hp8 & Lrow).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    assert (RXp : forall k, 0 <= k <= 296 -> 0 <= p + k < 2 ^ 64)
      by (pose proof JAP as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; intros k Hk; lia).
    assert (RXo : forall k, 0 <= k <= 32 -> 0 <= o + k < 2 ^ 64)
      by (pose proof JAO as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; intros k Hk; lia).
    pose proof (rs_rd4 rsegs mc p row 16 (proj1 (proj2 (proj2 (proj2 PI)))) ltac:(lia)) as R16.
    pose proof (rs_rd4 rsegs mc p row 20 (proj1 (proj2 (proj2 (proj2 PI)))) ltac:(lia)) as R20.
    change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 20) with 20 in R20.
    pose proof (rs_ic_range row) as RI. pose proof (rs_oc_range row) as RO.
    assert (SYF : forall X, synok row = false -> X = synth row b nb -> X = zeros 32).
    { intros X S E. rewrite E, Eb. change (synth row 0 nb) with (if synok row then gram row else zeros 32).
      rewrite S. reflexivity. }
    assert (RCF : synok row = false -> -1 = rc row b).
    { intros S. rewrite Eb. change (rc row 0) with (if synok row then 1 else -1). rewrite S. reflexivity. }
    hide_sec.
    unfold RB, BINV.RB.
    (* the input and output counts *)
    step.
    pose proof (RXp 16 ltac:(lia)) as RX16.
    pose proof (B.acl_shadow mc p 296 16 4 (p + 16) JAP ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH16.
    chk_core (p + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr add1.
    step. rewrite rs_sx32_ic. step.
    rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (ic row) 0) as [I0|I0]; cbv iota.
    { assert (S : synok row = false)
        by (unfold synok; replace (0 <=? ic row) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      eapply (exit_r fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption.
      - symmetry. exact (SYF _ S eq_refl).
      - exact (RCF S). }
    step.
    pose proof (RXp 20 ltac:(lia)) as RX20.
    pose proof (B.acl_shadow mc p 296 20 4 (p + 20) JAP ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH20.
    chk_core (p + 20) RX20 (Z_to_bv 5 12) SH20 pre_sr add1.
    step. rewrite rs_sx32_oc. step.
    rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (oc row) 0) as [O0|O0]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (0 <=? oc row) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite !andb_false_r. reflexivity. }
      eapply (exit_r fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption.
      - symmetry. exact (SYF _ S eq_refl).
      - exact (RCF S). }
    step. step. step.
    rewrite (rs_or3 (ic row) (oc row)) by lia.
    destruct (Z.eqb_spec (ic row mod 4) 0) as [IM|IM]; [destruct (Z.eqb_spec (oc row mod 4) 0) as [OM|OM]|];
      cbn [andb negb]; cbv iota.
    2,3: assert (S : synok row = false) by
           (unfold synok; rewrite ?(proj2 (Z.eqb_neq _ _) IM), ?(proj2 (Z.eqb_neq _ _) OM), ?andb_false_r;
            reflexivity);
         eapply (exit_r fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption;
         [ symmetry; exact (SYF _ S eq_refl) | exact (RCF S) ].
    step. rewrite rs_srliw2 by lia. step. rewrite rs_srliw2 by lia. step. step.
    assert (RSI : 0 <= ic row / 4 <= 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (RSO : 0 <= oc row / 4 <= 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    step. rewrite rc_ltu_lit by lia.
    destruct (Z.ltb_spec 12 (oc row / 4 + ic row / 4)) as [G|G]; cbv iota.
    { assert (S : synok row = false).
      { unfold synok. replace (ic row / 4 + oc row / 4 <=? 12) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r. reflexivity. }
      eapply (exit_r fr f spc j n w56 mc (zeros 32) J (-1)); try eassumption.
      - symmetry. exact (SYF _ S eq_refl).
      - exact (RCF S). }
    assert (SOK : synok row = true)
      by (unfold synok; repeat (apply andb_true_iff; split); first [apply Z.leb_le | apply Z.eqb_eq]; lia).
    (* the eight header bytes of the grammar block *)
    pose proof (RXo 0 ltac:(lia)) as RXo0. rewrite Z.add_0_r in RXo0.
    sho 0 1. chk_core o RXo0 (Z_to_bv 5 11) SH pre_sr no_extra.
    step. step. ost 0.
    pose proof (RXo 1 ltac:(lia)) as RXo1.
    sho 1 1. chk_core (o + 1) RXo1 (Z_to_bv 5 12) SH pre_sr no_extra.
    step. step. ost 1.
    pose proof (RXo 2 ltac:(lia)) as RXo2.
    sho 2 1. chk_core (o + 2) RXo2 (Z_to_bv 5 12) SH pre_sr no_extra.
    ost 2.
    step.
    pose proof (RXo 3 ltac:(lia)) as RXo3.
    sho 3 1. chk_core (o + 3) RXo3 (Z_to_bv 5 12) SH pre_sr no_extra.
    step. ost 3.
    (* the selector byte at p + 252 and the trap byte at p + 253 *)
    step.
    pose proof (RXp 252 ltac:(lia)) as RXp252.
    shp2 252 1.
    chk_core (p + 252) RXp252 (Z_to_bv 5 12) SH pre_sr no_extra.
    step.
    rrow 252%nat.
    pose proof (RXo 4 ltac:(lia)) as RXo4.
    sho 4 1. chk_core (o + 4) RXo4 (Z_to_bv 5 13) SH pre_sr no_extra.
    ost 4.
    step.
    pose proof (RXo 5 ltac:(lia)) as RXo5.
    sho 5 1. chk_core (o + 5) RXo5 (Z_to_bv 5 12) SH pre_sr no_extra.
    ost 5.
    step.
    pose proof (RXo 6 ltac:(lia)) as RXo6.
    sho 6 1. chk_core (o + 6) RXo6 (Z_to_bv 5 12) SH pre_sr no_extra.
    ost 6.
    step.
    pose proof (RXp 253 ltac:(lia)) as RXp253.
    shp2 253 1.
    chk_core (p + 253) RXp253 (Z_to_bv 5 12) SH pre_sr no_extra.
    step.
    rrow 253%nat.
    pose proof (RXo 7 ltac:(lia)) as RXo7.
    sho 7 1. chk_core (o + 7) RXo7 (Z_to_bv 5 13) SH pre_sr no_extra.
    ost 7.
    (* the layout byte at p + 290 *)
    step.
    pose proof (RXp 290 ltac:(lia)) as RXp290.
    shp2 290 1.
    chk_core (p + 290) RXp290 (Z_to_bv 5 12) SH pre_sr no_extra.
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
        eapply (blk68 fr f spc j n w56 _ J); try eassumption.
        rewrite (ZO OZ). reflexivity.
      + do 6 step. rewrite ?(rs_seqz (oc row / 4)) by lia. step.
        eapply (cl_ms fr f spc j n w56 _ (H8 ++ [] ++ zeros 24) J 0x85e18 8 nso 1).
        * exact HK.
        * exact Hp0.
        * exact Ho0.
        * eassumption.
        * apply ret_pc_even; [lia | reflexivity].
        * lia.
        * lia.
        * lia.
        * lia.
        * ulit. lia.
        * ulit. lia.
        * ulit. lia.
        * intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mcm PIm.
          change (Z_to_bv 8 1) with (bz 1) in PIm.
          rewrite (rs_upd_fill H8 [] (repeat (bz 1) nso) 24 8) in PIm
            by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
          rewrite repeat_length in PIm. cbn [app] in PIm.
          unfold RB, BINV.RB. step. step.
          eapply (blk68 fr f spc j n w56 mcm J); try eassumption.
          ulit. f_equal. lia.
    - (* layout 2: the input slots (value 2) first *)
      step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (ic row) 0) as [IZ|IZ]; cbv iota.
      + step.
        lazymatch goal with
        | PIc : BV _ _ _ _ _ ?X _ |- _ =>
            replace X with (H8 ++ repeat (bz 2) nsi ++ zeros (24 - nsi)) in PIc
              by (rewrite (ZI IZ); reflexivity)
        end.
        eapply (blk8c fr f spc j n w56 _ J); try eassumption.
        rewrite (ZI IZ). reflexivity.
      + do 5 step. rewrite ?(rs_seqz (ic row / 4)) by lia. step.
        eapply (cl_ms fr f spc j n w56 _ (H8 ++ [] ++ zeros 24) J 0x86628 8 nsi 2).
        * exact HK.
        * exact Hp0.
        * exact Ho0.
        * eassumption.
        * apply ret_pc_even; [lia | reflexivity].
        * lia.
        * lia.
        * lia.
        * lia.
        * ulit. lia.
        * ulit. lia.
        * ulit. lia.
        * intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mcm PIm.
          change (Z_to_bv 8 2) with (bz 2) in PIm.
          rewrite (rs_upd_fill H8 [] (repeat (bz 2) nsi) 24 8) in PIm
            by (unfold H8; cbn [length]; rewrite ?repeat_length; lia).
          rewrite repeat_length in PIm. cbn [app] in PIm.
          unfold RB, BINV.RB. step.
          eapply (blk8c fr f spc j n w56 mcm J); try eassumption.
          ulit. f_equal. lia.
  Qed.

End Main.
