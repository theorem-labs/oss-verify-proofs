(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 427 of its 441 lines of code are new or changed and 234 lines of the source are left out. *)
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

(* reac_box_model_block, image A (asan), part 6: the tail of case b = 0 - the 31-byte checksum loop at 0x866c0 (a shadow check before each byte), the check byte at o + 31 (store check at 0x866f8) and the release with the result 1. *)

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
    - pose proof (Happ 0 ltac:(lia)) as A0. rewrite Z.add_0_r in A0.
      pose proof (Happ (Z.of_nat (length bs) - 1) ltac:(lia)) as A1.
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



  (* --- b = 0 (0x85c88): the grammar block --- *)

  Definition H8 : list byte := [bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row].

  (* The 64-bit neg of the running sum, as the check byte. *)
  Lemma le1_neg : forall s, le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)].
  Proof.
    intros s. rewrite rc_le1_lit. f_equal. apply Z_to_bv8_mod. change (2 ^ 8) with 256.
    rewrite Z.mod_mod by lia. rewrite unsigned_lit_wrap.
    change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
  Qed.

  (* 0x866f8: the check byte at o + 31 (the store check joins 0x864b4 from both arms) and the release. *)
  Lemma stchk0 : forall fr f spc j n w56 mc J X (a1w : word)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 -> a1w = Z_to_bv 64 (psum X 31) ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 a1w x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x866f8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J X a1w x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 PI EX Er E1.
    pose proof Ro as Ro'. pose proof (psum_range X 31) as PR.
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (_ & _ & _ & JAO & _).
    assert (LX : length X = 32%nat)
      by (pose proof PI as (_ & [[[L _] _] _] & _); exact L).
    assert (RXo31 : 0 <= o + 31 < 2 ^ 64)
      by (pose proof JAO as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    pose proof (B.acl_shadow mc o 32 31 1 (o + 31) JAO ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear; lia) eq_refl) as SH.
    destruct SH as (kk & RK & OK & KR).
    subst a1w. unfold RB, BINV.RB.
    step.
    step. rewrite ?(unsigned_lit (o + 31)) by lia. rewrite ?rc_shr3.
    steps_until_if. clear RK.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR; lia).
    destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbn [negb]; cbv iota.
    - step. ost 31. rewrite le1_neg in PI0.
      eapply (fin1 fr f spc j n w56 _ (upd_bytes X (Z.to_nat 31) [bz (- psum X 31 mod 256)]) J);
        try eassumption.
      rewrite <- EX. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by lia.
      change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by lia.
      rewrite app_nil_r. reflexivity.
    - step. rewrite ?(unsigned_lit (o + 31)) by lia. rewrite rc_land7.
      step.
      pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl) as MB.
      rewrite (rc_lts_signed ((o + 31) mod 8) (bv_signed kk)) by (clear -MB KR; lia).
      replace ((o + 31) mod 8 <? bv_signed kk) with true
        by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]).
      cbv iota.
      step. ost 31. rewrite le1_neg in PI0.
      eapply (fin1 fr f spc j n w56 _ (upd_bytes X (Z.to_nat 31) [bz (- psum X 31 mod 256)]) J);
        try eassumption.
      rewrite <- EX. unfold withchk, chk, upd_bytes, bz. rewrite rs_psum_firstn by lia.
      change (Z.to_nat 31) with 31%nat. cbn [length Nat.add]. rewrite (skipn_all2 X) by lia.
      rewrite app_nil_r. reflexivity.
  Qed.

  (* 0x866c0: the 31-byte checksum loop of the b = 0 path. *)
  Lemma osum0 : forall k i fr f spc j n w56 mc J X (a0w a2w a3w : word)
      (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    (i + k = 31)%nat -> (0 < k)%nat -> a0w = Z_to_bv 64 (o + Z.of_nat i) -> a3w = a0w ->
    a2w = Z_to_bv 64 (Z.of_nat k) ->
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 a0w (Z_to_bv 64 (psum X i))
                         a2w a3w x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x866c0) fc None mc (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i fr f spc j n w56 mc J X a0w a2w a3w x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
        Hik Hk E0 E3 E2 HK Hp0 Ho0 PI EX Er; [lia|].
    pose proof Ro as Ro'.
    assert (LX : length X = 32%nat) by (pose proof PI as (_ & [[[L _] _] _] & _); exact L).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (_ & _ & _ & JAO & _).
    assert (RXoi : 0 <= o + Z.of_nat i < 2 ^ 64)
      by (pose proof JAO as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe Hik; lia).
    pose proof (rd_byte rsegs mc o X i (rw1 mc o 32 X (proj1 (proj2 PI))) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    pose proof (B.acl_shadow mc o 32 (Z.of_nat i) 1 (o + Z.of_nat i) JAO ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear; lia) eq_refl) as SH.
    subst a0w a3w a2w. unfold RB, BINV.RB.
    chk_core (o + Z.of_nat i) RXoi (Z_to_bv 5 15) SH pre_sr no_extra.
    step. step. step. step. rewrite psum_S_zxb. step. step.
    ulit.
    destruct k as [|k].
    - match goal with |- context [bv_eqb (Z_to_bv 64 ?z) (Z_to_bv 64 0)] =>
        rewrite (rc_eqb_lit z 0) by lia; replace (z =? 0) with true by (symmetry; apply Z.eqb_eq; lia) end.
      cbn [negb]. cbv iota.
      step.
      eapply (stchk0 fr f spc j n w56 mc J X); try eassumption.
      replace (S i) with 31%nat by lia. reflexivity.
    - match goal with |- context [bv_eqb (Z_to_bv 64 ?z) (Z_to_bv 64 0)] =>
        rewrite (rc_eqb_lit z 0) by lia; replace (z =? 0) with false by (symmetry; apply Z.eqb_neq; lia) end.
      cbn [negb]. cbv iota.
      eapply (IH (S i)); try eassumption; first [lia | f_equal; lia | reflexivity].
  Qed.


End Main.
