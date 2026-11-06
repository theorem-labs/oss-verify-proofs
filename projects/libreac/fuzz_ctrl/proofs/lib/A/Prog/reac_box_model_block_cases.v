(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 574 of its 588 lines of code are new or changed and 234 lines of the source are left out. *)
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

(* reac_box_model_block, image A (asan), part 5: the cases of the jump table at 0x219f4 for b = 1 (0x85eec) and b = 2 (0x85eac), which copy the JOIN block that b selects into the box with __asan_memcpy, and b = 3 (0x85eb8), which writes the four decimal digits of the field at p + 266 into the ASan frame (its shadow byte set to 4 for the call) and calls build_dt1_single, or leaves the box zero when the field exceeds 9999. *)

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
            pose proof (bv_lstore _ _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity | unfold wa; f_equal; lia])) as PI';
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
            pose proof (bv_store _ _ _ _ _ _ _ mc X J k AA bs HKt Hpt Hot PI ltac:(lia)
                          ltac:(simpl_sizes; lia) ltac:(first [reflexivity | unfold wa; f_equal; lia])) as PI';
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


  (* --- the cases of the jump table at 0x219f4 --- *)

  Lemma upd0 : forall (X Y : list byte), length X = length Y -> upd_bytes X 0 Y = Y.
  Proof.
    intros X Y L. unfold upd_bytes. cbn [firstn]. rewrite skipn_all2 by lia. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma rom_at : forall (mm : word -> option byte) (AA : Z) (bs : list byte), mem_inv rsegs mm ->
    (ro_bytes_b rsegs AA bs && (0 <=? AA) && (AA + Z.of_nat (length bs) <=? 2^64))%bool = true ->
    bytes_at rsegs mm AA bs.
  Proof.
    intros mm AA bs Hm H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply ro_bytes_at; [exact Hm | exact H2 | exact H3 |]. apply ro_bytes_b_sound. exact H1.
  Qed.

  (* The JOIN blocks are low application memory. *)
  Lemma join_app : forall x, JOIN_0013 <= x <= JOIN_0014 + 32 -> app_mem x.
  Proof.
    intros x Hx. unfold JOIN_0013, JOIN_0014 in Hx. unfold app_mem, LOWMEM_END. left. lia.
  Qed.

  (* 0x85ef4 (b = 1 and b = 2 join here): __asan_memcpy(o, JOIN, 32) and the result 1. *)
  Lemma cs_join : forall fr f spc j n w56 mc J (JA : Z) (JB : list byte) (a1 : word)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc (zeros 32) J ->
    (JA = JOIN_0013 \/ JA = JOIN_0014) -> bytes_at rsegs mc JA JB -> length JB = 32%nat ->
    addressable mc JA 32 -> JB = synth row b nb -> rc row b = 1 -> bv_unsigned a1 = JA ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 a1 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85ef4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J JA JB a1 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 PI EJA HJB LJB AJB EX Er E1.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI)
      as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    assert (DOJ : o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)
      by (hide_sec; destruct (HO Ho0) as (_ & _ & H); exact H).
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold RB, BINV.RB. step. step. step.
    eapply (cl_mc fr f spc j n w56 mc (zeros 32) J 0x85f00 0 32 JA JB); try eassumption.
    - apply ret_pc_even; [lia | reflexivity].
    - lia.
    - lia.
    - lia.
    - cbn [Z.of_nat]. rewrite Z.add_0_r. apply unsigned_lit. lia.
    - cbn [Z.of_nat]. rewrite unsigned_lit by lia. reflexivity.
    - cbn [Z.of_nat]. apply join_app. unfold JOIN_0013, JOIN_0014 in *. clear -EJA; lia.
    - cbn [Z.of_nat]. apply join_app. unfold JOIN_0013, JOIN_0014 in *. clear -EJA; lia.
    - cbn [Z.of_nat]. rewrite Z.add_0_r. unfold JOIN_0013, JOIN_0014 in *. clear -DOJ EJA; lia.
    - cbn [Z.of_nat]. left. unfold JOIN_0013, JOIN_0014 in *. clear -EJA HHM'; lia.
    - intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mc1 PI1.
      unfold RB, BINV.RB. step.
      eapply (fin1 fr f spc j n w56 mc1 (upd_bytes (zeros 32) 0 JB) J); try eassumption.
      rewrite <- EX. apply (upd0 (zeros 32) JB). unfold zeros. rewrite repeat_length. lia.
  Qed.

  (* b = 1 (0x85eec): the JOIN_0014 block. *)
  Lemma cs1 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 1 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85eec) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    pose proof PI as ((_ & _ & _ & MIc & _) & _).
    destruct (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as (_ & _ & _ & _ & _ & _ & _ & JJ1 & _).
    pose proof (JJ1 Eb) as AJ.
    unfold RB, BINV.RB. step. step.
    eapply (cs_join fr f spc j n w56 mc J JOIN_0014 J14); try eassumption.
    - right. reflexivity.
    - apply rom_at; [exact MIc | vm_compute; reflexivity].
    - reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite unsigned_lit; [reflexivity | unfold JOIN_0014; lia].
  Qed.

  (* b = 2 (0x85eac): the JOIN_0013 block. *)
  Lemma cs2 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 2 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85eac) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    pose proof PI as ((_ & _ & _ & MIc & _) & _).
    destruct (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as (_ & _ & _ & _ & _ & _ & _ & _ & JJ2).
    pose proof (JJ2 Eb) as AJ.
    unfold RB, BINV.RB. step. step. step.
    eapply (cs_join fr f spc j n w56 mc J JOIN_0013 J13); try eassumption.
    - left. reflexivity.
    - apply rom_at; [exact MIc | vm_compute; reflexivity].
    - reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite Eb. reflexivity.
    - rewrite unsigned_lit; [reflexivity | unfold JOIN_0013; lia].
  Qed.


  (* The four digit bytes written into the ASan frame at fr + 32, read back. *)
  Lemma four_bytes : forall (mm : word -> option byte) (AA : Z) (l0 l1 l2 l3 : list byte),
    length l0 = 1%nat -> length l1 = 1%nat -> length l2 = 1%nat -> length l3 = 1%nat ->
    0 <= AA -> AA + 4 <= 2 ^ 64 ->
    bytes_at rsegs (write_to_mem (write_to_mem (write_to_mem (write_to_mem mm (wa AA) l0)
                                                  (wa (AA + 1)) l1) (wa (AA + 2)) l2) (wa (AA + 3)) l3)
      AA (l0 ++ l1 ++ l2 ++ l3).
  Proof.
    intros mm AA l0 l1 l2 l3 L0 L1 L2 L3 H0 H1.
    destruct l0 as [|c0 [|? ?]]; try discriminate. destruct l1 as [|c1 [|? ?]]; try discriminate.
    destruct l2 as [|c2 [|? ?]]; try discriminate. destruct l3 as [|c3 [|? ?]]; try discriminate.
    cbn [app].
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error]; simpl Z.of_nat; [| | | | lia];
      repeat (rewrite mrd_w1 by lia);
      repeat match goal with
             | |- context [?x =? ?y] =>
                 first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia)
                       | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
             end;
      reflexivity.
  Qed.

  (* After the shadow byte of [fr + 32, fr + 40) is set to 4, the four bytes at fr + 32 are addressable. *)
  Lemma shadow4_addr : forall fr f spc j n w56 (mc : word -> option byte) (v : byte),
    FK fr f spc j n w56 -> bv_signed v = 4 ->
    addressable (write_to_mem mc (wa (fr / 8 + off + 4)) [v]) (fr + 32) 4.
  Proof.
    intros fr f spc j n w56 mc v HK Hv.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (FAP 32 ltac:(lia)) as AF32. pose proof (FAP 35 ltac:(lia)) as AF35.
    pose proof AF32 as AF32'. pose proof AF35 as AF35'.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF32', AF35'.
    split; [clear -AF32'; lia|]. split; [lia|]. split; [unfold APPMEM_END; clear -AF35'; lia|].
    intros i Hi. split.
    - replace (fr + 32 + i) with (fr + (32 + i)) by lia. apply FAP. lia.
    - exists v.
      assert (Esh : shadow_addr (fr + 32 + i) = fr / 8 + off + 4).
      { unfold shadow_addr. rewrite Hoff. clear -FR8 Hi. Z.div_mod_to_equations. lia. }
      rewrite Esh. split.
      + rewrite mrd_w1 by (clear -SH1 SH2; lia). rewrite Z.eqb_refl. reflexivity.
      + unfold shadow_ok. right. rewrite Hv. split; [|lia].
        replace ((fr + 32 + i) mod 8) with i by (clear -FR8 Hi; Z.div_mod_to_equations; lia). lia.
  Qed.

  (* b = 3 (0x85eb8): the four decimal digits of the 16-bit field at p + 266 through build_dt1_single. *)
  Lemma cs3 : forall fr f spc j n w56 mc J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> b = 3 -> BV fr j n w56 mc (zeros 32) J ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x85eb8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 Eb PI.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof Rp as Rp'. pose proof Ro as Ro'.
    assert (HPf : p mod 8 = 0 /\ length row = 296%nat)
      by (hide_sec; destruct (HP Hp0) as (H1 & H2 & _); split; assumption).
    destruct HPf as (Hp8 & Lrow).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof PI as ((MUc & WMc & RMc & MIc & SVc & HHc & F56c) & HO32 & HL & HRB & HNB).
    pose proof (rs_rd2 rsegs mc p row 266 HRB ltac:(lia)) as R1.
    change (Z.of_nat 266) with 266 in R1.
    pose proof (rs_rw16_range row 266) as RV.
    pose proof (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI) as JXf.
    destruct JXf as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    assert (RX : 0 <= p + 266 < 2 ^ 64)
      by (pose proof JAP as (Pa & _ & Pe & _); unfold APPMEM_END in Pe; clear -Pa Pe; lia).
    pose proof (B.acl_shadow mc p 296 266 2 (p + 266) JAP ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear -Hp8; Z.div_mod_to_equations; lia) eq_refl) as SH.
    pose proof (FAP 0 ltac:(lia)) as AF0. rewrite Z.add_0_r in AF0.
    pose proof (FAP 63 ltac:(lia)) as AF63.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF0, AF63.
    hide_sec.
    unfold RB, BINV.RB.
    step.
    chk_core (p + 266) RX (Z_to_bv 5 12) SH pre_sr add1.
    step. rewrite rs_zx16. step. step. step.
    (* the shadow byte of the digit buffer is set to 4 *)
    wstS (fr / 8 + off + 4) 1%nat. step. norm_store.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) => replace l with [Z_to_bv 8 4] by reflexivity
    end.
    pose proof (shadow4_addr fr f spc j n w56 mc (Z_to_bv 8 4) HK ltac:(reflexivity)) as AD4.
    pose proof (bv_sstore fr f spc j n w56 mc (zeros 32) J 4 (wa (fr / 8 + off + 4)) [Z_to_bv 8 4]
                  HK Hp0 Ho0 PI ltac:(lia) ltac:(cbn [length]; lia) eq_refl) as PI1.
    repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
    step.
    rewrite (unsigned_lit (rw16 row 266)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    assert (ES : synth row b nb = (if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32))
      by (rewrite Eb; reflexivity).
    assert (ER : rc row b = (if fwm row <=? 9999 then 1 else -1)) by (rewrite Eb; reflexivity).
    destruct (Z.leb_spec (fwm row) 9999) as [FW9|FW9]; unfold fwm in FW9.
    - (* the value fits in four digits: write them into the frame and call build_dt1_single *)
      if_t.
      do 30 step.
      (* the four digit bytes at fr + 32 *)
      wstF (fr + 32) 1%nat. step. norm_store.
      wstF (fr + 33) 1%nat. step. norm_store.
      wstF (fr + 34) 1%nat. step. norm_store.
      wstF (fr + 35) 1%nat. step. norm_store.
      repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem (write_to_mem (write_to_mem ?m0 _ ?l0) _ ?l1) _ ?l2) _ ?l3) _) =>
          pose proof (four_bytes m0 (fr + 32) l0 l1 l2 l3 ltac:(simpl_sizes; reflexivity)
                        ltac:(simpl_sizes; reflexivity) ltac:(simpl_sizes; reflexivity)
                        ltac:(simpl_sizes; reflexivity)
                        ltac:(clear -AF0 AF63; lia) ltac:(clear -AF0 AF63; lia)) as HD4;
          replace (fr + 32 + 1) with (fr + 33) in HD4 by lia;
          replace (fr + 32 + 2) with (fr + 34) in HD4 by lia;
          replace (fr + 32 + 3) with (fr + 35) in HD4 by lia
      end.
      (* the four bytes are the decimal digits of the field *)
      assert (Hv : 0 <= rw16 row 266 < 10000) by (clear -RV FW9; lia).
      lazymatch type of HD4 with
      | bytes_at _ _ _ ?DD =>
          assert (EDD : DD = digits (fwm row));
          [ unfold digits, fwm; rewrite !rc_le1_lit; cbn [app map];
            clear -Hv; revert Hv; generalize (rw16 row 266); intros v Hv;
            repeat apply rc_cons_eq; try reflexivity; unfold bz; rs_brute_tac v
          | rewrite EDD in HD4 ]
      end.
      (* the invariant across the four frame stores *)
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem (write_to_mem (write_to_mem ?m0 _ ?l0) _ ?l1) _ ?l2) _ ?l3) _) =>
          pose proof (bv_fstore fr f spc j n w56 m0 (zeros 32) J 32 (wa (fr + 32)) l0
                        HK Hp0 Ho0 PI1 ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIb;
          pose proof (bv_fstore fr f spc j n w56 _ (zeros 32) J 33 (wa (fr + 33)) l1
                        HK Hp0 Ho0 PIb ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIc;
          pose proof (bv_fstore fr f spc j n w56 _ (zeros 32) J 34 (wa (fr + 34)) l2
                        HK Hp0 Ho0 PIc ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PId;
          pose proof (bv_fstore fr f spc j n w56 _ (zeros 32) J 35 (wa (fr + 35)) l3
                        HK Hp0 Ho0 PId ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIe;
          assert (APFR : forall x, fr <= x < fr + 64 -> app_mem x)
            by (intros x Hx; replace x with (fr + (x - fr)) by lia; apply FAP; lia);
          pose proof (addr_keep_app _ (fr + 32) l0 (fr + 32) 4 AD4 ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADb;
          pose proof (addr_keep_app _ (fr + 33) l1 (fr + 32) 4 ADb ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADc;
          pose proof (addr_keep_app _ (fr + 34) l2 (fr + 32) 4 ADc ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADd;
          pose proof (addr_keep_app _ (fr + 35) l3 (fr + 32) 4 ADd ltac:(clear -AF0 AF63; lia)
                        ltac:(simpl_sizes; clear -AF0 AF63; lia) ltac:(simpl_sizes; lia)
                        ltac:(intros ii Hii; apply APFR; revert Hii; simpl_sizes; intros Hii; lia)) as ADe
      end.
      do 4 step.
      eapply (cl_bd fr f spc j n w56 _ J 0x865fc 4 (fr + 32) 0 (digits (fwm row))).
      + exact HK.
      + exact Hp0.
      + exact Ho0.
      + exact PIe.
      + apply ret_pc_even; [lia | reflexivity].
      + lia.
      + lia.
      + reflexivity.
      + rewrite unsigned_lit; [reflexivity | clear -Ro'; lia].
      + rewrite unsigned_lit; [reflexivity | lia].
      + rewrite unsigned_lit; [reflexivity | clear -AF0 AF63; lia].
      + cbn [Z.of_nat]. rewrite unsigned_lit; [reflexivity | lia].
      + exact HD4.
      + cbn [Z.of_nat]. exact ADe.
      + replace (fr + 32 + 7) with (fr + 39) by lia. apply APFR. lia.
      + cbn [Z.of_nat]. replace (fr + 32 + 4) with (fr + 36) by lia. apply APFR. lia.
      + cbn [Z.of_nat]. pose proof (djf fr f spc j n w56 HK Hp0 Ho0) as (DJo & _). clear -DJo; lia.
      + cbn [Z.of_nat]. right. clear -FRlo FRhi; lia.
      + intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mcf PIf.
        pose proof PIf as ((MUf & WMf & RMf & MIf & _) & _).
        unfold RB, BINV.RB. step. step.
        wstS (fr / 8 + off + 4) 1%nat. step. norm_store.
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 (wa ?aw) ?lw) _) =>
            pose proof (bv_sstore fr f spc j n w56 m0 (dt1s 0 (digits (fwm row))) J 4 (wa aw) lw
                          HK Hp0 Ho0 PIf ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIg
        end.
        repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
        step.
        eapply (exit_r fr f spc j n w56 _ (dt1s 0 (digits (fwm row))) J 1); try eassumption.
        * rewrite ES. replace (fwm row <=? 9999) with true by (symmetry; apply Z.leb_le; unfold fwm; lia).
          reflexivity.
        * rewrite ER. replace (fwm row <=? 9999) with true by (symmetry; apply Z.leb_le; unfold fwm; lia).
          reflexivity.
    - (* the value does not fit: the box stays zero and the result is -1 *)
      if_f.
      step. step. step.
      wstS (fr / 8 + off + 4) 1%nat. step. norm_store.
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 (wa ?aw) ?lw) _) =>
          pose proof (bv_sstore fr f spc j n w56 m0 (zeros 32) J 4 (wa aw) lw
                        HK Hp0 Ho0 PI1 ltac:(lia) ltac:(simpl_sizes; lia) eq_refl) as PIg
      end.
      repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
      step.
      eapply (exit_r fr f spc j n w56 _ (zeros 32) J (-1)); try eassumption.
      + rewrite ES. replace (fwm row <=? 9999) with false by (symmetry; apply Z.leb_gt; unfold fwm; lia).
        reflexivity.
      + rewrite ER. replace (fwm row <=? 9999) with false by (symmetry; apply Z.leb_gt; unfold fwm; lia).
        reflexivity.
  Qed.

End Main.
