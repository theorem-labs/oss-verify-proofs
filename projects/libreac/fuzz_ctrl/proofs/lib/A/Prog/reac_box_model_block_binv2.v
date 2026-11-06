(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 731 of its 745 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv.
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

(* reac_box_model_block, image A (asan), part 4: the calls the body makes - __asan_memset into the box and into the locals, __asan_memcpy into the box, and build_dt1_single - each rebuilding the body invariant at the memory the callee returns. *)

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.

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


  (* --- the calls the body makes --- *)

  (* A call that wrote exactly [AA + k, AA + k + n) of the cell at AA (and bytes outside the cell) updates it. *)
  Lemma rw_upd2 : forall (mm mm' : word -> option byte) (AA : Z) (N kk nn : nat) (X Y : list byte) (W : list ivl),
    rw_cells rsegs mm AA [CB N X] -> (kk + nn <= N)%nat -> length Y = nn ->
    munch W mm mm' -> wmono rsegs mm mm' ->
    (forall x, AA <= x < AA + Z.of_nat N ->
       ~ (AA + Z.of_nat kk <= x < AA + Z.of_nat kk + Z.of_nat nn) -> outside W x) ->
    bytes_at rsegs mm' (AA + Z.of_nat kk) Y ->
    rw_cells rsegs mm' AA [CB N (upd_bytes X kk Y)].
  Proof.
    intros mm mm' AA N kk nn X Y W HC Hkn LY MU WM HOut HY.
    pose proof HC as [[Hwf HB] HW]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
    cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    destruct HB as (Hlo & Hhi & HBp). destruct HY as (_ & _ & HYp).
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length by lia; exact LX | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      split; [exact Hlo|]. split; [rewrite upd_bytes_length by lia; exact Hhi|].
      intros i Hi. rewrite upd_bytes_length in Hi by lia.
      rewrite upd_bytes_nth by lia.
      destruct ((kk <=? i)%nat && (i <? kk + length Y)%nat)%bool eqn:Ec.
      + apply andb_true_iff in Ec. destruct Ec as [E1 E2].
        apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
        rewrite <- (HYp (i - kk)%nat ltac:(lia)). f_equal. f_equal. lia.
      + apply andb_false_iff in Ec.
        rewrite <- (HBp i ltac:(lia)). unfold mrd. rewrite (MU (wa (AA + Z.of_nat i))); [reflexivity|].
        rewrite wa_unsigned by lia. apply HOut; [lia|].
        destruct Ec as [E|E]; [apply Nat.leb_nle in E | apply Nat.ltb_nlt in E]; lia.
    - cbn [cells_size csize Nat.add] in HW |- *. rewrite ?Nat.add_0_r in HW |- *.
      exact (wr_at_transport rsegs mm mm' AA (Z.of_nat N) HW WM).
  Qed.

  (* __asan_memset(o + k, v, n): the box bytes [k, k + n) become v. *)
  Lemma cl_ms : forall fr f spc j n w56 mc X J (ret : Z) (kk nn : nat) (v : Z)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (kk + nn <= 32)%nat -> (1 <= nn)%nat -> (kk + 7 <= 32)%nat ->
    0 <= v < 256 ->
    bv_unsigned a0 = o + Z.of_nat kk -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat nn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (upd_bytes X kk (repeat (Z_to_bv 8 v) nn)) J ->
       evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMSET) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret kk nn v a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hkn Hn Hk7 Hv E0 E1 E2 K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (spc_bounds fr f spc j n w56 HK) as HSPC.
    assert (CFR : fr = spc \/ fr + 64 <= bv_unsigned sp - 4272)
      by (pose proof (call_facts fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as CF; tauto).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    hide_sec.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -HSPC HAlo HAhi Rsp HHM'; lia).
    pose proof (rs_rw_sub rsegs mc o 32 X kk nn HO32 Hkn) as HSub.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    unfold RB.
    eapply evt_cut.
    { eapply HMS with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn kk X));
        unfold ASAN_MEMSET_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSub.
      - lia.
      - apply (B.acl_addr_sub mc o 32); [exact JAO | lia | lia | lia].
      - unfold end_in_app. right. replace (o + Z.of_nat kk + Z.of_nat nn) with (o + Z.of_nat (kk + nn)) by lia.
        apply app_o; [exact Ho0 | lia].
      - right. replace (o + Z.of_nat kk + 7) with (o + (Z.of_nat kk + 7)) by lia.
        apply app_o; [exact Ho0 | lia].
      - destruct (AO Ho0) as (_ & _ & DRT). unfold RT_LO, RT_HI in *. clear -DRT Hkn Hn; lia.
      - clear -Dow HSPC HAlo HAhi Hkn Hn; lia.
      - exact STlo.
      - clear -HSPC HAlo HAhi; lia.
      - unfold HIGHMEM_BEG; clear -HHM'; lia.
      - unfold APPMEM_END; clear -HSPC HAlo HAhi HAE'; lia.
      - exact JAC.
      - exact JSW.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems & MU2 & WM2 & MI2
                    & ST2 & RW2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E1, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2.
    rewrite Z.mod_small in RW2 by lia.
    unfold ASAN_MEMSET_K in MU2, ST2.
    rewrite Hret.
    apply K.
    (* the invariant at the memory after the call *)
    assert (OUTC : forall x, (x < o + Z.of_nat kk \/ o + Z.of_nat kk + Z.of_nat nn <= x) ->
              (x < bv_unsigned sp - 4272 \/ bv_unsigned sp <= x) \/ (o <= x < o + 32) ->
              outside [(o + Z.of_nat kk, o + Z.of_nat kk + Z.of_nat nn); (spc - 2208, spc)] x).
    { intros x Hx1 Hx2. cbn [outside]. split; [lia|]. split; [|exact I].
      destruct Hx2 as [Hw|Hb]; [clear -Hw HSPC HAlo HAhi HHM'; lia | clear -Hb Dow HSPC HAlo HAhi; lia]. }
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)).
        rewrite repeat_length. clear -Hy; lia.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy HSPC HAlo HAhi HHM'; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx.
      assert (Ebox : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite Ebox in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw Hb].
      unfold B.Wf in Hw. cbn [outside] in Hw, Hb. destruct Hb as [Hb _].
      destruct Hw as (Hwin & _). cbn [outside]. split; [clear -Hb Hkn Hn; lia|].
      split; [clear -Hwin HSPC HAlo HAhi; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -Dow HSPC HAlo HAhi Hkn Hn; lia|]. split; [clear -HSPC HAlo HAhi; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfs Hkn Hn; lia|]. split; [clear -HFSb HHM' HSPC HAlo HAhi P1; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfr Hkn Hn; lia|]. split; [clear -CFR HSPC HAlo HAhi; lia | exact I].
    - split; [|split; [|split]].
      + apply (rw_upd2 mc m2 o 32 kk nn X (repeat (Z_to_bv 8 v) nn)
                 [(o + Z.of_nat kk, o + Z.of_nat kk + Z.of_nat nn); (spc - 2208, spc)] HO32 Hkn
                 ltac:(apply repeat_length) MU2 WM2).
        * intros x Hx Hx2. apply OUTC; [clear -Hx2; lia | right; clear -Hx; lia].
        * exact (rw1 m2 _ _ _ RW2).
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HL MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -Dow HSPC HAlo HAhi Hkn Hn; lia|]. split; [clear -HSPC HAlo HAhi; lia | exact I].
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpo Hkn Hn; lia|]. split; [clear -Dpw HSPC HAlo HAhi; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dno Hkn Hn; lia|]. split; [clear -Dnw HSPC HAlo HAhi; lia | exact I].
  Qed.


  (* __asan_memcpy(o + k, S, n): the box bytes [k, k + n) become src. *)
  Lemma cl_mc : forall fr f spc j n w56 mc X J (ret : Z) (kk nn : nat) (SS : Z) (src : list byte)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (kk + nn <= 32)%nat -> (1 <= nn)%nat -> (kk + 7 <= 32)%nat ->
    length src = nn ->
    bv_unsigned a0 = o + Z.of_nat kk -> bv_unsigned a1 = SS -> bv_unsigned a2 = Z.of_nat nn ->
    bytes_at rsegs mc SS src -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) -> app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= o + Z.of_nat kk \/ o + Z.of_nat kk + Z.of_nat nn <= SS) ->
    (SS + Z.of_nat nn <= bv_unsigned sp - 4272 \/ A <= SS) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (upd_bytes X kk src) J ->
       evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret kk nn SS src a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hkn Hn Hk7 LS E0 E1 E2 HSb HAS HS7 HSN DSO DSW K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -CF1 CF3 HHM' Rsp; lia).
    pose proof (rs_rw_sub rsegs mc o 32 X kk nn HO32 Hkn) as HSub.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    unfold RB.
    eapply evt_cut.
    { eapply HMC with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn kk X)) (src := src);
        unfold ASAN_MEMCPY_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSb.
      - exact LS.
      - exact HSub.
      - right. exact DSO.
      - lia.
      - exact HAS.
      - apply (B.acl_addr_sub mc o 32); [exact JAO | lia | lia | lia].
      - unfold end_in_app. right. exact HSN.
      - unfold end_in_app. right.
        replace (o + Z.of_nat kk + Z.of_nat nn) with (o + Z.of_nat (kk + nn)) by lia.
        apply app_o; [exact Ho0 | lia].
      - right. split; [exact HS7|].
        replace (o + Z.of_nat kk + 7) with (o + (Z.of_nat kk + 7)) by lia.
        apply app_o; [exact Ho0 | lia].
      - destruct (AO Ho0) as (_ & _ & DRT). unfold RT_LO, RT_HI in *. clear -DRT Hkn Hn; lia.
      - clear -Dow CF1 CF3 CF7 HAlo HAhi Hkn Hn; lia.
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
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. unfold ASAN_MEMCPY_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)). rewrite LS. clear -Hy; lia.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy CF1 CF3 HHM'; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx.
      assert (Ebox : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite Ebox in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw Hb].
      unfold B.Wf in Hw. cbn [outside] in Hw, Hb. destruct Hb as [Hb _]. destruct Hw as (Hwin & _).
      cbn [outside]. split; [clear -Hb Hkn Hn; lia|].
      split; [clear -Hwin CF1 CF3; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hkn Hn; lia|]. split; [clear -CF1 CF3; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfs Hkn Hn; lia|]. split; [clear -HFSb HHM' CF1 CF3 P1; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfr Hkn Hn; lia|].
      split; [clear -CF8 CF1 CF3 CF7 HAlo HAhi; lia | exact I].
    - split; [|split; [|split]].
      + apply (rw_upd2 mc m2 o 32 kk nn X src
                 [(o + Z.of_nat kk, o + Z.of_nat kk + Z.of_nat nn); (spc - 2224, spc)] HO32 Hkn LS MU2 WM2).
        * intros x Hx Hx2. cbn [outside]. split; [clear -Hx2; lia|].
          split; [clear -Hx Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
        * exact (rw1 m2 _ _ _ RW2).
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HL MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hkn Hn; lia|]. split; [clear -CF1 CF3 CF7; lia | exact I].
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpo Hkn Hn; lia|]. split; [clear -Dpw CF1 CF3; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dno Hkn Hn; lia|]. split; [clear -Dnw CF1 CF3; lia | exact I].
  Qed.


  (* The local bytes are application memory (they are inside the window). *)
  Lemma app_loc : forall fr f spc j n w56 mc X J t, FK fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BV fr j n w56 mc X J -> 0 <= t <= 56 -> app_mem (A + t).
  Proof.
    intros fr f spc j n w56 mc X J t HK Hp0 Ho0 PI Ht.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. hide_sec.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right.
    clear -HHM' HAE' HAlo HAhi Ht Rsp; lia.
  Qed.

  (* __asan_memset(A + d, v, n): the local bytes [d, d + n) become v. *)
  Lemma cl_ms_loc : forall fr f spc j n w56 mc X J (ret : Z) (dd nn : nat) (v : Z)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (dd + nn <= 56)%nat -> (1 <= nn)%nat -> (dd + 7 <= 56)%nat ->
    0 <= v < 256 ->
    bv_unsigned a0 = A + Z.of_nat dd -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat nn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' X (upd_bytes J dd (repeat (Z_to_bv 8 v) nn)) ->
       evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMSET) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret dd nn v a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hdn Hn Hd7 Hv E0 E1 E2 K.
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
    unfold RB.
    eapply evt_cut.
    { eapply HMS with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn dd J));
        unfold ASAN_MEMSET_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSub.
      - lia.
      - apply (B.acl_addr_sub mc A 56); [exact JAL | lia | lia | lia].
      - unfold end_in_app. right. replace (A + Z.of_nat dd + Z.of_nat nn) with (A + Z.of_nat (dd + nn)) by lia.
        apply (APL (Z.of_nat (dd + nn))); [exact HK | exact Hp0 | exact Ho0 | exact PI | lia].
      - right. replace (A + Z.of_nat dd + 7) with (A + (Z.of_nat dd + 7)) by lia.
        apply (APL (Z.of_nat dd + 7)); [exact HK | exact Hp0 | exact Ho0 | exact PI | lia].
      - unfold RT_LO, RT_HI. clear -HHM' HAlo HAhi Hdn; lia.
      - right. clear -CF7 HAlo HAhi; lia.
      - exact STlo.
      - clear -CF3; lia.
      - unfold HIGHMEM_BEG; clear -HHM'; lia.
      - exact CF5.
      - exact JAC.
      - exact JSW.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems & MU2 & WM2 & MI2
                    & ST2 & RW2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E1, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2.
    rewrite Z.mod_small in RW2 by lia. unfold ASAN_MEMSET_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)). rewrite repeat_length. clear -Hy; lia.
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
      + apply (rw_upd2 mc m2 A 56 dd nn J (repeat (Z_to_bv 8 v) nn)
                 [(A + Z.of_nat dd, A + Z.of_nat dd + Z.of_nat nn); (spc - 2208, spc)] HL Hdn
                 ltac:(apply repeat_length) MU2 WM2).
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


  (* build_dt1_single(o, v, S, n) with the box all zeros: the box becomes dt1s v D. *)
  Lemma cl_bd : forall fr f spc j n w56 mc J (ret : Z) (nn : nat) (SS v : Z) (D : list byte)
      (a0 a1 a2 a3 t0 t1 t2 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc (zeros 32) J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (nn <= 9)%nat -> (1 <= nn)%nat -> length D = nn ->
    bv_unsigned a0 = o -> bv_unsigned a1 = v -> bv_unsigned a2 = SS -> bv_unsigned a3 = Z.of_nat nn ->
    bytes_at rsegs mc SS D -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) ->
    app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= o \/ o + 32 <= SS) -> (A <= SS /\ SS + Z.of_nat nn <= A + 56) \/ (fr <= SS /\ SS + Z.of_nat nn <= fr + 64) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (dt1s v D) J ->
       evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J ret nn SS v D a0 a1 a2 a3 t0 t1 t2 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hn9 Hn1 LD E0 E1 E2 E3 HSb HAS HS7 HSN DSO DSR K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI)
      as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI)
      as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -CF1 CF3 HHM' Rsp; lia).
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) (spc - 2272) spc STlo ltac:(clear -CF1 CF3; lia))
      as [_ STbd].
    unfold RB.
    eapply evt_cut.
    { eapply HBD with (ob := zeros 32) (D := D); unfold BUILD_DT1_SINGLE_K;
        rewrite ?E0, ?E1, ?E2, ?E3, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact STbd.
      - lia.
      - exact Ho0.
      - unfold APPMEM_END in Boe; clear -Boe; lia.
      - exact HO32.
      - clear -HSN HAS; destruct HAS as (_ & _ & He & _); unfold APPMEM_END in He; lia.
      - rewrite LD. reflexivity.
      - exact HSb.
      - exact DSO.
      - clear -Dow CF1 CF3 CF7 HAlo HAhi; lia.
      - clear -DSR CF1 CF3 CF7 CF8; lia.
      - exact MI.
      - exact JAC.
      - exact JSW.
      - unfold HIGHMEM_BEG; clear -HHM' CF1 CF3; lia.
      - exact CF5.
      - exact JAO.
      - exact HAS.
      - replace (o + 32) with (o + 32) by reflexivity. apply app_o; [exact Ho0 | lia].
      - unfold end_in_app. right. exact HSN.
      - right. exact HS7.
      - destruct (AO Ho0) as (_ & _ & DRT). exact DRT. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m2 & Ems
                    & HB2 & _ & _ & MU2 & WM2 & MI2 & ST2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E1, E3, Nat2Z.id in HB2. rewrite E0, E3 in MU2. unfold BUILD_DT1_SINGLE_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (LDT : length (dt1s v D) = 32%nat) by (apply rs_dt1s_len; lia).
    assert (EDT : dt1_out nn v D (zeros 32) = dt1s v D) by (unfold dt1s; rewrite LD; reflexivity).
    rewrite EDT in HB2.
    assert (OUTC : forall x, (x < o \/ o + 32 <= x) -> (x < bv_unsigned sp - 4272 \/ bv_unsigned sp <= x) ->
              outside [(spc - 2272, spc); (o, o + 22 + Z.of_nat nn); (o + 31, o + 32)] x).
    { intros x H1 H2. cbn [outside]. split; [clear -H2 CF1 CF3; lia|].
      split; [clear -H1 Hn9; lia|]. split; [clear -H1; lia | exact I]. }
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy CF1 CF3 HHM'; lia.
      - apply (B.rd_of_bytes m2 _ _ HB2). rewrite LDT. clear -Hy Hn9; lia.
      - apply (B.rd_of_bytes m2 _ _ HB2). rewrite LDT. clear -Hy; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx.
      assert (Ebox : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite Ebox in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw Hb].
      unfold B.Wf in Hw. cbn [outside] in Hw, Hb. destruct Hb as [Hb _]. destruct Hw as (Hwin & _).
      cbn [outside]. split; [clear -Hwin CF1 CF3; lia|].
      split; [clear -Hb Hn9; lia|]. split; [clear -Hb; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -CF1 CF3; lia|]. split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hn9; lia|].
      split; [clear -Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -HFSb HHM' CF1 CF3 P1; lia|].
      split; [clear -Dfs Hn9; lia|]. split; [clear -Dfs; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -CF8 CF1 CF3 CF7 HAlo HAhi; lia|].
      split; [clear -Dfr Hn9; lia|]. split; [clear -Dfr; lia | exact I].
    - split; [|split; [|split]].
      + pose proof HO32 as [_ WO]. cbn [cells_size csize Nat.add] in WO.
        split; [split|].
        * cbn [cells_wf cell_wf]. split; [exact LDT | exact I].
        * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB2.
        * cbn [cells_size csize Nat.add]. exact (wr_at_transport rsegs mc m2 o (Z.of_nat 32) WO WM2).
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HL MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -CF1 CF3 CF7; lia|].
        split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hn9; lia|]. split; [clear -Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpw CF1 CF3; lia|]. split; [clear -Dpo Hn9; lia|]. split; [clear -Dpo; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dnw CF1 CF3; lia|]. split; [clear -Dno Hn9; lia|]. split; [clear -Dno; lia | exact I].
  Qed.

End Main.
