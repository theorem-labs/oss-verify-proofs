(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 773 of its 787 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi.
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

(* reac_box_model_block, image A (asan), part 3: the body's memory invariant BV (the frame facts, the box and the 56 locals as cells, the row and the name bytes), the disjointness of the box, row, name and JOIN blocks from the ASan frame, the ASan state at a body memory (bv_jx), the stores into the box, the locals, the frame and the frame's shadow, the exits at 0x864c0/0x864bc, the call footprint facts, and the stepping tactics. *)

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.

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


  (* --- the body's memory invariant (0x85c48 .. 0x864c0) --- *)

  Lemma rw1 : forall mm AA N X, rw_cells rsegs mm AA [CB N X] -> bytes_at rsegs mm AA X.
  Proof.
    intros mm AA N X [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
  Qed.

  Lemma inside_appr : forall W W' a nn, inside W' a nn -> inside (W ++ W') a nn.
  Proof.
    induction W as [|[lo hi] W IH]; intros W' a nn H; cbn [app inside]; [exact H | right; apply IH; exact H].
  Qed.

  (* The frame part of the body-end invariant (EB without the box result). *)
  Definition BF (fr j n : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    munch (EBW fr j n) m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (bv_unsigned sp + -104) SAVES /\
    (exists h, bytes_at rsegs mc FS (le8 h)) /\ bytes_at rsegs mc (fr + 56) (le8 w56).

  (* The body's invariant: the frame part, the box cell with content X, the 56 local bytes at A with content J, the
     row and the name bytes. *)
  Definition BV (fr j n : Z) (w56 : word) (mc : word -> option byte) (X J : list byte) : Prop :=
    BF fr j n w56 mc /\ rw_cells rsegs mc o [CB 32 X] /\ rw_cells rsegs mc A [CB 56 J] /\
    bytes_at rsegs mc p row /\
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> bytes_at rsegs mc (rname row) nb).

  (* Two ranges of a disjoint pair of footprints are apart. *)
  Lemma dj_pair : forall W D a bnd c d, fp_dj W D -> In (a, bnd) W -> In (c, d) D -> ly_dj a bnd c d.
  Proof.
    intros W D a bnd c d H H1 H2. unfold fp_dj in H. rewrite Forall_forall in H.
    pose proof (H _ H1) as H'. rewrite Forall_forall in H'. exact (H' _ H2).
  Qed.

  (* The box, the row, the name and the JOIN blocks are apart from the ASan frame [fr, fr + 64): the frame is in the
     window (real stack) or among the class-0 side-stack frames, and all four are apart from both. *)
  Definition DJF (fr : Z) : Prop :=
    (o + 32 <= fr \/ fr + 64 <= o) /\ (p + 296 <= fr \/ fr + 64 <= p) /\
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       rname row + Z.of_nat (length nb) <= fr \/ fr + 64 <= rname row) /\
    (JOIN_0014 + 32 <= fr \/ fr + 64 <= JOIN_0013).

  Lemma djf : forall fr f spc j n w56, FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> DJF fr.
  Proof.
    intros fr f spc j n w56 HK Hp0 Ho0. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & HDd0).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb. unfold ASAN_GT in P3.
    destruct (HP Hp0) as (_ & Hlrow & _ & Hdpw & _). destruct (HO Ho0) as (_ & Hdow & _).
    assert (EFR00 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFM0 : fs_frame FS 0 (fs_M 0) = FS + 36864 + 1048576).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
    - (* the real-stack frame is inside the window *)
      split; [clear -Hdow Efr HAlo HAhi; lia|].
      split; [clear -Hdpw Efr HAlo HAhi; lia|].
      split.
      + intros B5 H1 H2. destruct (HN Hp0 B5 H1 H2) as (_ & _ & Hdnw & _).
        clear -Hdnw Efr HAlo HAhi; lia.
      + unfold JOIN_0013, JOIN_0014. clear -Efr HAlo HAhi HHM'; lia.
    - (* a side-stack frame is among the class-0 frames *)
      assert (EM : fs_M 0 = 16384) by reflexivity. rewrite EM in Hj.
      assert (EFj : fs_frame FS 0 j = FS + 36864 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (FRIN : FS + 36864 <= fr /\ fr + 64 <= FS + 36864 + 1048576) by (rewrite Efr, EFj; clear -Hj; lia).
      assert (INFW : In (fs_frame FS 0 0, fs_frame FS 0 (fs_M 0)) (fp_w [0%nat] FS)).
      { unfold fp_w, fp_w1. cbn [flat_map app]. right. right. left. reflexivity. }
      assert (OUTW : forall a bnd, In (a, bnd) (reac_box_model_block_D p o) ->
                (bnd <= fr \/ fr + 64 <= a)).
      { intros a bnd Hin.
        pose proof (dj_pair (reac_box_model_block_D p o) (fp_w [0%nat] FS) a bnd
                      (fs_frame FS 0 0) (fs_frame FS 0 (fs_M 0)) HDd0 Hin INFW) as Hdj.
        unfold ly_dj in Hdj. rewrite EFR00, EFM0 in Hdj. clear -Hdj FRIN; lia. }
      assert (INO : In (o, o + 32) (reac_box_model_block_D p o)).
      { unfold reac_box_model_block_D. apply in_or_app. right.
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0). left. reflexivity. }
      assert (INP : In (p, p + 296) (reac_box_model_block_D p o)).
      { unfold reac_box_model_block_D. apply in_or_app. left.
        replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0). left. reflexivity. }
      split; [exact (OUTW o (o + 32) INO)|].
      split; [exact (OUTW p (p + 296) INP)|].
      split.
      + intros B5 H1 H2.
        pose proof (dj_pair [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)
                      (rname row) (rname row + Z.of_nat (length nb)) (fs_frame FS 0 0) (fs_frame FS 0 (fs_M 0))
                      (NDJ Hp0 B5 H1 H2) ltac:(left; reflexivity) INFW) as Hdj.
        unfold ly_dj in Hdj. rewrite EFR00, EFM0 in Hdj. clear -Hdj FRIN; lia.
      + unfold JOIN_0013, JOIN_0014. clear -FRIN P3; lia.
  Qed.

  (* The shadow byte of an application byte apart from the frame is outside the body's write set. *)
  Lemma sh_out : forall fr f spc j n w56 x, FK fr f spc j n w56 -> app_mem x -> ~ (fr <= x < fr + 64) ->
    outside (EBW fr j n) (shadow_addr x).
  Proof.
    intros fr f spc j n w56 x HK Hapx Hxfr. hide_sec.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (rt_app_shadow x Hapx) as Hsh.
    assert (Hylo : LOWMEM_END <= shadow_addr x).
    { clear -Hsh. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    assert (Hyhi : shadow_addr x < HIGHMEM_BEG).
    { clear -Hsh. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    unfold LOWMEM_END in Hylo. unfold HIGHMEM_BEG in Hyhi.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
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
      pose proof (B.acl_win_sh x fr (fr + 64) FR8 Hxfr) as HW.
      pose proof (B.sh_add8 fr 8 FR8) as E. replace (fr + 8 * 8) with (fr + 64) in E by lia.
      rewrite E in HW. exact HW.
    - destruct (Bool.bool_dec ((p =? 0) || (o =? 0)) true) as [Eo|Eo]; [rewrite Eo; exact I|].
      apply Bool.not_true_is_false in Eo. rewrite Eo.
      apply orb_false_iff in Eo. destruct Eo as [_ Eo]. apply Z.eqb_neq in Eo.
      destruct (AO Eo) as (AOa & _ & _).
      pose proof (B.acl_app_in m o 32 0 AOa ltac:(lia)) as Ao0. rewrite Z.add_0_r in Ao0.
      pose proof (B.acl_app_in m o 32 31 AOa ltac:(lia)) as Ao31.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ao0, Ao31.
      cbn [outside]. split; [clear -Hylo Hyhi Ao0 Ao31; lia | exact I].
  Qed.

  (* A range apart from the frame stays addressable across the body's writes. *)
  Lemma addr_keep : forall fr f spc j n w56 (mc : word -> option byte) (R nR : Z),
    FK fr f spc j n w56 -> munch (EBW fr j n) m mc -> addressable m R nR ->
    (forall x, R <= x < R + nR -> ~ (fr <= x < fr + 64)) -> addressable mc R nR.
  Proof.
    intros fr f spc j n w56 mc R nR HK MU HAd Hdj.
    apply (B.addr_munch (EBW fr j n) m mc R nR HAd MU).
    intros i Hi. apply (sh_out fr f spc j n w56); [exact HK | exact (B.acl_app_in m R nR i HAd Hi)|].
    apply Hdj. lia.
  Qed.

  (* The ASan state the callees and the shadow checks need at a body memory. *)
  Definition JX (mc : word -> option byte) : Prop :=
    asan_cells mc /\ shadow_rw mc /\ stk rsegs mc (bv_unsigned sp - 4272) (bv_unsigned sp) /\
    addressable mc o 32 /\ addressable mc p 296 /\ addressable mc A 56 /\
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 -> addressable mc (rname row) (Z.of_nat (length nb))) /\
    (b = 1 -> addressable mc JOIN_0014 32) /\ (b = 2 -> addressable mc JOIN_0013 32).

  Lemma bv_jx : forall fr f spc j n w56 mc X J, FK fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BV fr j n w56 mc X J -> JX mc.
  Proof.
    intros fr f spc j n w56 mc X J HK Hp0 Ho0 ((MU & WM & RM & _ & _ & _ & _) & _). hide_sec.
    destruct (djf fr f spc j n w56 HK Hp0 Ho0) as (DJo & DJp & DJn & DJj).
    assert (PTo : forall x, o <= x < o + 32 -> ~ (fr <= x < fr + 64)) by (clear -DJo; intros x Hx; lia).
    assert (PTp : forall x, p <= x < p + 296 -> ~ (fr <= x < fr + 64)) by (clear -DJp; intros x Hx; lia).
    pose proof (ebw_sub fr f spc j n w56 HK) as SUB.
    split; [exact (br_ac (EBW fr j n) mc MU SUB)|].
    split; [exact (B.shadow_rw_mono m mc SR0 WM RM)|].
    split; [exact (B.stk_mono m mc _ _ ST0 WM RM)|].
    split; [exact (addr_keep fr f spc j n w56 mc o 32 HK MU (proj1 (AO Ho0)) PTo)|].
    split; [exact (addr_keep fr f spc j n w56 mc p 296 HK MU (AP Hp0) PTp)|].
    split.
    { pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
      destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
      pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
      pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSb.
      apply (addr_keep fr f spc j n w56 mc A 56 HK MU).
      - apply (B.acl_addr_sub m (bv_unsigned sp - 4272) 4272); [exact AW0 | clear -HAlo HAhi; lia | lia
                                                               | clear -HAlo HAhi; lia].
      - clear -FRhi FRlo HFSb HAlo HAhi P1. intros x Hx. lia. }
    split.
    - intros B5 H1 H2.
      pose proof (DJn B5 H1 H2) as DN.
      exact (addr_keep fr f spc j n w56 mc (rname row) (Z.of_nat (length nb)) HK MU (ANB Hp0 B5 H1 H2)
               ltac:(clear -DN; intros x Hx; lia)).
    - split.
      + intros Eb. apply (addr_keep fr f spc j n w56 mc JOIN_0014 32 HK MU (AJ1 Eb)).
        clear -DJj. unfold JOIN_0013, JOIN_0014 in *. intros x Hx. lia.
      + intros Eb. apply (addr_keep fr f spc j n w56 mc JOIN_0013 32 HK MU (AJ2 Eb)).
        clear -DJj. unfold JOIN_0013, JOIN_0014 in *. intros x Hx. lia.
  Qed.


  (* --- stores inside the body --- *)

  Lemma upd_app : forall (Y R bs : list byte) k, (k + length bs <= length Y)%nat ->
    upd_bytes (Y ++ R) k bs = upd_bytes Y k bs ++ R.
  Proof.
    intros Y R bs k H. unfold upd_bytes. rewrite firstn_app, skipn_app.
    replace (k - length Y)%nat with 0%nat by lia. replace (k + length bs - length Y)%nat with 0%nat by lia.
    rewrite firstn_O, skipn_O, app_nil_r, <- !app_assoc. reflexivity.
  Qed.

  Lemma rw_cb0 : forall mm AA N Y cs (k : Z) bs, rw_cells rsegs mm AA (CB N Y :: cs) -> 0 <= k ->
    (Z.to_nat k + length bs <= N)%nat ->
    rw_cells rsegs (write_to_mem mm (wa (AA + k)) bs) AA (CB N (upd_bytes Y (Z.to_nat k) bs) :: cs).
  Proof.
    intros mm AA N Y cs k bs [[Hwf HB] HW] Hk Hn. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LY Hwf].
    cbn [cells_bytes cbytes] in HB. split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length; lia | exact Hwf].
    - cbn [cells_bytes cbytes]. rewrite <- upd_app by lia.
      apply bytes_at_write_inside; [exact HB | exact Hk | rewrite length_app; lia].
    - cbn [cells_size csize] in HW |- *. apply wr_at_write. exact HW.
  Qed.

  (* The ranges the body writes are apart from the cells the invariant keeps. *)
  Definition DJW (fr : Z) : Prop :=
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= p \/ p + 296 <= o) /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       (o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o) /\
       (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272)) /\
    (o + 32 <= FS \/ FS + 8 <= o) /\ (o + 32 <= fr \/ fr + 64 <= o) /\
    length row = 296%nat /\ o + 32 <= APPMEM_END /\ p + 296 <= APPMEM_END.

  Lemma djw : forall fr f spc j n w56, FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> DJW fr.
  Proof.
    intros fr f spc j n w56 HK Hp0 Ho0. hide_sec.
    destruct (djf fr f spc j n w56 HK Hp0 Ho0) as (DJoi & _ & _ & _).
    destruct (HP Hp0) as (_ & Hlrow & _ & Hdpw & Hdpo). destruct (HO Ho0) as (_ & Hdow & _).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd0).
    assert (INO : In (o, o + 32) (reac_box_model_block_D p o)).
    { unfold reac_box_model_block_D. apply in_or_app. right.
      replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0). left. reflexivity. }
    assert (OFS : o + 32 <= FS \/ FS + 8 <= o).
    { pose proof (dj_pair (reac_box_model_block_D p o) (fp_w [0%nat] FS) o (o + 32)
                    (fs_hint FS 0) (fs_hint FS 0 + 8) HDd0 INO
                    ltac:(unfold fp_w, fp_w1; cbn [flat_map app]; left; reflexivity)) as Hdj.
      unfold ly_dj, fs_hint in Hdj. cbn [Z.of_nat] in Hdj. clear -Hdj; lia. }
    destruct (AO Ho0) as (AOa & AOe & _). destruct (AP Hp0) as (_ & _ & APe & _).
    pose proof (B.acl_app_in m o 32 31 AOa ltac:(lia)) as Ao31.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ao31.
    split; [exact Hdow|]. split; [destruct Hdpo as [E|E]; [exfalso; exact (Ho0 E) | exact E]|].
    split; [exact Hdpw|].
    split; [|split; [exact OFS | split; [exact DJoi | split; [exact Hlrow |
      split; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AOe |- *; clear -AOe; lia
             | exact APe]]]]].
    intros B5 H1 H2. destruct (HN Hp0 B5 H1 H2) as (_ & _ & Hdnw & Hdno).
    split; [destruct Hdno as [E|E]; [exfalso; exact (Ho0 E) | exact E] | exact Hdnw].
  Qed.

  Lemma bv_ok : forall fr j n w56 mc X J (k : Z) (nn : nat), BV fr j n w56 mc X J -> 0 <= k ->
    k + Z.of_nat nn <= 32 -> store_ok rsegs mc (wa (o + k)) nn = true.
  Proof.
    intros fr j n w56 mc X J k nn (_ & [_ WO] & _) Hk Hn. cbn [cells_size csize Nat.add] in WO.
    change (Z.of_nat 32) with 32 in WO. apply (wr_at_store_ok rsegs mc o 32); [exact WO | lia | lia].
  Qed.

  Lemma bv_lok : forall fr j n w56 mc X J (k : Z) (nn : nat), BV fr j n w56 mc X J -> 0 <= k ->
    k + Z.of_nat nn <= 56 -> store_ok rsegs mc (wa (A + k)) nn = true.
  Proof.
    intros fr j n w56 mc X J k nn (_ & _ & [_ WL] & _) Hk Hn. cbn [cells_size csize Nat.add] in WL.
    change (Z.of_nat 56) with 56 in WL. apply (wr_at_store_ok rsegs mc A 56); [exact WL | lia | lia].
  Qed.

  (* A store of bs at o + k: the box content is updated, every other cell of the invariant is kept. *)
  Lemma bv_store : forall fr f spc j n w56 mc X J (k : Z) (AA : word) bs,
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J -> 0 <= k ->
    k + Z.of_nat (length bs) <= 32 -> AA = wa (o + k) ->
    BV fr j n w56 (write_to_mem mc AA bs) (upd_bytes X (Z.to_nat k) bs) J.
  Proof.
    intros fr f spc j n w56 mc X J k AA bs HK Hp0 Ho0 PI Hk Hn ->. hide_sec.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    unfold APPMEM_END in Boe, Bpe.
    pose proof (bv_ok fr j n w56 mc X J k (length bs) PI Hk Hn) as HS.
    destruct PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof HO32 as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
    assert (Ebox : (p =? 0) || (o =? 0) = false)
      by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
    assert (B0 : 0 <= o + k) by (clear -Ro Hk; lia).
    assert (B1 : o + k + Z.of_nat (length bs) <= 2 ^ 64) by (clear -Boe Hk Hn; lia).
    assert (DSAV : bv_unsigned sp + -104 + Z.of_nat 104 <= o + k \/
                   o + k + Z.of_nat (length bs) <= bv_unsigned sp + -104)
      by (clear -Dow Hk Hn Rsp; cbn [Z.of_nat]; lia).
    assert (DHINT : FS + Z.of_nat 8 <= o + k \/ o + k + Z.of_nat (length bs) <= FS)
      by (clear -Dfs Hk Hn; cbn [Z.of_nat]; lia).
    assert (DF56 : fr + 56 + Z.of_nat 8 <= o + k \/ o + k + Z.of_nat (length bs) <= fr + 56)
      by (clear -Dfr Hk Hn; cbn [Z.of_nat]; lia).
    assert (DLOC : A + Z.of_nat 56 <= o + k \/ o + k + Z.of_nat (length bs) <= A)
      by (clear -Dow Hk Hn HAlo HAhi Rsp; cbn [Z.of_nat]; lia).
    assert (DROW : p + Z.of_nat 296 <= o + k \/ o + k + Z.of_nat (length bs) <= p)
      by (clear -Dpo Hk Hn; cbn [Z.of_nat]; lia).
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_write (EBW fr j n) m mc (o + k) bs MU B0 B1).
      unfold B.EBW. rewrite Ebox. apply inside_appr. cbn [inside]. left. clear -Hk Hn; lia.
    - apply wmono_write; exact WM.
    - apply B.rd_mono_write; exact RM.
    - apply mem_inv_store; [exact MI | exact HS].
    - apply rw_cells_frame; [exact SV | exact B0 | exact B1 |].
      cbn [cells_size csize Nat.add B.SAVES]. exact DSAV.
    - exists hh. apply bytes_at_write_other; [exact HH | exact B0 | exact B1 |].
      rewrite length_le8. exact DHINT.
    - apply bytes_at_write_other; [exact F56 | exact B0 | exact B1 |].
      rewrite length_le8. exact DF56.
    - split; [|split; [|split]].
      + exact (rw_cb0 mc o 32 X [] k bs HO32 Hk ltac:(clear -Hk Hn; lia)).
      + apply rw_cells_frame; [exact HL | exact B0 | exact B1 |].
        cbn [cells_size csize Nat.add]. exact DLOC.
      + apply bytes_at_write_other; [exact HRB | exact B0 | exact B1 |]. rewrite Lrow. exact DROW.
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & _).
        apply bytes_at_write_other; [exact (HNB B5 H1 H2) | exact B0 | exact B1 |].
        clear -Dno Hk Hn; lia.
  Qed.

  (* A store of bs at A + k (the 56 local bytes): the locals are updated, every other cell is kept. *)
  Lemma bv_lstore : forall fr f spc j n w56 mc X J (k : Z) (AA : word) bs,
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J -> 0 <= k ->
    k + Z.of_nat (length bs) <= 56 -> AA = wa (A + k) ->
    BV fr j n w56 (write_to_mem mc AA bs) X (upd_bytes J (Z.to_nat k) bs).
  Proof.
    intros fr f spc j n w56 mc X J k AA bs HK Hp0 Ho0 PI Hk Hn ->. hide_sec.
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    unfold APPMEM_END in Boe, Bpe.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSb.
    pose proof (bv_lok fr j n w56 mc X J k (length bs) PI Hk Hn) as HS.
    destruct PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof HL as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LJ _].
    assert (B0 : 0 <= A + k) by (clear -HAlo HAhi Rsp Hk HHM'; lia).
    assert (B1 : A + k + Z.of_nat (length bs) <= 2 ^ 64) by (clear -HAlo HAhi Rsp Hk Hn; lia).
    assert (DSAV : bv_unsigned sp + -104 + Z.of_nat 104 <= A + k \/
                   A + k + Z.of_nat (length bs) <= bv_unsigned sp + -104)
      by (clear -HAlo HAhi Hk Hn; cbn [Z.of_nat]; lia).
    assert (DHINT : FS + Z.of_nat 8 <= A + k \/ A + k + Z.of_nat (length bs) <= FS)
      by (clear -HFSb HHM' HAlo HAhi Hk Hn P1; cbn [Z.of_nat]; lia).
    assert (DF56 : fr + 56 + Z.of_nat 8 <= A + k \/ A + k + Z.of_nat (length bs) <= fr + 56)
      by (clear -FRhi Hk Hn; cbn [Z.of_nat]; lia).
    assert (DBOX : o + Z.of_nat 32 <= A + k \/ A + k + Z.of_nat (length bs) <= o)
      by (clear -Dow HAlo HAhi Hk Hn Rsp HHM'; cbn [Z.of_nat]; lia).
    assert (DROW : p + Z.of_nat 296 <= A + k \/ A + k + Z.of_nat (length bs) <= p)
      by (clear -Dpw HAlo HAhi Hk Hn Rsp HHM'; cbn [Z.of_nat]; lia).
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_write (EBW fr j n) m mc (A + k) bs MU B0 B1).
      unfold B.EBW. apply inside_appl. unfold B.Wf. cbn [inside]. left.
      clear -HAlo HAhi Hk Hn Rsp HHM'; lia.
    - apply wmono_write; exact WM.
    - apply B.rd_mono_write; exact RM.
    - apply mem_inv_store; [exact MI | exact HS].
    - apply rw_cells_frame; [exact SV | exact B0 | exact B1 |].
      cbn [cells_size csize Nat.add B.SAVES]. exact DSAV.
    - exists hh. apply bytes_at_write_other; [exact HH | exact B0 | exact B1 |].
      rewrite length_le8. exact DHINT.
    - apply bytes_at_write_other; [exact F56 | exact B0 | exact B1 |].
      rewrite length_le8. exact DF56.
    - split; [|split; [|split]].
      + apply rw_cells_frame; [exact HO32 | exact B0 | exact B1 |].
        cbn [cells_size csize Nat.add]. exact DBOX.
      + exact (rw_cb0 mc A 56 J [] k bs HL Hk ltac:(clear -Hk Hn; lia)).
      + apply bytes_at_write_other; [exact HRB | exact B0 | exact B1 |]. rewrite Lrow. exact DROW.
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (_ & Dnw).
        apply bytes_at_write_other; [exact (HNB B5 H1 H2) | exact B0 | exact B1 |].
        clear -Dnw HAlo HAhi Hk Hn Rsp HHM'; lia.
  Qed.


  (* --- the body's register shape and its exits --- *)

  (* The registers the body keeps: sp is the aligned stack pointer spc, s0 the entry sp, s1 the aligned frame base A,
     s2 the side-stack frame (0 for the real-stack frame), s3 = o, s4 = p, s7 = fr, s8 the frame's shadow address and
     s9 the shadow offset; s5 holds the result so far and s6, s10, s11 are free. *)
  Definition RB (f fr : Z) (ra' sp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s10' s11'
      t3' t4' t5' t6' : word) : bvmap 5 word :=
    mkR ra' sp' gp tp t0' t1' t2' sp (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6' a7'
        (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5' s6' (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off))
        (Z_to_bv 64 off) s10' s11' t3' t4' t5' t6'.

  Lemma spc_bounds : forall fr f spc j n w56, FK fr f spc j n w56 -> A - 64 <= spc <= A.
  Proof.
    intros fr f spc j n w56 [(Ef & Efr & Esp & _) | (_ & _ & _ & Esp & _)]; lia.
  Qed.

  (* 0x864c0 with the result in s5: the frame release of reac_box_model_block_epi.v. *)
  Lemma exit_r : forall fr f spc j n w56 mc X J (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J -> X = synth row b nb -> r = rc row b ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 r) x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x864c0) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 ((MU & WM & RM & MI & SV & HH & F56) & HO32 & HL & HRB & HNB) EX Er.
    unfold RB. apply (epi r mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
                        spc fr f j n w56 HK).
    - split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|].
      split; [exact SV|]. split; [exact HH|]. split; [exact F56|].
      replace ((p =? 0) || (o =? 0)) with false
        by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite <- EX. exact (rw1 mc o 32 X HO32).
    - rewrite Er.
      replace ((p =? 0) || (o =? 0)) with false
        by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      reflexivity.
  Qed.

  (* 0x864bc: li s5, 1 and the frame release. *)
  Lemma fin1 : forall fr f spc j n w56 mc X J
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J -> X = synth row b nb -> rc row b = 1 ->
    evt rsegs Q0 (MS (RB f fr x1 (Z_to_bv 64 spc) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x864bc) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31
      HK Hp0 Ho0 PI EX Er.
    unfold RB. step.
    exact (exit_r fr f spc j n w56 mc X J 1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
             HK Hp0 Ho0 PI EX (eq_sym Er)).
  Qed.

  (* Every byte from o to o + 32 is application memory. *)
  Lemma app_o : o <> 0 -> forall t, 0 <= t <= 32 -> app_mem (o + t).
  Proof.
    intros Ho0 t Ht. hide_sec. destruct (AO Ho0) as (AOa & AOe & _).
    pose proof (B.acl_app_in m o 32 0 AOa ltac:(lia)) as A0. rewrite Z.add_0_r in A0.
    clear -A0 AOe Ht. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  Qed.



  (* Bytes of a cell read pointwise from its content. *)
  Lemma cell_bytes_pt : forall mm AA (N : nat) (Jc D : list byte) (k : nat), rw_cells rsegs mm AA [CB N Jc] ->
    (k + length D <= N)%nat ->
    (forall i, (i < length D)%nat -> nth_error Jc (k + i) = nth_error D i) ->
    bytes_at rsegs mm (AA + Z.of_nat k) D.
  Proof.
    intros mm AA N Jc D k [[Hwf HB] _] Hk Hpt. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LJ _].
    cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. destruct HB as (Ha & Hl & Hp).
    split; [lia|]. split; [lia|].
    intros i Hi. rewrite <- (Hpt i Hi). rewrite <- (Hp (k + i)%nat ltac:(lia)).
    f_equal. f_equal. lia.
  Qed.


  (* --- stores into the ASan frame and into its shadow (the b = 3 path) --- *)

  Lemma bv_fok : forall fr f spc j n w56 mc X J (k : Z) (nn : nat), FK fr f spc j n w56 ->
    BV fr j n w56 mc X J -> 0 <= k -> k + Z.of_nat nn <= 64 ->
    store_ok rsegs mc (wa (fr + k)) nn = true.
  Proof.
    intros fr f spc j n w56 mc X J k nn HK PI Hk Hn.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct PI as ((_ & WM & _) & _).
    eapply B.wv_store_ok; [|exact WM| |].
    - intros i Hi. replace (fr + k + i) with (fr + (k + i)) by lia. apply FW. lia.
    - pose proof (FAP 0 ltac:(lia)) as AF0. rewrite Z.add_0_r in AF0.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF0. clear -AF0 Hk; lia.
    - pose proof (FAP 63 ltac:(lia)) as AF63.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF63. clear -AF63 Hk Hn; lia.
  Qed.

  Lemma bv_sok : forall fr f spc j n w56 mc X J (k : Z) (nn : nat), FK fr f spc j n w56 ->
    BV fr j n w56 mc X J -> 0 <= k -> k + Z.of_nat nn <= 8 ->
    store_ok rsegs mc (wa (fr / 8 + off + k)) nn = true.
  Proof.
    intros fr f spc j n w56 mc X J k nn HK PI Hk Hn.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct PI as ((_ & WM & _) & _).
    eapply B.wv_store_ok; [|exact WM| |].
    - intros i Hi. replace (fr / 8 + off + k + i) with (fr / 8 + off + (k + i)) by lia. apply SW. lia.
    - clear -SH1 Hk; lia.
    - clear -SH2 Hk Hn; lia.
  Qed.

  (* The box, the locals, the row, the name, the saved registers, the hint word and the flag-address word are apart
     from the frame's 64 bytes and from its 8 shadow bytes. *)
  Lemma bv_frame_dj : forall fr f spc j n w56, FK fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    (o + 32 <= fr \/ fr + 64 <= o) /\ (p + 296 <= fr \/ fr + 64 <= p) /\
    (A + 56 <= fr \/ fr + 64 <= A) /\ (FS + 8 <= fr \/ fr + 64 <= FS) /\
    (bv_unsigned sp <= fr \/ fr + 64 <= bv_unsigned sp - 104) /\
    ((b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
      rname row + Z.of_nat (length nb) <= fr \/ fr + 64 <= rname row).
  Proof.
    intros fr f spc j n w56 HK Hp0 Ho0.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    destruct (djf fr f spc j n w56 HK Hp0 Ho0) as (DJo & DJp & DJn & _).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSb.
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    split; [exact DJo|]. split; [exact DJp|].
    split; [clear -FRhi HAlo HAhi; lia|].
    split; [clear -FRlo P1; lia|].
    split; [clear -FRhi HAlo HAhi; lia | exact DJn].
  Qed.

  (* A store of bs at fr + k (inside the frame, below the flag-address word at fr + 56). *)
  Lemma bv_fstore : forall fr f spc j n w56 mc X J (k : Z) (AA : word) bs,
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J -> 0 <= k ->
    k + Z.of_nat (length bs) <= 56 -> AA = wa (fr + k) ->
    BV fr j n w56 (write_to_mem mc AA bs) X J.
  Proof.
    intros fr f spc j n w56 mc X J k AA bs HK Hp0 Ho0 PI Hk Hn ->.
    destruct (bv_frame_dj fr f spc j n w56 HK Hp0 Ho0) as (Do & Dp & Dl & Dfs & Dsv & Dn).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_fok fr f spc j n w56 mc X J k (length bs) HK PI Hk ltac:(clear -Hn; lia)) as HS.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (Lrow : length row = 296%nat) by (hide_sec; destruct (HP Hp0) as (_ & H & _); exact H).
    hide_sec.
    destruct PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof (FAP 0 ltac:(lia)) as AF0. rewrite Z.add_0_r in AF0. pose proof (FAP 63 ltac:(lia)) as AF63.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF0, AF63.
    assert (B0 : 0 <= fr + k) by (clear -AF0 Hk; lia).
    assert (B1 : fr + k + Z.of_nat (length bs) <= 2 ^ 64) by (clear -AF63 Hk Hn; lia).
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_write (EBW fr j n) m mc (fr + k) bs MU B0 B1).
      unfold B.EBW. apply inside_appl. unfold B.Wf. cbn [inside]. right. right. right. left.
      clear -Hk Hn; lia.
    - apply wmono_write; exact WM.
    - apply B.rd_mono_write; exact RM.
    - apply mem_inv_store; [exact MI | exact HS].
    - apply rw_cells_frame; [exact SV | exact B0 | exact B1 |].
      cbn [cells_size csize Nat.add B.SAVES]. clear -Dsv Hk Hn; lia.
    - exists hh. apply bytes_at_write_other; [exact HH | exact B0 | exact B1 |].
      rewrite length_le8. clear -Dfs Hk Hn; lia.
    - apply bytes_at_write_other; [exact F56 | exact B0 | exact B1 |].
      rewrite length_le8. clear -Hk Hn; lia.
    - split; [|split; [|split]].
      + apply rw_cells_frame; [exact HO32 | exact B0 | exact B1 |].
        cbn [cells_size csize Nat.add]. clear -Do Hk Hn; lia.
      + apply rw_cells_frame; [exact HL | exact B0 | exact B1 |].
        cbn [cells_size csize Nat.add]. clear -Dl Hk Hn; lia.
      + apply bytes_at_write_other; [exact HRB | exact B0 | exact B1 |]. rewrite Lrow. clear -Dp Hk Hn; lia.
      + intros B5 H1 H2. pose proof (Dn B5 H1 H2) as Dn'.
        apply bytes_at_write_other; [exact (HNB B5 H1 H2) | exact B0 | exact B1 |]. clear -Dn' Hk Hn; lia.
  Qed.

  (* A store of one byte at the frame's shadow byte k (0 <= k < 8). *)
  Lemma bv_sstore : forall fr f spc j n w56 mc X J (k : Z) (AA : word) (bs : list byte),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J -> 0 <= k ->
    k + Z.of_nat (length bs) <= 8 -> AA = wa (fr / 8 + off + k) ->
    BV fr j n w56 (write_to_mem mc AA bs) X J.
  Proof.
    intros fr f spc j n w56 mc X J k AA bs HK Hp0 Ho0 PI Hk Hn ->.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_sok fr f spc j n w56 mc X J k (length bs) HK PI Hk Hn) as HS.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    assert (Lrow : length row = 296%nat) by (hide_sec; destruct (HP Hp0) as (_ & H & _); exact H).
    assert (APo : forall t, 0 <= t <= 32 -> app_mem (o + t)) by (apply app_o; exact Ho0).
    assert (APp : forall t, 0 <= t < 296 -> app_mem (p + t))
      by (hide_sec; intros t Ht; destruct (AP Hp0) as (_ & _ & _ & PA); exact (proj1 (PA t Ht))).
    assert (APn : (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
              forall t, 0 <= t < Z.of_nat (length nb) -> app_mem (rname row + t))
      by (hide_sec; intros B5 H1 H2 t Ht; destruct (ANB Hp0 B5 H1 H2) as (_ & _ & _ & PA);
          exact (proj1 (PA t Ht))).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    pose proof (P4 FS ltac:(lia)) as AFS. pose proof (P4 (FS + 7) ltac:(lia)) as AFS7.
    pose proof (FAP 56 ltac:(lia)) as AF56. pose proof (FAP 63 ltac:(lia)) as AF63.
    hide_sec. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (APo 0 ltac:(lia)) as AO0. rewrite Z.add_0_r in AO0.
    pose proof (APo 31 ltac:(lia)) as AO31.
    pose proof (APp 0 ltac:(lia)) as AP0. rewrite Z.add_0_r in AP0.
    pose proof (APp 295 ltac:(lia)) as AP295.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AO0, AO31, AP0, AP295, AFS, AFS7, AF56, AF63.
    destruct PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    assert (B0 : 0 <= fr / 8 + off + k) by (clear -SH1 Hk; lia).
    assert (B1 : fr / 8 + off + k + Z.of_nat (length bs) <= 2 ^ 64) by (clear -SH2 Hk Hn; lia).
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_write (EBW fr j n) m mc (fr / 8 + off + k) bs MU B0 B1).
      unfold B.EBW. apply inside_appl. unfold B.Wf, shadow_addr. rewrite Hoff.
      cbn [inside]. right. right. right. right. left. clear -Hk Hn; lia.
    - apply wmono_write; exact WM.
    - apply B.rd_mono_write; exact RM.
    - apply mem_inv_store; [exact MI | exact HS].
    - apply rw_cells_frame; [exact SV | exact B0 | exact B1 |].
      cbn [cells_size csize Nat.add B.SAVES]. clear -SH1 SH2 Hk Hn HHM' HAE' Rsp; lia.
    - exists hh. apply bytes_at_write_other; [exact HH | exact B0 | exact B1 |].
      rewrite length_le8. clear -SH1 SH2 Hk Hn AFS AFS7; lia.
    - apply bytes_at_write_other; [exact F56 | exact B0 | exact B1 |].
      rewrite length_le8. clear -SH1 SH2 Hk Hn AF56 AF63; lia.
    - split; [|split; [|split]].
      + apply rw_cells_frame; [exact HO32 | exact B0 | exact B1 |].
        cbn [cells_size csize Nat.add]. clear -SH1 SH2 Hk Hn AO0 AO31; lia.
      + apply rw_cells_frame; [exact HL | exact B0 | exact B1 |].
        cbn [cells_size csize Nat.add]. clear -SH1 SH2 Hk Hn HHM' HAE' Rsp HAlo HAhi; lia.
      + apply bytes_at_write_other; [exact HRB | exact B0 | exact B1 |].
        rewrite Lrow. clear -SH1 SH2 Hk Hn AP0 AP295; lia.
      + intros B5 H1 H2. pose proof (APn B5 H1 H2) as APn'.
        apply (B.bytes_keep mc _ (rname row) nb (HNB B5 H1 H2)).
        intros x Hx.
        pose proof (APn' (x - rname row) ltac:(clear -Hx; lia)) as APx.
        replace (rname row + (x - rname row)) with x in APx by lia.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APx.
        apply (mrd_wn_ne mc (fr / 8 + off + k) bs x);
          [exact B0 | exact B1 | clear -APx; lia | clear -APx SH1 SH2 Hk Hn; lia].
  Qed.


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

  (* The facts about a call's footprint that every wrapper below needs. *)
  Lemma call_facts : forall fr f spc j n w56 mc X J, FK fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BV fr j n w56 mc X J ->
    (bv_unsigned sp - 4272 <= spc <= bv_unsigned sp - 160) /\ (A <= bv_unsigned sp - 160) /\
    (bv_unsigned sp - 4272 + 4000 <= spc) /\ HIGHMEM_BEG <= bv_unsigned sp - 4272 /\ spc <= APPMEM_END /\
    A + 56 <= bv_unsigned sp - 104 /\ spc <= A /\
    (fr = spc \/ fr + 64 <= bv_unsigned sp - 4272).
  Proof.
    intros fr f spc j n w56 mc X J HK Hp0 Ho0 PI.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (spc_bounds fr f spc j n w56 HK) as HSPC.
    pose proof HHM as HHM'. pose proof HAE as HAE'. hide_sec.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (FRS : fr = spc \/ fr + 64 <= bv_unsigned sp - 4272).
    { pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
      unfold FS_SIZE in HFSb.
      destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
      - left. lia.
      - right. assert (EM : fs_M 0 = 16384) by reflexivity. rewrite EM in Hj.
        rewrite Efr. unfold fs_frame, fs_B. cbn [Z.of_nat]. clear -Hj HFSb. lia. }
    repeat split; try (unfold HIGHMEM_BEG, APPMEM_END; clear -HSPC HAlo HAhi HHM' HAE' Rsp; lia).
    exact FRS.
  Qed.


End Main.
