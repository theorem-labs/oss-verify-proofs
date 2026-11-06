(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 409 of its 423 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base.
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

(* reac_box_model_block, image A (asan, entry 0x85b44), part 2: the frame-release epilogue 0x864c0 -> 0x86520 from
   the body-end invariant EB of reac_box_model_block_base.v. The run stores the release magic word at the ASan
   frame, zeroes the frame's eight shadow bytes (real-stack frame) or poisons them and clears the class-0 flag byte
   (side-stack frame), and joins reac_box_model_block_base.epi_close. *)

Module B := reac_box_model_block_base.

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

  (* A store of bs at a inside the body footprint W, carried across the four facts the body keeps. *)
  Lemma est : forall (W : list ivl) (mc : word -> option byte) (a : Z) (bs : list byte),
    munch W m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> inside W a (Z.of_nat (length bs)) ->
    store_ok rsegs mc (wa a) (length bs) = true ->
    munch W m (write_to_mem mc (wa a) bs) /\ wmono rsegs m (write_to_mem mc (wa a) bs) /\
    rd_mono m (write_to_mem mc (wa a) bs) /\ mem_inv rsegs (write_to_mem mc (wa a) bs).
  Proof.
    intros W mc a bs MU WM RM MI Ha Hl Hin HS.
    split; [exact (munch_write W m mc a bs MU Ha Hl Hin)|].
    split; [exact (wmono_write rsegs m mc (wa a) bs WM)|].
    split; [exact (B.rd_mono_write m mc (wa a) bs RM) | exact (mem_inv_store rsegs mc (wa a) bs MI HS)].
  Qed.

  (* After a store step whose write_to_mem is left visible, carry the four facts across it. *)
  Ltac estep :=
    norm_store;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?pm (wa ?A0) ?bb) _) =>
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
     | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) =>
         try (replace l with [Z_to_bv 8 0] by reflexivity)
     end);
    estep;
    repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.

  (* An 8-byte read of a word written in memory. *)
  Lemma rd8_at : forall (mm : word -> option byte) (AA : Z) (v : word),
    bytes_at rsegs mm AA (le8 v) -> ov_read_bytes rsegs mm (wa AA) 8 = Some (le8 v).
  Proof.
    intros mm AA v H.
    pose proof (bytes_at_read rsegs mm AA (le8 v) 0 8 H ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as HR.
    rewrite Z.add_0_r in HR. rewrite skipn_O in HR.
    assert (E : firstn 8 (le8 v) = le8 v) by (apply firstn_all2; rewrite length_le8; lia).
    rewrite E in HR. exact HR.
  Qed.

  (* The frame-release epilogue 0x864c0 -> 0x86520, from the body-end invariant EB: the magic word, the frame's
     shadow bytes (0 for the real-stack frame, -11 for a side-stack frame) and, for a side-stack frame, the class-0
     flag byte cleared to 0. *)
  Lemma epi : forall (r : Z) (mc : word -> option byte)
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
    intros r mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      spc fr f j n w56 HK HEB Hr.
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
    assert (OUTWR2 : forall x, app_mem x -> (x < fr \/ fr + 8 <= x) ->
              outside [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] x).
    { intros x Hax Hfrx. cbn [outside]. split; [lia|]. split; [|exact I].
      assert (~ (fr / 8 + off <= x < fr / 8 + off + 8)) by (rewrite EA8; apply SHOUT; exact Hax). lia. }
    (* the facts of the box result the post needs, then the section premises hidden from lia *)
    assert (BOXF : (p =? 0) || (o =? 0) = false ->
              length (synth row b nb) = 32%nat /\ (forall x, o <= x < o + 32 -> app_mem x) /\
              (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272)).
    { intros E. unhide HP. unhide AO. unhide HO.
      apply orb_false_iff in E. destruct E as [Ep Eo]. apply Z.eqb_neq in Ep. apply Z.eqb_neq in Eo.
      destruct (HP Ep) as (_ & Hl & _). destruct (AO Eo) as (AOa & _ & _). destruct (HO Eo) as (_ & Hdw & _).
      split; [exact (rs_synth_len row b nb Hl)|]. split; [|exact Hdw].
      intros x Hx. pose proof (B.acl_app_in m o 32 (x - o) AOa ltac:(clear -Hx; lia)) as H.
      replace (o + (x - o)) with x in H by ring. exact H. }
    (* the magic word at [fr, fr + 8) *)
    step. step. wstF fr 8%nat. step. estep.
    repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
    destruct HKd as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
    - (* the real-stack frame: f = 0, fr = A - 64, spc = A - 64, j = 0, n = 0; the shadow is zeroed *)
      subst f j n spc.
      step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
      sst (fr / 8 + off + 4). sst (fr / 8 + off + 5). sst (fr / 8 + off + 6). sst (fr / 8 + off + 7).
      sst (fr / 8 + off + 0). sst (fr / 8 + off + 1). sst (fr / 8 + off + 2). sst (fr / 8 + off + 3).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mfin := mm) in * end.
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
        { unfold shadow_addr. rewrite Hoff. rewrite Efr.
          assert (Hm : (A - 64) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
          Z.div_mod_to_equations; lia. }
        assert (Hk : 0 <= (x - fr) / 8 < 8) by (rewrite Efr; clear -Hx HA32; Z.div_mod_to_equations; lia).
        rewrite Exsh. set (kk := (x - fr) / 8) in *. unfold mfin.
        rewrite !mrd_w1 by (clear -SH1 SH2 Hk; lia). rewrite !zeqb_addcancel.
        destruct Hk as [Hk0 Hk8].
        assert (Ek : kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5 \/ kk = 6 \/ kk = 7) by lia.
        destruct Ek as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity. }
      eapply epi_close.
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
             clear -Hx Hdw HAlo HAhi Efr; lia.
          -- unfold REAC_BOX_MODEL_BLOCK_K. apply (munch_weaken _ _ m mfin SUB). eassumption.
    - (* a side-stack frame: fr = fs_frame FS 0 j, f = fr, spc = A, n = 1; the shadow is -11 and the flag cleared *)
      subst f spc w56 n.
      assert (Hfrpos : 0 < fr < 2 ^ 64) by (clear -FRlo P1 FRhi HAhi HAE'; lia).
      assert (EM : fs_M 0 = 16384) by reflexivity. rewrite EM in Hj.
      assert (EFl : fs_flag FS 0 j = FS + 4096 + j) by
        (unfold fs_flag; cbn [Z.of_nat];
         replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
      assert (EFj : fs_frame FS 0 j = FS + 36864 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      step.
      replace (bv_eqb (Z_to_bv 64 fr) (Z_to_bv 64 0)) with false by (symmetry; apply rc_neq0_64; exact Hfrpos).
      cbv iota. step.
      sst (fr / 8 + off + 4). sst (fr / 8 + off + 5). sst (fr / 8 + off + 6). sst (fr / 8 + off + 7).
      sst (fr / 8 + off + 0). sst (fr / 8 + off + 1). sst (fr / 8 + off + 2). sst (fr / 8 + off + 3).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mld := mm) in * end.
      assert (MUr6 : munch [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8)] mc mld).
      { unfold mld. repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
        apply munch_refl. }
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
      step.
      (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) => try (replace l with [Z_to_bv 8 0] by reflexivity)
       end).
      estep.
      repeat match goal with HS : store_ok rsegs _ _ _ = true |- _ => clear HS end.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mfin := mm) in * end.
      assert (MUr : munch [(fr, fr + 8); (fr / 8 + off, fr / 8 + off + 8);
                           (fs_flag FS 0 j, fs_flag FS 0 j + 1)] mc mfin).
      { unfold mfin, mld.
        repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
        apply munch_refl. }
      assert (WMr : wmono rsegs mc mfin).
      { unfold mfin, mld. repeat apply wmono_write. apply wmono_refl. }
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
      assert (FLRB : mrd rsegs mfin (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)).
      { unfold mfin. rewrite mrd_w1 by (rewrite EFl; clear -P1 Hj HFSb HAE'; lia).
        rewrite Z.eqb_refl. reflexivity. }
      eapply epi_close.
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
End Main.
