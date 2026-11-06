(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 647 of its 661 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block reac_box_model_block_body reac_box_model_blockF.
(* Last: StepF's step / if_* / store_done / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of reac_box_model_block.v:215's store hook: that file made it Local (a Theorem Labs lane, approved by a Theorem Labs lane, 2026-10-30). *)
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


(* ------------------------------------------------------------------------------------------------------------ *)
(* This file's hooks (the prelude's, repeated: they are Local there). *)
Ltac mbF_fix_lit_store2 :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt2 :=
  try mbF_fix_lit_store2;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

Section BodyF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F.
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

  Hypothesis HMS : asan_memset_contract_F.
  Hypothesis HMC : asan_memcpy_contract_F.
  Hypothesis HBD : build_dt1_single_contract_F.
  Hypothesis HDH : dt1_head_contract_F.
  Hypothesis HNF : name_field_contract_F.
  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  (* PERF: the heavy section hypotheses, cleared before lia / Z.div_mod_to_equations (the plain file's clr, with
     the footprint hypotheses of this file added). *)
  Ltac clr := try clear HSM; try clear HA; try clear ST0; try clear MI0; try clear AC0; try clear SR0;
    try clear AW0; try clear FP0; try clear TLS0; try clear HP; try clear HN; try clear HO; try clear AP;
    try clear ANB; try clear AO; try clear AJ1; try clear AJ2; try clear NDJ; try clear HMS; try clear HMC;
    try clear HBD; try clear HDH; try clear HNF; try clear HRNG;
    repeat match goal with
    | H : _ -> _ /\ shcov _ _ _ /\ _ |- _ => clear H
    | H : _ -> _ -> _ /\ shcov _ _ _ /\ _ |- _ => clear H
    | H : _ -> shcov _ _ _ /\ _ |- _ => clear H
    | H : _ -> _ -> _ -> _ -> _ /\ shcov _ _ _ /\ _ |- _ => clear H
    | H : forall _ _ _ _ _ _, asan_tls_cells _ _ _ _ _ _ _ _ -> _ |- _ => clear H
    end.

  (* The pure lemmas of reac_box_model_block.v and reac_box_model_block_body.v, with this section's arguments.
     Their proofs are there; these are the same statements, so the scripts below read as the plain ones do. *)
  Lemma bf_addr_rebuild : forall mc,
    (forall i, 0 <= i < 4272 ->
       mrd rsegs mc (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0)) ->
    addressable mc (bv_unsigned sp - 4272) 4272.
  Proof. intros mc H. eapply (addr_rebuild sp m); eassumption. Qed.

  Lemma bf_sub_post : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    sub_fp (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]))
           (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof. intros fr f spc j n w56 HK. eapply (sub_post sp m p b o FS A row nb ob); eassumption. Qed.

  Lemma bf_sub_wf : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    sub_fp (Wf sp FS fr j n)
      ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof. intros fr f spc j n w56 HK. eapply (sub_wf sp m p b o FS A row nb); eassumption. Qed.

  Lemma bf_app_rng : forall X n, 0 < n -> (forall i, 0 <= i < n -> app_mem (X + i)) ->
    X + n <= 2147450880 \/ 17594333495296 <= X.
  Proof. intros X n Hn H. eapply (app_rng sp m p b o row nb); eassumption. Qed.

  Lemma bf_o_dj_fs : o <> 0 -> forall lo hi, In (lo, hi) (fp_w [0%nat] FS) -> o + 32 <= lo \/ hi <= o.
  Proof. intros Eo lo hi Hin. eapply (o_dj_fs sp tp m p o FS); eassumption. Qed.

  Lemma bf_rel_wsh : forall fr f spc j n w56 (m' : word -> option byte),
    FK FS A fr f spc j n w56 ->
    munch (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m m' ->
    (forall x, shadow_addr fr <= x < shadow_addr fr + 8 ->
       shadow_addr (bv_unsigned sp - 4272) <= x < shadow_addr (bv_unsigned sp) ->
       mrd rsegs m' (wa x) = Some (Z_to_bv 8 0)) ->
    forall i, 0 <= i < 4272 -> mrd rsegs m' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0).
  Proof.
    intros fr f spc j n w56 m' HK MU WSH i Hi.
    eapply (rel_wsh sp tp m p b o FS off A row nb ob); eassumption.
  Qed.

  Lemma bf_o_out_wf : o <> 0 -> forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    disjoint_from (Wf sp FS fr j n) o 32.
  Proof.
    intros Eo fr f spc j n w56 HK. eapply (o_out_wf sp tp m p b o FS off A row nb ob); eassumption.
  Qed.

  Lemma bf_o_sh_out_wf : o <> 0 -> forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n) (shadow_addr (o + i)).
  Proof.
    intros Eo fr f spc j n w56 HK i Hi.
    eapply (o_sh_out_wf sp tp m p b o FS off A row nb ob); eassumption.
  Qed.

  Lemma bf_fk_facts : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 64 -> app_mem (fr + i)) /\
    (fr + 64 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 8 -> wview rsegs m (wa (fr / 8 + off + i)) <> None) /\
    2147450880 <= fr / 8 + off /\ fr / 8 + off + 8 <= 17594333495296.
  Proof.
    intros fr f spc j n w56 HK.
    exact (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK).
  Qed.

  Lemma bf_rel_flags : forall (fr f spc j n : Z) (w56 : word) (m' : word -> option byte),
    FK FS A fr f spc j n w56 ->
    munch (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m m' ->
    (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    exists flags', bytes_at rsegs m' (fs_flag FS 0 0) flags' /\ Z.of_nat (length flags') = fs_M 0 /\
      Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
  Proof.
    intros fr f spc j n w56 m' HK MU Hfj.
    eapply (rel_flags sp tp m p b o FS off A row nb ob); eassumption.
  Qed.

  Lemma bf_br_ac : forall (Wm : list ivl) (m' : word -> option byte), munch Wm m m' ->
    sub_fp Wm (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS) ->
    asan_cells m'.
  Proof. intros Wm m' MU Hs. eapply (br_ac sp tp m p b o FS row nb ob); eassumption. Qed.

  Lemma bf_br_fp : forall (Wm : list ivl) (m' : word -> option byte) (h' : word) (flags' : list byte),
    munch Wm m m' -> wmono rsegs m m' -> rd_mono m m' ->
    sub_fp Wm (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS) ->
    bytes_at rsegs m' (fs_hint FS 0) (le8 h') ->
    bytes_at rsegs m' (fs_flag FS 0 0) flags' -> Z.of_nat (length flags') = fs_M 0 ->
    Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags' ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Proof.
    intros Wm m' h' flags' MU WM RM Hs Hint' Hflags' Hlen' HF01'.
    eapply (br_fp sp tp m p o FS); eassumption.
  Qed.

  (* 0x86e74 after the release stores: the post from the fine footprint, the flag readback, the window shadow at 0
     and the output block. *)
  Lemma rel_finF : forall (fr f spc j n : Z) (w56 : word) (m' : word -> option byte) (ret : Z) (h' : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    munch (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m m' ->
    wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    bytes_at rsegs m' FS (le8 h') ->
    (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    (forall i, 0 <= i < 4272 ->
       mrd rsegs m' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0)) ->
    (if (p =? 0) || (o =? 0) then True else bytes_at rsegs m' o (synth row b nb)) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 m' ret h' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      HK Er MU WM RM MI SV HH Hfj Hsh HX.
    pose proof (bf_sub_post fr f spc j n w56 HK) as SP.
    (* OPEN (a Theorem Labs lane, ctl_post_acall_kept): the class-0 flags, the hint and fs_place at m' come from the ENTRY
       facts across the malloc and the free (the post's fp [0%nat] m'). *)
    destruct (bf_rel_flags fr f spc j n w56 m' HK MU Hfj) as (flags' & HF & HL & H01).
    assert (HH0 : bytes_at rsegs m' (fs_hint FS 0) (le8 h'))
      by (replace (fs_hint FS 0) with FS by (unfold fs_hint; cbn [Z.of_nat]; lia); exact HH).
    apply (epi0F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A row nb RNG HRNG
             ret m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 spc fr f Er SV WM MI).
    - exact (stk_mono m m' _ _ ST0 WM RM).
    - exact (bf_br_ac _ m' MU SP).
    - exact (shadow_rw_mono m m' SR0 WM RM).
    - exact (bf_addr_rebuild m' Hsh).
    - exact (bf_br_fp _ m' h' flags' MU WM RM SP HH0 HF HL H01).
    - unfold reac_box_model_block_X in SP.
      exact (acl_tls_ret [0%nat] m m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o)
               [(shadow_addr (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K), shadow_addr (bv_unsigned sp))] _
               FP0 TLS0 MU SP).
    - revert MU HX SP. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros MU HX SP.
      + rewrite app_nil_r in MU. exact (munch_weaken _ _ m m' (bf_sub_wf fr f spc j n w56 HK) MU).
      + split; [exact HX|].
        apply orb_false_iff in Epo. destruct Epo as (_ & Eo).
        unfold reac_box_model_block_W in SP. rewrite Eo in SP.
        exact (munch_weaken _ _ m m' SP MU).
  Qed.

  Local Ltac cell_of_bytes bs ::=
    lazymatch bs with
    | le8 ?v => constr:(C8 v)
    | le4 ?v => constr:(C4 v)
    | le2 ?v => constr:(C2 v)
    | [?b] => constr:(C1 b)
    | le1 (zxb ?b) => constr:(C1 b)
    | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
    end.

  (* ---- The cut AT the class-0 flag store (a Theorem Labs lane 00:4xZ / 00:5xZ: ctl_release_of_free_law 0 switches the
     journal at the store) ---------------------------------------------------------------------------------------
     rel_runF's side arm is cut at 0x86e4c, the `sb zero,0(a0)` with a0 = fs_flag FS 0 j loaded from the frame word at
     fr + 56 (0x86e48), BEFORE the store: rel_preF is the stretch 0x86e14 .. 0x86e4c (the magic word, the eight f5
     shadow bytes, the load of the flag pointer), rel_flag_restF the rest (the store, the jump to 0x86e74).  The
     scripts are rel_runF's, verbatim, split at the cut; rel_flag_facts is what the side arm carried across it. *)
  Definition rel_flag_state (j ret : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 sp (Z_to_bv 64 A) (Z_to_bv 64 (fs_flag FS 0 j)) x11 x12 x13 x14 x15 x16
            x17 (Z_to_bv 64 (fs_frame FS 0 j)) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22
            (Z_to_bv 64 (fs_frame FS 0 j)) (Z_to_bv 64 (fs_frame FS 0 j / 8 + 2147450880)) (Z_to_bv 64 2147450880)
            s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x86e4c) fc None m1 (seg_rom rsegs).

  Definition rel_flag_facts (C : list ivl) (j : Z) (mc m1 : word -> option byte) (h : word) (vfl : byte) : Prop :=
    0 <= j < 16384 /\
    rw_cells rsegs m1 (fs_flag FS 0 j) [CB 1 [vfl]] /\
    munch ((bv_unsigned sp - 4272, bv_unsigned sp) :: (FS, FS + 8) :: (fs_flag FS 0 j, fs_flag FS 0 j + 1) ::
           (fs_frame FS 0 j, fs_frame FS 0 j + 64) ::
           (fs_frame FS 0 j / 8 + 2147450880, fs_frame FS 0 j / 8 + 2147450880 + 8) :: C) m m1 /\
    munch [(bv_unsigned sp - 4272, bv_unsigned sp); (FS, FS + 8); (fs_flag FS 0 j, fs_flag FS 0 j + 1);
           (fs_frame FS 0 j, fs_frame FS 0 j + 64);
           (fs_frame FS 0 j / 8 + 2147450880, fs_frame FS 0 j / 8 + 2147450880 + 8)] mc m1 /\
    wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\
    rw_cells rsegs m1 (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) /\
    bytes_at rsegs m1 FS (le8 h).

  (* The rest of the release from the flag store: the store, the jump to 0x86e74, the readback of the flag. *)
  Lemma rel_flag_restF : forall (C : list ivl) (j : Z) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    (forall (m' : word -> option byte) (h' x10' : word),
       munch (Wf sp FS (fs_frame FS 0 j) j 1 ++ C) m m' -> munch (Wf sp FS (fs_frame FS 0 j) j 1) mc m' ->
       wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' ->
       rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
       bytes_at rsegs m' FS (le8 h') ->
       (1 = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
       (forall x, shadow_addr (fs_frame FS 0 j) <= x < shadow_addr (fs_frame FS 0 j) + 8 ->
          shadow_addr (bv_unsigned sp - 4272) <= x < shadow_addr (bv_unsigned sp) ->
          mrd rsegs m' (wa x) = Some (Z_to_bv 8 0)) ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10' x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (fs_frame FS 0 j)) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 (fs_frame FS 0 j))
                 (Z_to_bv 64 ((fs_frame FS 0 j) / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs))) ->
    forall (m1 : word -> option byte) (h : word) (vfl : byte), rel_flag_facts C j mc m1 h vfl ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (rel_flag_state j ret x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1).
  Proof.
    intros C j mc ret x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 K m1 h vfl (Hj & FL & MU & MU2 & WM & RM & MI & SV & HH).
    mbF_open HRNG. unfold rel_flag_state.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    pose proof (bf_app_rng FS 11571200 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    assert (EFRj : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFJj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (RFLG : rng RNG (fs_flag FS 0 j) 1)
      by (eapply rng_sub; [exact RHDR | rewrite EFJj; clr; lia | rewrite EFJj; clr; lia]).
    assert (GSH : shadow_addr (fs_frame FS 0 j) + 8 <= shadow_addr (bv_unsigned sp - 4272)).
    { replace (shadow_addr (fs_frame FS 0 j) + 8) with (shadow_addr (fs_frame FS 0 j + 64))
        by (unfold shadow_addr; clr; Z.div_mod_to_equations; lia).
      apply acl_sh_ge. lia. }
    clear HSM HA ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF
      HPl P4 P5 HDd Rp Rb Ro.
    step.
      step.
      pose proof (proj2 (proj1 FL)) as FB.
      lazymatch type of FB with
      | bytes_at _ _ _ ?L =>
          assert (EFB : L = [Z_to_bv 8 0]) by (vm_compute; reflexivity); rewrite EFB in FB
      end.
      destruct FB as (B1 & B2 & B3).
      pose proof (B3 0%nat ltac:(cbn [length]; lia)) as B4. cbn [nth_error Z.of_nat] in B4.
      rewrite Z.add_0_r in B4.
      first [fold ASAN_K | change 2147450880 with ASAN_K]. rewrite <- Hoff.
      (* OPEN (a Theorem Labs lane, ctl_post_acall_kept): HH, the class-0 hint word, is carried across the flag store. *)
      apply (K _ h _ MU MU2 WM RM MI SV HH ltac:(intros _; exact B4)).
      intros xx Hx1 Hx2. exfalso. lia.
  Qed.

  (* 0x86e14 -> 0x86e74, cut at the flag store (KF): the magic word at the frame, the frame's shadow (0 on the real stack, 0xf5 on the side
     stack) and, on the side stack, the flag byte back to 0. Every store is inside Wf, so the tail C of the
     footprint is untouched and the caller carries its own facts about it over the local munch. *)
  Lemma rel_preF : forall (C : list ivl) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ C) fr w56 mc ->
    (forall (m' : word -> option byte) (h' x10' : word),
       munch (Wf sp FS fr j n ++ C) m m' -> munch (Wf sp FS fr j n) mc m' ->
       wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' ->
       rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
       bytes_at rsegs m' FS (le8 h') ->
       (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
       (forall x, shadow_addr fr <= x < shadow_addr fr + 8 ->
          shadow_addr (bv_unsigned sp - 4272) <= x < shadow_addr (bv_unsigned sp) ->
          mrd rsegs m' (wa x) = Some (Z_to_bv 8 0)) ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10' x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
                 (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs))) ->
    (0 <= j < fs_M 0 -> fr = fs_frame FS 0 j -> f = fr -> spc = A -> w56 = Z_to_bv 64 (fs_flag FS 0 j) -> n = 1 ->
       forall (m1 : word -> option byte) (h : word) (vfl : byte), rel_flag_facts C j mc m1 h vfl ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (rel_flag_state j ret x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1)) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Proof.
    intros C fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK HB K KF.
    mbF_open HRNG.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (bf_fk_facts fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    rewrite Hoff in SH1, SH2. unfold ASAN_K in SH1, SH2.
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    pose proof (bf_app_rng FS 11571200 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    destruct HB as (MU & WM & RM & MI & SV & (h & HH) & F56).
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    assert (SHin : forall i, 0 <= i < 8 -> in_shadow (fr / 8 + 2147450880 + i)).
    { intros i Hi. replace (fr / 8 + 2147450880 + i) with (shadow_addr (fr + 8 * i))
        by (rewrite sh_add8 by exact FR8; unfold shadow_addr, ASAN_K; lia).
      apply rt_app_shadow. apply FAP. lia. }
    rewrite Hoff. unfold ASAN_K.
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - (* the real-stack frame [A - 64, A) *)
      subst f fr spc j n.
      assert (RFRM : rng RNG (A - 64) 64) by (eapply rng_sub; [exact RWIN | clr; lia | clr; lia]).
      assert (BLK : shblk RNG ((A - 64) / 8 + ASAN_K))
        by (apply (mbF_blk RNG (bv_unsigned sp - 4272) 4272 (A - 64) SWIN FR8); clr; lia).
      unfold ASAN_K in BLK.
      unfold Wf, shadow_addr, ASAN_K in MU. cbn [app] in MU.
      pose proof (munch_refl (Wf sp FS (A - 64) 0 0) mc) as MU2.
      unfold Wf, shadow_addr, ASAN_K in MU2.
      destruct (sh_cells mc ((A - 64) / 8 + 2147450880) SRc SHin) as (w & CS).
      assert (HS : store_ok rsegs mc (wa (A - 64)) 8 = true)
        by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia | exact WM | lia | lia]).
      clear HSM HA ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF
        SRc SHin FW FAP SW Fsp FRA HPl P4 P5 HDd Rp Rb Ro.
      do 3 step. store_done. step. nt. do 8 step.
      pose proof (proj2 (proj1 CS)) as CB0.
      lazymatch type of CB0 with
      | bytes_at _ _ _ ?L =>
          assert (ECB : L = repeat (Z_to_bv 8 0) 8) by (vm_compute; reflexivity); rewrite ECB in CB0
      end.
      first [fold ASAN_K | change 2147450880 with ASAN_K]. rewrite <- Hoff.
      apply (K _ h _ MU MU2 WM RM MI SV HH ltac:(intros Hn1; exfalso; lia)).
      intros xx Hx1 Hx2. unfold shadow_addr, ASAN_K in Hx1.
      destruct CB0 as (B1 & B2 & B3).
      pose proof (B3 (Z.to_nat (xx - ((A - 64) / 8 + 2147450880)))
                    ltac:(rewrite repeat_length; lia)) as B4.
      replace ((A - 64) / 8 + 2147450880 + Z.of_nat (Z.to_nat (xx - ((A - 64) / 8 + 2147450880))))
        with xx in B4 by lia.
      rewrite B4. apply nth_rep0. lia.
    - (* a class-0 side-stack frame *)
      subst fr f spc n w56.
      change (fs_M 0) with 16384 in Hj.
      assert (EFRj0 : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (RFRM : rng RNG (fs_frame FS 0 j) 64)
        by (eapply rng_sub; [exact RFR | clr; lia | clr; lia]).
      assert (BLK : shblk RNG (fs_frame FS 0 j / 8 + ASAN_K))
        by (apply (mbF_blk RNG (FS + 36864) 1048576 (fs_frame FS 0 j) SFR FR8); clr; lia).
      unfold ASAN_K in BLK.
      assert (RFLG : rng RNG (fs_flag FS 0 j) 1)
        by (eapply rng_sub; [exact RHDR
                            | unfold fs_flag; cbn [Z.of_nat]; clr; lia
                            | unfold fs_flag; cbn [Z.of_nat]; clr; lia]).
      assert (EFRj : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFJj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
      assert (GSH : shadow_addr (fs_frame FS 0 j) + 8 <= shadow_addr (bv_unsigned sp - 4272)).
      { replace (shadow_addr (fs_frame FS 0 j) + 8) with (shadow_addr (fs_frame FS 0 j + 64))
          by (unfold shadow_addr; clr; Z.div_mod_to_equations; lia).
        apply acl_sh_ge. lia. }
      unfold Wf, shadow_addr, ASAN_K in MU. cbn [app] in MU.
      pose proof (munch_refl (Wf sp FS (fs_frame FS 0 j) j 1) mc) as MU2.
      unfold Wf, shadow_addr, ASAN_K in MU2.
      destruct (sh_cells mc (fs_frame FS 0 j / 8 + 2147450880) SRc SHin) as (w & CS).
      (* OPEN (a Theorem Labs lane, ctl_post_acall_kept): the flag cell's writability and byte come from the ENTRY fs_place
         (P5) across the malloc. *)
      pose proof (stk_mono m mc _ _ P5 WM RM) as STF.
      destruct (proj2 (proj2 STF) (fs_flag FS 0 j) ltac:(lia)) as (FLw & vfl & FLr). clear STF.
      pose proof (rw1 mc (fs_flag FS 0 j) vfl ltac:(lia) ltac:(lia) FLw FLr) as FL.
      apply bytes_ro8 in F56.
      assert (HS : store_ok rsegs mc (wa (fs_frame FS 0 j)) 8 = true)
        by (eapply wv_store_ok; [intros i Hi; apply FW; lia | exact WM | lia | lia]).
      clear HSM HA ST0 MI0 AC0 SR0 AW0 FP0 TLS0 HP HN HO AP ANB AO AJ1 AJ2 NDJ HMS HMC HBD HDH HNF
        SRc SHin FW FAP SW Fsp FRA HPl P4 P5 HDd Rp Rb Ro FLw FLr.
      do 3 step. store_done. step. nf. do 10 step.
      (* the cut AT the class-0 flag store *)
      eapply KF; [exact Hj | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
      exact (conj Hj (conj FL (conj MU (conj MU2 (conj WM (conj RM (conj MI (conj SV HH)))))))).
  Qed.

  (* 0x86e14 -> 0x86e74: the magic word at the frame, the frame's shadow (0 on the real stack, 0xf5 on the side
     stack) and, on the side stack, the flag byte back to 0. Every store is inside Wf, so the tail C of the
     footprint is untouched and the caller carries its own facts about it over the local munch. *)
  Lemma rel_runF : forall (C : list ivl) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ C) fr w56 mc ->
    (forall (m' : word -> option byte) (h' x10' : word),
       munch (Wf sp FS fr j n ++ C) m m' -> munch (Wf sp FS fr j n) mc m' ->
       wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' ->
       rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
       bytes_at rsegs m' FS (le8 h') ->
       (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
       (forall x, shadow_addr fr <= x < shadow_addr fr + 8 ->
          shadow_addr (bv_unsigned sp - 4272) <= x < shadow_addr (bv_unsigned sp) ->
          mrd rsegs m' (wa x) = Some (Z_to_bv 8 0)) ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10' x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
                 (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Proof.
    intros C fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK HB K.
    apply (rel_preF C fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK HB K).
    intros Hj Efr Ef Espc Ew En. subst fr. subst f spc w56 n.
    exact (rel_flag_restF C j mc ret x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 K).
  Qed.

  (* 0x86e14 -> Q0: the interface pin's rel_stmt. *)
  Lemma relF : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    FK FS A fr f spc j n w56 ->
    ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
       (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
    (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK Er HB HX.
    apply (rel_runF _ fr f spc j n w56 mc ret x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
             HK HB).
    intros m' h' x10' MU MU2 WM RM MI SV HH Hfj WSH.
    apply (rel_finF fr f spc j n w56 m' ret h' x1 x5 x6 x7 x10' x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
             HK Er MU WM RM MI SV HH Hfj (bf_rel_wsh fr f spc j n w56 m' HK MU WSH)).
    (* the output block, carried from mc past the release stores *)
    revert HX. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros HX; [exact HX|].
    assert (Eo : o <> 0)
      by (apply orb_false_iff in Epo; destruct Epo as (_ & E); apply Z.eqb_neq in E; exact E).
    assert (Ep : p <> 0)
      by (apply orb_false_iff in Epo; destruct Epo as (E & _); apply Z.eqb_neq in E; exact E).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (bf_fk_facts fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    rewrite Hoff in SH1, SH2. unfold ASAN_K in SH1, SH2.
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    destruct (HP Ep) as (_ & Hlen & _ & _ & _).
    destruct (HO Eo) as (HOC & HOS & HOJ). destruct (AO Eo) as (AOa & AOe & AOr).
    pose proof (bf_app_rng o 32 ltac:(lia) ltac:(intros i Hi; exact (acl_app_in m o 32 i AOa Hi))) as OAR.
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    assert (ODJ0 : o + 32 <= fs_hint FS 0 \/ fs_hint FS 0 + 8 <= o)
      by (apply (bf_o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; left; reflexivity).
    assert (ODJ1 : o + 32 <= fs_flag FS 0 0 \/ fs_flag FS 0 0 + fs_M 0 <= o)
      by (apply (bf_o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; right; left; reflexivity).
    assert (ODJ2 : o + 32 <= fs_frame FS 0 0 \/ fs_frame FS 0 (fs_M 0) <= o)
      by (apply (bf_o_dj_fs Eo); unfold fp_w, fp_w1; cbn [flat_map app]; right; right; left; reflexivity).
    rewrite EH0 in ODJ0. rewrite EF0, EM0 in ODJ1. rewrite EFR0, EFMf in ODJ2.
    apply (fl_bytes _ mc m' _ _ HX MU2).
    intros xx Hxx. rewrite (rs_synth_len row b nb Hlen) in Hxx.
    unfold Wf. cbn [outside fst snd].
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - subst j n.
      split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|].
      split; [clr; unfold shadow_addr, ASAN_K; lia | exact I].
    - subst n. change (fs_M 0) with 16384 in Hj.
      assert (EFRj : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFJj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
      split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|]. split; [clr; lia|].
      split; [clr; unfold shadow_addr, ASAN_K; lia | exact I].
  Qed.

  (* The shape of the seven case lemmas: the case PC the jump table selects, with the output block memset to 0. *)
  Definition case_stmtF (K pc : Z) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
      b = K -> p <> 0 -> o <> 0 ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
      rw_cells rsegs mc o [CB 32 (zeros 32)] ->
      evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
        (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
                (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  (* 0x866d4 -> the case lemmas: the early returns (p = 0, o = 0, 6 < b), the checked memset of the output block
     and the jump table at 0x219f4. *)
  Lemma dispF :
    case_stmtF 0 0x86714 -> case_stmtF 1 0x86a44 -> case_stmtF 2 0x869fc -> case_stmtF 3 0x86a08 ->
    case_stmtF 4 0x8691c -> case_stmtF 5 0x86a5c -> case_stmtF 6 0x86b24 ->
    KBF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS off A RNG
      (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  Proof.
    intros Hc0 Hc1 Hc2 Hc3 Hc4 Hc5 Hc6.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HK HB.
    mbF_open HRNG.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as HAb.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (bf_fk_facts fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & Cw & T & DB & k & _ & _ & HPl & _ & _ & _ & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5. unfold ASAN_GT in P3.
    pose proof HB as HB1. destruct HB1 as (MU & WM & RM & MI & SV & (h & HH) & F56).
    assert (Fspc : bv_unsigned sp - 240 <= spc /\ spc <= bv_unsigned sp - 160)
      by (destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)];
          rewrite Espc; clr; lia).
    assert (RFRM : rng RNG fr 64).
    { pose proof HK as HK'.
      destruct HK' as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      - eapply rng_sub; [exact RWIN | clr; lia | clr; lia].
      - unfold fs_frame, fs_B in Efr. cbn [Z.of_nat] in Efr. change (fs_M 0%nat) with 16384 in Hj.
        eapply rng_sub; [exact RFR | clr; lia | clr; lia]. }
    assert (BLK : shblk RNG (fr / 8 + ASAN_K)).
    { pose proof HK as HK'.
      destruct HK' as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      - apply (mbF_blk RNG (bv_unsigned sp - 4272) 4272 fr SWIN FR8); clr; lia.
      - unfold fs_frame, fs_B in Efr. cbn [Z.of_nat] in Efr. change (fs_M 0%nat) with 16384 in Hj.
        apply (mbF_blk RNG (FS + 36864) 1048576 fr SFR FR8); clr; lia. }
    step.
    try (match goal with
         | |- context [Z_to_bv 64 18446744073709551615] =>
             replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1))
               by (apply bv_eq; vm_compute; reflexivity)
         end).
    step.
    (* p = 0: the early return *)
    destruct (Z.eq_dec p 0) as [Ep0|Ep0].
    { assert (Ecnd : (p =? 0) || (o =? 0) = true)
        by (apply orb_true_iff; left; apply Z.eqb_eq; exact Ep0).
      nt. eapply relF; [exact HK | rewrite Ecnd; reflexivity | rewrite Ecnd; exact HB | rewrite Ecnd; exact I]. }
    nf. step.
    (* o = 0: the early return *)
    destruct (Z.eq_dec o 0) as [Eo0|Eo0].
    { assert (Ecnd : (p =? 0) || (o =? 0) = true)
        by (apply orb_true_iff; right; apply Z.eqb_eq; exact Eo0).
      nt. eapply relF; [exact HK | rewrite Ecnd; reflexivity | rewrite Ecnd; exact HB | rewrite Ecnd; exact I]. }
    nf.
    assert (Ecnd : (p =? 0) || (o =? 0) = false)
      by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
    destruct (HO Eo0) as (HOC & HOS & HOJ). destruct (AO Eo0) as (AOa & AOe & AOr).
    (* the output block and the runtime state at mc *)
    pose proof (bf_o_out_wf Eo0 fr f spc j n w56 HK) as ODJ.
    pose proof (bf_o_sh_out_wf Eo0 fr f spc j n w56 HK) as OUTS.
    assert (OC : rw_cells rsegs mc o [CB 32 ob])
      by (eapply rw_cells_transport; [exact HOC | exact MU | exact WM | exact ODJ]).
    assert (OADD : addressable mc o 32)
      by (eapply addr_munch; [exact AOa | exact MU | exact OUTS]).
    pose proof (stk_mono m mc _ _ ST0 WM RM) as STc0.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) STc0 ltac:(lia)) as (STc & _).
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    pose proof (bf_sub_post fr f spc j n w56 HK) as SP. rewrite Ecnd in SP.
    assert (ACc : asan_cells mc)
      by (exact (bf_br_ac _ mc MU (fun x Hx => out_app_l _ _ _ (SP x Hx)))).
    assert (Uo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; clr; lia).
    do 4 step.
    eapply evtF_cut.
    { eapply HMS with (junk := ob) (lo := bv_unsigned sp - 4272);
        change (bv_unsigned (Z_to_bv 64 32)) with 32; rewrite ?Uo, ?Uspc;
        unfold ASAN_MEMSET_K.
      - exact OC.
      - lia.
      - exact OADD.
      - right. exact AOe.
      - right. exact (acl_app_in m o 32 7 AOa ltac:(lia)).
      - exact AOr.
      - clr; lia.
      - exact STc.
      - clr; lia.
      - exact HHM.
      - clr; lia.
      - exact ACc.
      - exact SRc.
      - exact MI.
      - (* the byte-wise footprint *) exact RBY.
      - (* the image *) eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - (* the window of the call *) eapply rng_sub; [exact RWIN | clr; lia | clr; lia].
      - (* the 32 bytes at o *) destruct (ROUT Ep0 Eo0) as (ROr & _ & _ & _). exact ROr.
      - (* their shadow word cover *)
        destruct (ROUT Ep0 Eo0) as (_ & _ & _ & ROk). apply (mbF_shws RNG o 32 o 32 ROk); clr; lia.
      - (* the shadow word cover of the call's window *)
        apply (mbF_shws RNG (bv_unsigned sp - 4272) 4272 (spc - 2208) 2208 KWIN); clr; lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2
                    & MI2 & ST2 & RW2 & AC2 & SR2).
    subst ms'.
    change (bv_unsigned (Z_to_bv 64 32)) with 32 in MU2, RW2.
    rewrite Uo, Uspc in MU2. rewrite Uspc in ST2. rewrite Uo in RW2. unfold ASAN_MEMSET_K in MU2.
    change (Z.to_nat 32) with 32%nat in RW2.
    change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) 32) with (zeros 32) in RW2.
    replace (ret_pc (Z_to_bv 64 0x866f0)) with (Z_to_bv 64 0x866f0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* the body invariant at m2 *)
    assert (RM2 : rd_mono mc m2).
    { apply (rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ (mb_rw1 _ _ _ _ _ RW2)). unfold zeros. rewrite repeat_length. lia.
      - apply (rd_of_stk _ _ _ ST2). clr; lia. }
    assert (MU3 : munch (Wf sp FS fr j n ++ [(o, o + 32)]) m m2).
    { apply (munch_trans _ m mc m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. exact (out_app_l _ _ _ Hx).
      - eapply munch_weaken; [|exact MU2]. intros x Hx.
        pose proof (out_app_l _ _ _ Hx) as HxW. pose proof (out_app_r _ _ _ Hx) as HxO.
        unfold Wf in HxW. cbn [outside fst snd] in HxW. destruct HxW as (Hw & _).
        cbn [outside fst snd] in HxO. destruct HxO as (Ho & _).
        cbn [outside fst snd]. split; [exact Ho|]. split; [clr; lia | exact I]. }
    pose proof ODJ as ODJ'. unfold Wf in ODJ'. cbn [disjoint_from fst snd] in ODJ'.
    assert (Ffr : spc = fr \/ fr + 64 <= bv_unsigned sp - 4272)
      by (destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)];
          [left; lia | right; rewrite Efr; change (fs_M 0) with 16384 in Hj;
           unfold fs_frame, fs_B; cbn [Z.of_nat]; clr; lia]).
    assert (BI2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 m2).
    { split; [exact MU3|]. split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
      split; [exact (rd_mono_trans _ _ _ RM RM2)|]. split; [exact MI2|].
      split.
      { eapply rw_cells_transport; [exact SV | exact MU2 | exact WM2 |].
        cbn [disjoint_from fst snd cells_size csize SAVES Nat.add]. repeat split; try exact I; clr; lia. }
      split.
      { exists h. eapply bytes_at_transport; [exact HH | exact MU2 |].
        rewrite length_le8. cbn [disjoint_from fst snd]. repeat split; try exact I; clr; lia. }
      eapply bytes_at_transport; [exact F56 | exact MU2 |].
      rewrite length_le8. cbn [disjoint_from fst snd]. repeat split; try exact I; clr; lia. }
    do 2 step.
    (* 6 < b: the unknown kind returns -1 with the block left at zero *)
    destruct (Z.lt_ge_cases 6 b) as [Bgt|Ble].
    { nt.
      assert (Erc : rc row b = -1)
        by (unfold rc; replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      assert (Esy : synth row b nb = zeros 32)
        by (unfold synth; replace (6 <? b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      eapply relF; [exact HK | rewrite Ecnd, Erc; reflexivity | rewrite Ecnd; exact BI2 |].
      rewrite Ecnd, Esy. exact (mb_rw1 _ _ _ _ _ RW2). }
    nf.
    assert (Bk : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6) by (clr; lia).
    destruct Bk as [Bk|[Bk|[Bk|[Bk|[Bk|[Bk|Bk]]]]]];
      rewrite (mb_word (Z_to_bv 64 b) _ ltac:(rewrite unsigned_lit by lia; exact Bk));
      do 7 step;
      [ eapply Hc0 | eapply Hc1 | eapply Hc2 | eapply Hc3 | eapply Hc4 | eapply Hc5 | eapply Hc6 ];
      first [exact Bk | exact Ep0 | exact Eo0 | exact HK | exact BI2 | exact RW2].
  Qed.
End BodyF.
