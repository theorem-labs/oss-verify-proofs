(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module paths and module names changed; 431 of its 473 lines of code are new or changed and 938 lines of the source are left out. *)
(* The phase JOIN of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput: check_kept's row loop and the phase theorem.
   BoxBLxJoinRowDefs.v states the loop's cuts (LI_R at LP_M 0x80c2c and LP_N 0x80c44) and the call lemmas;
   BoxBLxJoin.v walks LP_K -> LP_L / LP_E (lj_kwalk) and LP_E -> LP_J / LP_X (lj_ewalk); BoxBLxJoinRowBC.v walks
   LP_M -> LP_N (lj_rowB, the name test) and LP_N -> LP_L (row j + 1) or LP_E (lj_rowC, the loop's branch).
   Here:
   - lj_rowA (LP_L 0x80b44 -> LP_M 0x80c2c): the UBSan guards of row j (the index 6 is not reached, s7 is a numeral;
     prev + 56 j and r + 56 j do not wrap: the slots sp1 + 0x78 = ~prev and sp1 + 0x70 = ~r), the ASan checks and the
     comparisons of row j's base / nch / pinned words (equal by lkept: both loads read the same chunk value),
     bcmp (prev.mac, ZERO, 6) at 0x80c10 and, when prev's MAC is not ZERO, bcmp (prev.mac, r.mac, 6) at 0x80c24,
     which is 0 by lkept (a MAC that is not ZERO stays), so the abort at 0x80fa4 is not reached;
   - lj_liter: one row, LI_L i j from LI_E i and LI_L i (j + 1);
   - lx_join: lj_kwalk of lj_ewalk and of the downward induction over lj_liter (the loop runs at most five rows).
   The engine's state must be closed, so each row is walked with j a numeral: the five rows are one proof script over
   the five goals of the case split on j (BoxBLxCase1Scan.v c1s_A is the model). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC45 YC85 BoxBLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Bytes Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxJoin BoxBLxJoinRowDefs BoxBLxJoinRowBC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* BoxBLxJoin.v's walk tactics (an Ltac definition does not leave its Section); the same text. *)
(* After a run with closed windows: the phase's facts extend to the run's memory (HKA : lx_keep .. m0 m). *)
Ltac lj_keep_run HKA :=
  lazymatch type of HKA with lx_keep ?cx ?fp ?W ?rs ?m0 ?m =>
  lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ m) (mrestrict _ ?m') |- _ =>
    let H := fresh "HKA" in
    assert (H : lx_keep cx fp W rs m0 m')
      by (eapply lx_keep_trans; [exact HKA | apply lj_keep_eq; exact (lj_aview_ro _ _ _ _ _ HFr0 ltac:(vm_compute; reflexivity))]);
    clear HKA; rename H into HKA;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end
  end end.
(* A register of the symbolic state, as the symbolic value it holds. *)
Ltac lj_reg HS r R :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R end.
(* A fact of the phase, from the cut's fact and the keep relation in the context. *)
Ltac lj_keepf0 L :=
  eapply L; try eassumption; try lia; try (left; reflexivity);
  try (unfold LSH_iter, LSH_entry; change (fs_frame_bytes LX_CID / 8) with 64; cbn [length app repeat]; lia).
Ltac lj_kf :=
  first [ solve [lj_keepf0 lx_saved_keep] | solve [lj_keepf0 lx_shadow_keep] | solve [lj_keepf0 lx_flag_keep]
        | solve [lj_keepf0 lx_slot_keep] | solve [lj_keepf0 lx_input_keep] | solve [lj_keepf0 lx_reg_keep]
        | solve [lj_keepf0 lx_prev_keep] | solve [lj_keepf0 lx_cur_keep] | solve [lj_keepf0 lx_slots_loop_keep] ].
(* lx_body at the landing state HS (registers from the symbolic state, the rest kept). *)
Ltac lj_land_body HS :=
  eapply lx_land; [eassumption | exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf].
(* Close region i's window in the seat's state, and normalize the state. *)
Ltac lj_unwin_tac HS i :=
  let H := fresh "HSu" in
  pose proof (lj_unwin _ _ _ i _ HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)) as H;
  clear HS; rename H into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
(* An address the phase's facts speak about (Seat's lx_keep_at), from the bounds in the context. *)
Ltac lj_keep_at_tac :=
  unfold lx_keep_at;
  first [ left; lia | right; left; lia | right; right; left; change (fs_frame_bytes LX_CID) with 512; lia
        | right; right; right; left; change (fs_frame_bytes LX_CID / 8) with 64; lia
        | right; right; right; right; apply Exists_cons_hd; cbn [fst snd]; unfold LX_REG; lia ].
(* After a call that kept the phase's facts (HK : lx_keep ...): the regions idxs survive (their windows are closed). *)
Ltac lj_reseat HS HP W3 mem2 HK idxs :=
  let K := run_K_hi HS in
  let HS2 := fresh "HS2" in
  lazymatch type of HP with aregs_preserved _ ?regs2 =>
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W3) mem2) HP idxs HS2 end;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in assert (HQ : Q);
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (apply lj_rkept; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
       [ let a := fresh "a" in let Ha := fresh "Ha" in
         intros a Ha; rewrite ?YN3v.ew_havoc_old in Ha by lia;
         repeat match goal with Hu : bv_unsigned (ew ?Ex ?n) = _ |- _ =>
           lazymatch type of Ha with context [bv_unsigned (ew Ex n)] => rewrite Hu in Ha end end;
         apply HK; lj_keep_at_tac
       | lia ])
    | specialize (HS2 HQ); clear HQ ] end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
(* After a call (havoc above K): the facts on the old atoms hold in the new environment (grant's restate). *)
Ltac lj_restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = v |- _ => fail
      | _ => let F' := fresh F in assert (F' : ew En n = v) by (rewrite OLD by lia; exact F); clear F; rename F' into F
      end
  | F : bv_unsigned (ew Eo ?n) = ?v |- _ =>
      lazymatch goal with
      | _ : bv_unsigned (ew En n) = v |- _ => fail
      | _ => let F' := fresh F in assert (F' : bv_unsigned (ew En n) = v) by (rewrite OLD by lia; exact F); clear F; rename F' into F
      end
  end end.
(* Name the environment after a call (havoc E K ws) and carry the old atoms' facts and lx_E into it. *)
Ltac lj_newenv HS E1 HE1 OLD :=
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
    remember (havoc Eo K ws) as E1 eqn:HE1 in HS;
    assert (OLD : forall q, (q < K)%nat -> ew E1 q = ew Eo q)
      by (let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq);
    let HEIn := fresh "HEI" in
    assert (HEIn : img_env VAL A_LIM E1)
      by (rewrite HE1; apply img_env_havoc_hi; [assumption | cbv; lia]);
    let HEn := fresh "HE" in
    lazymatch goal with HEo : lx_E ?cx ?fp Eo |- _ =>
      assert (HEn : lx_E cx fp E1)
        by (apply (lx_E_agree cx fp Eo E1 HEo); let n := fresh "n" in let Hn := fresh "Hn" in
            intros n Hn; apply OLD; unfold LA_EX in Hn; lia);
      clear HEo end;
    lj_restate OLD;
    repeat match goal with H : img_env _ _ Eo |- _ => clear H end
  end.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

Lemma lj_rowA : forall POST i j, lx_from B MT POST (LI_R B MT LP_M i j) -> lx_from B MT POST (LI_L B MT i j).
Proof.
  intros POST i j HLM.
  pose proof (lh_laws B MT HY) as LAWS.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (pos & r & fab & ren & bs & bs' & HBD & Hi & Hk & Hacc & HBLK & HPV & HIV & HFB & HRG & HIV' & HFB'
    & HKP & Hren & Hj & HCUR & HSL & H58 & R20 & R21 & R23 & R24 & R26 & R27).
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HLR & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof HIV as ((HL288 & HB1 & HB2 & HB3 & HB4 & HB5 & HB6) & HB7).
  unfold Boxreg.boxreg_B1 in HB1.
  pose proof HIV' as ((HL288' & HB1' & _) & _).
  pose proof HSL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  pose proof HJ as (HAR & _).
  pose proof HB as (HPRE0 & _ & _ & HPN & _ & _ & _ & _ & HRO0 & _).
  pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
  assert (HrIn : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hria, Hrceil.
  pose proof asan_consts as (C1 & _).
  pose proof (lx_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HSR0 & HSR1).
  pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)). pose (RUNTO := paj_run_to B LAWS).
  (* the five rows: the engine's state must be closed, so j is a numeral in each *)
  assert (Hj5 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
  destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]].

  all: pose proof (lkept_words bs bs' ren _ HKP Hj) as (KW8 & KW12 & KW20).
  all: lazymatch type of Hj with 0 <= ?jj < _ =>
    set (ex := [w64 (2 ^ 64 - 1 - r); w64 (2 ^ 64 - 1 - (lF cx fp + 64));
                w64 (lu4 bs (56 * jj + 8)); w64 (lu4 bs (56 * jj + 12)); w64 (lu4 bs (56 * jj + 20))]) end.
  all: set (E := lx_env cx fp (ms_regs ms3) ex).
  all: assert (HE : lx_E cx fp E) by exact (lx_env_E cx fp ms3 ex HLR).
  all: assert (E48 : ew E 48 = w64 (2 ^ 64 - 1 - r)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
  all: assert (E49 : ew E 49 = w64 (2 ^ 64 - 1 - (lF cx fp + 64))) by exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia)).
  all: lazymatch type of Hj with 0 <= ?jj < _ =>
    assert (E50 : ew E 50 = w64 (lu4 bs (56 * jj + 8))) by exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia));
    assert (E51 : ew E 51 = w64 (lu4 bs (56 * jj + 12))) by exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia));
    assert (E52 : ew E 52 = w64 (lu4 bs (56 * jj + 20))) by exact (lx_env_ex cx fp (ms_regs ms3) ex 4 ltac:(lia)) end.
  all: assert (HEI : img_env VAL A_LIM E) by exact (lx_env_img cx fp (ms_regs ms3) ex).
  all: assert (E20 : ew E 20 = w64 r) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 20 20%bv eq_refl) R20).
  all: assert (E24 : ew E 24 = w64 (56 * (ren mod 2 ^ 32)))
         by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 24 24%bv eq_refl) R24).
  all: assert (E26 : ew E 26 = w64 (56 * Boxreg.bx_n bs))
         by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 26 26%bv eq_refl) R26).
  all: assert (E27 : ew E 27 = w64 fab) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 27 27%bv eq_refl) R27).
  all: assert (U20E : bv_unsigned (ew E 20) = r) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).

  all: lazymatch type of Hj with 0 <= ?jj < _ =>
    assert (HS : st_ok_pi SEGS VAL E (lx_ss LP_L (lx_sr (RA_ov jj)) LSH_iter
                   (lx_slot_chunks [(0x70, SOff 48 0); (0x78, SOff 49 0)]) (RA_fcs jj) 0 0 0 0 [RA_blk jj] RA_G)
                   (restrict (w_H W3) ms3))
      by (eapply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR);
          [ exact HE
          | exact HBD
          | apply lx_regs_ok;
            [ apply lx_regs_ok_atoms
            | unfold RA_ov; apply Forall_cons;
              [ cbn [fst snd sv_denot]; rewrite R23; reflexivity | exact (lx_ovp_ok cx fp ms3 ex HLR R21) ] ]
          | apply Forall_cons;
            [ cbn [fst snd]; apply (lx_slot_atom cx W3 ms3 E 0x70 48 (2 ^ 64 - 1 - r) 0);
              [ rewrite Z.add_0_r; exact L70 | exact E48 | lia | lia ]
            | apply Forall_cons;
              [ cbn [fst snd]; apply (lx_slot_atom cx W3 ms3 E 0x78 49 (2 ^ 64 - 1 - (lF cx fp + 64)) 0);
                [ rewrite Z.add_0_r; exact L78 | exact E49 | lia | lia ]
              | apply Forall_nil ] ]
          | unfold RA_fcs; repeat apply Forall_cons; try apply Forall_nil;
            lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk (64 + ?m + ?c) (CVal 4 (SOff ?a 0))) =>
              apply (chunk_ok_val SEGS E _ (lF cx fp) (64 + m + c) 4 (SOff a 0) (lu4 bs (m + c)));
              [ rewrite lx_sv_SOff0; assumption
              | pose proof (lu4_range bs (m + c)); cbn; lia
              | cbn; lia
              | replace (lF cx fp + (64 + m + c)) with (lF cx fp + 64 + (m + c)) by lia;
                apply lu4_val_mem; [lia | rewrite HL288; cbn; lia |];
                intros t Ht; rewrite <- Z.add_assoc; apply HPV; unfold LX_REG; lia ] end
          | lia | lia | lia | lia
          | vm_compute; reflexivity
          | apply Forall_cons;
            [ unfold region_ok, RA_blk;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              rewrite U20E;
              split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
              repeat apply Forall_cons; try apply Forall_nil;
              lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 4 (SOff ?a 0))) =>
                apply (chunk_ok_val SEGS E _ r o 4 (SOff a 0) (lu4 bs o));
                [ rewrite lx_sv_SOff0; assumption
                | pose proof (lu4_range bs o); cbn; lia
                | cbn; lia
                | first [rewrite <- KW8 | rewrite <- KW12 | rewrite <- KW20];
                  apply lu4_val_mem; [lia | rewrite HL288'; cbn; lia |];
                  intros t Ht; rewrite <- Z.add_assoc; exact (HRG (o + t) ltac:(unfold LX_REG; lia)) ] end
            | apply Forall_nil ]
          | cbn [YP09.pairwise_disjoint YP09.all_disjoint]; repeat constructor
          | apply (lx_block_disj B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E 20 r r LX_REG);
            [exact HE | exact HrIn | exact U20E | lia | lia | change (req_size LX_REG) with 288; lia]
          | unfold RA_G; split; [|split; exact I]; cbn [f_atoms]; apply lj_atoms_ok_app;
            [ exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)
            | cbn [atoms_ok]; split; [|exact I]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20E;
              split; [lia|]; split; [exact Hr16 | lia] ] ]) end.
  all: lj_unwin_tac HS 1%nat.

  all: pose proof HE as (H2E & H8E & H3E & H4E & H22E & H32E & HSAVE & H46E & H47E).
  all: unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in H2E, H8E, H22E, H32E, H46E, H47E.
  all: assert (U32E : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact H32E | unfold SHADOW_OFF; lia]).
  all: assert (U46E : U E (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact H46E | lia]).
  all: assert (U20 : U E (SOff 20 0) = r) by (apply U_atom; [exact E20 | lia]).
  all: assert (U2E : bv_unsigned (ew E 2) = lsp1 cx) by (rewrite H2E; unfold w64; apply unsigned_lit_small; lia).
  all: assert (U8E : bv_unsigned (ew E 8) = lsp0 cx) by (rewrite H8E; unfold w64; apply unsigned_lit_small; lia).
  all: assert (U46 : bv_unsigned (ew E 46) = lF cx fp) by (rewrite H46E; unfold w64; apply unsigned_lit_small; lia).
  all: assert (U22E : bv_unsigned (ew E 22) = lSH cx fp) by (rewrite H22E; unfold w64; apply unsigned_lit_small; lia).
  all: assert (U49 : U E (SOff 49 0) = 2 ^ 64 - 1 - (lF cx fp + 64)) by (apply U_atom; [exact E49 | lia]).
  all: assert (U48 : U E (SOff 48 0) = 2 ^ 64 - 1 - r) by (apply U_atom; [exact E48 | lia]).
  all: assert (SHOK : sh_ok SEGS (SOff LA_SB 0) RA_SH E (mrestrict (w_H W3) (ms_mem ms3)))
         by (unfold sh_ok, RA_SH; apply Forall_cons;
             [ apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20 HAR HrIn U32E U20);
               [lia | lia | change (req_size LX_REG) with 288; lia]
             | apply Forall_cons;
               [ exact (lx_shent_frame B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E 64 352 U32E U46E HSH ltac:(lia))
               | apply Forall_nil ] ]).
  all: clearbody E.
  (* 0x80b44 .. 0x80b50: the row index guard (s7 <> 0x150, a numeral) and ~prev <u s7 *)
  all: paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  all: pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
  all: assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply lj_keep_eq; exact HMEQ).
  all: clear HF HFr HMEQ.
  all: psrr_branch_tok RUN BR HS SHOK LX_SBX.
  all: rewrite branch_ltu_U, U49, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | _ = true => exfalso; apply Z.ltb_lt in Hc; lia
       | _ = false => clear Hc
       end.
  (* 0x80b54 .. 0x80b58: ~r <u s7 *)
  all: paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  all: lj_keep_run HKA.
  all: psrr_branch_tok RUN BR HS SHOK LX_SBX.
  all: rewrite branch_ltu_U, U48, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | _ = true => exfalso; apply Z.ltb_lt in Hc; lia
       | _ = false => clear Hc
       end.
  (* 0x80b5c .. 0x80c10: the shadow checks and the three words (the engine decides them), to bcmp (prev.mac, ZERO, 6) *)
  all: paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  all: lj_keep_run HKA.
  all: pmkst HS.

  all: prreg HS (10%bv : bv 5) CR10; prreg HS (11%bv : bv 5) CR11; prreg HS (1%bv : bv 5) CR1;
       prreg HS (12%bv : bv 5) CR12; prreg HS (2%bv : bv 5) CR2;
       prreg HS (3%bv : bv 5) CR3; prreg HS (4%bv : bv 5) CR4.
  all: rewrite H2E in CR2; rewrite H3E, Hgp0 in CR3; rewrite H4E, Htp0 in CR4.
  all: assert (HspT : spZ (ms_regs ms1) = lsp1 cx)
         by (unfold spZ; rewrite CR2; unfold w64; apply unsigned_lit_small; lia).
  all: assert (HPV1 : lprev cx fp W3 ms1 bs) by lj_kf.
  all: assert (HSH1 : lshadow cx fp W3 ms1 LSH_iter) by lj_kf.
  all: pose proof (lj_bcmp_zero B MT HY cx fp W3 ms1 ly3 S3 _ k (ms_regs ms1) HB HJ HspT)
         as (_ & _ & _ & _ & _ & _ & _ & HZ0).
  all: lazymatch type of Hj with 0 <= ?jj < _ =>
       eapply SRr_bind;
       [ apply (lr_bcmp B MT HY cx fp W3 ly3 S3 k (ms_regs ms1) (ms_mem ms1) _ (lF cx fp + 64 + 56 * jj) (VAL (A_OBJ 4)) HB HJ);
         [ rewrite CR10, ?U46, ?H46E; unfold w64; f_equal; lia
         | rewrite CR11; unfold w64; rewrite <- (HEI (A_OBJ 4) ltac:(cbv; lia)); symmetry; apply Z_to_bv_bv_unsigned
         | rewrite CR12; reflexivity
         | exact HspT
         | exact CR3
         | exact CR4
         | rewrite CR1; apply ret_ok_codeptr_v; [lia | reflexivity]
         | exact (lj_bcmp_prev B MT HY cx fp W3 ms1 ly3 S3 _ k bs jj (ms_regs ms1) HB HJ HFR HPV1 HSH1 ltac:(lia) HspT)
         | destruct (lj_bcmp_zero B MT HY cx fp W3 ms1 ly3 S3 _ k (ms_regs ms1) HB HJ HspT)
             as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & _);
           exact (conj Z1 (conj Z2 (conj Z3 (conj Z4 (conj Z5 (conj Z6 Z7)))))) ]
       | idtac ] end.
  all: cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hcmp & Hfr).
  all: assert (HK : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms1) mem2)
         by exact (lr_keep_stk B MT HY cx fp W3 ms1 ly3 S3 _ k r (ms_mem ms1) mem2 HB HJ HFR HBLK Hfr).
  all: assert (HKA2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2)
         by (eapply lx_keep_trans; [exact HKA | exact HK]).
  all: clear HKA; rename HKA2 into HKA.
  all: rewrite CR1.
  all: lj_reseat HS HP W3 mem2 HK [0; 1; 2; 3; 4]%nat.
  all: lj_newenv HS E1 HE1 OLD1.
  all: assert (A10 : ew E1 516 = getr regs2 10)
         by (rewrite HE1; change 516%nat with (512 + 4)%nat;
             exact (YN3v.ew_havoc_new E 512 (map (getr regs2) CLOB) 4 (w64 0) ltac:(cbn; lia))).
  all: assert (U32E1 : U E1 (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact H32E | unfold SHADOW_OFF; lia]).
  all: assert (U46E1 : U E1 (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact H46E | lia]).
  all: assert (U20b : U E1 (SOff 20 0) = r) by (apply U_atom; [exact E20 | lia]).
  all: clear SHOK.
  all: pose proof HJ2 as (HAR2 & _).
  all: assert (SHOK : sh_ok SEGS (SOff LA_SB 0) RA_SH E1 (mrestrict (w_H W3) mem2))
         by (unfold sh_ok, RA_SH; apply Forall_cons;
             [ apply (lx_shent_block B LAWS ly3 S3 W3 mem2 md2 E1 r r LX_REG 0 288 20 HAR2 HrIn U32E1 U20b);
               [lia | lia | change (req_size LX_REG) with 288; lia]
             | apply Forall_cons;
               [ exact (lx_shent_frame B MT LAWS cx fp W3 (YK11.mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS))
                          ly3 S3 md2 k HB HJ2 HFR E1 64 352 U32E1 U46E1
                          (lx_shadow_keep cx fp W3 [(r, LX_REG)] ms3
                             (YK11.mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) LSH_iter HKA
                             ltac:(unfold LSH_iter; change (fs_frame_bytes LX_CID / 8) with 64;
                                   cbn [length app repeat]; lia) HSH)
                          ltac:(lia))
               | apply Forall_nil ] ]).
  all: clear HJ; rename HJ2 into HJ.
  all: paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  all: lj_keep_run HKA.
  all: assert (U516 : U E1 (SOff 516 0) = bv_unsigned (getr regs2 10))
         by (unfold U; rewrite lx_sv_SOff0, A10; reflexivity).
  all: psrr_branch_tok RUN BR HS SHOK LX_SBX.
  all: rewrite branch_eq_U, U516, U_lit in Hc by lia.

  all: lazymatch type of Hc with
       | _ = true => 
         paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_M; [apply lj_awr_ro; vm_compute; reflexivity |];
         lj_keep_run HKA;
         lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
           apply (HLM cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end;
         exists pos, r, fab, ren, bs, bs';
         split; [lj_land_body HS|];
         split; [exact Hi|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HBLK|];
         split; [lj_kf|]; split; [exact HIV|]; split; [exact HFB|];
         split; [lj_kf|]; split; [exact HIV'|]; split; [exact HFB'|]; split; [exact HKP|]; split; [exact Hren|];
         split; [exact Hj|];
         split; [lj_kf|]; split; [lj_kf|]; split; [lj_kf|];
         lj_reg HS (19%bv : bv 5) G19; lj_reg HS (20%bv : bv 5) G20; lj_reg HS (21%bv : bv 5) G21;
         lj_reg HS (23%bv : bv 5) G23; lj_reg HS (24%bv : bv 5) G24; lj_reg HS (25%bv : bv 5) G25;
         lj_reg HS (26%bv : bv 5) G26; lj_reg HS (27%bv : bv 5) G27;
         split; [rewrite G19, (lj_den_atom _ 20 r _ E20) by lia; f_equal; lia|];
         split; [rewrite G20, lx_sv_SOff0; exact E20|];
         split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|];
         split; [rewrite G23; reflexivity|];
         split; [rewrite G24, lx_sv_SOff0; exact E24|];
         split; [rewrite G25, (lj_den_atom _ 46 (lF cx fp) _ H46E) by lia; f_equal; lia|];
         split; [rewrite G26, lx_sv_SOff0; exact E26|];
         rewrite G27, lx_sv_SOff0; exact E27

       | _ = false =>
         apply Z.eqb_neq in Hc;
         lazymatch type of Hj with 0 <= ?jj < _ =>
           assert (HMNZ : Boxreg.bx_mac bs jj <> Boxreg.zero6)
             by (apply (lr_mac_nz cx fp W3 ms1 bs jj (VAL (A_OBJ 4)) HPV1 ltac:(lia) HZ0);
                 intros Hall; apply Hc; rewrite (proj2 Hcmp Hall); reflexivity);
           clear Hc end
       end.

  (* 0x80c18 .. 0x80c24: bcmp (prev.mac, r.mac, 6) *)
  all: paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  all: lj_keep_run HKA.
  all: pmkst HS.
  all: prreg HS (10%bv : bv 5) D10; prreg HS (11%bv : bv 5) D11; prreg HS (1%bv : bv 5) D1;
       prreg HS (12%bv : bv 5) D12; prreg HS (2%bv : bv 5) D2; prreg HS (3%bv : bv 5) D3; prreg HS (4%bv : bv 5) D4.
  all: rewrite H2E in D2; rewrite H3E, Hgp0 in D3; rewrite H4E, Htp0 in D4.
  all: assert (HspT0 : spZ (ms_regs ms0) = lsp1 cx)
         by (unfold spZ; rewrite D2; unfold w64; apply unsigned_lit_small; lia).
  all: assert (HPV0 : lprev cx fp W3 ms0 bs) by lj_kf.
  all: assert (HSH0 : lshadow cx fp W3 ms0 LSH_iter) by lj_kf.
  all: assert (HRG0 : lreg W3 ms0 r bs') by lj_kf.
  all: assert (HEQ0 := lr_mac_keep cx fp W3 ms0 r bs bs' ren _ HPV0 HRG0 HKP Hj ltac:(lia) HMNZ).
  all: lazymatch type of Hj with 0 <= ?jj < _ =>
       eapply SRr_bind;
       [ apply (lr_bcmp B MT HY cx fp W3 ly3 S3 k (ms_regs ms0) (ms_mem ms0) _ (lF cx fp + 64 + 56 * jj) (r + 56 * jj) HB HJ);
         [ rewrite D10, ?U46, ?H46E; unfold w64; f_equal; lia
         | rewrite D11, ?U20E, ?E20; unfold w64; f_equal; lia
         | rewrite D12; reflexivity
         | exact HspT0
         | exact D3
         | exact D4
         | rewrite D1; apply ret_ok_codeptr_v; [lia | reflexivity]
         | exact (lj_bcmp_prev B MT HY cx fp W3 ms0 ly3 S3 _ k bs jj (ms_regs ms0) HB HJ HFR HPV0 HSH0 ltac:(lia) HspT0)
         | exact (lj_bcmp_reg B MT HY cx fp W3 ms0 ly3 S3 _ k r bs' jj (ms_regs ms0) HB HJ HrIn HRG0 ltac:(lia) HspT0) ]
       | idtac ] end.
  all: cbv beta; intros W2 c2 _ (-> & regs3 & mem3 & md4 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  all: assert (HV0 : getr regs3 10 = w64 0) by (apply Hcmp3; exact HEQ0).
  all: assert (HK3 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms0) mem3)
         by exact (lr_keep_stk B MT HY cx fp W3 ms0 ly3 S3 _ k r (ms_mem ms0) mem3 HB HJ HFR HBLK Hfr3).
  all: assert (HKA3 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem3)
         by (eapply lx_keep_trans; [exact HKA | exact HK3]).
  all: clear HKA; rename HKA3 into HKA.
  all: rewrite D1.
  all: lj_reseat HS HP3 W3 mem3 HK3 [0; 1; 2; 3; 4]%nat.
  all: lj_newenv HS E2 HE2 OLD2.
  all: assert (A10b : ew E2 532 = getr regs3 10)
         by (rewrite HE2; change 532%nat with (528 + 4)%nat;
             exact (YN3v.ew_havoc_new E1 528 (map (getr regs3) CLOB) 4 (w64 0) ltac:(cbn; lia))).
  all: clear SHOK.
  all: assert (U32E2 : U E2 (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact H32E | unfold SHADOW_OFF; lia]).
  all: assert (U46E2 : U E2 (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact H46E | lia]).
  all: assert (U20c : U E2 (SOff 20 0) = r) by (apply U_atom; [exact E20 | lia]).
  all: pose proof HJ3 as (HAR3 & _).
  all: assert (SHOK : sh_ok SEGS (SOff LA_SB 0) RA_SH E2 (mrestrict (w_H W3) mem3))
         by (unfold sh_ok, RA_SH; apply Forall_cons;
             [ apply (lx_shent_block B LAWS ly3 S3 W3 mem3 md4 E2 r r LX_REG 0 288 20 HAR3 HrIn U32E2 U20c);
               [lia | lia | change (req_size LX_REG) with 288; lia]
             | apply Forall_cons;
               [ exact (lx_shent_frame B MT LAWS cx fp W3 (YK11.mkst regs3 (Z_to_bv 64 0) mem3 (seg_rom SEGS))
                          ly3 S3 md4 k HB HJ3 HFR E2 64 352 U32E2 U46E2
                          (lx_shadow_keep cx fp W3 [(r, LX_REG)] ms3
                             (YK11.mkst regs3 (Z_to_bv 64 0) mem3 (seg_rom SEGS)) LSH_iter HKA
                             ltac:(unfold LSH_iter; change (fs_frame_bytes LX_CID / 8) with 64;
                                   cbn [length app repeat]; lia) HSH)
                          ltac:(lia))
               | apply Forall_nil ] ]).
  all: clear HJ; rename HJ3 into HJ.
  all: assert (U532 : U E2 (SOff 532 0) = 0) by (unfold U; rewrite lx_sv_SOff0, A10b, HV0; reflexivity).
  all: psrr_branch_tok RUN BR HS SHOK LX_SBX.
  all: rewrite branch_ne_U, U532, U_lit in Hc by lia.
  all: lazymatch type of Hc with
       | _ = true => discriminate Hc
       | _ = false => clear Hc; 
         paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_M; [apply lj_awr_ro; vm_compute; reflexivity |];
         lj_keep_run HKA;
         lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
           apply (HLM cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end;
         exists pos, r, fab, ren, bs, bs';
         split; [lj_land_body HS|];
         split; [exact Hi|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HBLK|];
         split; [lj_kf|]; split; [exact HIV|]; split; [exact HFB|];
         split; [lj_kf|]; split; [exact HIV'|]; split; [exact HFB'|]; split; [exact HKP|]; split; [exact Hren|];
         split; [exact Hj|];
         split; [lj_kf|]; split; [lj_kf|]; split; [lj_kf|];
         lj_reg HS (19%bv : bv 5) G19; lj_reg HS (20%bv : bv 5) G20; lj_reg HS (21%bv : bv 5) G21;
         lj_reg HS (23%bv : bv 5) G23; lj_reg HS (24%bv : bv 5) G24; lj_reg HS (25%bv : bv 5) G25;
         lj_reg HS (26%bv : bv 5) G26; lj_reg HS (27%bv : bv 5) G27;
         split; [rewrite G19, (lj_den_atom _ 20 r _ E20) by lia; f_equal; lia|];
         split; [rewrite G20, lx_sv_SOff0; exact E20|];
         split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|];
         split; [rewrite G23; reflexivity|];
         split; [rewrite G24, lx_sv_SOff0; exact E24|];
         split; [rewrite G25, (lj_den_atom _ 46 (lF cx fp) _ H46E) by lia; f_equal; lia|];
         split; [rewrite G26, lx_sv_SOff0; exact E26|];
         rewrite G27, lx_sv_SOff0; exact E27

       end.
Qed.

(* One row of check_kept's loop: rows 0 .. 4 walk; a row beyond prev.n - 1 does not exist (LI_L's 0 <= j < prev.n). *)
Lemma lj_liter : forall POST (i j : nat),
  lx_from B MT POST (LI_E B MT i) -> lx_from B MT POST (LI_L B MT i (Z.of_nat (S j))) ->
  lx_from B MT POST (LI_L B MT i (Z.of_nat j)).
Proof.
  intros POST i j HLE HLL.
  destruct (lt_dec j 5) as [Hj5 | Hj5].
  - apply lj_rowA. apply (lj_rowB B MT HY POST i j Hj5). exact (lj_rowC B MT HY POST i j Hj5 HLE HLL).
  - (* no such row: LI_L has 0 <= j < prev.n <= 5 *)
    intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
    destruct HI as (pos & r & fab & ren & bs & bs' & _ & _ & _ & _ & _ & _ & HIV & _ & _ & _ & _ & _ & _ & Hj & _).
    exfalso. pose proof HIV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1. lia.
Qed.

(* The loop runs at most five rows: from row j on, with the turn's end given, the walk reaches the post. *)
Lemma lj_lrows : forall POST i, lx_from B MT POST (LI_E B MT i) ->
  forall d j, (j + d = 5)%nat -> lx_from B MT POST (LI_L B MT i (Z.of_nat j)).
Proof.
  intros POST i HLE d. induction d as [|d IH]; intros j Hd.
  - (* j = 5: LI_L has 0 <= j < prev.n <= 5 *)
    intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
    destruct HI as (pos & r & fab & ren & bs & bs' & _ & _ & _ & _ & _ & _ & HIV & _ & _ & _ & _ & _ & _ & Hj & _).
    exfalso. pose proof HIV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1. lia.
  - exact (lj_liter POST i j HLE (IH (S j) ltac:(lia))).
Qed.

(* The phase: from LP_K (0x80b08) the walk reaches the next loop head or the loop's exit. *)
Theorem lx_join : forall POST i,
  lx_from B MT POST (LI_X B MT) -> lx_from B MT POST (LI_J B MT (S i)) -> lx_from B MT POST (LI_K B MT i).
Proof.
  intros POST i HLX HLJ.
  pose proof (lj_ewalk B MT HY POST i HLX HLJ) as HLE.
  exact (lj_kwalk B MT HY POST i HLE (lj_lrows POST i HLE 5%nat 0%nat eq_refl)).
Qed.

End a.
