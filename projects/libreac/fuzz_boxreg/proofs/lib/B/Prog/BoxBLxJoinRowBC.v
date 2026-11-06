(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module paths and module names changed; 362 of its 405 lines of code are new or changed and 937 lines of the source are left out. *)
(* The phase JOIN of the walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput: two segments of check_kept's row
   loop (BoxBLxJoinRowDefs.v's cuts), row j of turn i:
   - lj_rowB, LP_M 0x80c2c -> LP_N 0x80c44: `beq s8, s7` (0x80c2c) skips the name test of the renamed row (s8 = 56
     renamed, s7 = 56 j: BoxBLxJoin.v lj_ren_eq); else strncmp (prev.name, r.name, 32) (0x80c3c; BoxBLxJoin.v
     lj_strncmp_at, its operands by lj_cstr_prev / lj_cstr_reg) returns 0, as a row that was not renamed keeps its name
     (BoxBLxJoinRowDefs.v lr_name_same), so `bnez a0` (0x80c40) to the abort 0x80fa4 is not taken;
   - lj_rowC, LP_N 0x80c44 -> LP_L 0x80b44 (row j + 1) or LP_E 0x80cb0: `addi s7, s7, 56`, `bne s10, s7` (s10 = 56 n,
     n = prev.n) back to the loop head while j + 1 < n, else `j` to the turn's end. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxJoin BoxBLxJoinRowDefs.
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

(* `bne s10, s7` (0x80c48) after `addi s7, s7, 56`: s10 = 56 n, s7 = 56 j + 56. *)
Lemma lr_bne_next : forall E (n j : Z), ew E 26 = w64 (56 * n) -> ew E 23 = w64 (56 * j) -> 0 <= n <= 5 -> 0 <= j < 5 ->
  branch_taken BC_NE (sv_denot E (SOff 26 0)) (sv_denot E (SOff 23 56)) = negb (n =? j + 1).
Proof.
  intros E n j H26 H23 Hn Hj. rewrite branch_ne_U, (U_atom E 26 (56 * n) H26) by lia.
  rewrite U_SOff, H23. unfold w64. rewrite unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia).
  f_equal. destruct (Z.eqb_spec (56 * n) (56 * j + 56)), (Z.eqb_spec n (j + 1)); lia.
Qed.

(* `beq s8, s7` (0x80c2c): s8 = 56 (ren mod 2 ^ 32), s7 = 56 j. *)
Lemma lr_beq_ren : forall E (ren j : Z), ew E 24 = w64 (56 * (ren mod 2 ^ 32)) -> ew E 23 = w64 (56 * j) ->
  -1 <= ren < 5 -> 0 <= j < 5 ->
  branch_taken BC_EQ (sv_denot E (SOff 24 0)) (sv_denot E (SOff 23 0)) = (j =? ren).
Proof.
  intros E ren j H24 H23 Hr Hj.
  pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hm.
  rewrite branch_eq_U, (U_atom E 24 _ H24), (U_atom E 23 _ H23) by lia.
  pose proof (lj_ren_eq ren j Hr Hj) as Hiff.
  destruct (Z.eqb_spec (56 * (ren mod 2 ^ 32)) (56 * j)), (Z.eqb_spec j ren); tauto.
Qed.

(* ---- LP_M -> LP_N: the name test of row j ---- *)
Lemma lj_rowB : forall POST (i j : nat), (j < 5)%nat ->
  lx_from B MT POST (LI_R B MT LP_N i (Z.of_nat j)) -> lx_from B MT POST (LI_R B MT LP_M i (Z.of_nat j)).
Proof.
  intros POST i j Hj5 HLN.
  pose proof (lh_laws B MT HY) as LAWS.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (pos & r & fab & ren & bs & bs' & HBD & Hi & Hk & Hacc & HBLK & HPV & HIV & HFB & HRG & HIV' & HFB'
    & HKP & Hren & Hj & HCUR & HSL & H58 & R19 & R20 & R21 & R23 & R24 & R25 & R26 & R27).
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HLR & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof HIV as ((HL288 & HB1 & _ & _ & _ & _ & HB6) & _).
  pose proof HIV' as ((HL288' & _) & _).
  unfold Boxreg.boxreg_B1 in HB1.
  set (E := lx_env cx fp (ms_regs ms3) []).
  assert (HE : lx_E cx fp E) by exact (lx_env_E cx fp ms3 [] HLR).
  assert (HEI : img_env VAL A_LIM E) by exact (lx_env_img cx fp (ms_regs ms3) []).
  assert (HS0 : st_ok_pi SEGS VAL E (lx_ss LP_M (lx_sr LX_OVP) LSH_iter (lx_slot_chunks []) [] 0 0 0 0 []
                                       (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
  { eapply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
    - exact HE.
    - exact HBD.
    - apply lx_regs_ok; [apply lx_regs_ok_atoms | exact (lx_ovp_ok cx fp ms3 [] HLR R21)].
    - constructor.
    - constructor.
    - lia.
    - lia.
    - lia.
    - lia.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - unfold lx_regions0. repeat constructor.
    - split; [|split; exact I]. exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE). }
  rename HS0 into HS.
  lj_unwin_tac HS 1%nat.
  pose proof HE as (H2E & H8E & H3E & H4E & H22E & H32E & HSAVE & H46E & H47E).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in H2E, H8E, H22E, H32E, H46E, H47E.
  assert (E19 : ew E 19 = w64 (r + 56 * Z.of_nat j))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 19 19%bv eq_refl) R19).
  assert (E20 : ew E 20 = w64 r) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 20 20%bv eq_refl) R20).
  assert (E23 : ew E 23 = w64 (56 * Z.of_nat j))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 23 23%bv eq_refl) R23).
  assert (E24 : ew E 24 = w64 (56 * (ren mod 2 ^ 32)))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 24 24%bv eq_refl) R24).
  assert (E25 : ew E 25 = w64 (lF cx fp + 64 + 56 * Z.of_nat j))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 25 25%bv eq_refl) R25).
  assert (E26 : ew E 26 = w64 (56 * Boxreg.bx_n bs))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 26 26%bv eq_refl) R26).
  assert (E27 : ew E 27 = w64 fab) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 27 27%bv eq_refl) R27).
  clearbody E.
  pose proof HB as (HPRE0 & _ & _ & HPN & _ & _ & _ & _ & HRO0 & _).
  pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
  pose proof HJ as (HAR & _).
  assert (HrIn : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size LX_REG) with 288 in Hrceil.
  pose proof asan_consts as (C1 & _).
  pose proof (lx_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HSHr0 & HSHr1).
  assert (U2E : bv_unsigned (ew E 2) = lsp1 cx) by (rewrite H2E; unfold w64; apply unsigned_lit_small; lia).
  assert (U8E : bv_unsigned (ew E 8) = lsp0 cx) by (rewrite H8E; unfold w64; apply unsigned_lit_small; lia).
  assert (U46E : bv_unsigned (ew E 46) = lF cx fp) by (rewrite H46E; unfold w64; apply unsigned_lit_small; lia).
  assert (U22E : bv_unsigned (ew E 22) = lSH cx fp) by (rewrite H22E; unfold w64; apply unsigned_lit_small; lia).
  assert (SHOK : sh_ok SEGS (SOff LA_SB 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)). pose (RUNTO := paj_run_to B LAWS).
  psrr_branch_tok RUN BR HS SHOK LX_SBX;
    rewrite (lr_beq_ren E ren (Z.of_nat j) E24 E23 ltac:(lia) ltac:(lia)) in Hc.
  - (* j = renamed: the renamed row's name is not tested; to 0x80c44 *)
    paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_N; [apply lj_awr_ro; vm_compute; reflexivity |].
    pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
    assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply lj_keep_eq; exact HMEQ).
    clear HF HFr HMEQ.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
      apply (HLN cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end.
    exists pos, r, fab, ren, bs, bs'.
    split; [lj_land_body HS|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV|]. split; [exact HFB|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|]. split; [exact HKP|]. split; [exact Hren|].
    split; [exact Hj|].
    split; [lj_kf|]. split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (19%bv : bv 5) G19. lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21.
    lj_reg HS (23%bv : bv 5) G23. lj_reg HS (24%bv : bv 5) G24. lj_reg HS (25%bv : bv 5) G25.
    lj_reg HS (26%bv : bv 5) G26. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G19, lx_sv_SOff0; exact E19|].
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    split; [rewrite G23, lx_sv_SOff0; exact E23|].
    split; [rewrite G24, lx_sv_SOff0; exact E24|].
    split; [rewrite G25, lx_sv_SOff0; exact E25|].
    split; [rewrite G26, lx_sv_SOff0; exact E26|].
    rewrite G27, lx_sv_SOff0; exact E27.
  - (* j <> renamed: strncmp (prev.name, r.name, 32) at 0x80c3c *)
    apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
    pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
    assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply lj_keep_eq; exact HMEQ).
    clear HF HFr HMEQ.
    (* at the call of strncmp: a0 = prev + 56 j + 24, a1 = r + 56 j + 24, a2 = 32 *)
    pmkst HS.
    prreg HS (1%bv : bv 5) CR1. prreg HS (2%bv : bv 5) CR2. prreg HS (3%bv : bv 5) CR3. prreg HS (4%bv : bv 5) CR4.
    prreg HS (10%bv : bv 5) CR10. prreg HS (11%bv : bv 5) CR11. prreg HS (12%bv : bv 5) CR12.
    rewrite H2E in CR2. rewrite H3E, Hgp0 in CR3. rewrite H4E, Htp0 in CR4.
    rewrite E25 in CR10. rewrite E19 in CR11. unfold w64 in CR10, CR11.
    rewrite unsigned_lit_small in CR10, CR11 by lia.
    assert (HNUL : In (Z_to_bv 8 0) (Boxreg.bx_name bs (Z.of_nat j))) by (apply HB6; exact Hj).
    assert (HNUL' : In (Z_to_bv 8 0) (Boxreg.bx_name bs' (Z.of_nat j))).
    { destruct (HKP (Z.of_nat j) Hj) as (_ & _ & _ & _ & [Heq | ->]); [contradiction | exact HNUL]. }
    assert (HPV1 : lprev cx fp W3 ms bs) by lj_kf.
    assert (HSH1 : lshadow cx fp W3 ms LSH_iter) by lj_kf.
    assert (HRG1 : lreg W3 ms r bs') by lj_kf.
    pose proof (lj_cstr_prev B MT HY cx fp W3 ms ly3 S3 _ k bs (Z.of_nat j) HB HJ HFR HPV1 HSH1 HL288 ltac:(lia) HNUL)
      as HX.
    pose proof (lj_cstr_reg B MT HY cx fp W3 ms ly3 S3 _ k r bs' (Z.of_nat j) HB HJ HrIn HRG1 HL288' ltac:(lia) HNUL')
      as HX'.
    assert (HRO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
      by (eapply lx_arodata_kept; [exact HJ | exact HRO0]).
    eapply SRr_bind.
    { eapply (lj_strncmp_at B MT HY W3 (ms_regs ms) (ms_mem ms) LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
        (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k (lF cx fp + 64 + 56 * Z.of_nat j + 24)
        (r + 56 * Z.of_nat j + 24) 32 (lsp1 cx - lsp0 cx) (getr (ms_regs ms) 1) (lname bs (Z.of_nat j))
        (lname bs' (Z.of_nat j)) HJ HRO1 CR10 CR11 CR12 ltac:(lia)).
      - unfold spZ at 1; rewrite CR2; unfold w64; rewrite unsigned_lit_small by lia; lia.
      - apply lj_sub_mod16; [exact Hsp32 | exact Hsp16].
      - lia.
      - unfold ESTACK, LX_STK; lia.
      - exact CR3.
      - exact CR4.
      - reflexivity.
      - rewrite CR1; apply ret_ok_codeptr_v; [lia | reflexivity].
      - exact HX.
      - exact HX'. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hres & Hfr & _).
    (* the names agree (lkept, j <> renamed): strncmp returns 0 *)
    assert (Hv0 : v = 0) by (apply Hres; exact (lr_name_same bs bs' ren (Z.of_nat j) HKP Hj Hc)).
    subst v. clear Hres HX HX' HPV1 HSH1 HRG1 HRO1.
    replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in Hfr by lia.
    assert (HK : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms) mem2)
      by exact (lr_keep_stk B MT HY cx fp W3 ms ly3 S3 _ k r (ms_mem ms) mem2 HB HJ HFR HBLK Hfr).
    assert (HKA2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by (eapply lx_keep_trans; [exact HKA | exact HK]).
    clear HKA Hfr; rename HKA2 into HKA.
    rewrite CR1.
    lj_reseat HS HP W3 mem2 HK [0; 1; 2; 3]%nat.
    lj_newenv HS E1 HE1 OLD1.
    clear SHOK. assert (SHOK : sh_ok SEGS (SOff LA_SB 0) [] E1 (mrestrict (w_H W3) mem2)) by constructor.
    clear HJ. rename HJ2 into HJ.
    (* bnez a0 (0x80c40) to the abort 0x80fa4: a0 = 0 *)
    lj_reg HS (10%bv : bv 5) G10. rewrite Hv in G10.
    clear Hc. psrr_branch_tok RUN BR HS SHOK LX_SBX.
    { exfalso. rewrite <- G10 in Hc. vm_compute in Hc. discriminate Hc. }
    (* to 0x80c44 *)
    paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_N; [apply lj_awr_ro; vm_compute; reflexivity |].
    lj_keep_run HKA.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
      apply (HLN cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end.
    exists pos, r, fab, ren, bs, bs'.
    split; [lj_land_body HS|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV|]. split; [exact HFB|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|]. split; [exact HKP|]. split; [exact Hren|].
    split; [exact Hj|].
    split; [lj_kf|]. split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (19%bv : bv 5) G19. lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21.
    lj_reg HS (23%bv : bv 5) G23. lj_reg HS (24%bv : bv 5) G24. lj_reg HS (25%bv : bv 5) G25.
    lj_reg HS (26%bv : bv 5) G26. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G19, lx_sv_SOff0; exact E19|].
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    split; [rewrite G23, lx_sv_SOff0; exact E23|].
    split; [rewrite G24, lx_sv_SOff0; exact E24|].
    split; [rewrite G25, lx_sv_SOff0; exact E25|].
    split; [rewrite G26, lx_sv_SOff0; exact E26|].
    rewrite G27, lx_sv_SOff0; exact E27.
Qed.

(* ---- LP_N -> LP_L (row j + 1) or LP_E: the loop's branch ---- *)
Lemma lj_rowC : forall POST (i j : nat), (j < 5)%nat ->
  lx_from B MT POST (LI_E B MT i) -> lx_from B MT POST (LI_L B MT i (Z.of_nat (S j))) ->
  lx_from B MT POST (LI_R B MT LP_N i (Z.of_nat j)).
Proof.
  intros POST i j Hj5 HLE HLL.
  pose proof (lh_laws B MT HY) as LAWS.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (pos & r & fab & ren & bs & bs' & HBD & Hi & Hk & Hacc & HBLK & HPV & HIV & HFB & HRG & HIV' & HFB'
    & HKP & Hren & Hj & HCUR & HSL & H58 & R19 & R20 & R21 & R23 & R24 & R25 & R26 & R27).
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HLR & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof HIV as ((HL288 & HB1 & _) & _).
  unfold Boxreg.boxreg_B1 in HB1.
  set (E := lx_env cx fp (ms_regs ms3) []).
  assert (HE : lx_E cx fp E) by exact (lx_env_E cx fp ms3 [] HLR).
  assert (HEI : img_env VAL A_LIM E) by exact (lx_env_img cx fp (ms_regs ms3) []).
  assert (HS0 : st_ok_pi SEGS VAL E (lx_ss LP_N (lx_sr LX_OVP) LSH_iter (lx_slot_chunks []) [] 0 0 0 0 []
                                       (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
  { eapply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
    - exact HE.
    - exact HBD.
    - apply lx_regs_ok; [apply lx_regs_ok_atoms | exact (lx_ovp_ok cx fp ms3 [] HLR R21)].
    - constructor.
    - constructor.
    - lia.
    - lia.
    - lia.
    - lia.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - unfold lx_regions0. repeat constructor.
    - split; [|split; exact I]. exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE). }
  rename HS0 into HS.
  lj_unwin_tac HS 1%nat.
  pose proof HE as (H2E & H8E & H3E & H4E & H22E & H32E & HSAVE & H46E & H47E).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in H2E, H8E, H22E, H32E, H46E, H47E.
  assert (E20 : ew E 20 = w64 r) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 20 20%bv eq_refl) R20).
  assert (E23 : ew E 23 = w64 (56 * Z.of_nat j))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 23 23%bv eq_refl) R23).
  assert (E24 : ew E 24 = w64 (56 * (ren mod 2 ^ 32)))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 24 24%bv eq_refl) R24).
  assert (E26 : ew E 26 = w64 (56 * Boxreg.bx_n bs))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 26 26%bv eq_refl) R26).
  assert (E27 : ew E 27 = w64 fab) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) [] 27 27%bv eq_refl) R27).
  clearbody E.
  pose proof asan_consts as (C1 & _).
  assert (SHOK : sh_ok SEGS (SOff LA_SB 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)). pose (RUNTO := paj_run_to B LAWS).
  (* addi s7, s7, 56 (0x80c44): the run stops at bne s10, s7 (0x80c48) *)
  paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
  assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply lj_keep_eq; exact HMEQ).
  clear HF HFr HMEQ.
  psrr_branch_tok RUN BR HS SHOK LX_SBX.
  all: rewrite (lr_bne_next E (Boxreg.bx_n bs) (Z.of_nat j) E26 E23 ltac:(lia) ltac:(lia)) in Hc.
  - (* j + 1 < n: back to the loop head 0x80b44, row j + 1 *)
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_L; [apply lj_awr_ro; vm_compute; reflexivity |].
    lj_keep_run HKA.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
      apply (HLL cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end.
    exists pos, r, fab, ren, bs, bs'.
    split; [lj_land_body HS|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV|]. split; [exact HFB|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|]. split; [exact HKP|]. split; [exact Hren|].
    split; [rewrite Nat2Z.inj_succ; lia|].
    split; [lj_kf|]. split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21. lj_reg HS (23%bv : bv 5) G23.
    lj_reg HS (24%bv : bv 5) G24. lj_reg HS (26%bv : bv 5) G26. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    split; [rewrite G23, (lj_den_atom _ 23 (56 * Z.of_nat j) 56 E23) by lia; rewrite Nat2Z.inj_succ; f_equal; lia|].
    split; [rewrite G24, lx_sv_SOff0; exact E24|].
    split; [rewrite G26, lx_sv_SOff0; exact E26|].
    rewrite G27, lx_sv_SOff0; exact E27.
  - (* j + 1 = n: the rows are done, 0x80cb0 *)
    paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_E; [apply lj_awr_ro; vm_compute; reflexivity |].
    lj_keep_run HKA.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
      apply (HLE cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end.
    exists pos, r, fab, bs'.
    split; [lj_land_body HS|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|].
    split; [lj_kf|]. split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    rewrite G27, lx_sv_SOff0; exact E27.
Qed.

End a.
