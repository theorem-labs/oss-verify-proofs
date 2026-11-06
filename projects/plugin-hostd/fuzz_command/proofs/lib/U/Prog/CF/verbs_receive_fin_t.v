(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v; 1022 of its 1119 lines of code are new or changed and 738 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/chain_words.v, with its module paths and module names changed; 183 of its 219 lines of code are new or changed and 1083 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 350 of its 401 lines of code are new or changed and 168 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail0 verbs_receive_tail_k reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail_m verbs_receive_tail_r.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail_e verbs_receive_tail_f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br2 verbs_receive_br3 verbs_receive_tail_a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcspn_c strncmp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tla_vim : forall v f, verb_is_m v f = true -> length (vfirst f) <> 11%nat -> length (vfirst f) <> 9%nat ->
  tla_cond v = false.
Proof.
  intros v f H H1 H2. unfold verb_is_m in H. apply andb_true_iff in H as [H _]. apply Nat.eqb_eq in H.
  unfold tla_cond.
  rewrite (VerbsFacts.verb_is_m_len_ne v fmt_preset_load)
    by (rewrite H; vm_compute (length (vfirst fmt_preset_load)); exact H1).
  rewrite (VerbsFacts.verb_is_m_len_ne v fmt_patch_set)
    by (rewrite H; vm_compute (length (vfirst fmt_patch_set)); exact H2).
  reflexivity.
Qed.

Definition nc_route (r : vroute) : bool :=
  match r with
  | RInst | RConn | RBroad | RLedger _ => false
  | _ => true
  end.

Lemma route_nc : forall tk, nc_route (route tk) = true -> exists v rest, tk = v :: rest /\ tla_cond v = false.
Proof.
  intros [|v args] H; [discriminate H|]. exists v, args. split; [reflexivity|].
  unfold route, route_mid, route_tail, route_conn, route_cd in H.
  repeat match type of H with
  | context [if ?b then _ else _] =>
      let Eb := fresh "Eb" in
      destruct b eqn:Eb; cbv beta iota in H;
      [ first [ apply list_eqb_eq in Eb; subst v; vm_compute; reflexivity
              | exact (tla_vim v _ Eb ltac:(intro E; vm_compute in E; discriminate E)
                         ltac:(intro E; vm_compute in E; discriminate E)) ] |]
  end.
  destruct (ledger_of v instance_info_verbs); [discriminate H|].
  destruct args as [|a [|b [|c r]]]; try discriminate H.
  all: cbv beta iota in H;
    repeat match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end;
    discriminate H.
Qed.

Section TN.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis CSPN : strcspn_contract.
Hypothesis NCMP : strncmp_contract.
Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Lemma tla_cmp_nc : forall (f : list byte) (A n : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m2 : word -> option byte) (p0 : word) (v a : list byte),
  verbs_receive_disp.img_cstr_b A f = true -> 0 <= A < 2 ^ 64 -> a1 = Z_to_bv 64 A ->
  Z.of_nat (length (vfirst f)) = n -> 0 <= n < 2 ^ 64 -> a2 = Z_to_bv 64 n ->
  length (tfirst v) = length (vfirst f) -> verb_is_m v f = tla_cond v -> tla_cond v = false ->
  bytes_at rsegs m2 (bv_unsigned p0) (v ++ [Z_to_bv 8 0]) -> Forall (fun b => bv_unsigned b <> 0) v ->
  mem_inv rsegs m2 -> munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 -> wmono rsegs m m2 ->
  evt rsegs (tla_post sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p0 v a)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 p0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17ae8) fc None m2 (seg_rom rsegs)).
Proof using NCMP.
  intros f A n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m2 p0 v a IMG RA E1 EN RN E2 LR CF NC HV NZ MI2 MU2 WM2.
  subst a1 a2.
  destruct (verbs_receive_disp.img_cstr m2 verbs_receive_disp.IMG_TOP sp A f MI2 (Z.le_refl _) IMG)
    as (fs & HFs & _).
  destruct (VerbsFacts.strncmp_verb v f fs NZ (proj1 (proj2 HFs)) LR) as (w & HW & RW & QW).
  rewrite EN in HW.
  do 2 zstep.
  eapply evt_cut.
  { eapply NCMP with (ls := v ++ [Z_to_bv 8 0]) (rs := f ++ Z_to_bv 8 0 :: fs) (v := w);
      [ exact HV | rewrite unsigned_lit by lia; exact (proj1 HFs) | rewrite unsigned_lit by lia; exact HW
      | exact MI2 ]. }
  intros ms' PO. unfold strncmp_post in PO.
  destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' & m3 &
                  E & MU3 & WM3 & MI3 & _ & _).
  subst ms'. tla_ret.
  zstep. rewrite verbs_receive_disp.eqb_small by exact RW. rewrite QW, CF, NC. cbv beta iota delta [negb].
  apply evt_done. unfold tla_post. rewrite NC.
  do 17 eexists. split; [reflexivity|].
  split; [intros Hc; discriminate Hc|].
  split; [eapply munch_trans; [exact MU2 | apply verbs_receive_disp.munch_nil; exact MU3]|].
  eapply wmono_trans; [exact WM2 | exact WM3].
Qed.

Lemma tla_k_nc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p0 can : word) (v a : list byte) (lo : Z),
  bytes_at rsegs m (bv_unsigned sp + 8) (le8 p0) ->
  VerbsMem.cstr0_at m (bv_unsigned p0) v ->
  bv_unsigned p0 + Z.of_nat (length v) + 1 <= lo ->
  Z.of_nat (length v) <= 8192 -> VerbsMem.ssp_at m can -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> verbs_receive_disp.IMG_TOP <= lo ->
  tla_cond v = false ->
  evt rsegs (tla_post sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p0 v a)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17aa8) fc None m (seg_rom rsegs)).
Proof using CSPN NCMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p0 can v a lo HP0 HV LV VL HSSP HMI ST LO HIT NC.
  pose proof (verbs_receive_disp.read_all _ _ _ HP0) as RD. rewrite length_le8 in RD.
  zstep. clear RD.
  do 4 zstep.
  eapply evt_cut.
  { eapply CSPN with (str := v) (slack := []) (set := map (Z_to_bv 8) [32; 9]) (lo := lo) (can := can);
    [ exact (proj1 HV)
    | apply verbs_receive_disp.nz_notin; exact (proj2 HV)
    | intros Hs; cbn in Hs; lia
    | rewrite unsigned_lit by lia; apply verbs_receive_disp.img_bytes; [exact HMI | vm_compute; reflexivity]
    | apply verbs_receive_disp.nz_lit; vm_compute; reflexivity
    | exact (proj1 HSSP)
    | exact (proj2 HSSP)
    | exact ST
    | lia
    | left; cbn [length]; lia
    | left; rewrite unsigned_lit by lia; cbn [length map]; unfold verbs_receive_disp.IMG_TOP in HIT; lia
    | left; unfold CSPN_SSP_GOT, verbs_receive_disp.IMG_TOP in *; lia
    | left; unfold CSPN_SSP_GUARD, verbs_receive_disp.IMG_TOP in *; lia
    | exact HMI ]. }
  intros ms' PO. unfold strcspn_post in PO.
  destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' & m2 &
                  E & MU2 & WM2 & MI2 & _).
  subst ms'. tla_ret. rewrite VerbsFacts.cspn_tfirst.
  assert (TR : forall X bs, bytes_at rsegs m X bs ->
                 X + Z.of_nat (length bs) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= X -> bytes_at rsegs m2 X bs).
  { intros X bs Hb Hd. eapply bytes_at_transport; [exact Hb | exact MU2 |]. cbn [disjoint_from].
    split; [exact Hd | exact I]. }
  assert (HV2 : bytes_at rsegs m2 (bv_unsigned p0) (v ++ [Z_to_bv 8 0])).
  { apply TR; [exact (proj1 HV)|]. left. rewrite length_app. cbn [length]. lia. }
  assert (LT : (length (tfirst v) <= length v)%nat) by apply VerbsFacts.upto_length.
  do 2 zstep. rewrite verbs_receive_disp.eqb_lit by lia.
  destruct (Z.of_nat (length (tfirst v)) =? 9) eqn:L9; cbv beta iota delta [negb].
  - apply Z.eqb_eq in L9.
    assert (EP : verb_is_m v fmt_preset_load = false).
    { apply VerbsFacts.verb_is_m_len_ne. vm_compute (length (vfirst fmt_preset_load)). lia. }
    do 3 zstep.
    eapply (tla_cmp_nc fmt_patch_set 0x109bc 9);
      [ vm_compute; reflexivity | lia | reflexivity | vm_compute; reflexivity | lia | reflexivity
      | vm_compute (length (vfirst fmt_patch_set)); lia
      | unfold tla_cond; rewrite EP; reflexivity
      | exact NC | exact HV2 | exact (proj2 HV) | exact MI2 | exact MU2 | exact WM2 ].
  - apply Z.eqb_neq in L9.
    do 2 zstep. rewrite verbs_receive_disp.eqb_lit by lia.
    destruct (Z.of_nat (length (tfirst v)) =? 11) eqn:L11; cbv beta iota delta [negb].
    + apply Z.eqb_eq in L11.
      assert (EP : verb_is_m v fmt_patch_set = false).
      { apply VerbsFacts.verb_is_m_len_ne. vm_compute (length (vfirst fmt_patch_set)). lia. }
      do 4 zstep.
      eapply (tla_cmp_nc fmt_preset_load 0x108e8 11);
        [ vm_compute; reflexivity | lia | reflexivity | vm_compute; reflexivity | lia | reflexivity
        | vm_compute (length (vfirst fmt_preset_load)); lia
        | unfold tla_cond; rewrite EP; destruct (verb_is_m v fmt_preset_load); reflexivity
        | exact NC | exact HV2 | exact (proj2 HV) | exact MI2 | exact MU2 | exact WM2 ].
    + apply evt_done. unfold tla_post. rewrite NC.
      do 17 eexists. split; [reflexivity|].
      split; [intros Hc; discriminate Hc|].
      split; [exact MU2 | exact WM2].
Qed.

Lemma tl_after_nc : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P v rest,
  VS fx rg 0x17aa8 mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  toks D = v :: rest -> tla_cond v = false ->
  (forall rg' mem' c', VS fx rg' 0x17b10 mem' md1 L1 A1 R1 O1 k1 qv None jk c' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS CSPN NCMP.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P v rest HST TK NC KONT.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _ & _ & _ & _ & _ & _ & _ & HS1).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  destruct (h_x B API S _ _ _ _ _ _ _ _ H (s_cb S, s_ncb S) (or_intror (or_introl eq_refl))) as [CBIN _].
  destruct (blk_low B API HF _ _ _ _ (s_cb S) (s_ncb S) 0 HM1 CBIN ltac:(unfold s_ncb; lia)) as (_ & CBC & _ & _).
  assert (EV0 : nth_error (toks D) 0 = Some v) by (rewrite TK; reflexivity).
  rewrite TK in LPT. cbn [length] in LPT.
  set (p0 := nth 0 (s_ps S) (Z_to_bv 64 0)).
  assert (EP0 : nth_error (s_ps S) 0 = Some p0) by (unfold p0; apply nth_error_nth'; lia).
  destruct (Forall2_nth _ _ _ _ _ _ TOK EP0 EV0) as (CV & _ & BV).
  assert (LV : Z.of_nat (length v) <= 8192).
  { pose proof (verbs_receive_route.toks_len D v ltac:(rewrite TK; left; reflexivity)).
    pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
  destruct (st_f18 B API HF _ _ _ _ HM1) as (_ & cn & SG1 & SG2).
  assert (SSP : VerbsMem.ssp_at (normalize rsegs mem1) cn).
  { split; apply (bytes_at_normalize rsegs); try exact RO1; rewrite <- SEGS.
    - apply CF.reply.le_at_bytes; [exact SG1 | unfold VerbsMem.SSP_GOT; lia | rewrite length_le8; unfold VerbsMem.SSP_GOT; lia].
    - apply CF.reply.le_at_bytes; [exact SG2 | unfold VerbsMem.SSP_GUARD; lia
                               | rewrite length_le8; unfold VerbsMem.SSP_GUARD; lia]. }
  assert (ST : stk rsegs (normalize rsegs mem1) (s_spf S - 96) (bv_unsigned (reg_get rg 2))).
  { rewrite SP2. split; [unfold s_spf, VR_K in *; lia|]. split; [unfold s_spf in *; lia|]. intros x Hx.
    assert (W : writable_at rsegs mem1 x).
    { rewrite <- SEGS. apply HS1. left. unfold s_spf, VR_K in *. lia. }
    destruct (writable_hi_present mem1 x ltac:(unfold s_spf, VR_K in *; lia) W) as [bb E].
    assert (NE : normalize rsegs mem1 (wa x) = mem1 (wa x)).
    { apply CF.RecKindB.normalize_rw. unfold wa. apply ro_addr_hi. unfold s_spf, VR_K in *. lia. }
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  eapply (@ka_w fx _ B API HF S HS rg 0x17aa8 mem1 md1 L1 A1 R1 O1 k1 qv None jk c [(s_spf S - 96, s_spf S)] _ P HST).
  - intros x _ Hx. cbn [Frame.outside]. split; [|exact I]. intros Hin. apply Hx. unfold s_spf, VR_K in *. lia.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply tla_k_nc with (p0 := p0) (can := cn) (v := v) (a := []) (lo := s_spf S - 96);
        [ rewrite SP2; apply (bytes_at_normalize rsegs); [exact RO1|];
          replace (s_spf S + 8) with (s_spf S + 8 + 8 * Z.of_nat 0) by lia; exact (frame_tok S mem1 jk 0 p0 FR EP0)
        | split; [apply (bytes_at_normalize rsegs); [exact RO1 | exact (proj1 CV)] | exact (proj2 CV)]
        | unfold s_spf, VR_K in *; lia
        | exact LV
        | exact SSP
        | apply mem_inv_normalize
        | exact ST
        | rewrite SP2; lia
        | unfold verbs_receive_disp.IMG_TOP, s_spf, VR_K in *; lia
        | exact NC ]. }
    intros ms' HQ. split; [exact HQ|].
    unfold tla_post in HQ.
    destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    E & _ & MU & WM).
    do 3 eexists. split; [exact E|]. split; [rewrite SP2 in MU; exact MU | exact WM].
  - intros R' pc' m' rg' mem2 HQ X MK.
    cbv beta in HQ. unfold tla_post in HQ.
    destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
                    E & _ & _ & _).
    rewrite NC in E.
    injection E as ER EP EM. subst R' pc' m'.
    assert (VR' : vregs S rg').
    { apply (tla_vregs S rg _ rg' VR X). intros r Hr H18. cs_cases r Hr; first [exfalso; lia | reflexivity]. }
    exact (KONT rg' mem2 _ (MK 0x17b10 eq_refl VR')).
Qed.

End TN.

Section TT.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis RP : forall f : YK11.FPState, @reply_contract f rc B API.
Hypothesis FREE : forall f : YK11.FPState, @free_contract f rc B API.
Hypothesis CSPN : strcspn_contract.
Hypothesis NCMP : strncmp_contract.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Lemma tl_tail_n : forall (f : YK11.FPState) rg mem md L A R O k q nq x jk c ret (qt : bool),
  VS f rg REPLY mem md L A R O k (if qt then 1 else s_q0 S) (Some (q, nq, x)) jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> getr rg 11 = Z_to_bv 64 q ->
  VerbsRun.run_step sup_reply_code_c.reply_code (s_R S)
    (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, x, qt) ->
  Verbs.after atoi_c.atoi_val (toks D) = None ->
  (k + 3 <= 32)%nat ->
  (forall rg' mem' md' L' A' O' c',
     VS f rg' ret mem' md' L' A' (fst (socket_send_m R (x ++ [Z_to_bv 8 0]))) O' (k + 1)
       (if qt then 1 else s_q0 S) None jk c' ->
     regs_preserved rg rg' ->
     (forall rg2 mem2 md2 L2 A2 O2 c2,
        VS f rg2 0x17b10 mem2 md2 L2 A2 (fst (socket_send_m R (x ++ [Z_to_bv 8 0]))) O2 (k + 1)
          (if qt then 1 else s_q0 S) None jk c2 -> SR rsegs c2 (vr_post B API S)) ->
     SR rsegs c' (vr_post B API S)) ->
  SR rsegs c (vr_post B API S).
Proof using HF HS RP FREE.
  intros f rg mem md L A R O k q nq x jk c ret qt HST E1 RET E11 RUN AN HK KONT.
  destruct (tl_text _ _ _ _ _ RUN) as [NZ LX].
  pose proof (tl_nrep _ _ _ _ _ RUN) as NR. pose proof (ok_nrep B API S HS) as NR0.
  apply (@tl_call_reply f rc B API HF S HS RP rg mem md L A R O k _ q nq x jk c ret _ HST E1 RET E11 NZ LX
           ltac:(lia) ltac:(lia)).
  intros rg' mem' md' L' A' O' c' HST' PR'.
  apply (KONT rg' mem' md' L' A' O' c' HST' PR').
  intros rg2 mem2 md2 L2 A2 O2 c2 HST2.
  apply (@tl_frees f rc B API HF S HS FREE rg2 mem2 md2 L2 A2 _ O2 (k + 1) _ jk c2 _ HST2).
  intros rg4 mem4 md4 L4 A4 c4 HT4.
  pose proof (tl_run _ _ _ _ _ RUN) as VR. rewrite AN in VR.
  exact (@tl_epi f rc B API HF S HS rg4 mem4 md4 L4 A4 _ O2 (k + 1) _ jk c4 x qt HT4 VR eq_refl).
Qed.

Lemma vr_tail_17834_n : forall rg0 k0 v rest,
  toks D = v :: rest -> tla_cond v = false -> (k0 + 11 <= 32)%nat ->
  join_k_ge B API S 0x178b0 19 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof using HF HS RP FREE CSPN NCMP.
  intros rg0 k0 v rest TK NC HK0 f rg mem md L A R O k q nq x jk c (qt & HST & _ & E19 & _ & _ & RUN & HK1).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x178b0 mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_17834. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK REPLY eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (tl_tail_n f rg' mem2 md L A R O k q _ x jk _ 0x178bc qt HST1).
  - rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite (getr_of_eqv _ _ 11 X eq_refl). exact E19.
  - exact RUN.
  - rewrite TK. destruct rest as [|a rest']; [reflexivity|]. cbn [Verbs.after].
    unfold tla_cond in NC. rewrite NC. reflexivity.
  - lia.
  - intros rg2 mem3 md3 L3 A3 O3 c3 HST3 _ DIR.
    pose proof HST3 as (_ & _ & VR3 & _).
    eapply (@ka_nw f _ B API HF S HS rg2 0x178bc mem3 md3 L3 A3 _ O3 (k + 1) _ _ jk c3 _ _ HST3 (tk_17840 _ _ _ _)).
    { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
    intros R' pc' rg4 mem4 EQ X4 MK4. cbv beta in EQ. injection EQ as E3 E4. subst R' pc'.
    pose proof (getr_eqv_of rg2 rg4 X4) as GE.
    eapply (@tl_after_nc f rc B API HF S HS CSPN NCMP rg4 mem4 md3 L3 A3 _ O3 (k + 1) _ jk _ _ v rest).
    + apply MK4; [reflexivity | apply (vregs_pres S rg2 rg4 VR3); intros r _; apply GE].
    + exact TK.
    + exact NC.
    + intros rg5 mem5 c5 HST5. exact (DIR rg5 mem5 md3 L3 A3 O3 c5 HST5).
Qed.

Lemma vr_tail_17830_n : forall rg0 k0 v rest,
  toks D = v :: rest -> tla_cond v = false -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x178ac 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof using HF HS RP FREE CSPN NCMP.
  intros rg0 k0 v rest TK NC HK0. apply join_k_of_ge.
  intros f rg mem md L A R O k q nq x jk c (qt & HST & HNQ & E10 & E18 & _ & RUN & HK1).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x178ac mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_17830. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (VR' : vregs S rg') by (apply (tl_vregs S rg rg' VR);
    match goal with |- getr _ ?r = _ => rewrite (getr_of_eqv _ _ r X eq_refl); reflexivity end).
  apply (vr_tail_17834_n rg0 k0 v rest TK NC HK0 f rg' mem2 md L A R O k q nq x jk _).
  exists qt. split; [exact (MK 0x178b0 eq_refl VR')|]. split; [exact HNQ|].
  split; [rewrite (getr_of_eqv _ _ 19 X eq_refl); exact E10|].
  split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); exact E18|].
  split; [intros [Hj|Hj]; lia|].
  split; [exact RUN | exact HK1].
Qed.

Lemma vr_tail_176c8_n : forall rg0 k0,
  Verbs.after atoi_c.atoi_val (toks D) = None -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x176c4 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof using HF HS RP FREE.
  intros rg0 k0 AN HK0. apply join_k_of_ge.
  intros f rg mem md L A R O k q nq x jk c (qt & HST & _ & E10 & _ & _ & RUN & HK1).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x176c4 mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_176c8. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK REPLY eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (tl_tail_n f rg' mem2 md L A R O k q _ x jk _ 0x176d0 qt HST1).
  - rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite (getr_of_eqv _ _ 11 X eq_refl). exact E10.
  - exact RUN.
  - exact AN.
  - lia.
  - intros rg2 mem3 md3 L3 A3 O3 c3 HST3 _ DIR.
    pose proof HST3 as (_ & _ & VR3 & _).
    eapply (@ka_nw f _ B API HF S HS rg2 0x176d0 mem3 md3 L3 A3 _ O3 (k + 1) _ _ jk c3 _ _ HST3 (tk_176d4 _ _ _ _)).
    { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
    intros R' pc' rg4 mem4 EQ X4 MK4. cbv beta in EQ. injection EQ as E3 E4. subst R' pc'.
    pose proof (getr_eqv_of rg2 rg4 X4) as GE.
    apply (DIR rg4 mem4 md3 L3 A3 O3 _).
    apply MK4; [reflexivity | apply (vregs_pres S rg2 rg4 VR3); intros r _; apply GE].
Qed.

Lemma vr_tail_nc_17830 : forall rg0 k0, nc_route (route (toks D)) = true -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x178ac 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof using HF HS RP FREE CSPN NCMP.
  intros rg0 k0 NR HK0. destruct (route_nc (toks D) NR) as (v & rest & TK & NC).
  exact (vr_tail_17830_n rg0 k0 v rest TK NC HK0).
Qed.

Lemma vr_tail_nc_176c8 : forall rg0 k0, nc_route (route (toks D)) = true -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x176c4 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof using HF HS RP FREE.
  intros rg0 k0 NR HK0. destruct (route_nc (toks D) NR) as (v & rest & TK & NC).
  apply vr_tail_176c8_n; [|exact HK0].
  rewrite TK. destruct rest as [|a rest']; [reflexivity|]. cbn [Verbs.after].
  unfold tla_cond in NC. rewrite NC. reflexivity.
Qed.

End TT.
