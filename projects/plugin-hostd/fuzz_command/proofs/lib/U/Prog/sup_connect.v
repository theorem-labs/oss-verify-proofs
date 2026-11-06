(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 530 of its 716 lines of code are new or changed and 2556 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma scn_pre :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16764) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a3 a2
                     (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16730) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 13 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma scn_mid1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16770) sp gp tp t0 t1 t2 s0 s1 a0 s3
                                    a2 a3 a4 a5 a6 a7 s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16764) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma scn_mid2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1677c) sp gp tp t0 t1 t2 s0 s1 s4 s2
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16770) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma scn_mid3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16788) sp gp tp t0 t1 t2 s0 s1 s4 s1
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1677c) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma scn_mid4 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16794) sp gp tp t0 t1 t2 s0 s1 s4 s0
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16788) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma scn_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 s30 s40 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [C8 s40; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0] -> 48 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s4 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                                    a3 a4 a5 a6 a7 s20 s30 s40 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16794) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 s30 s40 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 12 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import answer_c record_c xmalloc_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import arg_line_c sup_connect_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c.
Local Open Scope Z_scope.

Definition scn_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma scn_kx_trans : forall xs R1 R2 R3, scn_kx xs R1 R2 -> scn_kx xs R2 R3 -> scn_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma scn_kx_of_pres : forall xs R R', regs_preserved R R' -> scn_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma scn_kx_pres : forall xs R R', scn_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac scn_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac scn_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; scn_one X|]);
  subst rr; scn_one X.

Lemma scn_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 213032); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 213032); [left | right]; lia.
Qed.

Lemma scn_shape : forall m, ro_agree rsegs m -> answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA.
  assert (RO : forall i, 0 <= i <= 6 -> ro_addr rsegs (Z_to_bv 64 (0x10417 + i)) = true).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity. }
  split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (RO (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [apply no0_nz; vm_compute; reflexivity|]. split; [cbn; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|]. intros i Hi. apply RO. cbn in Hi. lia.
Qed.

Lemma scn_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma scn_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite scn_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : arg_s_contract B API.
Hypothesis ARGL : arg_line_contract B API.
Hypothesis ANS : answer_contract B API.

Lemma scn_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma scn_str : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  ro_agree rsegs mem ->
  str_arg B L A O S K mem p (Some x) ->
  exists slack, 0 <= p < 2 ^ 64 /\ p <> 0 /\
    bytes_at rsegs mc p (x ++ Z_to_bv 8 0 :: slack) /\ no0 x /\ Z.of_nat (length x) <= LMAX /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= S - K \/ S <= p) /\
    str_home B Lc Ac S p (Z.of_nat (length x) + 1) /\
    (forall a, p <= a < p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p x SI RA H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  str_home B Lc Ac S p (Z.of_nat (length x) + 1)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | left; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      right. left. exists q, k. split; [exact QC | lia].
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi.
        assert (RO : ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
        { destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
          pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
          apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2 | right; right; split; [exact H1 | split; [exact H2 | exact H3]]]]. }
  destruct CASES as (TX & PADP & HOMEc).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  exists sl.
  split; [lia|]. split; [exact Hp0|].
  split; [exact BS'|]. split; [exact N0|]. split; [exact LX|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; lia|].
  split; [rewrite length_app; cbn [length]; rewrite SL; destruct DJ as [D|D]; [left; lia | right; exact D]|].
  split; [exact HOMEc|].
  intros a Ha. apply NRA. rewrite length_app in Ha. cbn [length] in Ha. rewrite SL in Ha. lia.
Qed.

Theorem sup_connect_holds : sup_connect_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK REC ARGS ARGL ANS.
  unfold sup_connect_contract.
  intros L A regs mem md pv pl pa pb verb line port_a port_b R O b PRE G10 G11 G12 G13 SA1 SA2 SA3 SA4 GR RA FRM F18
    RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_CONNECT_K in PRE, PRK, HCEIL, HWS, SA1, SA2, SA3, SA4.
  unfold SUP_CONNECT.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  assert (AKL : ARG_LINE_K = 8272) by reflexivity.
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as HN.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & _ & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  change (snd (sup_connect_m R verb line port_a port_b)) with
    (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
       (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_connect_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
                  (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) <= 16)%nat).
  { pose proof (scn_len R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b] REC_MOD_HOST_SHAPE true HCODE)
      as H.
    assert (LX6 : length REC_MOD_HOST_SHAPE = 6%nat) by (vm_compute; reflexivity).
    rewrite LX6 in H. exact H. }
  pose proof (rec_entry_bounds R HN) as ER.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply scn_pre; [exact ST | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16764) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pb) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact G13).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 pa) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact G12).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; exact G11).
  assert (E1_19 : getr R1 19 = Z_to_bv 64 pv) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; exact G10).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 REC_CONNECT)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (K01 : scn_kx [2; 8; 9; 18; 19; 20] regs R1) by scn_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_CONNECT _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_CONNECT. lia. }
  intros L1 A1 regs1 m2 md1 O1 SI2 BLE1 PR1 R10 FK1.
  rewrite E1_1. rewrite sb_shift_refl in BLE1.
  pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply scn_mid1. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x16770) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs. exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2). }
  assert (E2_4 : getr R2 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs. exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) E1_4). }
  assert (E2_8 : getr R2 8 = Z_to_bv 64 pb).
  { rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs. exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8). }
  assert (E2_9 : getr R2 9 = Z_to_bv 64 pa).
  { rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs. exact (eq_trans (PR1 9 ltac:(unfold callee_saved; lia)) E1_9). }
  assert (E2_18 : getr R2 18 = Z_to_bv 64 pl).
  { rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs.
    exact (eq_trans (PR1 18 ltac:(unfold callee_saved; lia)) E1_18). }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact R10).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 pv).
  { rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs.
    exact (eq_trans (PR1 19 ltac:(unfold callee_saved; lia)) E1_19). }
  assert (E2_20 : getr R2 20 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 20 X2 eq_refl); simp_regs; exact R10).
  assert (K1r : scn_kx [2; 8; 9; 18; 19; 20] R1 regs1) by exact (scn_kx_of_pres _ _ _ PR1).
  assert (K12 : scn_kx [2; 8; 9; 18; 19; 20] regs1 R2) by scn_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (FK1 (bv_unsigned sp - 48 + i) ltac:(rewrite SP1; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  assert (SRC2 : arg_s_src B L1 A1 (spZ R2) m2 pv verb).
  { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1
             (rec_record R REC_CONNECT []) O1 b pv verb (spZ R2) SI2 RA).
    - rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP2. lia.
    - exact SA1. }
  destruct (sarg_facts B L1 A1 (spZ R2) m2 pv verb SRC2) as (NO2 & LX2).
  apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 R
           REC_CONNECT O1 b R2 pv verb _ SI2).
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { exact SRC2. }
  { eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX in *. lia. }
  intros L2 A2 regs2 m3 md2 p1 SI3 EQB2 INI2 PR2 FK2.
  rewrite E2_1.
  pose proof SI3 as (RJ3 & GR3 & _ & _ & _ & RA3 & F183 & RS3). pose proof RJ3 as (HM3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply scn_mid2. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x1677c) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs. exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E2_2). }
  assert (E3_4 : getr R3 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs. exact (eq_trans (PR2 4 ltac:(unfold callee_saved; lia)) E2_4). }
  assert (E3_8 : getr R3 8 = Z_to_bv 64 pb).
  { rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs. exact (eq_trans (PR2 8 ltac:(unfold callee_saved; lia)) E2_8). }
  assert (E3_9 : getr R3 9 = Z_to_bv 64 pa).
  { rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs. exact (eq_trans (PR2 9 ltac:(unfold callee_saved; lia)) E2_9). }
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs.
    exact (eq_trans (PR2 20 ltac:(unfold callee_saved; lia)) E2_20). }
  assert (E3_11 : getr R3 11 = Z_to_bv 64 pl).
  { rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs.
    exact (eq_trans (PR2 18 ltac:(unfold callee_saved; lia)) E2_18). }
  assert (E3_20 : getr R3 20 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 20 X3 eq_refl); simp_regs.
    exact (eq_trans (PR2 20 ltac:(unfold callee_saved; lia)) E2_20). }
  assert (K2r : scn_kx [2; 8; 9; 18; 19; 20] R2 regs2) by exact (scn_kx_of_pres _ _ _ PR2).
  assert (K23 : scn_kx [2; 8; 9; 18; 19; 20] regs2 R3) by scn_tac X3.
  assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct (FK2 (bv_unsigned sp - 48 + i) ltac:(rewrite SP2; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  destruct (rec_entry_at rsegs L2 A2 m3 R REC_CONNECT [sarg verb] _ GR3) as (P0 & CA).
  pose proof CA as (_ & _ & _ & _ & NA3 & _). cbn [snd length Z.of_nat] in NA3.
  destruct (scn_str 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b pl line SI3 RA SA2)
    as (slack & PR & Hp0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L2 A2 R3 m3 md2 e pl 1 line slack (sb_shift b A A2)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m3 md2 ARG_LINE_K R3 RJ3).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + lia.
      + rewrite SP3. lia.
      + rewrite SP3. lia.
      + rewrite E3_4. exact HTP.
    - exact E3_10.
    - exact E3_11.
    - exact (proj2 (proj2 ER)).
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA3.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP3. lia.
    - rewrite SP3. apply (scn_home_lower L2 A2 (bv_unsigned sp)); [lia | exact HOME].
    - unfold iv_apart. apply (scn_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 ER).
      + exact (proj1 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS3.
    - rewrite EQB2. eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono, sb_malloc_mono; exact BLE1|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX in *. lia.
    - exact RA3. }
  intros c3 (L3 & A3 & regs3 & m4 & md3 & -> & BK3 & UB3 & _ & RA4 & GK3 & RGN3 & ALT3).
  destruct ALT3 as [(H6 & _)|(_ & p2 & POST3 & Hp2 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS4)]; [lia|].
  rewrite SEGS in RA4, BN3, BS3, BX3.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP3 & _ & HF3 & _).
  assert (F184 : f18_words rsegs m4).
  { destruct (ax_statics AX L3 A3 m4 md3 PM3) as (_ & (g & Hg & HWg) & _).
    apply (f18_words_after m3 m4 g F183); [| exact Hg | rewrite SEGS, GRD in HWg; exact HWg].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK3 i Hi). }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 R
                REC_CONNECT [sarg verb] _ b ARG_LINE_K R3 _ L3 A3 regs3 m4 md3 (canon line) p2
                (Z.of_nat (length line) + 1)
                SI3 ltac:(cbn; lia) ltac:(rewrite SP3; lia) ltac:(rewrite SP3; lia) POST3
                ltac:(intros a Ha; cbv beta in Ha; change (Z.of_nat (length [sarg verb])) with 1; lia)
                Hp2 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI3 RS4 RA4 F184) as SI4.
  cbn [app] in SI4.
  pose proof FB3 as (FBlo & FBhi & _).
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF3 (bv_unsigned sp - 48 + i)) as [E W].
    - left. lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HM3 Ho). lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM3 Ho). lia.
    - unfold scratch_k. rewrite SP3. intros [H|H]; lia.
    - intros Hr. cbv beta in Hr. unfold G_REC, REC_SC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact E | apply W]. }
  assert (K3r : scn_kx [2; 8; 9; 18; 19; 20] R3 regs3) by exact (scn_kx_of_pres _ _ _ RP3).
  assert (EQB3 : sb_shift b A A3 = sb_malloc (sb_shift b A A2) (Z.of_nat (length line) + 1)).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A3).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L3 A3 bl1 bl2 p2 _ EB1 EB2). reflexivity. }
  rewrite E3_1, SEGS.
  pose proof SI4 as (RJ4 & _). pose proof RJ4 as (HM4 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply scn_mid3. }
  intros ms4 (can4 & -> & EQ4).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x16788) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs. exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E3_2). }
  assert (E4_4 : getr R4 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs. exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) E3_4). }
  assert (E4_8 : getr R4 8 = Z_to_bv 64 pb).
  { rewrite (getr_of_eqv _ _ 8 X4 eq_refl); simp_regs. exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E3_8). }
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs.
    exact (eq_trans (RP3 20 ltac:(unfold callee_saved; lia)) E3_20). }
  assert (E4_11 : getr R4 11 = Z_to_bv 64 pa).
  { rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs. exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) E3_9). }
  assert (E4_20 : getr R4 20 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 20 X4 eq_refl); simp_regs.
    exact (eq_trans (RP3 20 ltac:(unfold callee_saved; lia)) E3_20). }
  assert (K34 : scn_kx [2; 8; 9; 18; 19; 20] regs3 R4) by scn_tac X4.
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  assert (SRC4 : arg_s_src B L3 A3 (spZ R4) m4 pa port_a).
  { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L3 A3 m4 md3 _ _ b pa port_a
             (spZ R4) SI4 RA).
    - rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP4. lia.
    - exact SA3. }
  destruct (sarg_facts B L3 A3 (spZ R4) m4 pa port_a SRC4) as (NO4 & LX4).
  apply (sinv_arg_sn B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L3 A3 m4 md3 R
           REC_CONNECT [sarg verb; canon line] _ b R4 pa port_a _ SI4).
  { cbn [length]. lia. }
  { rewrite E4_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP4. lia. }
  { rewrite E4_4. exact HTP. }
  { exact E4_10. }
  { exact E4_11. }
  { exact SRC4. }
  { rewrite EQB3, EQB2. eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono, sb_malloc_mono, sb_malloc_mono; exact BLE1|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX in *. lia. }
  intros L4 A4 regs4 m5 md4 p3 SI5 EQB4 INI4 PR4 FK4.
  cbn [app] in SI5.
  rewrite E4_1.
  pose proof SI5 as (RJ5 & _). pose proof RJ5 as (HM5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (K4r : scn_kx [2; 8; 9; 18; 19; 20] R4 regs4) by exact (scn_kx_of_pres _ _ _ PR4).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. cbn in Hi.
    destruct (FK4 (bv_unsigned sp - 48 + i) ltac:(rewrite SP4; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply scn_mid4. }
  intros ms5 (can5 & -> & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x16794) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs. exact (eq_trans (PR4 2 ltac:(unfold callee_saved; lia)) E4_2). }
  assert (E5_4 : getr R5 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X5 eq_refl); simp_regs. exact (eq_trans (PR4 4 ltac:(unfold callee_saved; lia)) E4_4). }
  assert (E5_10 : getr R5 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs.
    exact (eq_trans (PR4 20 ltac:(unfold callee_saved; lia)) E4_20). }
  assert (E5_11 : getr R5 11 = Z_to_bv 64 pb).
  { rewrite (getr_of_eqv _ _ 11 X5 eq_refl); simp_regs. exact (eq_trans (PR4 8 ltac:(unfold callee_saved; lia)) E4_8). }
  assert (E5_20 : getr R5 20 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 20 X5 eq_refl); simp_regs.
    exact (eq_trans (PR4 20 ltac:(unfold callee_saved; lia)) E4_20). }
  assert (K45 : scn_kx [2; 8; 9; 18; 19; 20] regs4 R5) by scn_tac X5.
  assert (SP5 : spZ R5 = bv_unsigned sp - 48) by (unfold spZ; rewrite E5_2; apply unsigned_lit; lia).
  assert (SRC5 : arg_s_src B L4 A4 (spZ R5) m5 pb port_b).
  { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L4 A4 m5 md4 _ _ b pb port_b
             (spZ R5) SI5 RA).
    - rewrite SP5. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP5. lia.
    - exact SA4. }
  destruct (sarg_facts B L4 A4 (spZ R5) m5 pb port_b SRC5) as (NO5 & LX5).
  apply (sinv_arg_sn B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L4 A4 m5 md4 R
           REC_CONNECT [sarg verb; canon line; sarg port_a] _ b R5 pb port_b _ SI5).
  { cbn [length]. lia. }
  { rewrite E5_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP5. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP5. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP5. lia. }
  { rewrite E5_4. exact HTP. }
  { exact E5_10. }
  { exact E5_11. }
  { exact SRC5. }
  { rewrite EQB4, EQB3, EQB2. eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono, sb_malloc_mono, sb_malloc_mono, sb_malloc_mono; exact BLE1|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX in *. lia. }
  intros L5 A5 regs5 m6 md5 p4 SI6 EQB5 INI5 PR5 FK5.
  cbn [app] in SI6.
  rewrite E5_1.
  assert (R5_2 : getr regs5 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E5_2).
  assert (R5_20 : getr regs5 20 = Z_to_bv 64 e) by exact (eq_trans (PR5 20 ltac:(unfold callee_saved; lia)) E5_20).
  assert (K5r : scn_kx [2; 8; 9; 18; 19; 20] R5 regs5) by exact (scn_kx_of_pres _ _ _ PR5).
  assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m5); [exact FR5|]. intros i Hi. cbn in Hi.
    destruct (FK5 (bv_unsigned sp - 48 + i) ltac:(rewrite SP5; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  pose proof SI6 as (RJ6 & GR6 & ON6 & B16 & B26 & RA6 & F186 & RS6).
  pose proof RJ6 as (HM6 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM6) as (Hh6 & Hl6 & _).
  eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs5 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact R5_2.
    rewrite Q2.
    eapply scn_tail; [exact FR6 | lia]. }
  intros ms6 (can6 & -> & EQ6).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ6 eq_refl eq_refl) as (R6 & -> & X6).
  assert (E6_1 : getr R6 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_2 : getr R6 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_10 : getr R6 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X6 eq_refl); simp_regs; exact R5_20).
  assert (E6_11 : getr R6 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_12 : getr R6 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X6 eq_refl); simp_regs; reflexivity).
  assert (K56 : scn_kx [2; 8; 9; 18; 19; 20] regs5 R6) by scn_tac X6.
  assert (RP6 : regs_preserved regs R6).
  { apply (scn_kx_pres [2; 8; 9; 18; 19; 20]).
    - apply (scn_kx_trans _ regs R1 R6 K01).
      apply (scn_kx_trans _ R1 regs1 R6 K1r).
      apply (scn_kx_trans _ regs1 R2 R6 K12).
      apply (scn_kx_trans _ R2 regs2 R6 K2r).
      apply (scn_kx_trans _ regs2 R3 R6 K23).
      apply (scn_kx_trans _ R3 regs3 R6 K3r).
      apply (scn_kx_trans _ regs3 R4 R6 K34).
      apply (scn_kx_trans _ R4 regs4 R6 K4r).
      apply (scn_kx_trans _ regs4 R5 R6 K45).
      exact (scn_kx_trans _ R5 regs5 R6 K5r K56).
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X6 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (SP6 : spZ R6 = spZ regs) by (unfold spZ; rewrite E6_2; reflexivity).
  pose proof (scn_shape m6 RA6) as SHP.
  assert (BLE5 : sb_le (sb_shift b A A5)
                   (sb_malloc (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length (sarg verb)) + 1))
                      (Z.of_nat (length line) + 1)) (Z.of_nat (length (sarg port_a)) + 1))
                      (Z.of_nat (length (sarg port_b)) + 1))).
  { rewrite EQB5, EQB4, EQB3, EQB2. apply sb_malloc_mono, sb_malloc_mono, sb_malloc_mono, sb_malloc_mono. exact BLE1. }
  assert (ROOM6 : room_slots
            (sb_malloc (sb_malloc (sb_shift b A A5)
               (Z.of_nat (length (snd (rec_answer
                  (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
                  (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true))) + 1))
               (Z.of_nat (length (snd (rec_answer
                  (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
                  (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true))) + 1))
            (Z.of_nat (length (snd (rec_answer
               (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
               (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true))) + 1)).
  { eapply room_slots_mono; [| | exact ROOM].
    - apply sb_malloc_mono, sb_malloc_mono. exact BLE5.
    - unfold LMAX. lia. }
  rewrite <- SEGS in GR6, RA6, F186, SHP.
  pose proof (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK 12384 L A regs mem md O L5 A5 R6 m6 md5
                (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b]) _ b _ (sb_shift b A A5) e
                0x10417 (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true
                PRE AK RJ6 E6_1 SP6 RP6 E6_10 E6_11 ltac:(rewrite E6_12; reflexivity) GR6 (fun _ => SHP)
                (fun _ _ => ans_entry_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b] HN)
                FRM F186 RA6 RS6 eq_refl BLE5 ROOM6 ON6 B16 B26) as TR0.
  rewrite SEGS in TR0.
  eapply SR_mono; [exact TR0|].
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_connect_m R verb line port_a port_b)), O',
    (snd (sup_connect_m R verb line port_a port_b)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  repeat (split; [assumption|]). exact RES'.
Qed.

End P.
