(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 322 of its 506 lines of code are new or changed and 2558 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma sbr_pre :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists j0 m',
       ms' = MS (mkR (Z_to_bv 64 0x167e0) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 s1
                     (Z_to_bv 64 5) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 j0; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x167c4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sbr_mid :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x167ec) sp gp tp t0 t1 t2 s0 a0 a0 s0
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x167e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

Lemma sbr_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s1 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                                    a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x167ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' j0 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import answer_c record_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sup_broadcast_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c.

Definition sbr_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma sbr_kx_trans : forall xs R1 R2 R3, sbr_kx xs R1 R2 -> sbr_kx xs R2 R3 -> sbr_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma sbr_kx_of_pres : forall xs R R', regs_preserved R R' -> sbr_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma sbr_kx_pres : forall xs R R', sbr_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac sbr_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac sbr_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; sbr_one X|]);
  subst rr; sbr_one X.

Lemma sbr_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 213032); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 213032); [left | right]; lia.
Qed.

Lemma sbr_shape : forall m, ro_agree rsegs m -> answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
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

Lemma sbr_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma sbr_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite sbr_code_record. pose proof (resp_length (r_code R) H). lia.
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
Hypothesis ARGL : arg_line_contract B API.
Hypothesis ANS : answer_contract B API.

Lemma sbr_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma sbr_str : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
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

Theorem sup_broadcast_holds : sup_broadcast_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK REC ARGL ANS.
  unfold sup_broadcast_contract.
  intros L A regs mem md pl line R O b PRE A0 SA GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_BROADCAST_K in PRE, PRK, HCEIL, HWS, SA.
  unfold SUP_BROADCAST.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  assert (RKL : RECORD_K = 8336) by reflexivity.
  assert (AKL : ARG_LINE_K = 8272) by reflexivity.
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as HN.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & _ & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  change (snd (sup_broadcast_m R line)) with
    (snd (rec_answer (rec_record R REC_BROADCAST [canon line]) (REC_BROADCAST, [canon line]) REC_MOD_HOST_SHAPE true))
    in ROOM.
  unfold sup_broadcast_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_BROADCAST [canon line]) (REC_BROADCAST, [canon line])
                  REC_MOD_HOST_SHAPE true)) <= 16)%nat).
  { pose proof (sbr_len R REC_BROADCAST [canon line] REC_MOD_HOST_SHAPE true HCODE) as H.
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
    eapply sbr_pre; [exact ST | lia]. }
  intros ms1 (can1 & (j0 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x167e0) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact A0).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 REC_BROADCAST)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (K01 : sbr_kx [2; 8; 9] regs R1) by sbr_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  pose proof SI1 as (RJ1 & GR1a & _ & _ & _ & RA1a & F181a & RS1a).
  pose proof REC as RC. unfold record_contract in RC. rewrite SEGS in RC.
  eapply SR_bind.
  { apply (RC L A R1 m1 md REC_BROADCAST R O (sb_shift b A A)); [ | exact E1_10 | unfold REC_FN_COUNT, REC_BROADCAST; lia
      | exact GR1a | exact RA1a | exact F181a | exact RS1a].
    apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L A m1 md RECORD_K R1 RJ1).
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - lia.
    - rewrite SP1. lia.
    - rewrite SP1. lia.
    - rewrite E1_4. exact HTP. }
  intros c1 (L1 & A1 & regs1 & m2 & md1 & O1 & D & -> & POST1 & R10 & GR1 & OSUB & DIFF & PERM & OK1 & BL1 & RA1
    & F181 & INIT1 & RGN1 & NI & SBLE & RES1).
  destruct (sinv_record_post B API SEGS ERRNO_LOW AX 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b RECORD_K R1
              REC_BROADCAST L1 A1 regs1 m2 md1 O1 D SI1 ltac:(rewrite SP1; lia) ltac:(rewrite SP1; lia)
              POST1 GR1 OSUB DIFF PERM OK1 BL1 RA1 F181 INIT1 RGN1 NI SBLE RES1) as [SI2 BLE2].
  rewrite sb_shift_refl in BLE2.
  pose proof POST1 as (PM1 & _ & _ & _ & _ & RP1 & _ & HF1 & _).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF1 (bv_unsigned sp - 32 + i)) as [E W].
    - left. lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM1 Ho). lia.
    - unfold scratch_k. rewrite SP1. intros [H|H]; lia.
    - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia.
    - split; [exact E | apply W]. }
  destruct (rec_entry_at rsegs L1 A1 m2 R REC_BROADCAST [] O1 GR1) as (P0 & CA).
  pose proof CA as (_ & _ & _ & _ & NA2 & _). cbn [snd length Z.of_nat] in NA2.
  rewrite E1_1.
  destruct (mr_model B _ LAWS L1 A1 m2 md1 PM1) as (Hh1 & Hl1 & _).
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply sbr_mid. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x167ec) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32)).
  { rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs.
    exact (eq_trans (RP1 2 ltac:(unfold callee_saved; lia)) E1_2). }
  assert (E2_4 : getr R2 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs.
    exact (eq_trans (RP1 4 ltac:(unfold callee_saved; lia)) E1_4). }
  assert (E2_9 : getr R2 9 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs. exact R10. }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs. exact R10. }
  assert (E2_11 : getr R2 11 = Z_to_bv 64 pl).
  { rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs.
    exact (eq_trans (RP1 8 ltac:(unfold callee_saved; lia)) E1_8). }
  assert (K12 : sbr_kx [2; 8; 9] R1 regs1) by exact (sbr_kx_of_pres _ _ _ RP1).
  assert (K23 : sbr_kx [2; 8; 9] regs1 R2) by sbr_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 32) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2s & F182s & RS2s).
  destruct (sbr_str 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 _ O1 b pl line SI2 RA SA)
    as (slack & PR & Hp0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L1 A1 R2 m2 md1 e pl 0 line slack (sb_shift b A A1)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L1 A1 m2 md1 ARG_LINE_K R2 RJ2).
      + rewrite E2_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP2. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + lia.
      + rewrite SP2. lia.
      + rewrite SP2. lia.
      + rewrite E2_4. exact HTP.
    - exact E2_10.
    - exact E2_11.
    - exact (proj2 (proj2 ER)).
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA2.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP2. lia.
    - rewrite SP2. apply (sbr_home_lower L1 A1 (bv_unsigned sp)); [lia | exact HOME].
    - unfold iv_apart. apply (sbr_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 ER).
      + exact (proj1 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS2s.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX in *. lia.
    - exact RA2s. }
  intros c2 (L2 & A2 & R3 & m3 & md2 & -> & BK2 & UB2 & _ & RA2 & GK2 & RGN2 & ALT2).
  destruct ALT2 as [(H6 & _)|(_ & p2 & POST2 & Hp2 & _ & FB2 & BLK2 & BN2 & BS2 & BX2 & INI2 & RS2)]; [lia|].
  rewrite SEGS in RA2, BN2, BS2, BX2.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _ & HF2 & _).
  assert (F183 : f18_words rsegs m3).
  { destruct (ax_statics AX L2 A2 m3 md2 PM2) as (_ & (g & Hg & HWg) & _).
    apply (f18_words_after m2 m3 g F182s); [| exact Hg | rewrite SEGS, GRD in HWg; exact HWg].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK2 i Hi). }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 R
                REC_BROADCAST [] O1 b ARG_LINE_K R2 _ L2 A2 R3 m3 md2 (canon line) p2 (Z.of_nat (length line) + 1)
                SI2 ltac:(cbn; lia) ltac:(rewrite SP2; lia) ltac:(rewrite SP2; lia) POST2
                ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp2 FB2 BLK2 UB2 BK2 RGN2 BN2 BS2 BX2 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI2 RS2 RA2 F183) as SI3.
  cbn [app] in SI3.
  pose proof FB2 as (FBlo & FBhi & _).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF2 (bv_unsigned sp - 32 + i)) as [E W].
    - left. lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM1 Ho). lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM2 Ho). lia.
    - unfold scratch_k. rewrite SP2. intros [H|H]; lia.
    - intros Hr. cbv beta in Hr. unfold G_REC, REC_SC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact E | apply W]. }
  assert (R3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2_2).
  assert (R3_9 : getr R3 9 = Z_to_bv 64 e) by exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E2_9).
  assert (K34 : sbr_kx [2; 8; 9] R2 R3) by exact (sbr_kx_of_pres _ _ _ RP2).
  assert (BLE3 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length line) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A1 A2).
    rewrite <- (sb_shift_add (sb_shift b A A1) L1 A1 L2 A2 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  rewrite E2_1, SEGS.
  destruct (mr_model B _ LAWS L2 A2 m3 md2 PM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q3 : reg_get R3 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact R3_2.
    rewrite Q3.
    eapply sbr_tail; [exact FR3 | lia]. }
  intros ms4 (can4 & -> & EQ4).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  assert (E4_1 : getr R4 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs; exact R3_9).
  assert (E4_11 : getr R4 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_12 : getr R4 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X4 eq_refl); simp_regs; reflexivity).
  assert (K45 : sbr_kx [2; 8; 9] R3 R4) by sbr_tac X4.
  assert (RP4 : regs_preserved regs R4).
  { apply (sbr_kx_pres [2; 8; 9]).
    - apply (sbr_kx_trans _ regs R1 R4 K01).
      apply (sbr_kx_trans _ R1 regs1 R4 K12).
      apply (sbr_kx_trans _ regs1 R2 R4 K23).
      exact (sbr_kx_trans _ R2 R3 R4 K34 K45).
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X4 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (SP4 : spZ R4 = spZ regs) by (unfold spZ; rewrite E4_2; reflexivity).
  pose proof SI3 as (RJ3 & GR3 & ON3 & B13 & B23 & RA3 & F18_3 & RS3).
  pose proof (sbr_shape m3 RA3) as SHP.
  assert (ROOM3 : room_slots
            (sb_malloc (sb_malloc (sb_shift b A A2)
               (Z.of_nat (length (snd (rec_answer (rec_record R REC_BROADCAST [canon line]) (REC_BROADCAST, [canon line])
                  REC_MOD_HOST_SHAPE true))) + 1))
               (Z.of_nat (length (snd (rec_answer (rec_record R REC_BROADCAST [canon line]) (REC_BROADCAST, [canon line])
                  REC_MOD_HOST_SHAPE true))) + 1))
            (Z.of_nat (length (snd (rec_answer (rec_record R REC_BROADCAST [canon line]) (REC_BROADCAST, [canon line])
               REC_MOD_HOST_SHAPE true))) + 1)).
  { eapply room_slots_mono; [| | exact ROOM].
    - apply sb_malloc_mono, sb_malloc_mono. exact BLE3.
    - unfold LMAX. lia. }
  rewrite <- SEGS in GR3, RA3, F18_3, SHP.
  pose proof (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK 12384 L A regs mem md O L2 A2 R4 m3 md2
                (rec_record R REC_BROADCAST [canon line]) (O1 ++ [(p2, Z.of_nat (length line) + 1)]) b
                (sb_malloc b (Z.of_nat (length line) + 1)) (sb_shift b A A2) e 0x10417
                (REC_BROADCAST, [canon line]) REC_MOD_HOST_SHAPE true PRE AK RJ3 E4_1 SP4 RP4 E4_10 E4_11
                ltac:(rewrite E4_12; reflexivity) GR3 (fun _ => SHP)
                (fun _ _ => ans_entry_record R REC_BROADCAST [canon line] HN)
                FRM F18_3 RA3 RS3 eq_refl BLE3 ROOM3 ON3 B13 B23) as TR0.
  rewrite SEGS in TR0.
  eapply SR_mono; [exact TR0|].
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_broadcast_m R line)), O', (snd (sup_broadcast_m R line)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  repeat (split; [assumption|]). exact RES'.
Qed.

End P.
