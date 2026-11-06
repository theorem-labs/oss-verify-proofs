(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan): the inner walk, L02_inner of
   U/Prog/Seg/L02D.v, from its callee contracts K_L02. The walk 0x13aac .. 0x13b28 is here; from the
   join 0x13b28 on it is U/Prog/Seg/L02W_back.v (l02_back).
   - 0x13aac `beqz a0` (t <> 0, not taken); s7 = t; s10 = n = length s: n <> 0 copies the text, memcpy(t, src, n)
     (0x13ac4), n = 0 skips it;
   - 0x13ac8-0x13ad8: the trap 0x13acc (`not a0,s7; bltu a0,s10`: t + n < 2^64, not taken), s10 = t + n, the NUL
     `sb zero,0(s10)`; a0 = lb << 56;
   - 0x13adc `bltz a0`: lb >= 128: memset(longl, 'L', 120) (0x13b18), s9 = longl; else s10 = nfiles, lb = 0: s9 = 0;
     else snprintf(sp + 0x60, 40, "reac-pw.conf.d/%u-x.conf", lb) (0x13afc, snprintf_m_contract with the model
     equation of Prog/Seg/L02W_lab.v), s9 = sp + 0x60; s10 = nfiles on every path; to 0x13b28.
   Every memory the walk reaches differs from 0x13aac's only inside the text block, longl's 120 bytes, the callee
   stack [S - 65472, S - 240) and the label buffer [S - 144, S - 104) (W_front), all inside L02_W.
   Segment lemma of LLVMFuzzerTestOneInput's walk: L02's inner walk, UBSan. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c printf_facts_c
  printf_model_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require memcpy_c snprintf_m_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M L02W_lab.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import L02D L02W_inv L02W_back.
Import ListNotations.
Open Scope Z_scope.

(** ** Words *)
Lemma lxor_ones : forall t, 0 <= t < 2 ^ 64 -> Z.lxor t 18446744073709551615 = 18446744073709551615 - t.
Proof.
  intros t Ht.
  assert (E : Z.lxor t 18446744073709551615 = (Z.lnot t) mod 2 ^ 64).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec.
    replace 18446744073709551615 with (Z.ones 64) by reflexivity.
    destruct (Z_lt_le_dec n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
      destruct (Z.testbit t n); reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. rewrite xorb_false_r.
      rewrite <- (Z.mod_small t (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite E. unfold Z.lnot.
  replace (Z.pred (- t)) with ((18446744073709551615 - t) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(** ** Memory *)
(** The first n bytes of a writable block. *)
Lemma rw_prefix : forall m a k j n, rw_cells rsegs m a [CB k j] -> (n <= k)%nat ->
  exists j', length j' = n /\ rw_cells rsegs m a [CB n j'].
Proof.
  intros m a k j n [[(Lj & _) B] (W0 & W1 & W)] Hn. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  cbn [cell_wf] in Lj.
  exists (firstn n j). split; [rewrite length_firstn; lia|]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (bytes_at_sub m a j 0 n B ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H.
  - cbn [cells_size csize] in *. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
Qed.

Ltac mem_dst H :=
  destruct H as (MI & TM & SSP & CI & WI & HS16 & HSlo & HShi & ST & HROM & F28 & F30 & F38 & F40 & F48 & F50 &
    Hc0 & Hc16 & Hcn & Hcb & Hm0 & Hm16 & Hmn & Hmb & Ht0 & Ht16 & Htn & Htb & Hnt & Atm & Atc & Amc & Atl & Aml &
    Acl & RC0 & WRC & MC0 & WRM & SLM & TJ & SLT & SRC & Ast & LJ & LSL).

(** The memory facts at 0x13aac. *)
Lemma env0 : forall S c mm t nt src nf s rc mc m, L02_mem S c mm t nt src nf s rc mc m -> l02_env S c mm nf m.
Proof.
  intros S c mm t nt src nf s rc mc m H.
  mem_dst H.
  clear - MI TM SSP CI WI HSlo HShi ST F28 F30 F38 F40 F48 F50 WRC WRM SLM Hm16.
  unfold L02_FRAME in *.
  unfold l02_env. refine (conj MI (conj TM (conj SSP (conj CI (conj WI _))))).
  split; [destruct (stk_split rsegs m (S - 65536) (S - 65472) S ST ltac:(lia)) as [_ H1];
          destruct (stk_split rsegs m (S - 65472) (S - 240) S H1 ltac:(lia)) as [H2 _]; exact H2|].
  refine (conj F28 (conj F30 (conj F38 (conj F40 (conj F48 (conj F50 (conj WRC (conj WRM _)))))))).
  destruct SLM as (sl & B & L). exists (firstn 4 sl). split.
  - pose proof (bytes_at_sub m (mm + SEG_M_SIZE) sl 0 4 B) as H. rewrite Z.add_0_r in H. apply H.
    destruct (mod16_ex _ Hm16) as (k & ->). unfold SEG_M_SIZE in *.
    replace (- (16 * k + 9236)) with (4 + (- 2 * k - 1155) * 8) in L by lia. rewrite Z.mod_add in L by lia.
    cbn in L. lia.
  - rewrite length_firstn. destruct (mod16_ex _ Hm16) as (k & ->). unfold SEG_M_SIZE in *.
    replace (- (16 * k + 9236)) with (4 + (- 2 * k - 1155) * 8) in L by lia. rewrite Z.mod_add in L by lia.
    cbn in L. lia.
Qed.

(** The format "reac-pw.conf.d/%u-x.conf" in .rodata at L02_FMT. *)
Lemma fmt_ro : ro_bytes_b rsegs L02_FMT (pf_bytes (F_label ++ [0])) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fmt_len : length (F_label ++ [0]) = 25%nat.
Proof. reflexivity. Qed.

Lemma fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m L02_FMT (pf_bytes (F_label ++ [0])).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI | unfold L02_FMT; lia | |].
  - unfold pf_bytes. rewrite length_map, fmt_len. unfold L02_FMT. lia.
  - apply ro_bytes_b_sound. exact fmt_ro.
Qed.

(** Branch tactics: ntk for a branch the facts refute (not taken), tkn for one they force. *)
Ltac ntk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia
      | clear K ]
  | _ => idtac end.
Ltac tkn := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ clear K
      | exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia ]
  | _ => idtac end.

(** A condition with no variable left: compute it. *)
Ltac if_closed := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in
      lazymatch v with
      | true => replace cnd with true by (vm_compute; reflexivity)
      | false => replace cnd with false by (vm_compute; reflexivity)
      end; cbv iota
  end.

(** A load of one of main's frame cells. *)
Lemma rd8f : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v B.
  pose proof (bytes_at_read rsegs m a (le8 v) 0 8 B ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal.
Qed.

(** ** The walk *)
Section Front.
Variables (S c mm t nt src x1 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
  (gp tp s3 : word) (m0 : word -> option byte).
Hypothesis HK : K_L02.
Hypothesis HMEM : L02_mem S c mm t nt src nf s rc mc m0.
Hypothesis HMD : L02_model s lb rc mc.
Hypothesis Hf : 0 <= f < nf.
Hypothesis Hnf : nf <= 4.

Local Abbreviation s2 := (bv_not (Z_to_bv 64 mm)).
Local Abbreviation Post := (L02_post S c mm t nt x1 x6 f nf lb s rc mc ret (Z_to_bv 64 (S - 240)) gp tp
  s2 s3 (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 (mm + MC_N)) m0).

Lemma fr_static : l02_static S c mm t nt src s.
Proof. exact (l02_static_of S c mm t nt src nf s rc mc m0 lb HMEM HMD). Qed.

Lemma fr_J : L02_J S c mm t nt x1 x6 f nf lb s rc mc ret (Z_to_bv 64 (S - 240)) gp tp s2 s3 (Z_to_bv 64 33)
  (Z_to_bv 64 x6) (Z_to_bv 64 (mm + MC_N)) m0.
Proof.
  exact (l02_back HK S c mm t nt src x1 x6 f nf lb s rc mc ret _ gp tp _ s3 _ _ _ m0 fr_static HMD eq_refl eq_refl
    eq_refl eq_refl Hf Hnf eq_refl).
Qed.

Lemma fr_bounds : 2 ^ 40 + 65536 <= S <= 2 ^ 47 /\ 0 < c /\ c + 16616 <= S - 65536 /\ 0 < mm /\
  mm + 9236 <= S - 65536 /\ 0 < t /\ t + nt <= S - 65536 /\ nt = Z.of_nat (length s) + 1 /\ 0 <= src /\
  Z.of_nat (length s) <= 65535 /\ (t + nt <= 0x10000 \/ 0x55000 <= t).
Proof.
  pose proof fr_static as H. st_dst H.
  pose proof (nat_le_65535 _ HsL).
  pose proof (noimg_bound t nt Htn ltac:(clear - Ht0; lia) ltac:(clear - Hnt; lia)) as Ti.
  clear - HSlo HShi Hc0 Hcb Hm0 Hmb Ht0 Htb Hnt Hsrc Ti H. unfold SEG_C_SIZE, SEG_M_SIZE in *. lia.
Qed.

(** The writes of the walk to 0x13b28. *)
Definition W_front : list ivl :=
  [(t, t + nt); (0x33460, 0x33460 + 120); (S - 65472, S - 240); (S - 144, S - 104)].

Lemma W_front_all : sub_fp W_front (A_all S c mm t nt).
Proof. unfold W_front, A_all. clear HK HMEM HMD Hf Hnf. fp_tac. Qed.

(** The text block and its slack: outside longl, the stack and the label buffer. *)
Lemma txt_out : forall x, t <= x < t + nt + (- (t + nt)) mod 8 ->
  outside [(0x33460, 0x33460 + 120); (S - 65472, S - 240); (S - 144, S - 104)] x.
Proof.
  intros x Hx. pose proof fr_bounds as (BS & _ & _ & _ & _ & Bt0 & Btb & _ & _ & _ & Ti).
  destruct (rup8 (t + nt)) as (R & q & Eq). cbn [outside]. repeat split; try exact I; lia.
Qed.

(** The blocks are outside W_front. *)
Lemma c_out : forall x, c <= x < c + SEG_C_SIZE -> outside W_front x.
Proof.
  intros x Hx. pose proof fr_static as H. pose proof (st_num _ _ _ _ _ _ _ H) as HN. num_dst HN.
  clear - Hx NAtc NAcl Ncb Nc0 Nt0 Ntb Nnt NSlo. cbn [W_front outside]. repeat split; try exact I; lia.
Qed.
Lemma m_out : forall x, mm <= x < mm + SEG_M_SIZE -> outside W_front x.
Proof.
  intros x Hx. pose proof fr_static as H. pose proof (st_num _ _ _ _ _ _ _ H) as HN. num_dst HN.
  clear - Hx NAtm NAml Nmb Nm0 Nt0 Ntb Nnt NSlo. cbn [W_front outside]. repeat split; try exact I; lia.
Qed.

(** What the join needs of the memory there, from a memory m that differs from m0 inside W_front. *)
Lemma fr_join : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lp : Z),
  frm0 fc -> munch W_front m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (S - 65472) (S - 240) -> txt_at t s m -> lab_ok S lp (label_of lb) m ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) (Z_to_bv 64 lb)
             (Z_to_bv 64 lp) (Z_to_bv 64 nf) (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b28) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lp FRM MU WM MIm TMm STm TXT LAB.
  pose proof fr_static as HST. pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  pose proof HMEM as H. mem_dst H.
  refine (fr_J ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 lb) t3 t4 t5 t6 F fc m lp FRM _ WM _ TXT _ _ LAB).
  - eapply munch_weaken; [|exact MU]. eapply sub_fp_trans; [exact W_front_all | apply A_all_W].
  - exact (env_tr S c mm nf t nt m0 m W_front HN (env0 _ _ _ _ _ _ _ _ _ _ _ HMEM) MU W_front_all WM MIm TMm STm).
  - exact (rc_tr m0 m W_front c rc RC0 MU c_out).
  - exact (mc_tr m0 m W_front mm mc MC0 MU m_out).
Qed.

(** sub_fp of explicit interval lists (no destruct: the section's hypotheses stay put). *)
Ltac fp2 := unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; repeat split; try exact I; lia.

(** The text kept by a write in longl, the callee stack or the label buffer. *)
Lemma txt_keep : forall m m' W, txt_at t s m -> munch W m m' ->
  sub_fp W [(0x33460, 0x33460 + 120); (S - 65472, S - 240); (S - 144, S - 104)] -> txt_at t s m'.
Proof.
  intros m m' W (sl & B & L) MU SF. exists sl. split; [|exact L].
  pose proof fr_bounds as (_ & _ & _ & _ & _ & _ & _ & Bnt & _).
  eapply bytes_at_out; [exact B | exact MU |]. rewrite length_app, zb_length. cbn [length].
  intros x Hx. apply SF. apply txt_out. rewrite Bnt. lia.
Qed.

(** The text after its NUL: its bytes, the NUL at t + n, the block's slack from 0x13aac. *)
Lemma txt_nul : forall m1, bytes_at rsegs m1 t (zb s) ->
  munch [(t, t + nt)] m0 (write_to_mem m1 (wa (t + Z.of_nat (length s))) [ZERO]) ->
  txt_at t s (write_to_mem m1 (wa (t + Z.of_nat (length s))) [ZERO]).
Proof.
  intros m1 B1 MU. pose proof fr_bounds as (BS & _ & _ & _ & _ & Bt0 & Btb & Bnt & _).
  pose proof HMEM as H. mem_dst H. destruct SLT as (sl & BSL & LSL').
  pose proof (Z.mod_pos_bound (- (t + nt)) 8 ltac:(lia)) as MB.
  set (k := Z.to_nat ((- (t + nt)) mod 8)).
  assert (Hk : Z.of_nat k = (- (t + nt)) mod 8) by (unfold k; lia).
  clearbody k.
  pose proof (bytes_at_sub m0 (t + nt) sl 0 k BSL ltac:(lia)) as B0. rewrite Z.add_0_r in B0.
  cbn [skipn] in B0.
  exists (firstn k sl). split.
  - apply bytes_at_app. split.
    + eapply bytes_at_write_other; [exact B1 | lia | cbn [length]; lia | rewrite zb_length; lia].
    + replace (ZERO :: firstn k sl) with ([ZERO] ++ firstn k sl) by reflexivity.
      apply bytes_at_app. rewrite zb_length. split.
      * apply bytes_at_write_same; cbn [length]; lia.
      * cbn [length]. replace (t + Z.of_nat (length s) + Z.of_nat 1) with (t + nt) by (cbn; lia).
        eapply bytes_at_out; [exact B0 | exact MU |]. intros x Hx. cbn [outside]. split; [lia | exact I].
  - rewrite length_firstn. replace (t + Z.of_nat (length s) + 1) with (t + nt) by lia. lia.
Qed.

(** The memory after the NUL: the frame and the stack region as at 0x13aac. *)
Lemma m2_env : forall m2, munch [(t, t + nt)] m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 ->
  MemNorm.task_mem rsegs m2 -> l02_env S c mm nf m2 /\ stk rsegs m2 (S - 65536) S.
Proof.
  intros m2 MUa WMa MIa TMa. pose proof fr_bounds as (BS & _ & _ & _ & _ & Bt0 & Btb & _).
  pose proof HMEM as H. mem_dst H.
  assert (ST2 : stk rsegs m2 (S - 65536) S).
  { eapply stk_transport_disjoint; [exact ST | exact MUa | exact WMa |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [|exact ST2].
  pose proof fr_static as HST. pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  destruct (stk_split rsegs m2 (S - 65536) (S - 65472) S ST2 ltac:(lia)) as [_ H1].
  destruct (stk_split rsegs m2 (S - 65472) (S - 240) S H1 ltac:(lia)) as [H2 _].
  refine (env_tr S c mm nf t nt m0 m2 [(t, t + nt)] HN (env0 _ _ _ _ _ _ _ _ _ _ _ HMEM) MUa _ WMa MIa TMa H2).
  unfold A_all. fp2.
Qed.

Lemma bit7 : forall b, 0 <= b < 256 -> bv_lts (Z_to_bv 64 (Z.shiftl b 56)) (Z_to_bv 64 0) = (128 <=? b).
Proof.
  intros b H. unfold bv_lts. rewrite !Z_to_bv_signed. rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (0 + 2 ^ 63)) by lia.
  destruct (Z_lt_le_dec b 128) as [L|L].
  - rewrite (Z.mod_small (b * 2 ^ 56 + 2 ^ 63)) by lia.
    replace (128 <=? b) with false by (symmetry; apply Z.leb_gt; lia). apply Z.ltb_ge. lia.
  - replace ((b * 2 ^ 56 + 2 ^ 63) mod 2 ^ 64) with (b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64).
    + replace (128 <=? b) with true by (symmetry; apply Z.leb_le; lia). apply Z.ltb_lt. lia.
    + first [apply Z.mod_unique with (q := 1) | symmetry; apply Z.mod_unique with (q := 1)]; [left; lia | lia].
Qed.

Lemma pf_bytes_nul : forall l, pf_bytes (l ++ [0]) = zb l ++ [ZERO].
Proof. intros l. unfold pf_bytes, zb. rewrite map_app. reflexivity. Qed.

(** A numeric side condition: lengths of literal lists, unsigned literals, then lia. *)
Ltac nl := cbn [length Z.of_nat]; repeat rewrite unsigned_lit by lia; lia.

(** ** 0x13adc - 0x13b24: the three label paths *)
Lemma walk_lab : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 : word) (F : bvmap 5 word) (fc : bv 32)
    (m2 : word -> option byte),
  frm0 fc -> munch [(t, t + nt)] m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 -> MemNorm.task_mem rsegs m2 ->
  txt_at t s m2 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 x1) (Z_to_bv 64 (Z.shiftl lb 56))
             a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t)
             (Z_to_bv 64 lb) s9 (Z_to_bv 64 (t + Z.of_nat (length s))) (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13adc) fc None m2 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 F fc m2 FRM MU2 WM2 MI2 TM2 TX2.
  pose proof fr_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Bnt & Bsrc & BL & Ti).
  pose proof HMD as (HsF & HsL & Hlb & R1 & R2 & R3 & M1 & M2 & M3).
  pose proof HK as (_ & HSN & HMS & _).
  pose proof HMEM as H. mem_dst H. clear F28 F30 F38 F40 F48 F50.
  destruct (m2_env m2 MU2 WM2 MI2 TM2) as (ENV2 & STF).
  pose proof ENV2 as ENV2'. env_dst ENV2'. destruct ESSP as (G1 & g & G2).
  pose proof (rd8f m2 _ _ F40) as R40.
  (* bltz a0: bit 7 of lb *)
  zstep. rewrite bit7 by lia.
  destruct (Z_lt_le_dec lb 128) as [Llo|Lhi].
  - replace (128 <=? lb) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
    (* 0x13ae0 ld s10,0x40(sp); beqz s8 *)
    zstep. zstep. rewrite eqb_lits by lia.
    destruct (Z.eq_dec lb 0) as [Z0|Z0].
    + (* lb = 0: s9 = 0 *)
      replace (lb =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      zstep.
      eapply fr_join; [exact FRM | | exact WM2 | exact MI2 | exact TM2 | exact EST | exact TX2 |].
      * eapply munch_weaken; [|exact MU2]. unfold W_front. fp2.
      * rewrite Z0, label_of_zero. reflexivity.
    + (* 0 < lb < 128: snprintf(sp + 0x60, 40, fmt, lb) *)
      replace (lb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      destruct (lab_txt_ok lb ltac:(lia)) as (LT & LF).
      destruct (stk_rw m2 (S - 65536) S (S - 144) 40 STF ltac:(lia) ltac:(lia)) as (jk & RWk).
      pose proof (rd8f m2 _ _ F30) as R30. unfold L02_FMT in R30.
      do 6 zstep.
      eapply evt_cut.
      { eapply (HSN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (S - 65472) g F_label
          [Printf_model.PA_u lb] (Z.of_nat (length (lab_txt lb))) (lab_txt lb) jk []);
          cbv zeta; try rewrite !unsigned_lit by lia.
        - exact (fmt_at m2 MI2).
        - unfold snprintf_c.RO_LO. lia.
        - unfold snprintf_c.RO_END. assert (LFl : length F_label = 24%nat) by reflexivity. rewrite LFl.
          cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
        - exact (proj1 lab_fmt_good).
        - exact (proj2 lab_fmt_good).
        - cbn [pm_args_ok app pm_arg_ok]. split; [|exact I]. split; [lia|].
          rewrite ?unsigned_lit by lia. apply Z.mod_small. lia.
        - cbn [u64s]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia.
        - nl.
        - nl.
        - exact (lab_pm lb ltac:(lia)).
        - repeat rewrite unsigned_lit by lia. replace (S - 240 + 96) with (S - 144) by lia. exact RWk.
        - nl.
        - nl.
        - nl.
        - repeat rewrite unsigned_lit by lia. apply noimg_hi. lia.
        - repeat rewrite unsigned_lit by lia. exact EST.
        - unfold SNPRINTF_K. nl.
        - unfold IMG_END. nl.
        - nl.
        - exact FRM.
        - exact MI2.
        - exact TM2.
        - exact G1.
        - exact G2. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc3 &
        m3 & -> & MU3 & WM3 & MI3 & TM3 & FRM3 & _ & ST3 & B3).
      rewrite ret_pc_even by (try lia; reflexivity).
      repeat (rewrite unsigned_lit in MU3 by lia). repeat (rewrite unsigned_lit in ST3 by lia).
      repeat (rewrite unsigned_lit in B3 by lia).
      change (firstn (Z.to_nat (40 - 1)) (lab_txt lb)) with (snprintf_s 40 F_label [AI lb]) in MU3, B3.
      rewrite lab_snprintf in MU3, B3 by lia. rewrite pf_bytes_nul in B3.
      (* 0x13b00 j 0x13b28 *)
      zstep.
      eapply fr_join; [exact FRM3 | | exact (wmono_trans _ _ _ _ WM2 WM3) | exact MI3 | exact TM3 | exact ST3 | | ].
      * eapply munch_trans; [eapply munch_weaken; [|exact MU2] | eapply munch_weaken; [|exact MU3]];
          unfold W_front; fp2.
      * eapply txt_keep; [exact TX2 | exact MU3 | fp2].
      * rewrite label_of_mid by lia. unfold lab_ok. split; [lia|]. split; [|split; [exact LF | right; lia]].
        set (len := Z.of_nat (length (lab_txt lb))).
        pose proof (Z.mod_pos_bound (- (S - 240 + 96 + len + 1)) 8 ltac:(lia)) as MB.
        set (k := Z.to_nat ((- (S - 240 + 96 + len + 1)) mod 8)).
        assert (Hk : Z.of_nat k = (- (S - 240 + 96 + len + 1)) mod 8) by (unfold k; lia).
        clearbody k.
        pose proof RWk as [[_ Bk] _]. cbn [cells_bytes cbytes] in Bk. rewrite app_nil_r in Bk.
        destruct RWk as [[Wk _] _]. cbn [cells_wf cell_wf] in Wk. destruct Wk as [Lk _].
        pose proof (bytes_at_sub m2 (S - 144) jk (length (lab_txt lb) + 1) k Bk ltac:(unfold len in *; lia))
          as Bs.
        exists (firstn k (skipn (length (lab_txt lb) + 1) jk)). split.
        -- replace (zb (lab_txt lb) ++ ZERO :: firstn k (skipn (length (lab_txt lb) + 1) jk))
             with ((zb (lab_txt lb) ++ [ZERO]) ++ firstn k (skipn (length (lab_txt lb) + 1) jk))
             by (rewrite <- app_assoc; reflexivity).
           apply bytes_at_app. split; [exact B3|].
           rewrite length_app, zb_length. cbn [length].
           replace (S - 240 + 96 + Z.of_nat (length (lab_txt lb) + 1))
             with (S - 144 + Z.of_nat (length (lab_txt lb) + 1)) by lia.
           eapply bytes_at_out; [exact Bs | exact MU3 |]. rewrite length_firstn, length_skipn.
           intros x Hx. cbn [outside]. unfold len in *. repeat split; try exact I; lia.
        -- rewrite length_firstn, length_skipn. unfold len in *. lia.
  - (* lb >= 128: memset(longl, 'L', 120) *)
    replace (128 <=? lb) with true by (symmetry; apply Z.leb_le; lia). cbv iota.
    destruct LJ as (lj & LJ).
    assert (LJ2 : rw_cells rsegs m2 0x33460 [CB 120 lj]).
    { eapply rw_cells_transport; [exact LJ | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize].
      unfold apart, SA, SEG_UBSAN in Atl. cbn [sa_longl] in Atl. split; [lia | exact I]. }
    do 6 zstep.
    eapply evt_cut.
    { eapply HMS with (junk := lj); rewrite ?unsigned_lit by lia; [exact LJ2 | exact MI2]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 &
      WM3 & MI3 & RW3).
    rewrite ret_pc_even by (try lia; reflexivity).
    repeat (rewrite unsigned_lit in MU3 by lia). repeat (rewrite unsigned_lit in RW3 by lia).
    assert (MU03 : munch [(t, t + nt); (0x33460, 0x33460 + 120)] m0 m3).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU2] | eapply munch_weaken; [|exact MU3]]; fp2. }
    assert (R40' : ov_read_bytes rsegs m3 (wa (S - 240 + 64)) 8 = Some (le8 (Z_to_bv 64 nf))).
    { apply rd8f. eapply bytes_at_out; [exact F40 | exact MU3 |]. rewrite length_le8.
      intros x Hx. cbn [outside]. split; [lia | exact I]. }
    clear R40.
    (* 0x13b1c ld s10,0x40(sp); j 0x13b28 *)
    zstep. zstep.
    eapply fr_join; [exact FRM | | exact (wmono_trans _ _ _ _ WM2 WM3) | exact MI3 | | | | ].
    + eapply munch_weaken; [|exact MU03]. unfold W_front. fp2.
    + eapply task_mem_out; [exact TM2 | exact MU3|]. intros x Hx. rewrite TASK_SIZE_val.
      destruct (Z_lt_le_dec x (0x33460 + 120)) as [L|L]; [left; lia|]. right. cbn [outside]. split; [lia | exact I].
    + eapply stk_transport_disjoint; [exact EST | exact MU3 | exact WM3 |]. cbn [disjoint_from]. split; [lia | exact I].
    + eapply txt_keep; [exact TX2 | exact MU3 | fp2].
    + rewrite label_of_hi by lia. destruct longl_ok as (LL & LF).
      destruct LSL as (sl & BSL & LSLn).
      unfold lab_ok. split; [lia|]. split; [|split; [exact LF | left; rewrite LL; lia]].
      exists sl. split.
      * apply bytes_at_app. split.
        -- pose proof RW3 as [[_ Bl] _]. cbn [cells_bytes cbytes] in Bl. rewrite app_nil_r in Bl.
           replace (zb longl) with (repeat (Z_to_bv 8 (76 mod 256)) (Z.to_nat 120)) by reflexivity. exact Bl.
        -- rewrite zb_length, LL. unfold SA, SEG_UBSAN in BSL. cbn [sa_longl] in BSL.
           eapply bytes_at_out; [exact BSL | exact MU03 |]. intros x Hx. cbn [outside]. cbn [length] in Hx.
           unfold apart, SA, SEG_UBSAN in Atl. cbn [sa_longl] in Atl. repeat split; try exact I; lia.
      * rewrite LSLn, LL. reflexivity.
Qed.

(** ** 0x13ac8 - 0x13ad8: the wrap trap, the NUL *)
Lemma walk_nul : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 : word) (F : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte),
  frm0 fc -> munch [(t, t + Z.of_nat (length s))] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
  bytes_at rsegs m1 t (zb s) ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) (Z_to_bv 64 lb) s9
             (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ac8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 F fc m1 FRM MU1 WM1 MI1 TX1.
  pose proof fr_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Bnt & Bsrc & BL & Ti).
  pose proof HMD as (HsF & HsL & Hlb & R1 & R2 & R3 & M1 & M2 & M3).
  (* not a0,s7; bltu a0,s10: t + n < 2^64, not taken *)
  zstep. rewrite lxor_ones by lia.
  zstep. unfold bv_ltu. rewrite !unsigned_lit by lia. ntk.
  (* add s10,s7,s10; slli a0,s8,0x38 *)
  zstep. zstep.
  (* sb zero,0(s10): the NUL at t + n *)
  pose proof HMEM as H. mem_dst H. destruct TJ as (tj & [_ WT]).
  cbn [cells_size csize] in WT. rewrite Nat.add_0_r, Z2Nat.id in WT by lia.
  pose proof (wr_at_transport rsegs m0 m1 t nt WT WM1) as WT1.
  assert (HS : store_ok rsegs m1 (wa (t + Z.of_nat (length s))) 1 = true).
  { apply (wr_at_store_ok rsegs m1 t nt); [exact WT1 | lia | lia]. }
  zstep.
  change (le1 (Z_to_bv 64 0)) with [ZERO].
  change (Z_to_bv 64 (t + Z.of_nat (length s))) with (wa (t + Z.of_nat (length s))).
  assert (MUs : munch [(t + Z.of_nat (length s), t + Z.of_nat (length s) + 1)] m1
                  (write_to_mem m1 (wa (t + Z.of_nat (length s))) [ZERO])).
  { exact (munch_store m1 (t + Z.of_nat (length s)) [ZERO] ltac:(lia) ltac:(cbn [length]; lia)). }
  assert (MU2 : munch [(t, t + nt)] m0 (write_to_mem m1 (wa (t + Z.of_nat (length s))) [ZERO])).
  { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MUs]]; fp2. }
  apply walk_lab; [exact FRM | exact MU2 | exact (wmono_write rsegs m0 m1 _ _ WM1) | | | ].
  - exact (mem_inv_store rsegs m1 _ [ZERO] MI1 HS).
  - eapply task_mem_out; [exact TM | exact MU2|]. intros x Hx. rewrite TASK_SIZE_val.
    destruct (Z_lt_le_dec x (t + nt)) as [L|L]; [left; lia|]. right. cbn [outside]. split; [lia | exact I].
  - exact (txt_nul m1 TX1 MU2).
Qed.

(** ** 0x13aac - 0x13ac4: t <> 0, s7 = t, the text copy *)
Lemma walk_entry : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  frm0 fc ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 x1) (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6
             a7 s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) s7 (Z_to_bv 64 lb) (Z_to_bv 64 src)
             (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13aac) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 F fc FRM.
  pose proof fr_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Bnt & Bsrc & BL & Ti).
  pose proof HK as (HMC & _).
  pose proof HMEM as H. mem_dst H.
  (* beqz a0: t <> 0, not taken *)
  zstep. rewrite eqb_lits by lia. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  (* mv s7,a0; beqz s10 *)
  zstep. zstep. rewrite eqb_lits by lia.
  destruct (Nat.eq_dec (length s) 0) as [N0|N0].
  - (* no text bytes: no copy *)
    replace (Z.of_nat (length s) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
    apply walk_nul; [exact FRM | apply munch_refl | apply wmono_refl | exact MI |].
    split; [lia|]. rewrite zb_length, N0. split; [lia|]. intros i Hi. cbn in Hi. lia.
  - replace (Z.of_nat (length s) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    destruct TJ as (tj & TJ).
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite zb_length in BSRC.
    destruct (rw_prefix m0 t _ tj (length s) TJ ltac:(lia)) as (j' & Lj' & RWj).
    (* mv a0,s7; mv a1,s9; mv a2,s10; jal memcpy *)
    do 4 zstep.
    eapply evt_cut.
    { eapply HMC with (src := zb s) (junk := j'); rewrite ?unsigned_lit by lia.
      - exact SRC.
      - rewrite zb_length, Nat2Z.id. reflexivity.
      - rewrite Nat2Z.id. exact RWj.
      - unfold apart in Ast. lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 &
      WM1 & MI1 & RW1 & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    repeat (rewrite unsigned_lit in MU1 by lia). repeat (rewrite unsigned_lit in RW1 by lia).
    rewrite Nat2Z.id in RW1.
    apply walk_nul; [exact FRM | exact MU1 | exact WM1 | exact MI1 |].
    destruct RW1 as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1.
Qed.

End Front.

(** ** The inner walk of segment L02 *)
Theorem L02_inner_holds : K_L02 -> L02_inner.
Proof.
  intros HK. unfold L02_inner.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    S c mm t nt src x1 x6 f nf lb s rc mc ret Esp Ea0 Es11 Es2 Es5 Es0 Hf Hnf Es4 Es10 Es9 Es1 Es6 Es8 FRM HMD HMEM.
  subst. unfold L02_FRAME.
  eapply walk_entry; [exact HK | exact HMEM | exact HMD | exact Hf | exact Hnf | exact FRM].
Qed.
