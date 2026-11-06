From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecGlue RecStep answer_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma res_ok_slots_cap : forall A b, res_ok_slots A b -> sb_live b <= sb_cap b.
Proof. intros A b (_ & _ & _ & _ & _ & _ & _ & _ & (_ & H) & _). exact H. Qed.

Lemma room_slots_cap : forall b n, room_slots b n -> sb_live b + 1 <= sb_cap b.
Proof. intros b n (_ & H & _). exact H. Qed.

Lemma sptr_eq_dec : forall p q : sptr, {p = q} + {p <> q}.
Proof.
  intros [r o] [r' o']. destruct (Nat.eq_dec r r') as [Er|Er]; [|right; congruence].
  destruct (Z.eq_dec o o') as [Eo|Eo]; [left; congruence | right; congruence].
Defined.

Lemma preserved_parts : forall (regs R : bvmap 5 word),
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr R (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr R (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr R (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) -> getr R (Z_to_bv 5 18) = getr regs (Z_to_bv 5 18) ->
  regs_preserved regs R.
Proof.
  intros regs R KR E2 E8 E9 E18 r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|].
  destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  destruct (Z.eq_dec r 9) as [->|N9]; [exact E9|].
  destruct (Z.eq_dec r 18) as [->|N18]; [exact E18|].
  exact (KR r Hr N2 N8 N9 N18).
Qed.

Lemma rc_sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rc_slot_addr : forall c (i : nat), (i < 16)%nat ->
  Z_to_bv 64 (c + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3))) + 72)
  = Z_to_bv 64 (c + 72 + 56 * Z.of_nat i).
Proof.
  intros c i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma rc_cells_rebytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  rewrite Es. exact Hw.
Qed.

Lemma rc_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rc_cells_rebytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
Qed.

Lemma rc_cell8 : forall m a v, GLOB_LO <= a -> a + 8 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le8 v) -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v H1 H2 H. apply (rc_cells_rebytes _ _ [CB (length (le8 v)) (le8 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le8; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le8. reflexivity.
Qed.

Lemma rc_cells_bytes : forall m a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs).
Proof. intros m a cs [[_ H] _]. exact H. Qed.

Definition kept_ex (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma kept_ex_trans : forall xs R1 R2 R3, kept_ex xs R1 R2 -> kept_ex xs R2 R3 -> kept_ex xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma kept_ex_of_pres : forall xs R R', regs_preserved R R' -> kept_ex xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma kept_ex_pres : forall xs R R', kept_ex xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac kept_ex_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac kept_ex_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; kept_ex_one X|]);
  subst rr; kept_ex_one X.

Lemma fp_kept_trans : forall f1 f2 f3 : YK11.FPState, fp_kept f1 f2 -> fp_kept f2 f3 -> fp_kept f1 f3.
Proof. intros f1 f2 f3 [_ H1] [Z3 H2]. split; [exact Z3|]. intros r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma sb_malloc_le2 : forall b b' n n', sb_le b b' -> n <= n' -> sb_le (sb_malloc b n) (sb_malloc b' n').
Proof. intros b b' n n' H Hn. unfold sb_le, sb_malloc in *. cbn. lia. Qed.

Definition SHAPE_RESP0 : Z := 0x10417.

Lemma shape_lit_ro : forall i, 0 <= i < 7 -> ro_addr rsegs (Z_to_bv 64 (SHAPE_RESP0 + i)) = true.
Proof.
  intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
Qed.

Lemma shape_lit_at : forall m, ro_agree rsegs m -> ans_shape rsegs m SHAPE_RESP0 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA. unfold ans_shape. split; [|split; [apply no0_nz; vm_compute; reflexivity|]].
  - split; [unfold SHAPE_RESP0; lia|]. split; [cbn; unfold SHAPE_RESP0; lia|].
    intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (shape_lit_ro (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [change (length REC_MOD_HOST_SHAPE) with 6%nat; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|].
    intros i Hi. change (length REC_MOD_HOST_SHAPE) with 6%nat in Hi. apply shape_lit_ro. lia.
Qed.

Lemma inst_resp0_length : length (inst REC_MOD_HOST_SHAPE) = 6%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma rec_answer_len : forall R e x chg, r_refuse R = 0 \/ -2^31 <= r_code R < 2^31 ->
  (r_refuse R = 0 -> x = REC_MOD_HOST_SHAPE) ->
  (length (snd (rec_answer R e x chg)) <= 16)%nat.
Proof.
  intros R e x chg H Hx. unfold rec_answer. destruct (r_refuse R =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite (Hx E). cbn [snd hand_back]. rewrite inst_resp0_length. lia.
  - apply Z.eqb_neq in E. destruct H as [H|H]; [contradiction|]. cbn [snd hand_back].
    pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma rc_c4_bytes : forall m a v, rw_cells rsegs m a [C4 v] -> bytes_at rsegs m a (le4 v).
Proof. intros m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rc_c8_bytes : forall m a v, rw_cells rsegs m a [C8 v] -> bytes_at rsegs m a (le8 v).
Proof. intros m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rc_c44_bytes : forall m a v1 v2, rw_cells rsegs m a [C4 v1; C4 v2] ->
  bytes_at rsegs m a (le4 v1) /\ bytes_at rsegs m (a + 4) (le4 v2).
Proof.
  intros m a v1 v2 [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  apply bytes_at_app in Hb as [H1 H2]. rewrite length_le4 in H2. split; [exact H1 | exact H2].
Qed.

Lemma rc_ro_agree_munch : forall segs m m' W, ro_agree segs m -> munch W m m' ->
  (forall x : word, ro_addr segs x = true -> outside W (bv_unsigned x)) -> ro_agree segs m'.
Proof. intros segs m m' W H MU HO a Ha. unfold mrd. rewrite (MU a (HO a Ha)). exact (H a Ha). Qed.

Lemma ro_agree_munch_sg : forall m m' W, ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> 2 ^ 20 <= a \/ (GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)) ->
  ro_agree rsegs m'.
Proof.
  intros m m' W RA MU HW. apply (rc_ro_agree_munch rsegs m m' W RA MU). intros y Hy.
  pose proof (bv_unsigned_in_range 64 y) as Ry. unfold bv_modulus in Ry.
  destruct (RecSeq.outside_dec W (bv_unsigned y)) as [H|H]; [exact H|]. exfalso.
  destruct (HW (bv_unsigned y) Ry H) as [H1|H1].
  - rewrite <- (Z_to_bv_bv_unsigned y), ro_addr_hi in Hy by lia. discriminate.
  - pose proof (glob_ro_false (bv_unsigned y) H1) as G. unfold wa in G. rewrite Z_to_bv_bv_unsigned in G.
    rewrite G in Hy. discriminate.
Qed.

Lemma f18_munch : forall m m' W, f18_words rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> 2 ^ 20 <= a \/ (GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)) ->
  f18_words rsegs m'.
Proof.
  intros m m' W [G1 (cn & G2)] MU HW.
  assert (K : forall a, 0 <= a < 2 ^ 20 -> ~ (GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N) ->
            mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a -> writable_at rsegs m' a)).
  { intros a Ha Hg.
    assert (O : outside W a).
    { destruct (RecSeq.outside_dec W a) as [H|H]; [exact H|]. exfalso. destruct (HW a ltac:(lia) H); lia. }
    split; [exact (munch_mbyte rsegs W m m' a MU ltac:(lia) O) | exact (proj1 (munch_writable rsegs W m m' a MU ltac:(lia) O))]. }
  unfold f18_words. split.
  - apply (rw_cells_transfer rsegs m); [exact G1|]. intros i Hi. cbn in Hi.
    apply K; unfold snprintf_c.GOT_GUARD, GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia.
  - exists cn. apply (rw_cells_transfer rsegs m); [exact G2|]. intros i Hi. cbn in Hi.
    apply K; unfold snprintf_c.GUARD, GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia.
Qed.

Lemma rec_rep_entry : forall segs gr sc L A mem R O fn As,
  rec_rep segs gr sc L A mem (rec_record R fn As) O -> (length (r_calls R) <= 16)%nat ->
  records segs (blocks L A) mem (rec_entry gr sc R) fn As.
Proof.
  intros segs gr sc L A mem R O fn As H Hn.
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hl|Hg].
  - rewrite (rec_entry_lt gr sc R Hl). rewrite (rec_record_lt R fn As Hl) in H.
    apply (rec_rep_records segs gr sc L A mem _ O (length (r_calls R)) (fn, As) H).
    cbn [set_calls r_calls]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  - assert (E : length (r_calls R) = 16%nat) by lia. rewrite (rec_entry_full gr sc R E).
    rewrite (rec_record_full R fn As E) in H. exact (rec_rep_spill_records segs gr sc L A mem _ O H).
Qed.

Lemma r_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma r_calls_record_le : forall R fn As, (length (r_calls R) <= 16)%nat -> (length (r_calls (rec_record R fn As)) <= 16)%nat.
Proof.
  intros R fn As H. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E; cbn [set_calls set_spill r_calls].
  - apply Nat.ltb_lt in E. rewrite length_app. cbn [length]. lia.
  - exact H.
Qed.

Section Glob.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis FGI : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis FGO : forall L A mem md a, MR L A mem md -> in_globals frame_G a -> ~ owned B L A a.

Lemma rec_area_glob : forall a, rec_area a -> in_globals frame_G a.
Proof.
  intros a H. apply glob_in. change (Z.of_nat GLOB_N) with 1020.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, GLOB_LO in *. lia.
Qed.

Lemma blocks_out : forall Lc Ac memc mdc p k i, MR Lc Ac memc mdc -> In (p, k) (blocks Lc Ac) -> 0 <= i < k ->
  4096 <= p + i < alloc_ceiling /\ ~ in_img B (p + i).
Proof using LAWS AX.
  intros Lc Ac memc mdc p k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & E & Hq).
  cbn [fst snd] in E. injection E as <- <-.
  destruct (mr_blocks B MR LAWS Lc Ac memc mdc q k' i HM Hq Hi) as (_ & H4 & H5 & _).
  split; [lia|]. exact (ax_blocks_img AX Lc Ac memc mdc q k' i HM Hq Hi).
Qed.

Lemma fresh_rec_apart : forall q n, (forall i, 0 <= i < n -> ~ in_img B (q + i)) -> 0 < n ->
  iv_apart q n G_REC REC_SIZE /\ iv_apart q n REC_SC SC_SIZE.
Proof using FGI.
  intros q n H Hn.
  assert (G : forall lo len, (forall a, lo <= a < lo + len -> rec_area a) -> 0 < len -> iv_apart q n lo len).
  { intros lo len HR Hl. unfold iv_apart.
    destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (lo + len) q) as [D'|D']; [right; exact D'|]. exfalso.
    apply (H (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia.
    exact (proj1 (FGI _ (rec_area_glob _ (HR (Z.max q lo) ltac:(lia))))). }
  split; apply G; try (unfold REC_SIZE, SC_SIZE; lia); intros a Ha; unfold rec_area; lia.
Qed.

Lemma rec_area_low : forall a, rec_area a -> 0 <= a < 2 ^ 21.
Proof. intros a H. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in H. lia. Qed.

Lemma glob_low : forall a, in_globals frame_G a -> 0 <= a < 2 ^ 21.
Proof using SEGS FGI. intros a H. exact (in_img_low B SEGS a (proj1 (FGI a H))). Qed.

Lemma blk_out_img : forall Lc Ac memc mdc p n i, MR Lc Ac memc mdc -> In (p, n) (user_blocks Ac) -> 0 <= i < n ->
  4096 <= ptr_addr Lc p + i < alloc_ceiling /\ ~ in_img B (ptr_addr Lc p + i).
Proof using LAWS AX.
  intros Lc Ac memc mdc p n i HM Hp Hi.
  destruct (mr_blocks B MR LAWS Lc Ac memc mdc p n i HM Hp Hi) as (_ & H4 & H5 & _).
  split; [lia|]. exact (ax_blocks_img AX Lc Ac memc mdc p n i HM Hp Hi).
Qed.

Lemma rjr_munch_rec : forall K S gone L A mem md Lc Ac memc mdc memc' W,
  rjr B MR K S rec_area gone L A mem md Lc Ac memc mdc ->
  munch W memc memc' -> wmono rsegs memc memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> (S - K <= a < S) \/ rec_area a) ->
  rjr B MR K S rec_area gone L A mem md Lc Ac memc' mdc.
Proof using SEGS LAWS AX FGI FGO.
  intros K S gone L A mem md Lc Ac memc mdc memc' W R MU WM HW.
  pose proof (rjr_bounds B MR K S rec_area gone L A mem md Lc Ac memc mdc R) as (B1 & B2 & B3).
  pose proof alloc_ceiling_val as AC.
  pose proof R as (HM & HWA & _ & _ & HL & _).
  assert (IMG : forall a, rec_area a -> in_img B a) by (intros a Ha; exact (proj1 (FGI a (rec_area_glob a Ha)))).
  assert (OUTB : forall p n i, In (p, n) (user_blocks Ac) -> 0 <= i < n -> outside W (ptr_addr Lc p + i)).
  { intros p n i Hc Hi. destruct (blk_out_img Lc Ac memc mdc p n i HM Hc Hi) as [H1 H2].
    destruct (RecSeq.outside_dec W (ptr_addr Lc p + i)) as [H|H]; [exact H|]. exfalso.
    destruct (HW (ptr_addr Lc p + i) ltac:(lia) H) as [H3|H3]; [lia | exact (H2 (IMG _ H3))]. }
  apply (rjr_munch B MR SEGS LAWS K S rec_area gone L A mem md Lc Ac memc mdc memc' W R MU
           ltac:(rewrite SEGS; exact WM)).
  - intros a Ra Hn _. exact (HW a Ra Hn).
  - intros a Ra Hn Ho. destruct (HW a Ra Hn) as [H|H].
    + destruct (mr_owned_low B MR LAWS Lc Ac memc mdc a HM Ho). lia.
    + exact (FGO Lc Ac memc mdc a HM (rec_area_glob a H) Ho).
  - intros a Ha. destruct (RecSeq.outside_dec W a) as [H|H]; [exact H|]. exfalso.
    destruct (HW a ltac:(lia) H) as [H1|H1]; [lia | pose proof (rec_area_low a H1); lia].
  - intros p n i Hp Hg Hi. pose proof (rjr_in_cur B MR K S rec_area gone L A mem md Lc Ac memc mdc p n R Hp Hg) as Hc.
    rewrite <- (ptr_addr_stable A L Lc p n HWA Hp HL). exact (OUTB p n i Hc Hi).
  - intros p n i Hp Hi. destruct (mr_blocks B MR LAWS Lc Ac memc mdc p n i HM Hp Hi) as (Hpr & H4 & H5 & _).
    exact (munch_present W memc memc' (ptr_addr Lc p + i) MU ltac:(lia) (OUTB p n i Hp Hi) Hpr).
Qed.

Lemma post_k_keep : forall Kc L A regs mem md E L' A' regs' mem' md' a,
  call_post_k B MR Kc L A regs mem md E L' A' regs' mem' md' -> MR L A mem md ->
  alloc_ceiling + Kc <= spZ regs -> 0 <= Kc ->
  ((spZ regs <= a < 2 ^ 64) \/ in_globals frame_G a) -> ~ E a ->
  mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof using SEGS LAWS ERRNO_LOW FGI FGO.
  intros Kc L A regs mem md E L' A' regs' mem' md' a P HM HS HK Ha HE.
  destruct P as (PM & _ & _ & _ & _ & _ & _ & PF & _). rewrite SEGS in PF.
  pose proof alloc_ceiling_val as AC.
  destruct Ha as [Ha|Ha].
  - apply PF; [left; lia
              | intros Ho; destruct (mr_owned_low B MR LAWS L A mem md a HM Ho); lia
              | intros Ho; destruct (mr_owned_low B MR LAWS L' A' mem' md' a PM Ho); lia
              | unfold scratch_k; intros [H|H]; lia | exact HE].
  - destruct (FGI a Ha) as (I1 & _ & _ & I4). pose proof (glob_low a Ha) as GL.
    apply PF; [right; exact I1 | exact (FGO L A mem md a HM Ha) | exact (FGO L' A' mem' md' a PM Ha)
              | unfold scratch_k; intros [H|H]; [lia | exact (I4 H)] | exact HE].
Qed.

Lemma cells_post_k : forall Kc L A regs mem md E L' A' regs' mem' md' a cs,
  call_post_k B MR Kc L A regs mem md E L' A' regs' mem' md' -> MR L A mem md ->
  alloc_ceiling + Kc <= spZ regs -> 0 <= Kc ->
  rw_cells rsegs mem a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ((spZ regs <= a + i < 2 ^ 64) \/ in_globals frame_G (a + i)) /\ ~ E (a + i)) ->
  rw_cells rsegs mem' a cs.
Proof using SEGS LAWS ERRNO_LOW FGI FGO.
  intros Kc L A regs mem md E L' A' regs' mem' md' a cs P HM HS HK H HC.
  apply (rw_cells_transfer rsegs mem); [exact H|]. intros i Hi. destruct (HC i Hi) as [Ha HE].
  destruct (post_k_keep Kc L A regs mem md E L' A' regs' mem' md' (a + i) P HM HS HK Ha HE) as [K1 K2].
  split; [exact K1 | apply K2].
Qed.

Lemma bytes_post_k : forall Kc L A regs mem md E L' A' regs' mem' md' a bs,
  call_post_k B MR Kc L A regs mem md E L' A' regs' mem' md' -> MR L A mem md ->
  alloc_ceiling + Kc <= spZ regs -> 0 <= Kc ->
  bytes_at rsegs mem a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ((spZ regs <= a + i < 2 ^ 64) \/ in_globals frame_G (a + i)) /\ ~ E (a + i)) ->
  bytes_at rsegs mem' a bs.
Proof using SEGS LAWS ERRNO_LOW FGI FGO.
  intros Kc L A regs mem md E L' A' regs' mem' md' a bs P HM HS HK H HC.
  apply (bytes_at_transfer rsegs mem); [exact H|]. intros i Hi. destruct (HC i Hi) as [Ha HE].
  exact (proj1 (post_k_keep Kc L A regs mem md E L' A' regs' mem' md' (a + i) P HM HS HK Ha HE)).
Qed.

End Glob.
