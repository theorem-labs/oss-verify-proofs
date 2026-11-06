From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si Tac_sh1.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState PropExec Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import strlen_c check_str_c strcmp_c reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj.
Open Scope Z_scope.

Section Fx.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma strlen_call : strlen_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (str slack : list byte) (Q : machine_state -> Prop),
  ro_agree rsegs m ->
  bytes_at rsegs m (bv_unsigned a0) (str ++ z8 :: slack) -> ~ In z8 str ->
  (- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5'
                          a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (MState.ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros SL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m str slack Q Hro HB NZ WP K.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs Hro).
    eapply SL with (str := str) (slack := slack);
      [apply bytes_at_normalize; assumption | exact NZ | exact WP | apply mem_inv_normalize]. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  apply K.
  - exact (munch_rel rsegs [] m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME WM).
  - exact (ro_agree_same rsegs m mm Hro SAME).
Qed.

Lemma stk_normalize : forall m lo hi, stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> ro_addr rsegs (wa a) = false) -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hro. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hw [b Hb]].
  assert (E : normalize rsegs m (wa a) = m (wa a)) by (unfold normalize; rewrite (Hro a Ha); reflexivity).
  split.
  - unfold wview in *. rewrite E. exact Hw.
  - exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma check_str_call : check_str_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (r o c lo : Z) (str slack : list byte) (Q : machine_state -> Prop),
  ro_agree rsegs m ->
  -2^31 <= r < 2^31 -> a0 = Z_to_bv 64 r -> 0 <= o < 2^64 -> a1 = Z_to_bv 64 o ->
  0 <= c < 2^64 -> a2 = Z_to_bv 64 c ->
  (0 <= r -> check_str_ok m sp r o c str slack) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_STR_FRAME <= bv_unsigned sp ->
  (forall a, lo <= a < bv_unsigned sp -> ro_addr rsegs (wa a) = false) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(bv_unsigned sp - CHECK_STR_FRAME, bv_unsigned sp)] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (MState.ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 CHECK_STR) fc None m (seg_rom rsegs)).
Proof.
  intros CS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r o c lo str slack Q Hro Hr E0 Ho E1 Hc E2 OK ST HL HRO K.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs Hro).
    eapply CS with (str := str) (slack := slack) (lo := lo);
      [exact Hr | exact E0 | exact Ho | exact E1 | exact Hc | exact E2 | | | exact HL |
      apply mem_inv_normalize].
    - intros H0. destruct (OK H0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      split; [exact Q1|]. split; [exact Q2|]. split; [apply bytes_at_normalize; assumption|].
      split; [exact Q4|]. split; [exact Q5 | exact Q6].
    - apply stk_normalize; assumption. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  apply K.
  - exact (munch_rel rsegs _ m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME WM).
  - exact (ro_agree_same rsegs m mm Hro SAME).
Qed.

Lemma strcmp_call : strcmp_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sx sy : list byte) (Q : machine_state -> Prop),
  bytes_at rsegs m (bv_unsigned a0) (sx ++ [z8]) -> ~ In z8 sx ->
  bytes_at rsegs m (bv_unsigned a1) (sy ++ [z8]) -> ~ In z8 sy ->
  (forall r x11 x12 x13 : word, (r = Z_to_bv 64 0 <-> sx = sy) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r x11 x12 x13 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (MState.ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 STRCMP) fc None m (seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sx sy Q H1 H2 H3 H4 K.
  eapply evt_cut; [eapply SC; eassumption|].
  intros s (r & x11 & x12 & x13 & -> & HR). apply K. exact HR.
Qed.

Lemma cat_call : reac_box_catalogue_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (c : Z) (Q : machine_state -> Prop),
  a0 = Z_to_bv 64 c -> c <> 0 -> c mod 8 = 0 -> wr_at rsegs m c 8 ->
  (forall (a1' : word) (m' : word -> option byte),
     bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) -> munch [(c, c + 8)] m m' -> wmono rsegs m m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BOX_CATALOGUE) a1' a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (MState.ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).
Proof.
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m c Q E0 Hc0 Hc8 HW K.
  eapply evt_cut; [eapply CC; [exact E0 | right; split; assumption]|].
  intros s (a1' & m' & -> & HP). destruct (Z.eqb_spec c 0) as [Ec|Ec]; [contradiction|].
  destruct HP as (HB & MU & WM & _). apply K; assumption.
Qed.

End Fx.

Fixpoint rd_list (mem : word -> option byte) (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => (match mem (Z_to_bv 64 a) with Some b => b | None => z8 end) :: rd_list mem (a + 1) k'
  end.

Lemma rd_list_len : forall mem k a, length (rd_list mem a k) = k.
Proof. intros mem k. induction k as [|k IH]; intros a; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rd_list_nth : forall mem k a j, (j < k)%nat ->
  nth_error (rd_list mem a k) j =
  Some (match mem (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => z8 end).
Proof.
  intros mem k. induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j]; cbn [rd_list nth_error].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. reflexivity.
Qed.

Lemma bytes_at_ro_agree_u : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes rsegs a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR Ha Hl Hb. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (ro_bytes_nth rsegs bs a i b Hb E) as [H1 H2]. rewrite (HR _ H2). exact H1.
Qed.

Lemma bytes_at_fs_u : forall m a l k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n (H1 & H2 & H) Hkn.
  assert (Hlen : length (firstn n (skipn k l)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. rewrite Hlen in Hi.
  rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite H by lia.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma name_cstr_u : forall m a idb, bytes_at rsegs m a idb -> length idb = RcIdentModel.ID_SIZE ->
  RcIdentModel.bz (RcIdentModel.nthb idb 19) = 0 ->
  cstr m (a + 3) (name_str idb).
Proof.
  intros m a idb H Hl H19. pose proof (Tac_sh1.model_name_len idb Hl) as Lm.
  assert (Hm : nth 16 (RcIdentModel.model_name idb) (RcIdentModel.zb 0) = nth 19 idb (RcIdentModel.zb 0)).
  { unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP.
    rewrite nth_first by lia.
    rewrite (nth_skip0 (skipn 3 idb)), skipn_skipn, <- nth_skip0. reflexivity. }
  assert (Hf : (RcIdentModel.first_zero (RcIdentModel.model_name idb) <= 16)%nat).
  { apply first_zero_le; [lia|]. rewrite Hm. exact H19. }
  assert (Hz : nth (RcIdentModel.first_zero (RcIdentModel.model_name idb)) (RcIdentModel.model_name idb) (RcIdentModel.zb 0) = z8).
  { pose proof (Tac_sh1.first_zero_nth (RcIdentModel.model_name idb) ltac:(lia)) as E.
    rewrite <- (Tac_sh1.zb_bz (nth _ (RcIdentModel.model_name idb) (RcIdentModel.zb 0))). rewrite E. reflexivity. }
  unfold cstr, name_str. rewrite <- Hz. rewrite <- Tac_sh1.firstn_S_nth by lia.
  unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP.
  rewrite firstn_firstn.
  replace (Nat.min (S (RcIdentModel.first_zero (firstn 17 (skipn 3 idb)))) 17) with (S (RcIdentModel.first_zero (firstn 17 (skipn 3 idb))))
    by (unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP in Hf; lia).
  change 3 with (Z.of_nat 3). apply bytes_at_fs_u; [exact H|].
  unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP in Hf.
  unfold RcIdentModel.ID_SIZE in Hl. lia.
Qed.

Lemma present_high_u : forall (m : word -> option byte) a, LOWTOP <= a < 2 ^ 64 ->
  wview rsegs m (wa a) <> None -> exists b, m (wa a) = Some b.
Proof.
  intros m a Ha H. unfold wview in H. destruct (m (wa a)) as [b|]; [exists b; reflexivity|].
  rewrite wa_unsigned in H by lia. rewrite (noseg a) in H by lia. contradiction.
Qed.

Lemma stk_after : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  LOWTOP <= lo -> hi <= 2 ^ 64 -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi HS MU WM Hlo Hhi. apply (stk_transport rsegs W m m' lo hi HS MU WM).
  intros x Hx. right. apply present_high_u; [lia|]. apply WM. destruct HS as (_ & _ & HS').
  exact (proj1 (HS' x ltac:(lia))).
Qed.

Section FrmI.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma FF_segs_i : ms_segs B = rsegs.
Proof. destruct FF as (H & _). exact H. Qed.
Local Abbreviation ACL := (@YM05.alloc_ceiling rc).

Lemma blk_range : forall L A mem md a k, aa_MR (APIf rc) L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= ACL.
Proof.
  intros L A mem md a k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn in Eq. injection Eq as <- <-.
  exact (mr_blocks_range _ _ (aa_laws (APIf rc)) _ _ _ _ q k' HM Hq).
Qed.

Lemma blk_present : forall L A mem md a k i, aa_MR (APIf rc) L A mem md -> In (a, k) (blocks L A) ->
  0 <= i < k -> present mem (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn in Eq. injection Eq as <- <-.
  exact (proj1 (mr_blocks _ _ (aa_laws (APIf rc)) _ _ _ _ q k' i HM Hq Hi)).
Qed.

Lemma slack_ok : forall L A mem md p n s, aa_MR (APIf rc) L A mem md -> In (p, n) (blocks L A) ->
  cstr mem p s -> Z.of_nat (length s) + 1 <= n ->
  exists slack, bytes_at rsegs mem p (s ++ z8 :: slack) /\
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= ACL.
Proof.
  intros L A mem md p n s HM Hin HC Hn.
  pose proof (blk_range _ _ _ _ _ _ HM Hin) as [B1 B2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  assert (HSL : block_slack_present B (APIf rc)).
  { destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & HFA).
    destruct (HFA rc fx) as (_ & _ & _ & _ & _ & H & _). exact H. }
  set (x := p + Z.of_nat (length s) + 1).
  set (e := 8 * ((p + n + 7) / 8)).
  assert (He1 : p + n <= e) by (unfold e; Z.div_mod_to_equations; lia).
  assert (He2 : e <= ACL) by (unfold e; Z.div_mod_to_equations; lia).
  assert (PR : forall a, x <= a < e -> present mem a).
  { intros a Ha. destruct (Z_lt_le_dec a (p + n)) as [Hlt|Hge].
    - replace a with (p + (a - p)) by lia. apply (blk_present L A mem md p n); [exact HM | exact Hin | lia].
    - exact (HSL L A mem md p n a HM Hin ltac:(unfold e in Ha; lia)). }
  exists (rd_list mem x (Z.to_nat (e - x))). rewrite rd_list_len.
  destruct HC as (C1 & C2 & C3). rewrite length_app in C2. cbn [length] in C2.
  split; [| split; [fold x; Z.div_mod_to_equations; lia | fold x; lia]].
  split; [lia|]. split; [rewrite length_app; cbn [length]; rewrite rd_list_len; lia|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite rd_list_len in Hi.
  replace (s ++ z8 :: rd_list mem x (Z.to_nat (e - x))) with ((s ++ [z8]) ++ rd_list mem x (Z.to_nat (e - x)))
    by (rewrite <- app_assoc; reflexivity).
  destruct (Nat.lt_ge_cases i (length s + 1)) as [Hl|Hl].
  - rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia). apply C3. rewrite length_app. cbn. lia.
  - rewrite nth_error_app2 by (rewrite length_app; cbn [length]; lia). rewrite length_app. cbn [length].
    rewrite rd_list_nth by lia.
    destruct (PR (p + Z.of_nat i) ltac:(unfold x; lia)) as [b Hb].
    replace (x + Z.of_nat (i - (length s + 1))) with (p + Z.of_nat i) by (unfold x; lia).
    unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma nmb_in : forall g nm tk dp L A, Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) ->
  In (nm, bsz (t_cap_name (g_in g))) (blocks L A) /\ In (tk, bsz (t_cap_tok (g_in g))) (blocks L A) /\
  In (dp, bsz (t_cap_disp (g_in g))) (blocks L A).
Proof.
  intros g nm tk dp L A HP.
  repeat split; (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; left; unfold NMB; cbn; tauto]).
Qed.

Lemma FR_md : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros g km hb L A regs mem md H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  exact (kb_md B (APIf rc) L A mem md HM).
Qed.

Lemma FR_parts : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  g_S g mod 16 = 0 /\ ACL + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  YK11.getr regs 2 = Z_to_bv 64 (fsp g) /\ aa_MR (APIf rc) L A mem md /\ ro_agree rsegs mem /\
  stk rsegs mem (g_S g - SLOT_K) (g_S g) /\
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at rsegs mem a).
Proof.
  intros g km hb L A regs mem md H.
  destruct H as ((_ & _ & _ & G4 & G5 & G6 & _) & H2 & _ & _ & _ & HSTK & HMI & _ & HM & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & HSW).
  unfold MI in HMI. rewrite FF_segs_i in HMI, HSW. auto 10.
Qed.

End FrmI.
