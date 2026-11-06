From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg printf_facts_c snprintf_c reac_boxreg_declare_c memcpy_c memcpy.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import read_name_c read_name.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top LLVMFuzzerTestOneInput_join LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Fixpoint nm_str (l : list byte) : list Z :=
  match l with
  | [] => []
  | x :: l' => if bv_unsigned x =? 0 then [] else bv_unsigned x :: nm_str l'
  end.

Fixpoint nm_rest (l : list byte) : list byte :=
  match l with
  | [] => []
  | x :: l' => if bv_unsigned x =? 0 then l' else nm_rest l'
  end.

Lemma nm_byte : forall x : byte, Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma nm_split : forall l : list byte,
  l ++ [Z_to_bv 8 0] = pf_bytes (nm_str (l ++ [Z_to_bv 8 0]) ++ [0]) ++ nm_rest (l ++ [Z_to_bv 8 0]).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [app nm_str nm_rest]. destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
  - assert (Ex : x = Z_to_bv 8 0) by (rewrite <- E; symmetry; apply nm_byte). subst x. reflexivity.
  - unfold pf_bytes in *. cbn [app map]. rewrite nm_byte. f_equal. exact IH.
Qed.

Lemma nm_str_ok : forall l : list byte, Forall (fun c => 0 < c < 256) (nm_str l).
Proof.
  induction l as [|x l IH]; cbn [nm_str]; [constructor|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; [constructor|].
  constructor; [|exact IH]. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma nm_pf0 : forall (s : list Z) (t : list byte), pf_bytes (s ++ [0]) ++ t = pf_bytes s ++ Z_to_bv 8 0 :: t.
Proof. intros s t. unfold pf_bytes. rewrite map_app, <- app_assoc. reflexivity. Qed.

Lemma nm_len : forall (s : list Z) (t : list byte),
  Z.of_nat (length (pf_bytes (s ++ [0]) ++ t)) = Z.of_nat (length s) + 1 + Z.of_nat (length t).
Proof. intros s t. unfold pf_bytes. rewrite !length_app, length_map, length_app. cbn [length]. lia. Qed.

Lemma nm_walk : forall (s : list Z) (t1 t2 : list byte) k, Forall (fun c => 0 < c < 256) s ->
  strncmp_walk (pf_bytes (firstn (S k) s) ++ Z_to_bv 8 0 :: t1) (pf_bytes s ++ Z_to_bv 8 0 :: t2) k = Some 0.
Proof.
  induction s as [|c s IH]; intros t1 t2 k H; [reflexivity|].
  apply Forall_cons_iff in H. destruct H as [Hc Hs].
  assert (E : bv_unsigned (Z_to_bv 8 c) = c)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
  change (pf_bytes (firstn (S k) (c :: s)) ++ Z_to_bv 8 0 :: t1) with
    (Z_to_bv 8 c :: (pf_bytes (firstn k s) ++ Z_to_bv 8 0 :: t1)).
  change (pf_bytes (c :: s) ++ Z_to_bv 8 0 :: t2) with (Z_to_bv 8 c :: (pf_bytes s ++ Z_to_bv 8 0 :: t2)).
  cbn [strncmp_walk]. rewrite E. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Z.eqb_refl. cbn [orb negb].
  destruct k as [|k]; [cbn; rewrite Z.sub_diag; reflexivity|]. cbn [Nat.eqb orb]. exact (IH t1 t2 k Hs).
Qed.

Lemma nm_strncmp_field : forall (s : list Z) (slack : list byte), Forall (fun c => 0 < c < 256) s ->
  strncmp_model (name_field s) (pf_bytes (s ++ [0]) ++ slack) 31 = Some 0.
Proof.
  intros s slack H. unfold strncmp_model, name_field. change (31 =? 0) with false. cbv iota.
  change (Z.to_nat (31 - 1)) with 30%nat.
  replace (32 - Nat.min (length s) 31)%nat with (S (31 - Nat.min (length s) 31)) by lia.
  cbn [repeat]. rewrite nm_pf0. exact (nm_walk s _ _ 30 H).
Qed.

Lemma nm_strncmp_set : forall (s : list Z) (slack : list byte), Forall (fun c => 0 < c < 256) s ->
  strncmp_model (pf_bytes (firstn 31 s ++ [0])) (pf_bytes (s ++ [0]) ++ slack) 31 = Some 0.
Proof.
  intros s slack H. unfold strncmp_model. change (31 =? 0) with false. cbv iota.
  change (Z.to_nat (31 - 1)) with 30%nat.
  rewrite <- (app_nil_r (pf_bytes (firstn 31 s ++ [0]))). rewrite !nm_pf0. exact (nm_walk s [] slack 30 H).
Qed.

Lemma nm_collect : forall (m : word -> option byte) a (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat n -> exists v, mrd rsegs m (wa (a + j)) = Some v) ->
  exists l, bytes_at rsegs m a l /\ length l = n.
Proof.
  intros m a n Ha. induction n as [|n IH]; intros Hn H.
  - exists []. split; [apply bytes_at_nil; lia | reflexivity].
  - destruct IH as (l & Hl & Ln); [lia | intros j Hj; apply H; lia |].
    destruct (H (Z.of_nat n) ltac:(lia)) as (v & Hv).
    exists (l ++ [v]). split; [|rewrite length_app, Ln; cbn [length]; lia].
    apply (proj2 (bytes_at_app rsegs m a l [v])). split; [exact Hl|].
    rewrite Ln. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi.
    destruct i as [|i]; [|cbn [length] in Hi; lia]. cbn [nth_error].
    replace (a + Z.of_nat n + Z.of_nat 0) with (a + Z.of_nat n) by lia. exact Hv.
Qed.

Lemma nm_present_mrd : forall (m : word -> option byte) x, present m x -> exists v, mrd rsegs m (wa x) = Some v.
Proof. intros m x (v & Hv). exists v. unfold mrd, wa. rewrite Hv. reflexivity. Qed.

Lemma nm_mod8 : forall x t, x <= 8 * t -> (- x) mod 8 <= 8 * t - x.
Proof.
  intros x t H. replace (- x) with ((8 * t - x) + (- t) * 8) by lia. rewrite Z.mod_add by lia.
  apply Z.mod_le; lia.
Qed.

Lemma nm_up8 : forall y c, y <= c -> c mod 8 = 0 -> 8 * ((y + 7) / 8) <= c.
Proof. intros y c H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma nm_up8_ge : forall y, y <= 8 * ((y + 7) / 8).
Proof. intros y. Z.div_mod_to_equations. lia. Qed.

Lemma nm_task_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> bv_unsigned x < TASK_SIZE) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU HW a b E. destruct (lf_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (T a b E).
  - right. exact (HW a O).
Qed.

Lemma nm_rw_rel_cj : forall m m0 A cs, MemNorm.mem_rel_cj rsegs m m0 ->
  rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (MemNorm.bytes_at_rel_cj rsegs m m0 A _ HR Hb)]|].
  exact (MemNorm.wr_at_rel_cj rsegs m m0 A _ HR Hw).
Qed.

Lemma rn_k_range : forall pl, 0 <= rn_k pl <= 47 /\ rn_k pl <= Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1.
Proof.
  intros [|x rest]; cbn [rn_k length]; [lia|].
  pose proof (Z.mod_pos_bound (bv_unsigned x) 48 ltac:(lia)). lia.
Qed.

Lemma rn_name_len : forall pl, Z.of_nat (length (bsub pl 1 (rn_k pl))) = rn_k pl.
Proof.
  intros [|x rest]; [reflexivity|].
  change (rn_k (x :: rest)) with (Z.min (bv_unsigned x mod 48) (Z.of_nat (length rest))).
  unfold bsub. change (skipn (Z.to_nat 1) (x :: rest)) with rest.
  pose proof (Z.mod_pos_bound (bv_unsigned x) 48 ltac:(lia)) as Hm.
  rewrite length_firstn, Nat.min_l by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Definition lf_cells (regs0 : bvmap 5 word) (j0 : list byte) (fab : Z) (j1 bs jm : list byte) (ip ln : Z) : list cell :=
  CB 8 j0 :: C8 (Z_to_bv 64 fab) :: CB 16 j1 :: CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 ip) :: C8 (Z_to_bv 64 ln) ::
  llvm_saved_cells regs0.

Lemma lf_cells_split : forall m A regs0 j0 fab j1 bs jm ip ln,
  rw_cells rsegs m A (lf_cells regs0 j0 fab j1 bs jm ip ln) <->
  rw_cells rsegs m A [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1] /\
  rw_cells rsegs m (A + 32) [CB 288 bs; CB 8 jm] /\
  rw_cells rsegs m (A + 328) [C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 ln)] /\
  rw_cells rsegs m (A + 344) (llvm_saved_cells regs0).
Proof.
  intros m A regs0 j0 fab j1 bs jm ip ln. split.
  - intros H. unfold lf_cells in H.
    destruct (top_rwc_split m A [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1]
      (CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 ip) :: C8 (Z_to_bv 64 ln) :: llvm_saved_cells regs0) H) as [H1 H2].
    change (Z.of_nat (cells_size _)) with 32 in H2.
    destruct (top_rwc_split m (A + 32) [CB 288 bs; CB 8 jm]
      (C8 (Z_to_bv 64 ip) :: C8 (Z_to_bv 64 ln) :: llvm_saved_cells regs0) H2) as [H3 H4].
    change (Z.of_nat (cells_size _)) with 296 in H4.
    destruct (top_rwc_split m (A + 32 + 296) [C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 ln)] (llvm_saved_cells regs0) H4)
      as [H5 H6].
    change (Z.of_nat (cells_size _)) with 16 in H6.
    replace (A + 32 + 296) with (A + 328) in H5, H6 by lia. replace (A + 328 + 16) with (A + 344) in H6 by lia.
    auto.
  - intros (H1 & H2 & H3 & H4). unfold lf_cells.
    pose proof (top_rwc_join m (A + 328) [C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 ln)] _ (A + 344) H3
      ltac:(cbn; lia) H4) as H34.
    pose proof (top_rwc_join m (A + 32) [CB 288 bs; CB 8 jm] _ (A + 328) H2 ltac:(cbn; lia) H34) as H234.
    exact (top_rwc_join m A [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1] _ (A + 32) H1 ltac:(cbn; lia) H234).
Qed.

Ltac lf_reg H R x E := lazymatch goal with |- _ = ?v => change (YK11.getr R (Z_to_bv 5 x) = v) end;
  rewrite (H x ltac:(unfold callee_saved; lia)); exact E.
Ltac lf_reg2 H R x E := lazymatch goal with |- _ = ?v => change (reg_get R (Z_to_bv 5 x) = v) end;
  rewrite (H x ltac:(lia)); exact E.

Lemma lf_base_pres : forall regs0 R R' r fab i, llvm_regs_base regs0 R r fab i -> regs_preserved R R' ->
  llvm_regs_base regs0 R' r fab i.
Proof.
  intros regs0 R R' r fab i (E2 & E3 & E4 & E8 & E24 & E25 & E26 & E27) H.
  split; [lf_reg H R' 2 E2|]. split; [lf_reg H R' 3 E3|]. split; [lf_reg H R' 4 E4|]. split; [lf_reg H R' 8 E8|].
  split; [lf_reg H R' 24 E24|]. split; [lf_reg H R' 25 E25|]. split; [lf_reg H R' 26 E26 | lf_reg H R' 27 E27].
Qed.

Lemma lf_base_eqv : forall regs0 R Rold regs' r fab i, llvm_regs_base regs0 Rold r fab i ->
  (forall x, x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ 24 <= x <= 27 -> reg_get R (Z_to_bv 5 x) = reg_get Rold (Z_to_bv 5 x)) ->
  Regs6ss.xregs_eqv R regs' -> llvm_regs_base regs0 regs' r fab i.
Proof.
  intros regs0 R Rold regs' r fab i (E2 & E3 & E4 & E8 & E24 & E25 & E26 & E27) H HX.
  unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ HX).
  split; [lf_reg2 H R 2 E2|]. split; [lf_reg2 H R 3 E3|]. split; [lf_reg2 H R 4 E4|]. split; [lf_reg2 H R 8 E8|].
  split; [lf_reg2 H R 24 E24|]. split; [lf_reg2 H R 25 E25|]. split; [lf_reg2 H R 26 E26 | lf_reg2 H R 27 E27].
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SLACK : block_slack_present B API.

Lemma nm_mrd_some : forall m a v, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  mrd rsegs m (wa a) = Some v -> m (Z_to_bv 64 a) = Some v.
Proof.
  intros m a v HS Hn Ha H. unfold mrd, wa in H. destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [exact H|].
  rewrite MemNorm.seg_rom_unmapped in H; [discriminate|].
  rewrite (MState.unsigned_lit a Ha). destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity].
  exfalso. exact (Hn (lf_find_img B a seg HS F)).
Qed.

Lemma nm_bytes_writable : forall m A l, ms_segs B = rsegs -> bytes_at rsegs m A l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> ~ in_img B (A + i)) ->
  forall a, A <= a < A + Z.of_nat (length l) -> YP09.writable_at rsegs m a.
Proof.
  intros m A l HS (H0 & H1 & H) Hn a Ha.
  pose proof (H (Z.to_nat (a - A)) ltac:(lia)) as E. replace (A + Z.of_nat (Z.to_nat (a - A))) with a in E by lia.
  destruct (nth_error l (Z.to_nat (a - A))) as [v|] eqn:N; [|apply nth_error_None in N; lia].
  pose proof (Hn (a - A) ltac:(lia)) as Hn'. replace (A + (a - A)) with a in Hn' by lia.
  unfold YP09.writable_at. rewrite (lf_wview_out B m a HS Hn' ltac:(lia)).
  rewrite (nm_mrd_some m a v HS Hn' ltac:(lia) E). discriminate.
Qed.

Lemma nm_wr_at : forall m A l, ms_segs B = rsegs -> bytes_at rsegs m A l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> ~ in_img B (A + i)) -> wr_at rsegs m A (Z.of_nat (length l)).
Proof.
  intros m A l HS HB Hn. pose proof (bytes_at_bound rsegs m A l HB) as Bd.
  split; [lia|]. split; [lia|]. intros i Hi.
  exact (nm_bytes_writable m A l HS HB Hn (A + i) ltac:(lia)).
Qed.

Lemma nm_mine_writable : AllocExtra B (aa_MR API) -> ms_segs B = rsegs ->
  forall L0 A0 L A mem md x k y, aa_MR API L A mem md -> lf_mine L0 A0 L A x k -> x <= y < x + k ->
  YP09.writable_at rsegs mem y.
Proof.
  intros AX SEGS L0 A0 L A mem md x k y HM MINE Hy.
  pose proof YM05.alloc_ceiling_lt as Hlt.
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md x k y HM MINE Hy) as (_ & N2 & N3 & (v & Hv) & _).
  unfold YP09.writable_at. rewrite (lf_wview_out B mem y SEGS N2 ltac:(lia)). rewrite Hv. discriminate.
Qed.

Lemma nm_cj_keep : forall a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < TASK_SIZE ->
  MemNorm.cj_drop rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a HS Hn Ha. unfold TASK_SIZE in Ha. unfold MemNorm.cj_drop.
  rewrite (lf_ro_addr_out B a HS Hn ltac:(lia)). cbn [orb].
  rewrite (MState.unsigned_lit a ltac:(lia)).
  destruct (find_segment rsegs a 1); [reflexivity|]. apply Z.leb_gt. unfold TASK_SIZE. lia.
Qed.

Lemma nm_rw_cj : forall m A cs, ms_segs B = rsegs -> ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ in_img B (A + i)) -> A + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  rw_cells rsegs (MemNorm.normalize_cj rsegs m) A cs.
Proof.
  intros m A cs HS Hro [[Hwf Hb] Hw] Hn Ht. pose proof (rw_cells_bound rsegs m A cs (conj (conj Hwf Hb) Hw)) as Bd.
  split; [split; [exact Hwf|]|].
  - apply (MemNorm.bytes_at_normalize_cj_low rsegs m A _ Hro); [|exact Hb].
    rewrite cells_bytes_length by exact Hwf. exact Ht.
  - apply (MemNorm.wr_at_norm_cj rsegs m _ A _ (MemNorm.mem_rel_cj_normalize rsegs m Hro) Hw).
    intros i Hi. apply nm_cj_keep; [exact HS | exact (Hn i Hi) | unfold TASK_SIZE in *; lia].
Qed.

Lemma nm_bytes_cj : forall m A l, ro_agree rsegs m -> bytes_at rsegs m A l -> A + Z.of_nat (length l) <= TASK_SIZE ->
  bytes_at rsegs (MemNorm.normalize_cj rsegs m) A l.
Proof. intros m A l Hro H Ht. exact (MemNorm.bytes_at_normalize_cj_low rsegs m A l Hro Ht H). Qed.

Lemma nm_stk_cj : forall m lo hi, ms_segs B = rsegs -> ro_agree rsegs m -> LF_RES_TOP <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> YP09.writable_at rsegs m a) -> Frame.stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi HS Hro Hlo Hhi H. apply lf_stk; [exact Hlo | unfold TASK_SIZE in Hhi; lia |].
  intros a Ha. unfold YP09.writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a HS Hi); lia).
  rewrite (MemNorm.wview_rel_cj rsegs m _ _ (MemNorm.mem_rel_cj_normalize rsegs m Hro)
             (nm_cj_keep a HS Hni ltac:(unfold LF_RES_TOP in Hlo; lia))).
  exact (H a Ha).
Qed.

Lemma llvm_payload_mrd : forall stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> p <= x < p + n ->
  exists v, mrd rsegs mem (wa x) = Some v.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x
    ((SEGS & _) & _ & _ & (HM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _) FR Hx.
  destruct FR as (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _).
  destruct Hpl as [[E _] | [Hn (q & Hq & Hqp)]]; [lia|].
  assert (Hb : In (p, n) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
  destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n (x - p) HM0 Hq ltac:(lia)) as ((v & Hv) & H1 & H2 & _).
  rewrite Hqp in H1, H2, Hv. replace (p + (x - p)) with x in Hv by lia.
  exists v. pose proof (Hbyt p n (x - p) Hb ltac:(lia)) as E. replace (p + (x - p)) with x in E by lia.
  change (mrd rsegs mem (wa x)) with (mbyte rsegs mem x). rewrite <- SEGS. rewrite E. unfold mbyte. rewrite Hv.
  reflexivity.
Qed.

Lemma llvm_payload_bound : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b -> 0 < n -> 4096 <= p /\ p + n <= YM05.alloc_ceiling.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b
    (_ & _ & _ & (HM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _) Hn.
  destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  destruct (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM0 Hq) as [H1 H2]. rewrite Hqp in H1, H2. lia.
Qed.

Lemma llvm_guards : forall stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b -> aa_MR API L A mem md ->
  bytes_at rsegs mem GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ exists g : word, bytes_at rsegs mem GUARD (le8 g).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md ((SEGS & _ & _ & HGG & HG & AX) & _) HM.
  destruct (ax_statics AX L A mem md HM) as (Hgot & (g & Hg & Hguard) & _).
  rewrite HGG, HG, SEGS in Hgot. rewrite HG, SEGS in Hguard.
  split.
  - exact (KindBGlue.word_mem_le8 rsegs mem _ _ Hgot ltac:(unfold LLVM_GUARD; lia)
             ltac:(unfold LLVM_GUARD_GOT; lia) ltac:(unfold LLVM_GUARD_GOT; lia)).
  - exists (Z_to_bv 64 g).
    exact (KindBGlue.word_mem_le8 rsegs mem _ _ Hguard Hg ltac:(unfold LLVM_GUARD; lia) ltac:(unfold LLVM_GUARD; lia)).
Qed.

Lemma llvm_name_parts : forall L A mem md s k (T : list byte),
  aa_MR API L A mem md -> In (s, k + 1) (blocks L A) -> 0 <= k -> 0 <= s -> s + k + 1 <= YM05.alloc_ceiling ->
  bytes_at rsegs mem s (T ++ [Z_to_bv 8 0]) -> Z.of_nat (length T) = k ->
  exists slack : list byte,
    bytes_at rsegs mem s (pf_bytes (nm_str (T ++ [Z_to_bv 8 0]) ++ [0]) ++ slack) /\
    Z.of_nat (length (nm_str (T ++ [Z_to_bv 8 0]))) <= k /\
    (- (s + Z.of_nat (length (nm_str (T ++ [Z_to_bv 8 0]))) + 1)) mod 8 <= Z.of_nat (length slack) /\
    s + Z.of_nat (length (nm_str (T ++ [Z_to_bv 8 0]))) + 1 + Z.of_nat (length slack) = 8 * ((s + k + 1 + 7) / 8).
Proof.
  intros L A mem md s k T HM Hin Hk Hs Hc HB HT.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof YM05.alloc_ceiling_lt as Hlt.
  pose proof (nm_up8_ge (s + k + 1)) as Hge.
  assert (Hle : 8 * ((s + k + 1 + 7) / 8) <= YM05.alloc_ceiling)
    by (apply nm_up8; [lia | Z.div_mod_to_equations; lia]).
  assert (PR : forall j, 0 <= j < Z.of_nat (Z.to_nat (8 * ((s + k + 1 + 7) / 8) - (s + k + 1))) ->
                 exists v, mrd rsegs mem (wa (s + k + 1 + j)) = Some v).
  { intros j Hj. apply nm_present_mrd.
    pose proof (SLACK L A mem md s (k + 1) (s + k + 1 + j) HM Hin) as SP.
    replace (s + (k + 1)) with (s + k + 1) in SP by lia. apply SP. lia. }
  destruct (nm_collect mem (s + k + 1) (Z.to_nat (8 * ((s + k + 1 + 7) / 8) - (s + k + 1))) ltac:(lia) ltac:(lia) PR)
    as (SL & HSL & LSL).
  pose proof (nm_split T) as ES.
  set (str := nm_str (T ++ [Z_to_bv 8 0])) in *. set (rest := nm_rest (T ++ [Z_to_bv 8 0])) in *.
  assert (LT : Z.of_nat (length (T ++ [Z_to_bv 8 0])) = k + 1) by (rewrite length_app; cbn [length]; lia).
  assert (L2 : Z.of_nat (length str) + 1 + Z.of_nat (length rest) = k + 1) by (rewrite <- nm_len, <- ES; exact LT).
  exists (rest ++ SL). split; [|split; [lia|]].
  - rewrite app_assoc, <- ES. apply (proj2 (bytes_at_app rsegs mem s _ SL)). split; [exact HB|]. rewrite LT.
    replace (s + (k + 1)) with (s + k + 1) by lia. exact HSL.
  - rewrite length_app, LSL. split; [|lia].
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    replace (Z.of_nat (length rest) + (8 * ((s + k + 1 + 7) / 8) - (s + k + 1)))
      with (8 * ((s + k + 1 + 7) / 8) - (s + Z.of_nat (length str) + 1)) by lia.
    apply nm_mod8. lia.
Qed.

Lemma llvm_rn_glue : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  forall (fx' : FPState) regs mem md L A r bsr bres RA j0 fab j1 bs jm ip pl (P : config -> Prop), 0 < n ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> lf_mine L0 A0 L A r 288 ->
  res_ok_slots A bres -> room_ag bres (rn_k pl + 1) ->
  YK11.getr regs 1 = Z_to_bv 64 RA -> YK0s.ret_ok (Z_to_bv 64 RA) ->
  YK11.getr regs 2 = Z_to_bv 64 (spZ regs0 - 448) -> YK11.getr regs 4 = YK11.getr regs0 4 ->
  YK11.getr regs 10 = Z_to_bv 64 (spZ regs0 - 448 + 328) ->
  rw_cells rsegs mem (spZ regs0 - 448) (lf_cells regs0 j0 fab j1 bs jm ip (Z.of_nat (length pl))) ->
  rw_cells rsegs mem r [CB 288 bsr] ->
  bytes_at rsegs mem ip pl -> p <= ip -> ip + Z.of_nat (length pl) <= p + n ->
  (forall L' A' regs' mem' md' s,
     lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L' A' mem' md' ->
     lf_mine L0 A0 L' A' r 288 -> lf_mine L0 A0 L' A' s (rn_k pl + 1) ->
     (s + rn_k pl + 1 <= r \/ r + 288 <= s) ->
     res_ok_slots A' (sb_malloc bres (rn_k pl + 1)) ->
     regs_preserved regs regs' -> YK11.getr regs' 10 = Z_to_bv 64 s ->
     bytes_at rsegs mem' s (bsub pl 1 (rn_k pl) ++ [Z_to_bv 8 0]) ->
     rw_cells rsegs mem' (spZ regs0 - 448)
       (lf_cells regs0 j0 fab j1 bs jm (ip + Z.min (Z.of_nat (length pl)) 1 + rn_k pl)
          (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl)) ->
     rw_cells rsegs mem' r [CB 288 bsr] ->
     SR rsegs (mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 RA) mem' (YK11.seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 READ_NAME) mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b CTX fx' regs mem md L A r bsr bres RA j0 fab j1 bs jm ip pl P
    Hn0 FR MINE RES ROOM G1 HRA G2 G4 G10 CF CR HPL Hp1 Hp2 K.
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hstk & Hra & Hpre & Hsn & Hsp47 & Hres0 & Hroom & Hro0
    & Hrelro & Hfrm0 & Hn26).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  unfold LLVM_K, LLVM_FRAME in Hstk.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. pose proof YM05.alloc_ceiling_lt as Hlt.
  pose proof (rn_k_range pl) as Hkr.
  pose proof (llvm_payload_bound stk empty L0 A0 regs0 mem0 md0 ra p n b CTX Hn0) as Hpb.
  set (S := spZ regs0) in *.
  assert (Hsp : spZ regs = S - 448) by (unfold spZ; rewrite G2; apply MState.unsigned_lit; lia).
  pose proof (proj1 (lf_cells_split mem (S - 448) regs0 j0 fab j1 bs jm ip (Z.of_nat (length pl))) CF)
    as (CF1 & CF2 & CF3 & CF4).
  assert (HBc : bytes_at rsegs mem (S - 448 + 328) (le8 (Z_to_bv 64 ip) ++ le8 (Z_to_bv 64 (Z.of_nat (length pl))))).
  { destruct CF3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (HWc : wr_at rsegs mem (S - 448 + 328) 16) by (destruct CF3 as [_ Hw]; exact Hw).
  assert (HBLK : pl <> [] -> exists a len, In (a, len) (blocks L A) /\ a <= ip /\ ip + Z.of_nat (length pl) <= a + len).
  { intros Hne. destruct Hpl as [[E0 _] | [_ (q & Hq & Hqp)]]; [lia|].
    exists p, n. split; [apply Hblk; apply blocks_In; exists q; split; [exact Hqp | exact Hq] | lia]. }
  pose proof (bytes_at_bound rsegs mem ip pl HPL) as HPLb.
  rewrite <- SEGS.
  eapply SR_bind.
  { apply (@read_name_holds fx' rc B API (MALLOC fx') memcpy_holds L A regs mem md (S - 448 + 328) ip pl bres).
    - exact SEGS.
    - rewrite HMAL. reflexivity.
    - exact ERRNO_LOW.
    - split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [rewrite G1; exact HRA|].
      split; [rewrite Hsp; replace (S - 448) with (S + (-28) * 16) by lia; rewrite Z.mod_add by lia; exact Hal|].
      split; [rewrite Hsp; unfold ALLOC_STACK; lia|]. split; [rewrite Hsp; lia|].
      split; [intros a Ha; apply Hstw; rewrite Hsp in Ha; unfold ALLOC_STACK in Ha; lia|].
      split; [rewrite G4; exact Htp|]. split; [exact Herr|].
      intros E. rewrite HID in E. discriminate.
    - exact HID.
    - exact G10.
    - pose proof (Z.div_mod S 16 ltac:(lia)) as Hd.
      replace (S - 448 + 328) with ((2 * (S / 16) - 15) * 8) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. lia.
    - rewrite SEGS. exact HBc.
    - rewrite SEGS. exact HWc.
    - lia.
    - rewrite SEGS. exact HPL.
    - exact HBLK.
    - rewrite SEGS. exact Hro.
    - exact RES.
    - exact ROOM. }
  intros c2 (L' & A' & regs' & mem' & md' & s & -> & Hro' & Hgk & Hpost & G10' & Hs0 & Hfresh & (b1 & b2 & Eb1 & Eb2)
    & HBs & HBc' & Hkept & Hid' & Hres').
  rewrite SEGS, G1.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  destruct Hfresh as (Hs1 & Hs2 & Hs3).
  rewrite SEGS in Hro', HBs, HBc'.
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md').
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | rewrite Hsp; unfold ALLOC_STACK; lia | rewrite Hsp; lia | | | | | | exact Hid' | exact Hro' | exact Hgk ].
    - intros a [Ha|Ha]; [left; lia|]. right. split; [lia|].
      pose proof (Hs3 (a - s) ltac:(lia)) as N. replace (s + (a - s)) with a in N by lia. exact N.
    - intros a Ha. unfold rn_writes.
      destruct (Z_le_dec (S - 448 + 328) a) as [h1|h1]; destruct (Z_lt_dec a (S - 448 + 328 + 16)) as [h2|h2];
        first [left; left; lia | right; intros [h|h]; lia].
    - intros a [Ha|Ha] Hs; [|lia]. rewrite SEGS.
      apply (nm_bytes_writable mem' (S - 448 + 328) _ SEGS HBc'); [|rewrite length_app, !length_le8; cbn; lia].
      intros j Hj Hij. pose proof (lf_in_img_top B _ SEGS Hij). lia.
    - intros a0 k0 Hin. pose proof (Hblk a0 k0 Hin) as Hin2. rewrite Eb2 in Hin2. rewrite Eb1.
      apply in_app_or in Hin2. apply in_or_app. destruct Hin2 as [Hin2|Hin2]; [left; exact Hin2 | right; right; exact Hin2].
    - intros a0 k0 i0 Hin Hi0. exact (Hkept a0 k0 i0 (Hblk a0 k0 Hin) (fun H => H) Hi0). }
  destruct MINE as (Hrin & Hr0 & Hrd).
  assert (Hrin2 : In (r, 288) (b1 ++ b2)) by (rewrite <- Eb2; exact Hrin).
  assert (MINE' : lf_mine L0 A0 L' A' r 288).
  { split; [|split; [lia | exact Hrd]]. rewrite Eb1. apply in_app_or in Hrin2. apply in_or_app.
    destruct Hrin2 as [h|h]; [left; exact h | right; right; exact h]. }
  pose proof (mr_blocks_disjoint B (aa_MR API) (aa_laws API) L' A' mem' md' HM2) as HP. rewrite Eb1 in HP.
  assert (MINEs : lf_mine L0 A0 L' A' s (rn_k pl + 1)).
  { split; [rewrite Eb1; apply in_or_app; right; left; reflexivity|]. split; [lia|].
    intros a j Hin. pose proof (Hblk a j Hin) as Hin3. rewrite Eb2 in Hin3.
    destruct (pairwise_app_mid _ b1 (s, rn_k pl + 1) b2 (a, j) HP Hin3) as [H|H];
      unfold ranges_disjoint in H; cbn [fst snd] in H; lia. }
  assert (Hsr : s + rn_k pl + 1 <= r \/ r + 288 <= s).
  { destruct (pairwise_app_mid _ b1 (s, rn_k pl + 1) b2 (r, 288) HP Hrin2) as [H|H];
      unfold ranges_disjoint in H; cbn [fst snd] in H; lia. }
  assert (Hfrm2 : forall a, S - 448 <= a < S -> ~ (S - 448 + 328 <= a < S - 448 + 344) ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (YP09.writable_at rsegs mem a <-> YP09.writable_at rsegs mem' a)).
  { intros a Ha Hc. rewrite <- SEGS. apply Hfr2.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    - unfold scratch_k. rewrite Hsp. unfold ALLOC_STACK.
      intros [h|h]; [lia | pose proof (lf_errno_low B ERRNO_LOW a h); lia].
    - unfold rn_writes. intros [h|h]; lia. }
  assert (CF1' : rw_cells rsegs mem' (S - 448) [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1]).
  { apply (lf_rw_cells_frame mem); [exact CF1|]. intros a Ha. change (Z.of_nat (cells_size _)) with 32 in Ha.
    apply Hfrm2; lia. }
  assert (CF2' : rw_cells rsegs mem' (S - 448 + 32) [CB 288 bs; CB 8 jm]).
  { apply (lf_rw_cells_frame mem); [exact CF2|]. intros a Ha. change (Z.of_nat (cells_size _)) with 296 in Ha.
    apply Hfrm2; lia. }
  assert (CF4' : rw_cells rsegs mem' (S - 448 + 344) (llvm_saved_cells regs0)).
  { apply (lf_rw_cells_frame mem); [exact CF4|]. intros a Ha.
    change (Z.of_nat (cells_size (llvm_saved_cells regs0))) with 104 in Ha. apply Hfrm2; lia. }
  assert (CF3' : rw_cells rsegs mem' (S - 448 + 328)
    [C8 (Z_to_bv 64 (ip + Z.min (Z.of_nat (length pl)) 1 + rn_k pl));
     C8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))]).
  { split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HBc'] |].
    pose proof (nm_wr_at mem' (S - 448 + 328) _ SEGS HBc') as W.
    rewrite length_app, !length_le8 in W. change (Z.of_nat (8 + 8)) with 16 in W.
    change (Z.of_nat (cells_size _)) with 16. apply W.
    intros j Hj Hij. pose proof (lf_in_img_top B _ SEGS Hij). lia. }
  assert (CFn : rw_cells rsegs mem' (S - 448)
    (lf_cells regs0 j0 fab j1 bs jm (ip + Z.min (Z.of_nat (length pl)) 1 + rn_k pl)
       (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))).
  { apply (proj2 (lf_cells_split mem' (S - 448) regs0 j0 fab j1 bs jm _ _)). auto. }
  assert (CR' : rw_cells rsegs mem' r [CB 288 bsr]).
  { apply (lf_rw_cells_frame mem); [exact CR|]. intros a Ha. change (Z.of_nat (cells_size [CB 288 bsr])) with 288 in Ha.
    split.
    - pose proof (Hkept r 288 (a - r) Hrin (fun H => H) ltac:(lia)) as E. replace (r + (a - r)) with a in E by lia.
      rewrite <- SEGS. exact E.
    - split; intros _.
      + exact (nm_mine_writable AX SEGS L0 A0 L' A' mem' md' r 288 a HM2 MINE' ltac:(lia)).
      + exact (nm_mine_writable AX SEGS L0 A0 L A mem md r 288 a HM (conj Hrin (conj Hr0 Hrd)) ltac:(lia)). }
  exact (K L' A' regs' mem' md' s FR2 MINE' MINEs Hsr Hres' Hrp G10' HBs CFn CR').
Qed.

Lemma llvm_free_glue : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  forall (fx' : FPState) regs mem md L A r bsr s nk bres RA cs (P : config -> Prop),
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> lf_mine L0 A0 L A r 288 -> lf_mine L0 A0 L A s nk ->
  (s + nk <= r \/ r + 288 <= s) -> res_ok_slots A bres ->
  YK11.getr regs 1 = Z_to_bv 64 RA -> YK0s.ret_ok (Z_to_bv 64 RA) ->
  YK11.getr regs 2 = Z_to_bv 64 (spZ regs0 - 448) -> YK11.getr regs 4 = YK11.getr regs0 4 -> YK11.getr regs 10 = Z_to_bv 64 s ->
  rw_cells rsegs mem (spZ regs0 - 448) cs -> Z.of_nat (cells_size cs) = 448 ->
  rw_cells rsegs mem r [CB 288 bsr] ->
  (forall L' A' regs' mem' md',
     lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L' A' mem' md' -> lf_mine L0 A0 L' A' r 288 ->
     res_ok_slots A' (sb_free bres nk) -> regs_preserved regs regs' ->
     rw_cells rsegs mem' (spZ regs0 - 448) cs -> rw_cells rsegs mem' r [CB 288 bsr] ->
     SR rsegs (mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 RA) mem' (YK11.seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_FREE) mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b CTX fx' regs mem md L A r bsr s nk bres RA cs P
    FR MINE MINEs Hsr RES G1 HRA G2 G4 G10 CF Hcs CR K.
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hstk & Hra & Hpre & Hsn & Hsp47 & Hres0 & Hroom & Hro0
    & Hrelro & Hfrm0 & Hn26).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  unfold LLVM_K, LLVM_FRAME in Hstk.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. pose proof YM05.alloc_ceiling_lt as Hlt.
  set (S := spZ regs0) in *.
  assert (Hsp : spZ regs = S - 448) by (unfold spZ; rewrite G2; apply MState.unsigned_lit; lia).
  pose proof MINEs as (Hsin & Hs0 & Hsd).
  pose proof Hsin as Hsin'. apply blocks_In in Hsin' as (q & Hq & Hqin).
  assert (Hfreed : forall a, ptr_addr L q <= a < ptr_addr L q + nk -> a < YM05.alloc_ceiling /\ ~ in_img B a /\
             forall a0 k0, In (a0, k0) (blocks L0 A0) -> ~ (a0 <= a < a0 + k0)).
  { intros a Ha. rewrite Hq in Ha.
    destruct (lf_mine_bytes B API AX L0 A0 L A mem md s nk a HM MINEs Ha) as (N1 & N2 & N3 & _ & N4).
    split; [lia|]. split; [exact N2 | exact N4]. }
  rewrite <- SEGS.
  eapply SR_bind.
  { replace (Z_to_bv 64 LLVM_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite HFRE; reflexivity).
    apply (FREE fx' L A regs mem md q nk bres).
    - split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [rewrite G1; exact HRA|].
      split; [rewrite Hsp; replace (S - 448) with (S + (-28) * 16) by lia; rewrite Z.mod_add by lia; exact Hal|].
      split; [rewrite Hsp; unfold ALLOC_STACK; lia|]. split; [rewrite Hsp; lia|].
      split; [intros a Ha; apply Hstw; rewrite Hsp in Ha; unfold ALLOC_STACK in Ha; lia|].
      split; [rewrite G4; exact Htp|]. split; [exact Herr|]. intros E. rewrite HID in E. discriminate.
    - rewrite SEGS. exact Hro.
    - exact Hqin.
    - rewrite G10, Hq. reflexivity.
    - exact RES. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt
    & Hlen & Hres2).
  rewrite SEGS, G1.
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | rewrite Hsp; unfold ALLOC_STACK; lia | rewrite Hsp; lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. right. destruct (Hfreed a Ha) as (N1 & N2 & _). auto.
    - intros a Ha. right. intros Hf. destruct (Hfreed a Hf) as (N1 & _). lia.
    - intros a Hf Ha. destruct (Hfreed a Hf) as (N1 & _). lia.
    - intros a0 k0 Hin. pose proof (Hblk a0 k0 Hin) as Hin2. rewrite Eb1 in Hin2. rewrite Eb2.
      apply in_app_or in Hin2. apply in_or_app.
      destruct Hin2 as [Hin2|[Hin2|Hin2]]; [left; exact Hin2 | | right; exact Hin2].
      exfalso. injection Hin2 as E1 E2. subst a0 k0. destruct (Hsd _ _ Hin); rewrite Hq in *; lia.
    - intros a0 k0 i Hin Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin)); [|exact Hi].
      intros E. rewrite Hq in E. subst a0. destruct (Hsd _ _ Hin); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  destruct MINE as (Hrin & Hr0 & Hrd).
  assert (MINE' : lf_mine L0 A0 L2 A2 r 288).
  { split; [|split; [lia | exact Hrd]]. pose proof Hrin as Hrin2. rewrite Eb1 in Hrin2. rewrite Eb2.
    apply in_app_or in Hrin2. apply in_or_app. destruct Hrin2 as [h|[h|h]]; [left; exact h | | right; exact h].
    exfalso. injection h as E1 E2. rewrite Hq in E1. lia. }
  assert (CF' : rw_cells rsegs mem2 (S - 448) cs).
  { apply (lf_rw_cells_frame mem); [exact CF|]. intros a Ha. rewrite Hcs in Ha.
    rewrite <- SEGS. apply Hfr2.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    - unfold scratch_k, scratch. pose proof Hsp. unfold ALLOC_STACK.
      intros [h|h]; [lia | pose proof (lf_errno_low B ERRNO_LOW a h); lia].
    - intros Hf. destruct (Hfreed a Hf) as (N1 & _). lia. }
  assert (CR' : rw_cells rsegs mem2 r [CB 288 bsr]).
  { apply (lf_rw_cells_frame mem); [exact CR|]. intros a Ha. change (Z.of_nat (cells_size [CB 288 bsr])) with 288 in Ha.
    split.
    - pose proof (Hkept r 288 (a - r) Hrin ltac:(intros E; rewrite Hq in E; lia) ltac:(lia)) as E.
      replace (r + (a - r)) with a in E by lia. rewrite <- SEGS. exact E.
    - split; intros _.
      + exact (nm_mine_writable AX SEGS L0 A0 L2 A2 mem2 md2 r 288 a HM2 MINE' ltac:(lia)).
      + exact (nm_mine_writable AX SEGS L0 A0 L A mem md r 288 a HM (conj Hrin (conj Hr0 Hrd)) ltac:(lia)). }
  exact (K L2 A2 regs2 mem2 md2 FR2 MINE' Hres2 Hrp CF' CR').
Qed.

End G.
