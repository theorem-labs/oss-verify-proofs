From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require PropExec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Exec Frame Cells Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterApp Ledger put_c put_kb WriterRet.
Import ListNotations.
Local Open Scope Z_scope.

Lemma land_m2_mod : forall u, Z.land u (-2) mod 2 = 0.
Proof.
  intros u. replace (Z.land u (-2)) with (Z.shiftl (Z.shiftr u 1) 1).
  - rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply Z.mod_mul. lia.
  - rewrite <- (Z.ldiff_ones_r u 1) by lia. rewrite Z.ldiff_land. reflexivity.
Qed.

Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. assert (E : bv_unsigned k mod 2 = 0).
  { unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in H. apply (f_equal bv_unsigned) in H.
    rewrite Z_to_bv_unsigned, Z.add_0_r in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
    rewrite <- H. pose proof (land_m2_mod (bv_unsigned k)).
    set (w := Z.land (bv_unsigned k) (-2)) in *. Z.div_mod_to_equations. lia. }
  transitivity (ret_pc (Z_to_bv 64 (bv_unsigned k))); [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite ret_pc_even; [apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range | exact E].
Qed.

Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof.
  intros z Hz He. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ. apply bv_eq.
  rewrite !Z_to_bv_unsigned, Z.add_0_r. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small z) by lia.
  replace (Z.land z (-2)) with z.
  - rewrite ?Z.mod_small by lia; reflexivity.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec. destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Z.bit0_odd. replace (Z.odd z) with false; [reflexivity|].
      rewrite Zodd_mod. rewrite He. reflexivity.
    + replace (Z.testbit (-2) i) with true; [rewrite andb_true_r; reflexivity|].
      replace (-2) with (Z.lnot 1) by reflexivity. rewrite Z.lnot_spec by lia.
      rewrite Z.bits_above_log2 by (cbn; lia). reflexivity.
Qed.

Lemma getr_reg : forall regs (r : reg), bv_eqb r 0 = false -> getr regs r = reg_get regs r.
Proof. intros regs r H. unfold getr. rewrite H. reflexivity. Qed.

Lemma getr_mkR_of : forall regs k, getr (mkR_of regs) k = getr regs k.
Proof.
  intros regs k. unfold getr. destruct (bv_eqb k 0) eqn:E; [reflexivity|].
  symmetry. apply mkR_of_eqv. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (k = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst k. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_kept : forall regs R F pc fc rv m ro x,
  ms_eqv (MS R F pc fc rv m ro) x ->
  (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr (mkR_of regs) (Z_to_bv 5 r)) ->
  regs_preserved regs (ms_regs x).
Proof.
  intros regs R F pc fc rv m ro x HE H r Hr. rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HE), H by exact Hr.
  apply getr_mkR_of.
Qed.

Ltac callee_cases :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |];
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hr' as [->|Hr']; [reflexivity|]); subst r; reflexivity.

Lemma pres_get : forall R F pc fc rv m ro x regs1 (r : reg),
  ms_eqv (MS R F pc fc rv m ro) x -> regs_preserved (ms_regs x) regs1 -> callee_saved (bv_unsigned r) ->
  reg_get regs1 r = reg_get R r.
Proof.
  intros R F pc fc rv m ro x regs1 r HE RP Hr.
  assert (Hz : bv_eqb r 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros E. rewrite E in Hr. unfold callee_saved in Hr.
    match type of Hr with context [bv_unsigned ?k] => let v := eval vm_compute in (bv_unsigned k) in
      change (bv_unsigned k) with v in Hr end; lia. }
  assert (Er : Z_to_bv 5 (bv_unsigned r) = r)
    by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
  rewrite <- !getr_reg by exact Hz. pose proof (RP (bv_unsigned r) Hr) as E. rewrite Er in E.
  rewrite E. exact (eqv_getr _ _ _ _ _ _ _ _ _ HE).
Qed.

Lemma resume_regs : forall R F pc fc rv m ro x regs1,
  ms_eqv (MS R F pc fc rv m ro) x -> regs_preserved (ms_regs x) regs1 ->
  mkR_of regs1 =
  mkR (reg_get regs1 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) (reg_get regs1 5) (reg_get regs1 6)
      (reg_get regs1 7) (reg_get R 8) (reg_get R 9) (reg_get regs1 10) (reg_get regs1 11) (reg_get regs1 12)
      (reg_get regs1 13) (reg_get regs1 14) (reg_get regs1 15) (reg_get regs1 16) (reg_get regs1 17)
      (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23)
      (reg_get R 24) (reg_get R 25) (reg_get R 26) (reg_get R 27) (reg_get regs1 28) (reg_get regs1 29)
      (reg_get regs1 30) (reg_get regs1 31).
Proof.
  intros R F pc fc rv m ro x regs1 HE RP. unfold mkR_of. f_equal;
    (apply (pres_get R F pc fc rv m ro x regs1 _ HE RP); unfold callee_saved;
     match goal with |- context [bv_unsigned ?k] => let v := eval vm_compute in (bv_unsigned k) in
       change (bv_unsigned k) with v end; lia).
Qed.

Lemma bytes_at_eqm : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (Ha & Hb & H) E. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- mbyte_mrd, E by lia. rewrite mbyte_mrd. apply H. exact Hi.
Qed.

Lemma rw_cells_eqm : forall m m' A cs, Step.rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte rsegs m' (A + i) = mbyte rsegs m (A + i) /\ (writable_at rsegs m (A + i) -> writable_at rsegs m' (A + i))) ->
  Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf Hb] (W1 & W2 & Hw)] E. split; [split; [exact Hwf|]|].
  - eapply bytes_at_eqm; [exact Hb|]. intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. apply E. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. apply (proj2 (E i Hi)). exact (Hw i Hi).
Qed.

Fixpoint img_ok (s : Z) (bs : list Z) : bool :=
  match bs with
  | [] => true
  | b :: r =>
      ro_addr rsegs (wa s) &&
      match mbyte rsegs (fun _ => None) s with Some v => (bv_unsigned v =? b) | None => false end &&
      img_ok (s + 1) r
  end.

Lemma img_ok_sound : forall bs s i, img_ok s bs = true -> 0 <= i < Z.of_nat (length bs) ->
  ro_addr rsegs (wa (s + i)) = true /\ mbyte rsegs (fun _ => None) (s + i) = Some (Z_to_bv 8 (nth (Z.to_nat i) bs 0)).
Proof.
  induction bs as [|b r IH]; intros s i H Hi; cbn [length Z.of_nat] in Hi; [lia|].
  cbn [img_ok] in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. split; [exact H1|]. cbn [nth Z.to_nat].
    destruct (mbyte rsegs (fun _ => None) s) as [v|]; [|discriminate]. apply Z.eqb_eq in H2. subst b.
    f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [Z.to_nat nth]. symmetry. apply bv_wrap_small.
    apply bv_unsigned_in_range.
  - destruct (IH (s + 1) (i - 1) H3 ltac:(rewrite Nat2Z.inj_succ in Hi; lia)) as [R1 R2].
    replace (s + 1 + (i - 1)) with (s + i) in R1, R2 by lia.
    split; [exact R1|]. rewrite R2. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis PUTC : put_contract B API RF.
Let MR := aa_MR API.

Lemma img_zbytes : forall mem s bs, ro_agree rsegs mem -> img_ok s bs = true -> zbytes_at B mem s bs.
Proof using SEGS.
  intros mem s bs HI H i Hi. rewrite SEGS. destruct (img_ok_sound bs s i H Hi) as [R1 R2].
  rewrite <- R2, !mbyte_mrd, (HI _ R1). reflexivity.
Qed.

Lemma img_where : forall regs Lam s n buf bs,
  existsb (fun sg => (bv_unsigned (fst sg) <=? s) && (s <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
    (segments_reserved rsegs) = true ->
  img_ok s bs = true -> Z.of_nat (length bs) = n ->
  s_where B regs Lam s n buf.
Proof using SEGS.
  intros regs Lam s n buf bs HS HO HL. right. left. split.
  - unfold in_img. rewrite SEGS. split; [intros E; rewrite E in HS; discriminate|].
    apply existsb_exists in HS. destruct HS as (sg & Hin & Hb). exists sg. split; [exact Hin|].
    apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - intros i Hi. exact (proj1 (img_ok_sound bs s i HO ltac:(lia))).
Qed.

Lemma off_errno_sub : forall a n a' n', off_errno B a n -> a <= a' -> a' + n' <= a + n -> off_errno B a' n'.
Proof. intros a n a' n' H H1 H2. unfold off_errno in *. lia. Qed.

Lemma put_call : forall Kc S L A regs mem md o s n bs buf st Lam peak b (P : config -> Prop),
  S - Kc <= spZ regs - PUT_K -> spZ regs <= S -> alloc_ceiling + Kc <= S -> S < 2 ^ 63 -> spZ regs mod 16 = 0 ->
  (forall a, S - Kc <= a < S -> writable_at (ms_segs B) mem a) ->
  (forall a, errno_at B a -> writable_at (ms_segs B) mem a) ->
  getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK0s.ret_ok (getr regs 1) ->
  MR L A mem md -> WF A -> bounded A -> st_init_done A = true -> ro_agree (ms_segs B) mem ->
  getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
  pj_out_ok B mem Lam o buf (Z.of_nat (length (w_text st))) (w_cap st) (w_failed st) (w_text st) ->
  ledger B L A mem Lam peak (w_cnt st) (w_fail st) -> rf_ok RF A b ->
  S <= o -> off_errno B o 32 -> off_errno B (S - Kc) Kc ->
  zbytes_at B mem s bs -> Z.of_nat (length bs) = n -> bytes_ok bs -> 0 <= s < 2 ^ 64 -> s + n <= 2 ^ 64 ->
  s_where B regs Lam s n buf -> (s + n <= o \/ o + 32 <= s) ->
  Z.of_nat (length (w_text st)) + n + 1 <= WMAX ->
  (w_failed st = 0 -> w_cap st < Z.of_nat (length (w_text st)) + n + 1 ->
     rf_room RF b (newcap (w_cap st) (Z.of_nat (length (w_text st)) + n + 1) + 16)) ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved regs regs1 ->
     wr_rel B API RF (spZ regs - PUT_K) (spZ regs) L A mem md o buf st Lam peak b [bs] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (mkst regs1 (getr regs 1) mem1 (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PUT) mem (seg_rom (ms_segs B))) md) P.
Proof using AX SEGS PUTC.
  intros Kc S L A regs mem md o s n bs buf st Lam peak b P H1 H2 H3 H4 H5 HWs HWe Htp Hra HM HW HB HIN HI
    R10 R11 R12 PJ LG RS HO EO ES ZB LN BO RSs RSn SW SO NEED ROOM K.
  destruct st as [failed text cap cnt fail calls]. cbn [w_text w_cap w_failed w_cnt w_fail w_calls] in *.
  pose proof (Nat2Z.is_nonneg (length text)) as LT0.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RR. change (bv_modulus 64) with (2 ^ 64) in RR.
  assert (PREk : call_pre_k B MR PUT_K L A regs mem md).
  { unfold call_pre_k. split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
    split; [exact H5|]. split; [unfold PUT_K, REALLOC_STACK, ALLOC_STACK in *; lia|]. split; [lia|].
    split; [intros a Ha; apply HWs; lia|]. split; [exact Htp|]. split; [exact HWe|].
    intros Hf. rewrite HIN in Hf. discriminate. }
  assert (ESp : off_errno B (spZ regs - PUT_K) PUT_K) by (eapply off_errno_sub; [exact ES | lia | lia]).
  eapply SR_bind.
  { exact (PUTC L A regs mem md b o s n buf (Z.of_nat (length text)) cap failed text bs Lam peak cnt fail calls
      SEGS PREk HI R10 R11 R12 PJ LG ltac:(lia) EO ESp ZB LN BO RSs RSn SW SO NEED RS ROOM). }
  intros c' PR.
  destruct (wr_rel_put B API RF SEGS AX (spZ regs - PUT_K) (spZ regs) L A regs mem md o n buf (Z.of_nat (length text))
    cap failed text bs Lam peak cnt fail calls b c' PREk PJ LG LN NEED ltac:(lia) ltac:(lia)
    ltac:(unfold PUT_K, REALLOC_STACK, ALLOC_STACK in *; lia) ltac:(unfold spZ in *; lia) PR)
    as (L1 & A1 & regs1 & mem1 & md1 & buf1 & Lam1 & peak1 & b1 & Ec & RP & R).
  subst c'. exact (K regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R).
Qed.

Lemma wr_cells : forall lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 F cs,
  MR L A mem md ->
  wr_rel B API RF lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  Step.rw_cells rsegs mem F cs -> alloc_ceiling <= F -> hi <= F ->
  (F + Z.of_nat (cells_size cs) <= o \/ o + 32 <= F) -> off_errno B F (Z.of_nat (cells_size cs)) ->
  Step.rw_cells rsegs mem1 F cs.
Proof using SEGS.
  intros lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 F cs HM R1 RC H1 H2 H3 H4.
  pose proof (Step.rw_cells_bound _ _ _ _ RC) as RB.
  pose proof R1 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
  apply (rw_cells_eqm mem mem1 F cs RC). intros i Hi. rewrite <- SEGS.
  assert (Hd : alloc_ceiling <= F + i < 2 ^ 64 \/ in_img B (F + i)) by (left; lia).
  assert (N0 : ~ owned B L A (F + i)) by (apply (not_owned_hi B API _ _ _ _ _ HM); lia).
  assert (N1 : ~ owned B L1 A1 (F + i)) by (apply (not_owned_hi B API _ _ _ _ _ HM1); lia).
  assert (N2 : ~ (lo <= F + i < hi)) by lia.
  assert (N3 : ~ errno_at B (F + i)) by (unfold errno_at, off_errno in *; lia).
  assert (N4 : ~ (o <= F + i < o + 32)) by lia.
  assert (N5 : ~ alloc_statics (F + i)) by (intros S; pose proof (statics_low (F + i) S); lia).
  destruct (FR (F + i) Hd N0 N1 N2 N3 N4 N5) as [E W].
  split; [exact E | tauto].
Qed.

Lemma wr_writable : forall lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 x y,
  wr_rel B API RF lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  lo <= x -> y <= hi ->
  (forall a, x <= a < y -> writable_at (ms_segs B) mem a) ->
  (forall a, errno_at B a -> writable_at (ms_segs B) mem a) ->
  (forall a, x <= a < y -> writable_at (ms_segs B) mem1 a) /\
  (forall a, errno_at B a -> writable_at (ms_segs B) mem1 a).
Proof.
  intros lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 x y R1 H1 H2 W1 W2.
  pose proof R1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WR).
  split; intros a Ha; [apply WR; [left; lia | apply W1; exact Ha] | apply WR; [right; exact Ha | apply W2; exact Ha]].
Qed.

Lemma post_shape : forall regs R m' x md,
  ms_eqv (MS R (@fp_regs fx) (ret_pc (reg_get regs 1)) (@fp_csr fx) None m' (PropExec.seg_rom rsegs)) x ->
  ret_pc (reg_get regs 1) = getr regs 1 ->
  mkCfg x md = mkCfg (YK11.mkst (ms_regs x) (getr regs 1) m' (YK11.seg_rom (ms_segs B))) md /\ ms_mem x = m'.
Proof using SEGS.
  intros regs R m' x md HE PC. split.
  - rewrite SEGS. f_equal. rewrite <- PC. exact (eqv_shape _ _ _ _ HE).
  - destruct HE as (_ & _ & _ & _ & _ & _ & HM & _). cbn in HM. congruence.
Qed.

End C.
