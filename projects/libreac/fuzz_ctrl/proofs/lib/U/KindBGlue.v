From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge Bytes.
Import ListNotations.
Local Open Scope Z_scope.

Definition rmk (regs : bvmap 5 word) : bvmap 5 word :=
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
    (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
    (getr regs 29) (getr regs 30) (getr regs 31).

Lemma kb_getr_eqv : forall R R', Regs6ss.xregs_eqv R R' -> forall r, getr R' r = getr R r.
Proof.
  intros R R' H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma kb_rmk_getr : forall regs r, getr (rmk regs) r = getr regs r.
Proof. intros regs r. apply kb_getr_eqv. exact (Regs6ss.mkR_of_eqv regs). Qed.

Lemma kb_preserved_trans : forall r1 r2 r3, regs_preserved r1 r2 -> regs_preserved r2 r3 -> regs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma kb_preserved_getr : forall r1 r2 r3, regs_preserved r1 r2 -> (forall r, getr r3 r = getr r2 r) ->
  regs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite H2. exact (H1 r Hr). Qed.

Ltac kb_saved :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]; [subst r; reflexivity .. |];
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

Lemma kb_vm_id : forall md, with_vmmaps (m_vmmaps md) md = md.
Proof. intros [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma kb_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma kb_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

Lemma kb_ret_pc : forall k, YK0s.ret_ok k -> MState.ret_pc k = k.
Proof.
  intros k Hk. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, kb_mod2_land; apply kb_land_m2).
  rewrite <- (MState.Z_to_bv_bv_unsigned k). apply MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

Lemma kb_find_segment : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma kb_outside : forall W x, (forall lo hi, In (lo, hi) W -> ~ (lo <= x < hi)) -> Frame.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn; [exact I|].
  split; [apply (H lo hi); left; reflexivity|].
  apply IH. intros lo' hi' Hin. apply (H lo' hi'). right. exact Hin.
Qed.

Lemma kb_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
Qed.

Section Words.
Variable segs : list Segment.

Lemma kb_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma kb_le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma kb_le_byte_range : forall v w k, 0 <= le_byte v w k < 256.
Proof. intros. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma kb_byte_unsigned : forall v w k, bv_unsigned (Z_to_bv 8 (le_byte v w k)) = le_byte v w k.
Proof.
  intros v w k. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (kb_le_byte_range v w k).
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma kb_unsigned_zxb : forall b : byte, bv_unsigned (Mem.zxb b) = bv_unsigned b.
Proof.
  intros b. unfold Mem.zxb. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in H. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.

Lemma kb_le8_digits : forall v, 0 <= v < 2 ^ 64 ->
  v = le_byte v 8 0 + 256 * (le_byte v 8 1 + 256 * (le_byte v 8 2 + 256 * (le_byte v 8 3 +
      256 * (le_byte v 8 4 + 256 * (le_byte v 8 5 + 256 * (le_byte v 8 6 + 256 * le_byte v 8 7)))))).
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v) by lia.
  assert (S : forall x k, Z.shiftr x (8 * Z.of_nat (S k)) = Z.shiftr (Z.shiftr x (8 * Z.of_nat k)) 8).
  { intros x k. rewrite Z.shiftr_shiftr by lia. f_equal. lia. }
  rewrite !S. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mbyte_munch : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  mbyte segs m' a = mbyte segs m a.
Proof.
  intros W m m' a H Ha Ho. unfold mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite MState.unsigned_lit by exact Ha. exact Ho.
Qed.

Lemma writable_munch : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros W m m' a H Ha Ho. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite MState.unsigned_lit by exact Ha. exact Ho.
Qed.

Lemma present_munch : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  present m a -> present m' a.
Proof.
  intros W m m' a H Ha Ho [b Hb]. exists b. rewrite (H (Z_to_bv 64 a)); [exact Hb|].
  rewrite MState.unsigned_lit by exact Ha. exact Ho.
Qed.

Lemma outside_one : forall lo hi x, x < lo \/ hi <= x -> Frame.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact I]. Qed.

Lemma outside_app : forall W1 W2 x, Frame.outside (W1 ++ W2) x -> Frame.outside W1 x /\ Frame.outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH W2 x H2) as [H3 H4]. split; [split; assumption | exact H4].
Qed.

Lemma munch_cat : forall W1 W2 m m1 m2, Frame.munch W1 m m1 -> Frame.munch W2 m1 m2 -> Frame.munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 H1 H2 x Hx. destruct (outside_app W1 W2 _ Hx) as [Ha Hb].
  rewrite (H2 x Hb). apply H1. exact Ha.
Qed.

Lemma word_mem_frame : forall mem mem' a v, word_mem segs mem a v ->
  (forall k, 0 <= k < 8 -> mbyte segs mem' (a + k) = mbyte segs mem (a + k)) -> word_mem segs mem' a v.
Proof. intros mem mem' a v Hw H k Hk. rewrite H by lia. exact (Hw k Hk). Qed.

Lemma word_mem_le8 : forall mem a v, word_mem segs mem a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  Mem.bytes_at segs mem a (Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros mem a v Hw Hv Ha Hb. split; [exact Ha|]. rewrite Mem.length_le8. split; [lia|].
  intros i Hi. unfold Mem.le8, word_to_le_bytes. rewrite kb_nth_le_bytes by exact Hi.
  rewrite MState.unsigned_lit by lia. rewrite <- kb_le_byte_bv by exact Hv. exact (Hw i Hi).
Qed.

Lemma bytes_at_le8_word : forall mem a w, Mem.bytes_at segs mem a (Mem.le8 w) -> word_mem segs mem a (bv_unsigned w).
Proof.
  intros mem a w (Ha & Hb & H) k Hk.
  pose proof (bv_unsigned_in_range 64 w) as Hr.
  rewrite kb_le_byte_bv by exact Hr.
  rewrite Mem.length_le8 in H. specialize (H k Hk). unfold Mem.le8, word_to_le_bytes in H.
  rewrite kb_nth_le_bytes in H by exact Hk. exact H.
Qed.

Lemma word_mem_byte1 : forall mem a v k, word_mem segs mem a v -> 0 <= a -> a + 8 <= 2 ^ 64 -> (k < 8)%nat ->
  ov_read_bytes segs mem (Mem.wa (a + Z.of_nat k)) 1 = Some [Z_to_bv 8 (le_byte v 8 k)].
Proof.
  intros mem a v k Hw Ha Hb Hk.
  assert (H1 : Mem.bytes_at segs mem (a + Z.of_nat k) [Z_to_bv 8 (le_byte v 8 k)]).
  { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    destruct i as [|i]; [|lia].
    replace (a + Z.of_nat k + Z.of_nat 0) with (a + Z.of_nat k) by lia. exact (Hw k Hk). }
  replace (a + Z.of_nat k) with (a + Z.of_nat k + 0) at 1 by lia.
  rewrite (Mem.bytes_at_read segs mem (a + Z.of_nat k) _ 0 1 H1) by (cbn; lia). reflexivity.
Qed.

Lemma word_mem_of_shr : forall mem a v, 0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)))) ->
  word_mem segs mem a v.
Proof. intros mem a v Hv H k Hk. rewrite kb_le_byte_bv by exact Hv. exact (H k Hk). Qed.

Lemma kb_word_munch : forall mem mem' W a v, word_mem segs mem a v -> Frame.munch W mem mem' ->
  (forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ Frame.outside W (a + k)) -> word_mem segs mem' a v.
Proof.
  intros mem mem' W a v Hw Hm H. apply (word_mem_frame mem); [exact Hw|].
  intros k Hk. destruct (H k Hk) as [Hr Ho]. unfold mbyte. rewrite (Hm (Z_to_bv 64 (a + k))); [reflexivity|].
  rewrite MState.unsigned_lit by exact Hr. exact Ho.
Qed.

Lemma kb_mem_inv_munch : forall W m m', Mem.mem_inv segs m -> Frame.munch W m m' ->
  (forall x : word, ~ Frame.outside W (bv_unsigned x) -> wview segs m x <> None) -> Mem.mem_inv segs m'.
Proof.
  intros W m m' Hi Hm HW x b Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (Hm x Ho) in Hx. exact (Hi x b Hx).
  - destruct (m x) as [b'|] eqn:E; [exact (Hi x b' E)|]. exact (Mem.wview_not_ro segs m x (HW x Ho) E).
Qed.

Lemma kb_mem_inv_cj_munch : forall W m m', mem_inv_cj segs m -> Frame.munch W m m' ->
  (forall x : word, ~ Frame.outside W (bv_unsigned x) -> wview segs m x <> None) -> mem_inv_cj segs m'.
Proof.
  intros W m m' Hi Hm HW x b Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (Hm x Ho) in Hx. exact (Hi x b Hx).
  - destruct (m x) as [b'|] eqn:E; [exact (Hi x b' E)|].
    split; [exact (Mem.wview_not_ro segs m x (HW x Ho) E)|].
    pose proof (HW x Ho) as Hw. unfold wview in Hw. rewrite E in Hw.
    destruct (find_segment segs (bv_unsigned x) 1) as [seg|]; [left; discriminate | contradiction].
Qed.

End Words.

Ltac kb_pow :=
  repeat match goal with
  | |- context [Z.pow 2 ?c] =>
      let v := eval vm_compute in (Z.pow 2 c) in
      lazymatch v with Zpos _ => change (Z.pow 2 c) with v end
  end.

Ltac kb_side := kb_pow; first [ lia | Z.div_mod_to_equations; lia ].

Ltac kb_free t :=
  lazymatch t with
  | context [Z.lor _ _] => fail
  | context [@bv_unsigned 64 (Z_to_bv 64 _)] => fail
  | _ => idtac
  end.

Ltac kb_bounds :=
  repeat match goal with
  | |- context [le_byte ?v ?w ?k] =>
      lazymatch goal with
      | _ : 0 <= le_byte v w k < 256 |- _ => fail
      | _ => pose proof (kb_le_byte_range v w k)
      end
  end.

Lemma kb_lor_low : forall a b n, 0 <= n -> 0 <= a -> 0 <= b < 2 ^ n -> a mod 2 ^ n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low a n i Hlt), Hm, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma kb_lor_low_r : forall a b n, 0 <= n -> 0 <= a -> 0 <= b < 2 ^ n -> a mod 2 ^ n = 0 -> Z.lor b a = a + b.
Proof. intros a b n H1 H2 H3 H4. rewrite Z.lor_comm. exact (kb_lor_low a b n H1 H2 H3 H4). Qed.

Ltac kb_lor_one a b :=
  first [ rewrite (kb_lor_low a b 8) by kb_side | rewrite (kb_lor_low_r b a 8) by kb_side
        | rewrite (kb_lor_low a b 16) by kb_side | rewrite (kb_lor_low_r b a 16) by kb_side
        | rewrite (kb_lor_low a b 24) by kb_side | rewrite (kb_lor_low_r b a 24) by kb_side
        | rewrite (kb_lor_low a b 32) by kb_side | rewrite (kb_lor_low_r b a 32) by kb_side
        | rewrite (kb_lor_low a b 40) by kb_side | rewrite (kb_lor_low_r b a 40) by kb_side
        | rewrite (kb_lor_low a b 48) by kb_side | rewrite (kb_lor_low_r b a 48) by kb_side
        | rewrite (kb_lor_low a b 56) by kb_side | rewrite (kb_lor_low_r b a 56) by kb_side ].

Ltac kb_lbu :=
  rewrite ?kb_unsigned_zxb, ?kb_byte_unsigned; kb_bounds;
  repeat match goal with |- context [Z.shiftl ?x ?c] => rewrite (Z.shiftl_mul_pow2 x c) by lia end;
  repeat match goal with
  | |- context [@bv_unsigned 64 (Z_to_bv 64 ?e)] => kb_free e; rewrite (MState.unsigned_lit e) by kb_side
  | |- context [Z.lor ?a ?b] => kb_free a; kb_free b; kb_lor_one a b
  end.

Ltac kb_lbu8 v := kb_lbu; pose proof (kb_le8_digits v ltac:(lia)); kb_pow; lia.

Section KindB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Lemma kb_md : forall L A mem md, MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros L A mem md H. destruct (mr_model _ _ (aa_laws API) _ _ _ _ H) as (H1 & H2 & _). split; assumption.
Qed.

Lemma kb_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom segs) /\ K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SR segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) P) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SR_canon segs (mkst regs pc mem (seg_rom segs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

Definition img_low : Prop :=
  (forall a, in_img B a -> 0 <= a < alloc_ceiling) /\
  (forall x seg, find_segment segs x 1 = Some seg -> 0 <= x < alloc_ceiling).

Definition img_check (C : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? C) segs &&
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? C) (segments_reserved segs).

Lemma img_low_of_check : forall C, img_check C = true -> C <= alloc_ceiling -> img_low.
Proof.
  intros C H HC. unfold img_check in H. apply andb_prop in H as [H1 H2].
  rewrite forallb_forall in H1, H2. split.
  - intros a (_ & s & Hs & Ha). specialize (H2 s Hs). apply Z.leb_le in H2.
    pose proof (bv_unsigned_in_range 64 (fst s)). pose proof (bv_unsigned_in_range 64 (snd s)). lia.
  - intros x seg Hf. destruct (kb_find_segment segs x 1 seg Hf) as (Hin & Hlo & Hhi).
    specialize (H1 seg Hin). apply Z.leb_le in H1. lia.
Qed.

Lemma kb_stk : img_low -> forall K L A regs mem md, call_pre_k B MR K L A regs mem md -> 0 <= K ->
  Frame.stk segs mem (spZ regs - K) (spZ regs).
Proof.
  intros [_ HI] K L A regs mem md (HM & _ & _ & _ & _ & Hlo & Hhi & HW & _) HK.
  pose proof alloc_ceiling_val as Hc.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hw : writable_at segs mem a) by (apply HW; lia).
  split; [exact Hw|].
  revert Hw. unfold Mem.mrd, Mem.wa, writable_at, wview.
  destruct (mem (Z_to_bv 64 a)) as [b|]; intros Hw; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by lia.
  destruct (find_segment segs a 1) as [seg|] eqn:F; [|contradiction].
  exfalso. destruct (HI a seg F). lia.
Qed.

Lemma kb_MR_A : forall L A mem mem' md W, MR L A mem md -> Frame.munch W mem mem' ->
  (forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
     Frame.outside W x) ->
  MR L A mem' md.
Proof.
  intros L A mem mem' md W HM Hm HW.
  pose proof alloc_ceiling_lt as Hc.
  assert (Heq : forall x, 0 <= x < alloc_ceiling ->
            (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
            mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Ho. apply Hm. rewrite MState.unsigned_lit by lia. apply HW; assumption. }
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  apply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
  - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    unfold mbyte. rewrite (Heq a); [reflexivity | lia | left; exact Ho].
  - intros a Ho (b & Hb). pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    exists b. rewrite (Heq a); [exact Hb | lia | left; exact Ho].
  - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as ((b & Hb) & H1 & H2 & _).
    exists b. rewrite (Heq (ptr_addr L p + i)); [exact Hb | lia |].
    right. exists (ptr_addr L p), n. split; [|lia]. unfold blocks. apply in_map_iff.
    exists (p, n). split; [reflexivity | exact Hin].
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

Lemma kb_blocks_munch : forall L A mem mem' md W, MR L A mem md -> Frame.munch W mem mem' ->
  (forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
     Frame.outside W x) ->
  forall a n i, In (a, n) (blocks L A) -> 0 <= i < n -> mbyte segs mem' (a + i) = mbyte segs mem (a + i).
Proof.
  intros L A mem mem' md W HM Hm HO a n i Hin Hi.
  pose proof Hin as Hin'. unfold blocks in Hin'. apply in_map_iff in Hin' as ([q n'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as Ea En. subst a n.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n' HM Hq) as [H1 H2].
  pose proof alloc_ceiling_lt.
  apply (mbyte_munch segs W); [exact Hm | lia |].
  apply HO; [lia|]. right. exists (ptr_addr L q), n'. split; [exact Hin | lia].
Qed.

Definition kb_mid (K sp : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ ((sp - K <= a < sp) \/ (errno_addr B <= a < errno_addr B + 4)) ->
     ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, (sp - K <= a < sp) \/ (errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem' a).

Lemma kb_mid_call : forall K L A regs mem md E L' A' regs' mem' md',
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  kb_mid K (spZ regs) L A mem md E L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [|exact H6].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H7 (conj H8 (conj H9 H10)))))))).
Qed.

Lemma kb_post : forall K L A regs mem md E L' A' regs' mem' md',
  kb_mid K (spZ regs) L A mem md E L' A' mem' md' -> regs_preserved regs regs' ->
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) H6.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 H10))))))))).
Qed.

Lemma kb_mid_E : forall K sp L A mem md (E E' : Z -> Prop) L' A' mem' md',
  kb_mid K sp L A mem md E L' A' mem' md' -> (forall a, E a -> E' a) -> kb_mid K sp L A mem md E' L' A' mem' md'.
Proof.
  intros K sp L A mem md E E' L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He. apply H8; auto.
Qed.

Lemma kb_mid_refl : forall K sp L A mem md E, MR L A mem md -> WF A -> bounded A ->
  (forall a, (sp - K <= a < sp) \/ (errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  kb_mid K sp L A mem md E L A mem md.
Proof.
  intros K sp L A mem md E HM HW HB HS.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [intros; reflexivity|]. split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; reflexivity|]. exact HS.
Qed.

Lemma kb_mid_A : img_low -> forall K sp L A mem md mem' W (E : Z -> Prop),
  MR L A mem md -> WF A -> bounded A ->
  (forall a, (sp - K <= a < sp) \/ (errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  Frame.munch W mem mem' -> Frame.wmono segs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - K <= x < sp) -> ~ E x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
     Frame.outside W x) ->
  kb_mid K sp L A mem md E L A mem' md.
Proof.
  intros [HI _] K sp L A mem md mem' W E HM HWF HB HS Hm Hw HE HO.
  pose proof alloc_ceiling_lt as Hc. pose proof alloc_ceiling_val as Hc'.
  split; [exact (kb_MR_A L A mem mem' md W HM Hm HO)|].
  split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [intros; reflexivity|]. split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split.
  { intros a Ha Ho _ Hs He.
    assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply HI in Ha; lia]).
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { apply Hm. rewrite MState.unsigned_lit by exact Hr. apply HE; [exact Hr | tauto | exact He]. }
    unfold mbyte, writable_at, wview. rewrite Hx. tauto. }
  split.
  { intros p n i Hin _ Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (_ & H1 & H2 & _).
    unfold mbyte. rewrite (Hm (Z_to_bv 64 (ptr_addr L p + i))); [reflexivity|].
    rewrite MState.unsigned_lit by lia. apply HO; [lia|]. right. exists (ptr_addr L p), n. split; [|lia].
    apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin]. }
  intros a Ha. unfold writable_at. apply Hw. exact (HS a Ha).
Qed.

Lemma kb_mid_seqAX : forall K sp L A mem md E1 mem1 K2 sp2 E2 L' A' mem' md',
  kb_mid K sp L A mem md E1 L A mem1 md ->
  kb_mid K2 sp2 L A mem1 md E2 L' A' mem' md' ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling + K <= sp -> sp <= 2 ^ 64 ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> ~ E2 a) ->
  kb_mid K sp L A mem md (fun a => E1 a \/ E2 a) L' A' mem' md'.
Proof.
  intros K sp L A mem md E1 mem1 K2 sp2 E2 L' A' mem' md'
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1) (M2 & W2 & B2 & Y2 & P2 & D2 & F2 & K2' & S2) H1 H2 H3 H4 H5.
  pose proof alloc_ceiling_val as Hc.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [exact Y2|]. split; [exact P2|].
  split; [exact D2|].
  split.
  { intros a Ha Ho Ho' Hs He.
    destruct (F1 a Ha Ho Ho ltac:(tauto) ltac:(tauto)) as [E1a E1w].
    destruct (F2 a Ha Ho Ho' ltac:(intros [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]) ltac:(tauto))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin' Hi. rewrite (K2' p n i Hin Hin' Hi). exact (K1 p n i Hin Hin Hi). }
  intros a Ha.
  assert (Hd : (sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4) \/
               ~ ((sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4))) by lia.
  destruct Hd as [Hd|[Hd|Hd]]; [apply S2; left; exact Hd | apply S2; right; exact Hd |].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hd; right; exact Ha].
  assert (No : ~ owned B L A a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho); lia).
  assert (No' : ~ owned B L' A' a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho); lia).
  apply (proj2 (F2 a ltac:(left; lia) No No' Hd ltac:(apply H5; lia))). apply S1. left. exact Ha.
Qed.

Lemma kb_mid_seqXA : forall K sp L A mem md E1 L' A' mem1 md' K2 sp2 E2 mem',
  kb_mid K sp L A mem md E1 L' A' mem1 md' ->
  kb_mid K2 sp2 L' A' mem1 md' E2 L' A' mem' md' ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling + K <= sp -> sp <= 2 ^ 64 ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> ~ E2 a) ->
  kb_mid K sp L A mem md (fun a => E1 a \/ E2 a) L' A' mem' md'.
Proof.
  intros K sp L A mem md E1 L' A' mem1 md' K2 sp2 E2 mem'
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1) (M2 & W2 & B2 & Y2 & P2 & D2 & F2 & K2' & S2) H1 H2 H3 H4 H5.
  pose proof alloc_ceiling_val as Hc.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [exact Y1|]. split; [exact P1|].
  split; [exact D1|].
  split.
  { intros a Ha Ho Ho' Hs He.
    destruct (F1 a Ha Ho Ho' ltac:(tauto) ltac:(tauto)) as [E1a E1w].
    destruct (F2 a Ha Ho' Ho' ltac:(intros [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]) ltac:(tauto))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin' Hi. rewrite <- (P1 p n Hin Hin'). rewrite (K2' p n i Hin' Hin' Hi).
    rewrite (P1 p n Hin Hin'). exact (K1 p n i Hin Hin' Hi). }
  intros a Ha.
  assert (Hd : (sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4) \/
               ~ ((sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4))) by lia.
  destruct Hd as [Hd|[Hd|Hd]]; [apply S2; left; exact Hd | apply S2; right; exact Hd |].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hd; right; exact Ha].
  assert (No' : ~ owned B L' A' a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho); lia).
  apply (proj2 (F2 a ltac:(left; lia) No' No' Hd ltac:(apply H5; lia))). apply S1. left. exact Ha.
Qed.

Lemma kb_mid_tail : img_low -> forall K sp L A mem md E1 L' A' mem1 md' mem' W (E2 : Z -> Prop),
  kb_mid K sp L A mem md E1 L' A' mem1 md' ->
  Frame.munch W mem1 mem' -> Frame.wmono segs mem1 mem' -> (forall x, mem1 x <> None -> mem' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - K <= x < sp) -> ~ E2 x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> owned B L' A' x -> Frame.outside W x) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     Frame.outside W (ptr_addr L p + i)) ->
  kb_mid K sp L A mem md (fun a => E1 a \/ E2 a) L' A' mem' md'.
Proof.
  intros [HI _] K sp L A mem md E1 L' A' mem1 md' mem' W E2 (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1)
    Hm Hw Hp HE HO HB.
  pose proof alloc_ceiling_lt as Hc. pose proof alloc_ceiling_val as Hc'.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & Hmat).
  split.
  { apply (mr_frame _ _ (aa_laws API) L' A' mem1 mem' md' md' M1).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (mbyte_munch segs W); [exact Hm | lia | apply HO; [lia | exact Ho]].
    - intros a Ho Hpr. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (present_munch W mem1); [exact Hm | lia | apply HO; [lia | exact Ho] | exact Hpr].
    - intros q n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i M1 Hin Hi) as ((b & Hb) & _).
      destruct (mem' (Z_to_bv 64 (ptr_addr L' q + i))) as [b'|] eqn:E; [exists b'; exact E|].
      exfalso. apply (Hp (Z_to_bv 64 (ptr_addr L' q + i))); [rewrite Hb; discriminate | exact E].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact W1|]. split; [exact B1|]. split; [exact Y1|]. split; [exact P1|]. split; [exact D1|].
  split.
  { intros a Ha Ho Ho' Hs He.
    assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply HI in Ha; lia]).
    destruct (F1 a Ha Ho Ho' ltac:(tauto) ltac:(tauto)) as [E1a E1w].
    assert (Hout : Frame.outside W a) by (apply HE; [exact Hr | tauto | tauto]).
    split.
    - rewrite (mbyte_munch segs W mem1 mem' a Hm Hr Hout). exact E1a.
    - rewrite E1w. exact (writable_munch segs W mem1 mem' a Hm Hr Hout). }
  split.
  { intros p n i Hin Hin' Hi.
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n M1 Hin') as [R1 R2].
    rewrite (P1 p n Hin Hin') in R1, R2.
    rewrite (mbyte_munch segs W mem1 mem' (ptr_addr L p + i) Hm ltac:(lia) (HB p n i Hin Hin' Hi)).
    exact (K1 p n i Hin Hin' Hi). }
  intros a Ha. unfold writable_at. apply Hw. exact (S1 a Ha).
Qed.

Lemma kb_auxv : forall sec lo mem mem' W L A md, MR L A mem md -> auxv_pre B sec lo mem -> Frame.munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> lo <= x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> owned B L A x -> Frame.outside W x) ->
  auxv_pre B sec lo mem'.
Proof.
  intros sec lo mem mem' W L A md HM (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) Hm Hhi Hlo.
  exists av, ar. pose proof alloc_ceiling_lt as Hc.
  assert (Hst : forall k, 0 <= k < 8 -> 0 <= ms_libc B + 8 + k < alloc_ceiling /\ owned B L A (ms_libc B + 8 + k)).
  { intros k Hk. assert (Ho : owned B L A (ms_libc B + 8 + k)) by (right; unfold static_owned; right; right; left; lia).
    split; [exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) | exact Ho]. }
  split.
  { apply (kb_word_munch segs mem mem' W); [exact H1 | exact Hm |]. intros k Hk. destruct (Hst k Hk) as [Hr Ho].
    split; [lia | apply Hlo; [lia | exact Ho]]. }
  split.
  { intros k Hk. apply (kb_word_munch segs mem mem' W); [exact (H2 k Hk) | exact Hm |]. intros j Hj.
    assert (Z.of_nat k < 10) by lia. split; [lia | apply Hhi; lia]. }
  split.
  { apply (kb_word_munch segs mem mem' W); [exact H3 | exact Hm |]. intros j Hj. split; [lia | apply Hhi; lia]. }
  split.
  { apply (kb_word_munch segs mem mem' W); [exact H4 | exact Hm |]. intros j Hj. split; [lia | apply Hhi; lia]. }
  repeat split; assumption.
Qed.

Lemma kb_pre_A : forall K f K1 L A regs mem md regs1 mem1 W,
  call_pre_k B MR K L A regs mem md -> 0 <= f -> 0 <= K1 -> f + K1 <= K ->
  spZ regs1 = spZ regs - f -> spZ regs1 mod 16 = 0 ->
  getr regs1 4 = getr regs 4 -> YK0s.ret_ok (getr regs1 1) ->
  Frame.munch W mem mem1 -> Frame.wmono segs mem mem1 ->
  (forall x, 0 <= x < 2 ^ 64 -> spZ regs <= x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
     Frame.outside W x) ->
  call_pre_k B MR K1 L A regs1 mem1 md.
Proof.
  intros K f K1 L A regs mem md regs1 mem1 W (HM & HWF & HB & Hra & Hal & Hlo & Hhi & HW & Htp & Herr & Haux)
    Hf HK1 HfK Hsp Hal1 Htp1 Hra1 Hm Hw Hup Hown.
  split; [exact (kb_MR_A L A mem mem1 md W HM Hm Hown)|].
  split; [exact HWF|]. split; [exact HB|]. split; [exact Hra1|]. split; [exact Hal1|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; unfold writable_at; apply Hw; exact (HW a ltac:(lia))|].
  split; [rewrite Htp1; exact Htp|].
  split; [intros a Ha; unfold writable_at; apply Hw; exact (Herr a Ha)|].
  intros Hd. apply (auxv_pre_mono B (ly_sec L) (spZ regs) (spZ regs1) mem1); [lia|].
  apply (kb_auxv (ly_sec L) (spZ regs) mem mem1 W L A md HM (Haux Hd) Hm Hup).
  intros x Hx Ho. apply Hown; [exact Hx | left; exact Ho].
Qed.

Definition globals_free (G : list (Z * Z)) : Prop :=
  forall a, in_globals G a ->
    in_img B a /\ 0 <= a < alloc_ceiling /\
    (exists seg, find_segment segs a 1 = Some seg /\ seg_writable seg = true) /\
    ~ (errno_addr B <= a < errno_addr B + 4) /\
    forall L A mem md, MR L A mem md -> ~ owned B L A a /\ forall p n, In (p, n) (blocks L A) -> ~ (p <= a < p + n).

Lemma globals_avoid : forall G W L A mem md, globals_free G -> MR L A mem md ->
  (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> in_globals G x) ->
  forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
  Frame.outside W x.
Proof.
  intros G W L A mem md HG HM HW x Hx Ho. apply kb_outside. intros lo hi Hin Hlh.
  destruct (HG x (HW lo hi x Hin Hlh)) as (_ & _ & _ & _ & H). destruct (H L A mem md HM) as [Hn Hb].
  destruct Ho as [Ho|(p & n & Hp & Hpn)]; [exact (Hn Ho) | exact (Hb p n Hp Hpn)].
Qed.

Lemma globals_writable : forall G mem a, globals_free G -> in_globals G a -> mbyte segs mem a <> None ->
  writable_at segs mem a.
Proof.
  intros G mem a HG Ha. destruct (HG a Ha) as (_ & Hr & (seg & Hf & Hwr) & _).
  pose proof alloc_ceiling_lt as Hc.
  unfold mbyte, writable_at, wview, seg_rom, memory_read.
  rewrite !MState.unsigned_lit by lia.
  destruct (mem (Z_to_bv 64 a)) as [b|]; [intros _; discriminate|].
  change (Z.of_N 1) with 1. rewrite Hf. cbv beta iota zeta. rewrite Hwr. cbv beta iota.
  destruct (seg_readable seg); [|intros H; exfalso; apply H; reflexivity].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))); intros H; exact H.
Qed.

Lemma globals_wr_at : forall G mem a v, globals_free G -> (forall k, 0 <= k < 8 -> in_globals G (a + k)) ->
  word_mem segs mem a v -> Mem.wr_at segs mem a 8.
Proof.
  intros G mem a v HG Hin Hw. pose proof alloc_ceiling_lt as Hc.
  destruct (HG (a + 0) (Hin 0 ltac:(lia))) as (_ & Ha & _).
  destruct (HG (a + 7) (Hin 7 ltac:(lia))) as (_ & Ha7 & _).
  split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hb : mbyte segs mem (a + i) <> None).
  { replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. rewrite (Hw (Z.to_nat i)) by lia. discriminate. }
  exact (globals_writable G mem (a + i) HG (Hin i Hi) Hb).
Qed.

Lemma kb_post_globals : forall G K L A regs mem md (E : Z -> Prop) L' A' regs' mem' md' a,
  globals_free G -> MR L A mem md -> call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  alloc_ceiling + K <= spZ regs -> in_globals G a -> ~ E a -> mbyte segs mem' a = mbyte segs mem a.
Proof.
  intros G K L A regs mem md E L' A' regs' mem' md' a HG HM HP Hsp Ha HE.
  destruct HP as (HM' & _ & _ & _ & _ & _ & _ & HF & _).
  destruct (HG a Ha) as (Hi & Hr & _ & He & Ho).
  destruct (Ho L A mem md HM) as [Hn _]. destruct (Ho L' A' mem' md' HM') as [Hn' _].
  assert (Hs : ~ scratch_k B K regs a) by (unfold scratch_k; intros [Hs|Hs]; [lia | exact (He Hs)]).
  exact (proj1 (HF a (or_intror Hi) Hn Hn' Hs HE)).
Qed.

End KindB.
