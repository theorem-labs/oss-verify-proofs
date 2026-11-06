From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import MState Mem Exec Frame Cells Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterSpecFacts WriterApp Ledger fuzz_realloc_c memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import put_c put_kb put_blocks.
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

Lemma getr_reg : forall regs (r : reg), bv_eqb r 0 = false -> getr regs r = reg_get regs r.
Proof. intros regs r H. unfold getr. rewrite H. reflexivity. Qed.

Lemma ranges_apart : forall a n b k, 0 < n -> 0 < k ->
  (forall z, a <= z < a + n -> b <= z < b + k -> False) -> a + n <= b \/ b + k <= a.
Proof.
  intros a n b k Hn Hk H. destruct (Z_le_gt_dec (a + n) b) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (b + k) a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.

Lemma bytes_list : forall m a k, 0 <= a -> 0 <= k -> a + k <= 2 ^ 64 ->
  (forall i, 0 <= i < k -> present m (a + i)) ->
  exists l, Z.of_nat (length l) = k /\ bytes_at rsegs m a l.
Proof.
  intros m a k Ha Hk Hb H.
  assert (G : forall n : nat, Z.of_nat n <= k -> exists l, length l = n /\
            forall i, (i < n)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = nth_error l i).
  { induction n as [|n IH]; intros Hn.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (l & Hl & Hi).
      destruct (H (Z.of_nat n) ltac:(lia)) as (b & Hb').
      exists (l ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi'. destruct (Nat.eqb_spec i n) as [->|Hne].
      + rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn. unfold mrd, wa. rewrite Hb'. reflexivity.
      + rewrite nth_error_app1 by lia. apply Hi. lia. }
  destruct (G (Z.to_nat k) ltac:(lia)) as (l & Hl & Hi). exists l. split; [lia|].
  split; [lia|]. split; [lia|]. intros i Hi'. apply Hi. lia.
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

Lemma rw_cells_bytes : forall m A cs, Step.rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma wx_apart_img : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [W Hb]. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ HR (ro_false_of_wview rsegs m m0 _ HR W)). exact W.
  - rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 -> Step.rw_cells rsegs m0 A cs -> Step.rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma stk_norm : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> ro_addr rsegs (wa a) = false) -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RO (H1 & H2 & H) HF. pose proof (mem_rel_normalize rsegs m RO) as HN.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [W Hb]. split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ HN (HF a Ha)). exact W.
  - rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ HN). exact Hb.
Qed.

Lemma rw_cells_norm : forall m A cs, ro_agree rsegs m -> Step.rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  Step.rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RO [[Hwf Hb] Hw] HF. pose proof (mem_rel_normalize rsegs m RO) as HN.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ RO Hb)]|].
  exact (wr_at_norm rsegs m (normalize rsegs m) A _ HN Hw HF).
Qed.

Lemma ms_rel_MS : forall s R F pc fc rv m0 ro, ms_rel rsegs s (MS R F pc fc rv m0 ro) -> s = MS R F pc fc rv (ms_mem s) ro.
Proof.
  intros s R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _).
  destruct s. unfold MS in *. cbn in *. subst. reflexivity.
Qed.

Lemma put_post_norm : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list ivl) (m : word -> option byte) (o b l c : Z) (pad : list byte) (pre bs : list Z) R pc rv,
  ro_agree rsegs m ->
  Exec.evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W (normalize rsegs m)
                    (fun m' => put_text m' o b l c pad pre bs))
    (MS R F pc fc rv (normalize rsegs m) (PropExec.seg_rom rsegs)) ->
  Exec.evt rsegs (fun x => put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m
                    (fun m' => put_text m' o b l c pad pre bs) x /\ ro_agree rsegs (ms_mem x))
    (MS R F pc fc rv m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m o b l c pad pre bs R pc rv RO H.
  pose proof (mem_rel_normalize rsegs m RO) as HN.
  eapply evt_mono; [exact (evt_normalize rsegs _ R F pc fc rv m _ wx_apart_img RO H)|].
  intros x (x0 & (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m0 & E0 & MU & WM & ST & REC & TXT)
    & HR & HO).
  subst x0. pose proof (ms_rel_MS _ _ _ _ _ _ _ _ HR) as EX.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & HM). change (mem_rel rsegs (ms_mem x) m0) in HM.
  split; [|exact (ro_agree_same rsegs m _ RO HO)].
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, (ms_mem x).
  split; [exact EX|].
  split; [exact (munch_rel rsegs W m (normalize rsegs m) (ms_mem x) m0 HN HM HO MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem x) m0 HN HM HO WM)|].
  split; [exact (stk_rel _ _ _ _ HM ST)|].
  split; [exact (rw_cells_rel _ _ _ _ HM REC) | exact (proj2 (bytes_at_rel rsegs _ _ _ _ HM) TXT)].
Qed.

Lemma mbyte_ro : forall m m' a, ro_agree rsegs m -> ro_agree rsegs m' -> ro_addr rsegs (wa a) = true ->
  mbyte rsegs m' a = mbyte rsegs m a.
Proof. intros m m' a H H' R. rewrite !mbyte_mrd, (H' _ R), (H _ R). reflexivity. Qed.

Section P.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Let MR := aa_MR API.

Lemma word4_iff : forall m a v, 0 <= a -> a + 4 <= 2 ^ 64 ->
  (word4_mem B m a v <-> bytes_at rsegs m a (le4 (Z_to_bv 64 v))).
Proof using SEGS.
  intros m a v Ha Hb. unfold word4_mem. rewrite SEGS. split.
  - intros H. split; [lia|]. split; [rewrite length_le4; lia|].
    intros i Hi. rewrite length_le4 in Hi. rewrite <- mbyte_mrd, H by exact Hi.
    unfold le4. rewrite nth_Z_to_le by exact Hi. rewrite le_byte_bv, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite le4_byte by exact Hi. reflexivity.
  - intros (_ & _ & H) k Hk. rewrite mbyte_mrd, H by (rewrite length_le4; exact Hk).
    unfold le4. rewrite nth_Z_to_le by exact Hk. rewrite le_byte_bv, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite le4_byte by exact Hk. reflexivity.
Qed.

Lemma zbytes_iff : forall m a l, 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (zbytes_at B m a l <-> bytes_at rsegs m a (map (Z_to_bv 8) l)).
Proof using SEGS. intros m a l Ha Hb. unfold zbytes_at. rewrite SEGS. apply zbytes_core; assumption. Qed.

Lemma pj_rec_of : forall m Lam o buf len cap failed text, pj_out_ok B m Lam o buf len cap failed text ->
  exists pad, pj_rec m o buf len cap failed pad.
Proof using SEGS.
  intros m Lam o buf len cap failed text PJ.
  destruct PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & _).
  rewrite SEGS in HRW, Wb, Wl, Wc.
  assert (STK : stk rsegs m (o + 28) (o + 32)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HRW (a - o) ltac:(lia)) as [W (v & Hv)].
    replace (o + (a - o)) with a in W, Hv by lia. split; [exact W|]. exists v. exact Hv. }
  destruct (stk_bytes rsegs m (o + 28) (o + 32) STK ltac:(lia)) as (pad & Lp & Bp).
  replace (Z.to_nat (o + 32 - (o + 28))) with 4%nat in Lp by lia.
  exists pad. unfold pj_rec. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split. exact Lp.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [apply word_mem_iff; [lia | lia | exact Wb]|]. rewrite length_le8.
    apply bytes_at_app. split; [apply word_mem_iff; [lia | lia | exact Wl]|]. rewrite length_le8.
    replace (o + Z.of_nat 8 + Z.of_nat 8) with (o + 16) by lia.
    apply bytes_at_app. split; [apply word_mem_iff; [lia | lia | exact Wc]|]. rewrite length_le8.
    replace (o + 16 + Z.of_nat 8) with (o + 24) by lia.
    apply bytes_at_app. split; [apply word4_iff; [lia | lia | exact Wf]|]. rewrite length_le4.
    replace (o + 24 + Z.of_nat 4) with (o + 28) by lia. exact Bp.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (HRW i Hi)).
Qed.

Lemma pj_out_of : forall m Lam o buf len cap failed text pad,
  pj_rec m o buf len cap failed pad -> o mod 8 = 0 ->
  0 <= buf < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> (failed = 0 \/ failed = 1) ->
  bytes_ok text -> Z.of_nat (length text) = len ->
  ((cap = 0 /\ buf = 0 /\ len = 0) \/
   ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ In (buf, cap) Lam /\
    (forall i, 0 <= i < cap + 16 -> ~ alloc_statics (buf - 16 + i)) /\
    len < cap /\ bytes_at rsegs m buf (map (Z_to_bv 8) (text ++ [0])))) ->
  pj_out_ok B m Lam o buf len cap failed text.
Proof using SEGS.
  intros m Lam o buf len cap failed text pad REC H8 Rb Rl Rc Hf BO LT CAP.
  pose proof (Step.rw_cells_bound _ _ _ _ REC) as RB. cbn [cells_size csize] in RB.
  destruct REC as [[Hwf BY] (_ & _ & HW)]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (_ & _ & _ & _ & Lp & _).
  cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. cbn [cells_size csize] in HW.
  pose proof BY as BY0.
  apply bytes_at_app in BY as [Bb BY]. rewrite length_le8 in BY.
  apply bytes_at_app in BY as [Bl BY]. rewrite length_le8 in BY.
  apply bytes_at_app in BY as [Bc BY]. rewrite length_le8 in BY.
  apply bytes_at_app in BY as [Bf _].
  unfold pj_out_ok. rewrite SEGS.
  split; [exact H8|]. split; [lia|]. split; [lia|].
  split.
  { intros i Hi. split; [exact (HW i ltac:(cbn; lia))|].
    destruct BY0 as (_ & _ & HB). rewrite mbyte_mrd. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite HB by (rewrite !length_app, !length_le8, length_le4, Lp; lia).
    destruct (nth_error _ _) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E.
    rewrite !length_app, !length_le8, length_le4, Lp in E. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply word_mem_iff; [lia | lia | exact Bb]|].
  split; [apply word_mem_iff; [lia | lia | replace (o + 8) with (o + Z.of_nat 8) by lia; exact Bl]|].
  split; [apply word_mem_iff; [lia | lia | replace (o + 16) with (o + Z.of_nat 8 + Z.of_nat 8) by lia; exact Bc]|].
  split; [apply word4_iff; [lia | lia | replace (o + 24) with (o + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia; exact Bf]|].
  split; [exact Hf|]. split; [exact BO|]. split; [exact LT|].
  destruct CAP as [C0|(Hj & Hin & Hst & Hlt & Hb)]; [left; exact C0|right].
  split; [exact Hj|]. split; [exact Hin|]. split; [exact Hst|]. split; [exact Hlt|].
  apply zbytes_iff; [pose proof (bytes_at_bound _ _ _ _ Hb) as BB; rewrite length_map in BB; lia
    | pose proof (bytes_at_bound _ _ _ _ Hb) as BB; rewrite length_map in BB; lia | exact Hb].
Qed.

Lemma getr_mkR_of : forall regs k, getr (mkR_of regs) k = getr regs k.
Proof using.
  intros regs k. unfold getr. destruct (bv_eqb k 0) eqn:E; [reflexivity|].
  symmetry. apply mkR_of_eqv. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (k = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst k. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma lblock_of : forall L A m Lam peak cnt fail x k, ledger B L A m Lam peak cnt fail -> In (x, k) Lam ->
  0 <= k /\ In (x - 16, k + 16) (blocks L A) /\ word_mem (ms_segs B) m (x - 16) k /\
  (forall i, 0 <= i < k + 16 -> ~ in_img B (x - 16 + i)).
Proof using.
  intros L A m Lam peak cnt fail x k HL Hin. destruct HL as (_ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (HF _ Hin).
Qed.

Lemma present_wr_at : forall m a k, 0 <= a -> a + k <= 2 ^ 64 -> (forall i, 0 <= i < k -> present m (a + i)) ->
  wr_at rsegs m a k.
Proof using.
  intros m a k Ha Hb H. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (H i Hi) as (v & Hv). unfold wview, wa. rewrite Hv. discriminate.
Qed.

Lemma s_target : forall L A m md Lam peak cnt fail q c s n,
  MR L A m md -> ledger B L A m Lam peak cnt fail -> In (q, c) Lam -> 0 <= n ->
  (alloc_ceiling <= s \/ (forall i, 0 <= i < n -> ro_addr rsegs (wa (s + i)) = true) \/
   (exists x y, In (x, y) Lam /\ x <> q /\ x <= s /\ s + n <= x + y)) ->
  n = 0 \/ c = 0 \/ s + n <= q \/ q + c <= s.
Proof using API SEGS.
  intros L A m md Lam peak cnt fail q c s n HM HL Hq Hn HS.
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM HL Hq) as Rq.
  destruct HS as [HS|[HS|(x & y & Hx & Hne & H1 & H2)]].
  - right. right. right. lia.
  - destruct (Z.eq_dec n 0) as [->|Hn0]; [left; reflexivity|]. right.
    destruct (Z.eq_dec c 0) as [->|Hc0]; [left; reflexivity|]. right.
    destruct (lblock_of _ _ _ _ _ _ _ _ _ HL Hq) as (Hc & _ & _ & NI).
    apply ranges_apart; [lia | lia |].
    intros z Hz1 Hz2. apply (NI (z - q + 16)); [lia|]. replace (q - 16 + (z - q + 16)) with z by lia.
    apply (ro_in_img B SEGS); [lia|]. replace z with (s + (z - s)) by lia. apply HS. lia.
  - right. right. destruct (lblock_of _ _ _ _ _ _ _ _ _ HL Hx) as (Hy & Bx & _).
    destruct (lblock_of _ _ _ _ _ _ _ _ _ HL Hq) as (Hc & Bq & _).
    destruct (blocks_disj B API _ _ _ _ _ _ _ _ HM Bx Bq ltac:(lia)); lia.
Qed.

Definition ppre L A regs mem md b o s n buf len cap failed (text bs : list Z) Lam peak cnt fail : Prop :=
  call_pre_k B MR PUT_K L A regs mem md /\ ro_agree rsegs mem /\
  getr regs 10 = Z_to_bv 64 o /\ getr regs 11 = Z_to_bv 64 s /\ getr regs 12 = Z_to_bv 64 n /\
  pj_out_ok B mem Lam o buf len cap failed text /\ ledger B L A mem Lam peak cnt fail /\
  spZ regs <= o /\ off_errno B o 32 /\ off_errno B (spZ regs - PUT_K) PUT_K /\
  zbytes_at B mem s bs /\ Z.of_nat (length bs) = n /\ bytes_ok bs /\ 0 <= s < 2 ^ 64 /\ s + n <= 2 ^ 64 /\
  s_where B regs Lam s n buf /\ (s + n <= o \/ o + 32 <= s) /\ len + n + 1 <= WMAX /\
  rf_ok RF A b /\ (failed = 0 -> cap < len + n + 1 -> rf_room RF b (newcap cap (len + n + 1) + 16)).

Definition pgoal L A regs mem md b o n buf len cap failed (text bs : list Z) Lam peak cnt fail calls : Prop :=
  SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 put_c.PUT) mem (YK11.seg_rom rsegs)) md)
    (put_ret B API RF L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b).

Ltac pp_setup PP regs o s n mem :=
  destruct PP as (PRE & ROm & R10 & R11 & R12 & PJ & LG & SPO & EO & ES & ZB & LN & BO & RS & RSN & SW & SO & NEED & RES & ROOM);
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux);
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat);
  pose proof ceil_big as CEB; unfold IMG_TOP in CEB;
  assert (SP2 : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite getr_reg by reflexivity; reflexivity);
  assert (Q10 : reg_get regs 10 = Z_to_bv 64 o) by (rewrite <- getr_reg by reflexivity; exact R10);
  assert (Q11 : reg_get regs 11 = Z_to_bv 64 s) by (rewrite <- getr_reg by reflexivity; exact R11);
  assert (Q12 : reg_get regs 12 = Z_to_bv 64 n) by (rewrite <- getr_reg by reflexivity; exact R12);
  assert (STK : stk rsegs mem (spZ regs - PUT_K) (spZ regs))
    by (apply stk_hi; [unfold IMG_TOP, PUT_K, REALLOC_STACK, ALLOC_STACK in *; lia | lia | intros a Ha; rewrite <- SEGS; apply HWs;
        unfold PUT_K, REALLOC_STACK, ALLOC_STACK in *; lia]);
  assert (PC : ret_pc (reg_get regs 1) = getr regs 1) by (rewrite <- getr_reg by reflexivity; apply ret_pc_ok; exact Hra);
  unfold PUT_K, REALLOC_STACK, ALLOC_STACK in Hceil, STK, ES.

Ltac callee_cases :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |];
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hr' as [->|Hr']; [reflexivity|]); subst r; reflexivity.

Lemma regs_kept : forall regs R F pc fc rv m ro x,
  ms_eqv (MS R F pc fc rv m ro) x ->
  (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr (mkR_of regs) (Z_to_bv 5 r)) ->
  regs_preserved regs (ms_regs x).
Proof using.
  intros regs R F pc fc rv m ro x HE H r Hr. rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HE), H by exact Hr.
  apply getr_mkR_of.
Qed.

Lemma pj_keep : forall m m' Lam o buf len cap failed text pad,
  pj_out_ok B m Lam o buf len cap failed text -> pj_rec m' o buf len cap failed pad ->
  (cap <> 0 -> buf + cap <= 2 ^ 64 /\ forall i, 0 <= i < len + 1 -> mbyte rsegs m' (buf + i) = mbyte rsegs m (buf + i)) ->
  pj_out_ok B m' Lam o buf len cap failed text.
Proof using SEGS.
  intros m m' Lam o buf len cap failed text pad PJ REC E.
  pose proof PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BOt & LT & CAP).
  apply (pj_out_of _ _ _ _ _ _ _ _ pad REC H8 Rb Rl Rc Hf BOt LT).
  destruct CAP as [C0|(Hj & Hin & Hst & Hlt & Hz)]; [left; exact C0|right].
  split; [exact Hj|]. split; [exact Hin|]. split; [exact Hst|]. split; [exact Hlt|].
  assert (Hc : cap <> 0) by (destruct Hj as (j & Hj & ->); pose proof (Z.pow_pos_nonneg 2 j); lia).
  destruct (E Hc) as [Hbc E'].
  assert (Hb2 : buf + Z.of_nat (length (text ++ [0])) <= 2 ^ 64) by (rewrite length_app; cbn; lia).
  eapply bytes_at_eqm; [exact (proj1 (zbytes_iff m buf (text ++ [0]) ltac:(lia) Hb2) Hz)|].
  intros i Hi. rewrite length_map, length_app in Hi. cbn in Hi. apply E'. lia.
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

Hypothesis RE : fuzz_realloc_contract B API RF.
Hypothesis MC : memcpy_contract.

Lemma arm_failed : forall L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls,
  ppre L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail -> failed <> 0 ->
  pgoal L A regs mem md b o n buf len cap failed text bs Lam peak cnt fail calls.
Proof using SEGS.
  intros L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls PP HF.
  pp_setup PP regs o s n mem.
  destruct (pj_rec_of _ _ _ _ _ _ _ _ PJ) as [pad REC].
  pose proof PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BOt & LT & CAP).
  unfold pgoal. eapply kA_lift; [exact Hh | exact Hl | |].
  { unfold mkR_of. rewrite Q10. eapply put_failed; [exact REC | lia | rewrite SP2; exact STK
      | rewrite SP2; unfold PUT_FRAME; lia | rewrite SP2; right; exact SPO]. }
  intros x y HQ HEQ HRM.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ey & MU & WM & ST' & REC').
  subst y. rewrite SP2 in MU. unfold PUT_FRAME in MU.
  destruct (post_shape _ _ _ x md HEQ PC) as [CF XM].
  apply SR_ret. unfold put_ret. cbv zeta.
  assert (Hst : put1 (mkW failed text cap cnt fail calls) bs = mkW failed text cap cnt fail calls)
    by (unfold put1; cbn [w_failed]; destruct (failed =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]).
  rewrite Hst. cbn [w_text w_cap w_failed w_cnt w_fail].
  exists L, A, (ms_regs x), m', md, buf, Lam, peak, b.
  rewrite XM in HRM.
  split; [exact CF|].
  split; [rewrite SEGS; apply (ro_munch_hi _ _ mem m' ROm MU); unfold IMG_TOP; lia|].
  split.
  { apply (guard_munch B API L A mem md _ mem m' HM MU). intros i Hi.
    destruct (got_low B API L A mem md i HM Hi) as [_ GL]. cbn [outside]. split; [lia | exact I]. }
  split; [intros H; exact H|].
  split; [apply Nat.le_refl|].
  split.
  { rewrite LT. apply (pj_keep mem m' Lam o buf len cap failed text pad PJ REC').
    intros Hc. destruct CAP as [C0|(_ & Hin & _ & Hlt & _)]; [lia|].
    pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin).
    split; [lia|]. intros i Hi.
    apply raw_mbyte. apply (munch_raw _ _ _ _ MU); [lia | cbn [outside]; split; [lia | exact I]]. }
  split.
  { eapply (ledger_munch B API); [exact HM | exact LG | exact MU | |].
    - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. cbn [outside]. split; [lia | exact I].
    - intros x0 k i Hin Hi. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin).
      pose proof (lblock_of _ _ _ _ _ _ _ _ _ LG Hin) as (Hk0 & _).
      cbn [outside]. split; [lia | exact I]. }
  split; [exact RES|].
  left. split; [exact HF|]. do 7 (split; [reflexivity|]).
  split.
  { eapply (keeps_munch B API); [exact HM | exact MU |]. intros a k i Hin _ Hi.
    pose proof (block_range B API _ _ _ _ _ _ HM Hin). cbn [outside]. split; [lia | exact I]. }
  split; [intros q k Hq _; exact Hq|].
  eapply (post_nocall B API SEGS); [exact PRE | exact MU | exact WM | exact HRM | | |].
  - intros z Hz Hn. left. cbn [outside] in Hn. unfold PUT_K, REALLOC_STACK, ALLOC_STACK. lia.
  - intros a Ha. pose proof (owned_low B API _ _ _ _ _ HM Ha). cbn [outside]. split; [lia | exact I].
  - eapply regs_kept; [exact HEQ|]. unfold mkR_of. callee_cases.
Qed.

Lemma s_low : forall regs L A m md Lam peak cnt fail s n buf, MR L A m md -> ledger B L A m Lam peak cnt fail ->
  0 <= s < 2 ^ 64 -> s + n <= 2 ^ 64 -> 0 <= n -> s_where B regs Lam s n buf ->
  s + n <= alloc_ceiling \/ spZ regs <= s.
Proof using SEGS.
  intros regs L A m md Lam peak cnt fail s n buf HM HL Hs Hsn Hn SW. pose proof ceil_big as CB. unfold IMG_TOP in CB.
  destruct SW as [[SW _]|[[HI HR]|(x & y & Hx & _ & H1 & H2)]].
  - right. exact SW.
  - left. destruct (Z.eq_dec n 0) as [->|Hn0].
    + pose proof (in_img_low B SEGS s HI). unfold IMG_TOP in *. lia.
    + pose proof (ro_addr_low (s + (n - 1)) (HR (n - 1) ltac:(lia)) ltac:(lia) ltac:(lia)). unfold IMG_TOP in *. lia.
  - left. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM HL Hx). lia.
Qed.

Lemma s_shape : forall regs Lam s n buf, s_where B regs Lam s n buf -> alloc_ceiling <= spZ regs ->
  alloc_ceiling <= s \/ (forall i, 0 <= i < n -> ro_addr rsegs (wa (s + i)) = true) \/
  (exists x y, In (x, y) Lam /\ x <> buf /\ x <= s /\ s + n <= x + y).
Proof using.
  intros regs Lam s n buf SW H. destruct SW as [[SW _]|[[_ HR]|HB]]; [left; lia | right; left; exact HR | right; right; exact HB].
Qed.

Lemma arm_fast : forall L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls,
  ppre L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail -> failed = 0 -> len + n + 1 <= cap ->
  pgoal L A regs mem md b o n buf len cap failed text bs Lam peak cnt fail calls.
Proof using SEGS MC.
  intros L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls PP HF HC.
  pp_setup PP regs o s n mem. subst failed.
  destruct (pj_rec_of _ _ _ _ _ _ _ _ PJ) as [pad REC].
  pose proof PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BOt & LT & CAP).
  destruct CAP as [C0|(Hj & Hin & Hst & Hlt & Hz)]; [lia|].
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin) as RBk.
  pose proof (lblock_of _ _ _ _ _ _ _ _ _ LG Hin) as (Hc0 & Bbuf & _).
  assert (HN : mem_rel rsegs mem (normalize rsegs mem)) by exact (mem_rel_normalize rsegs mem ROm).
  assert (NIb : forall i, 0 <= i < cap -> ro_addr rsegs (wa (buf + i)) = false).
  { intros i Hi. destruct (lblock_of _ _ _ _ _ _ _ _ _ LG Hin) as (_ & _ & _ & NI).
    apply (ro_false_noimg B SEGS); [lia|]. replace (buf + i) with (buf - 16 + (i + 16)) by lia. apply NI. lia. }
  assert (RECn : pj_rec (normalize rsegs mem) o buf len cap 0 pad).
  { unfold pj_rec in *. apply (rw_cells_norm _ _ _ ROm REC). intros i Hi. cbn [cells_size csize] in Hi.
    apply ro_false_hi. unfold IMG_TOP. lia. }
  assert (STKn := stk_norm _ _ _ ROm STK ltac:(intros a Ha; apply ro_false_hi; unfold IMG_TOP; lia)).
  assert (PRS : forall i, 0 <= i < cap -> present mem (buf + i))
    by (intros i Hi; exact (ledger_block_present B API _ _ _ _ _ _ _ _ _ _ _ HM LG Hin Hi)).
  assert (TB : bytes_at rsegs mem buf (map (Z_to_bv 8) (text ++ [0])))
    by (apply (proj1 (zbytes_iff mem buf (text ++ [0]) ltac:(lia) ltac:(rewrite length_app; cbn; lia))); exact Hz).
  assert (PRE' : bytes_at rsegs mem buf (map (Z_to_bv 8) text))
    by (rewrite map_app in TB; apply bytes_at_app in TB; exact (proj1 TB)).
  assert (SRC : bytes_at rsegs mem s (map (Z_to_bv 8) bs))
    by (apply (proj1 (zbytes_iff mem s bs ltac:(lia) ltac:(lia))); exact ZB).
  destruct (bytes_list mem (buf + len) n ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi; replace (buf + len + i) with (buf + (len + i)) by lia; apply PRS; lia)) as (junkb & LJ & JB).
  assert (LJ' : length junkb = length bs) by lia.
  pose proof (s_low regs L A mem md Lam peak cnt fail s n buf HM LG RS RSN ltac:(lia) SW) as SLOW.
  pose proof (s_target L A mem md Lam peak cnt fail buf cap s n HM LG Hin ltac:(lia) (s_shape _ _ _ _ _ SW ltac:(lia))) as SDJ.
  unfold pgoal. eapply kA_lift; [exact Hh | exact Hl | |].
  { unfold mkR_of. rewrite Q10, Q11, Q12. rewrite <- LN.
    eapply put_post_norm; [exact ROm|].
    eapply put_fast; [exact MC | exact RECn | lia | exact LT | lia
      | apply (wr_at_norm rsegs mem _ buf cap HN); [apply present_wr_at; [lia | lia | exact PRS] | exact NIb]
      | exact (bytes_at_normalize rsegs mem _ _ ROm PRE') | exact (bytes_at_normalize rsegs mem _ _ ROm SRC) | lia
      | exact (bytes_at_normalize rsegs mem _ _ ROm JB) | exact LJ' | exact (mem_inv_normalize rsegs mem)
      | rewrite SP2; exact STKn | rewrite SP2; unfold PUT_FRAME; lia | rewrite SP2; right; exact SPO
      | rewrite SP2; left; lia | left; lia | rewrite SP2; lia | lia]. }
  intros x y [HQ ROy] HEQ HRM.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ey & MU & WM & ST' & REC' & TXT').
  subst y. rewrite SP2, LN in MU. unfold PUT_FRAME in MU. rewrite LN in REC'.
  destruct (post_shape _ _ _ x md HEQ PC) as [CF XM].
  apply SR_ret. unfold put_ret. cbv zeta.
  assert (Hst' : put1 (mkW 0 text cap cnt fail calls) bs = mkW 0 (text ++ bs) cap cnt fail calls).
  { unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls]. change (0 =? 0) with true. cbn [negb].
    rewrite LT, LN. destruct (Z.leb_spec (len + n + 1) cap); [reflexivity | lia]. }
  rewrite Hst'. cbn [w_text w_cap w_failed w_cnt w_fail].
  exists L, A, (ms_regs x), m', md, buf, Lam, peak, b.
  rewrite XM in HRM.
  split; [exact CF|].
  split; [rewrite SEGS; change (ro_agree rsegs m') in ROy; exact ROy|].
  split.
  { apply (guard_munch B API L A mem md _ mem m' HM MU). intros i Hi.
    destruct (got_low B API L A mem md i HM Hi) as [GO GL].
    cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
    intros Hr. destruct (block_facts B API _ _ _ _ _ _ (ms_got_guard B + i - (buf - 16)) HM Bbuf ltac:(lia)) as (_ & _ & _ & NO).
    apply NO. replace (buf - 16 + (ms_got_guard B + i - (buf - 16))) with (ms_got_guard B + i) by lia. exact GO. }
  split; [intros H; exact H|].
  split; [apply Nat.le_refl|].
  split.
  { assert (LTB : Z.of_nat (length (text ++ bs)) = len + n) by (rewrite length_app; lia).
    rewrite LTB. apply (pj_out_of _ _ _ _ _ _ _ _ pad REC' H8 Rb ltac:(lia) Rc ltac:(left; reflexivity)).
    - unfold bytes_ok in *. apply Forall_app. split; assumption.
    - exact LTB.
    - right. split; [exact Hj|]. split; [exact Hin|]. split; [exact Hst|]. split; [lia|].
      rewrite <- app_assoc. exact TXT'. }
  split.
  { eapply (ledger_munch B API); [exact HM | exact LG | exact MU | |].
    - intros a Ha. cbn [outside]. pose proof Ha as Ha'. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha'.
      split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hr. apply (Hst (a - buf + 16)); [lia|]. replace (buf - 16 + (a - buf + 16)) with a by lia. exact Ha.
    - intros x0 k i Hx0 Hi. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hx0).
      pose proof (lblock_of _ _ _ _ _ _ _ _ _ LG Hx0) as (Hk0 & Bx0 & _).
      cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
      destruct (Z.eq_dec x0 buf) as [->|Hne]; [lia|].
      destruct (blocks_disj B API _ _ _ _ _ _ _ _ HM Bx0 Bbuf ltac:(lia)); lia. }
  split; [exact RES|].
  right. left. split; [reflexivity|]. split; [exact HC|]. do 7 (split; [reflexivity|]).
  split.
  { eapply (keeps_munch B API); [exact HM | exact MU |]. intros a k i Ha Hne Hi.
    pose proof (block_range B API _ _ _ _ _ _ HM Ha).
    cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
    destruct (blocks_disj B API _ _ _ _ _ _ _ _ HM Ha Bbuf Hne); lia. }
  split; [intros q k Hq _; exact Hq|].
  eapply (post_nocall B API SEGS); [exact PRE | exact MU | exact WM | exact HRM | | |].
  - intros z Hz0 Hn. cbn [outside] in Hn. unfold fast_writes, PUT_K, REALLOC_STACK, ALLOC_STACK.
    destruct (Z_le_gt_dec (spZ regs - 48) z); destruct (Z_lt_ge_dec z (spZ regs)); [left; lia | ..];
    right; lia.
  - intros a Ha. pose proof (owned_low B API _ _ _ _ _ HM Ha). cbn [outside]. split; [lia|]. split; [lia|].
    split; [|exact I]. intros Hr. destruct (block_facts B API _ _ _ _ _ _ (a - (buf - 16)) HM Bbuf ltac:(lia)) as (_ & _ & _ & NO).
    apply NO. replace (buf - 16 + (a - (buf - 16))) with a by lia. exact Ha.
  - eapply regs_kept; [exact HEQ|]. unfold mkR_of. callee_cases.
Qed.

Lemma reg_pres : forall regs1 regs2 r, regs_preserved regs1 regs2 -> callee_saved r ->
  reg_get regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r).
Proof using.
  intros regs1 regs2 r P Hr. rewrite <- (P r Hr). unfold getr.
  replace (bv_eqb (Z_to_bv 5 r) 0) with false; [reflexivity|].
  symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. change (bv_unsigned (0 : bv 5)) with 0.
  unfold callee_saved in Hr. rewrite Z.mod_small by lia. lia.
Qed.

Lemma in_app_skip : forall {T} (b1 b2 : list T) e f, In f (b1 ++ e :: b2) -> f <> e -> In f (b1 ++ b2).
Proof using.
  intros T b1 b2 e f H Hne. apply in_app_or in H. apply in_or_app. destruct H as [H|[H|H]]; auto. congruence.
Qed.

Lemma newblock_disj : forall L A mem md c1 c2 x k y j, MR L A mem md -> blocks L A = c1 ++ (x, k) :: c2 ->
  In (y, j) (c1 ++ c2) -> x + k <= y \/ y + j <= x.
Proof using API.
  intros L A mem md c1 c2 x k y j HM E Hy. pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as P.
  rewrite E in P. destruct (pairwise_mid _ _ _ _ _ P Hy) as [H|H]; unfold ranges_disjoint in H; cbn in H; lia.
Qed.

Ltac rfact PRES HEQ r :=
  etransitivity; [exact (reg_pres _ _ r PRES ltac:(unfold callee_saved; lia))
                 | rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity].

Lemma pre_realloc : forall L A regs mem md mem1 regs1,
  call_pre_k B MR PUT_K L A regs mem md ->
  munch [(spZ regs - 48, spZ regs)] mem mem1 -> wmono rsegs mem mem1 -> rm mem mem1 ->
  getr regs1 1 = Z_to_bv 64 0x162d8 -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs1 4 = getr regs 4 ->
  call_pre_k B MR (REALLOC_STACK + 48) L A regs1 mem1 md.
Proof using SEGS.
  intros L A regs mem md mem1 regs1 PRE MU WM RM G1 G2 G4.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  unfold PUT_K, REALLOC_STACK, ALLOC_STACK in *.
  assert (SP1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply unsigned_lit; lia).
  rewrite <- SEGS in WM.
  assert (OW : forall a, owned B L A a -> outside [(spZ regs - 48, spZ regs)] a)
    by (intros a Ha; pose proof (owned_low B API _ _ _ _ _ HM Ha); cbn [outside]; split; [lia | exact I]).
  unfold call_pre_k. rewrite SP1.
  split; [exact (mr_munch B API _ _ _ _ _ _ HM MU RM OW)|].
  split; [exact HWF|]. split; [exact HB|].
  split; [rewrite G1; reflexivity|].
  split; [Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply WM; apply HWs; lia|].
  split; [rewrite G4; exact Htp|].
  split; [intros a Ha; apply WM; apply HWe; exact Ha|].
  intros Hi. destruct (Haux Hi) as (av & ar & W1 & W2 & W3 & W4 & R1 & R2 & R3 & R4 & R5 & R6).
  exists av, ar.
  assert (HL0 : forall k, 0 <= k < 8 -> owned B L A (ms_libc B + 8 + k)).
  { intros k Hk. right. unfold static_owned. right. right. left. lia. }
  pose proof (owned_low B API _ _ _ _ _ HM (HL0 0 ltac:(lia))) as RL0.
  pose proof (owned_low B API _ _ _ _ _ HM (HL0 7 ltac:(lia))) as RL7.
  split.
  { eapply (word_mem_munch B); [exact MU | lia | lia | | exact W1].
    intros k Hk. exact (OW _ (HL0 k Hk)). }
  split.
  { intros k Hk. eapply (word_mem_munch B); [exact MU | lia | lia | | exact (W2 k Hk)].
    intros j Hj. cbn [outside]. split; [lia | exact I]. }
  split.
  { eapply (word_mem_munch B); [exact MU | lia | lia | | exact W3]. intros j Hj. cbn [outside]. split; [lia | exact I]. }
  split.
  { eapply (word_mem_munch B); [exact MU | lia | lia | | exact W4]. intros j Hj. cbn [outside]. split; [lia | exact I]. }
  repeat split; lia.
Qed.

Lemma xport_hi : forall L A regs1 mem1 md E2 L' A' regs2 mem2 md' a,
  call_post_k B MR (REALLOC_STACK + 48) L A regs1 mem1 md E2 L' A' regs2 mem2 md' -> MR L A mem1 md ->
  alloc_ceiling <= a < 2 ^ 64 -> spZ regs1 <= a -> ~ (errno_addr B <= a < errno_addr B + 4) ->
  (forall x, E2 x -> x < alloc_ceiling) ->
  mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a -> writable_at rsegs mem2 a).
Proof using SEGS.
  intros L A regs1 mem1 md E2 L' A' regs2 mem2 md' a CPK HM1 Ha Hs He HE.
  pose proof CPK as (HM2 & _ & _ & _ & _ & _ & _ & HFR & _).
  rewrite <- SEGS.
  destruct (HFR a (or_introl Ha)) as [F1 F2].
  - intros Ho. pose proof (owned_low B API _ _ _ _ _ HM1 Ho). lia.
  - intros Ho. pose proof (owned_low B API _ _ _ _ _ HM2 Ho). lia.
  - intros [H|H]; [lia | exact (He H)].
  - intros H. pose proof (HE a H). lia.
  - split; [exact F1 | tauto].
Qed.

Lemma rw_cells_hi : forall L A regs1 mem1 md E2 L' A' regs2 mem2 md' a cs,
  call_post_k B MR (REALLOC_STACK + 48) L A regs1 mem1 md E2 L' A' regs2 mem2 md' -> MR L A mem1 md ->
  Step.rw_cells rsegs mem1 a cs -> alloc_ceiling <= a -> spZ regs1 <= a ->
  (a + Z.of_nat (cells_size cs) <= errno_addr B \/ errno_addr B + 4 <= a) ->
  (forall x, E2 x -> x < alloc_ceiling) ->
  Step.rw_cells rsegs mem2 a cs.
Proof using SEGS.
  intros L A regs1 mem1 md E2 L' A' regs2 mem2 md' a cs CPK HM1 RC Ha Hs He HE.
  pose proof (Step.rw_cells_bound _ _ _ _ RC) as RB.
  apply (rw_cells_eqm mem1 mem2 a cs RC). intros i Hi.
  apply (xport_hi _ _ _ _ _ _ _ _ _ _ _ _ CPK HM1); [lia | lia | lia | exact HE].
Qed.

Lemma arm_grow : forall L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls,
  ppre L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail -> failed = 0 -> cap < len + n + 1 ->
  pgoal L A regs mem md b o n buf len cap failed text bs Lam peak cnt fail calls.
Proof using SEGS RE MC.
  intros L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls PP HF HC.
  pp_setup PP regs o s n mem. subst failed.
  destruct (pj_rec_of _ _ _ _ _ _ _ _ PJ) as [pad REC].
  pose proof PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BOt & LT & CAP).
  assert (CAPF : cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j)
    by (destruct CAP as [(C0 & _ & _)|(Hj & _)]; [left; exact C0 | right; exact Hj]).
  assert (BUF0 : cap = 0 -> buf = 0 /\ len = 0)
    by (intros C0; destruct CAP as [(_ & B0 & L0)|((j & Hj & Ej) & _)]; [split; assumption | pose proof (Z.pow_pos_nonneg 2 j); lia]).
  assert (CAPNZ : cap <> 0 -> In (buf, cap) Lam /\ (forall i, 0 <= i < cap + 16 -> ~ alloc_statics (buf - 16 + i)) /\
                    len < cap /\ zbytes_at B mem buf (text ++ [0]))
    by (intros Cn; destruct CAP as [(C0 & _)|(_ & Hin & Hst & Hlt & Hz)]; [lia | repeat split; assumption]).
  assert (BR : 0 <= buf /\ buf + cap <= alloc_ceiling /\ (cap <> 0 -> 4112 <= buf)).
  { destruct (Z.eq_dec cap 0) as [C0|Cn]; [destruct (BUF0 C0); repeat split; lia|].
    pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (CAPNZ Cn))). repeat split; lia. }
  destruct (newcap_pow cap (len + n + 1) CAPF ltac:(unfold WMAX in NEED; lia)) as (jn & Hjn & NCE & NCL).
  assert (PJ1 : 0 < 2 ^ jn) by (apply Z.pow_pos_nonneg; lia).
  assert (PJ2 : 2 ^ jn <= 2 ^ 51) by (apply Z.pow_le_mono_r; lia).
  set (C := newcap cap (len + n + 1)) in *.
  assert (CR : 4096 <= C <= 2 ^ 63) by (rewrite NCE; change (2 ^ 51) with 2251799813685248 in PJ2; lia).
  pose proof (s_low regs L A mem md Lam peak cnt fail s n buf HM LG RS RSN ltac:(lia) SW) as SLOW.
  assert (SRC : bytes_at rsegs mem s (map (Z_to_bv 8) bs))
    by (apply (proj1 (zbytes_iff mem s bs ltac:(lia) ltac:(lia))); exact ZB).
  unfold pgoal. eapply kA_lift; [exact Hh | exact Hl | |].
  { unfold mkR_of. rewrite Q10, Q11, Q12.
    eapply put_grow_to_call; [exact REC | lia | lia | unfold WMAX in NEED; lia | lia | exact CAPF
      | rewrite SP2; exact STK | rewrite SP2; unfold PUT_FRAME; lia | rewrite SP2; right; exact SPO]. }
  intros x y HQ HEQ HRM.
  destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & Ey & MU1 & WM1 & ST1 & FR1 & REC1).
  subst y. rewrite SP2 in MU1, ST1, FR1. unfold PUT_FRAME in MU1, ST1, FR1.
  assert (XM : ms_mem x = m1) by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
  rewrite XM in HRM.
  rewrite (eqv_shape _ _ _ _ HEQ).
  assert (G1 : getr (ms_regs x) 1 = Z_to_bv 64 0x162d8) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G2 : getr (ms_regs x) 2 = Z_to_bv 64 (spZ regs - 48))
    by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); cbn -[Z_to_bv bv_unsigned]; rewrite SP2; reflexivity).
  assert (G4 : getr (ms_regs x) 4 = getr regs 4) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G10 : getr (ms_regs x) 10 = Z_to_bv 64 buf) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G11 : getr (ms_regs x) 11 = Z_to_bv 64 C) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (SPx : spZ (ms_regs x) = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply unsigned_lit; lia).
  assert (PR1 : forall i, 0 <= i < cap -> present m1 (buf + i)).
  { intros i Hi. apply (present_rm mem m1 _ HRM).
    exact (ledger_block_present B API _ _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (CAPNZ ltac:(lia))) Hi). }
  destruct (bytes_list m1 buf cap ltac:(lia) ltac:(lia) ltac:(lia) PR1) as (old & LO & BO1).
  assert (OLD : forall i, 0 <= i < cap -> mbyte (ms_segs B) m1 (buf + i) = nth_error old (Z.to_nat i)).
  { intros i Hi. rewrite SEGS, mbyte_mrd. destruct BO1 as (_ & _ & H).
    replace (buf + i) with (buf + Z.of_nat (Z.to_nat i)) by lia. apply H. lia. }
  assert (RO1 : ro_agree rsegs m1) by (apply (ro_munch_hi _ _ mem m1 ROm MU1); unfold IMG_TOP; lia).
  assert (LG1 : ledger B L A m1 Lam peak cnt fail).
  { eapply (ledger_munch B API); [exact HM | exact LG | exact MU1 | |].
    - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. cbn [outside]. split; [lia | exact I].
    - intros x0 k i Hin Hi. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin).
      pose proof (lblock_of _ _ _ _ _ _ _ _ _ LG Hin) as (Hk0 & _). cbn [outside]. split; [lia | exact I]. }
  assert (PRE1 : call_pre_k B MR (REALLOC_STACK + 48) L A (ms_regs x) m1 md)
    by (eapply pre_realloc; [exact PRE | exact MU1 | exact WM1 | exact HRM | exact G1 | exact G2 | exact G4]).
  pose proof PRE1 as (HM1 & _).
  eapply SR_bind.
  { rewrite <- SEGS. eapply (RE L A (ms_regs x) m1 md buf cap C old b Lam peak cnt fail); [exact PRE1 | exact G10 | exact G11 | lia | exact LG1
      | rewrite SEGS; exact RO1
      | destruct (Z.eq_dec cap 0) as [C0|Cn]; [left; destruct (BUF0 C0); split; assumption | right; exact (proj1 (CAPNZ Cn))]
      | exact LO | exact OLD | exact RES | exact (ROOM eq_refl HC)
      | unfold C; pose proof (newcap_le28 cap (len + n + 1) CAPF ltac:(unfold WMAX in NEED; lia)) as NC28;
        assert (E30 : 2 ^ 30 = 4 * 2 ^ 28) by reflexivity; lia]. }
  intros c' (L' & A' & regs2 & mem2 & md' & res & Ec & RO2 & GK2 & INIT & LB8 & CPK & STR & R10' & _ & ARMS).
  subst c'. rewrite G1, SEGS. rewrite SEGS in RO2.
  pose proof CPK as (HM2 & HWF2 & HB2 & HLL & HPT & PRES & HMD & HFR & HBK & HSW).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (K2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - PUT_FRAME)) by rfact PRES HEQ 2.
  assert (K3 : reg_get regs2 3 = reg_get regs 3) by rfact PRES HEQ 3.
  assert (K4 : reg_get regs2 4 = reg_get regs 4) by rfact PRES HEQ 4.
  assert (K8 : reg_get regs2 8 = Z_to_bv 64 o) by rfact PRES HEQ 8.
  assert (K9 : reg_get regs2 9 = Z_to_bv 64 n) by rfact PRES HEQ 9.
  assert (K18 : reg_get regs2 18 = Z_to_bv 64 s) by rfact PRES HEQ 18.
  assert (K19 : reg_get regs2 19 = Z_to_bv 64 C) by rfact PRES HEQ 19.
  assert (K20 : reg_get regs2 20 = reg_get regs 20) by rfact PRES HEQ 20.
  assert (K21 : reg_get regs2 21 = reg_get regs 21) by rfact PRES HEQ 21.
  assert (K22 : reg_get regs2 22 = reg_get regs 22) by rfact PRES HEQ 22.
  assert (K23 : reg_get regs2 23 = reg_get regs 23) by rfact PRES HEQ 23.
  assert (K24 : reg_get regs2 24 = reg_get regs 24) by rfact PRES HEQ 24.
  assert (K25 : reg_get regs2 25 = reg_get regs 25) by rfact PRES HEQ 25.
  assert (K26 : reg_get regs2 26 = reg_get regs 26) by rfact PRES HEQ 26.
  assert (K27 : reg_get regs2 27 = reg_get regs 27) by rfact PRES HEQ 27.
  assert (K10 : reg_get regs2 10 = Z_to_bv 64 res) by (rewrite <- getr_reg by reflexivity; exact R10').
  assert (STK2 : stk rsegs mem2 (spZ regs - 8352) (spZ regs - 48)).
  { apply stk_hi; [unfold IMG_TOP in *; lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSW. left. rewrite SPx. unfold REALLOC_STACK, ALLOC_STACK. lia. }
  assert (ESx : forall a, spZ regs - 8352 <= a < spZ regs -> ~ (errno_addr B <= a < errno_addr B + 4))
    by (intros a Ha He; unfold off_errno in ES; lia).
  assert (TXT1 : forall i, 0 <= i < cap -> mbyte rsegs m1 (buf + i) = mbyte rsegs mem (buf + i)).
  { intros i Hi. apply raw_mbyte. apply (munch_raw _ _ _ _ MU1); [lia | cbn [outside]; split; [lia | exact I]]. }
  assert (WS1 : forall z, 0 <= z < 2 ^ 64 -> ~ outside [(spZ regs - 48, spZ regs)] z ->
                  (spZ regs - PUT_K <= z < spZ regs) \/ False)
    by (intros z Hz Hn; cbn [outside] in Hn; left; unfold PUT_K, REALLOC_STACK, ALLOC_STACK; lia).
  destruct ARMS as [(Hcf & Hres & EL' & EA' & Emd & RSb & WO & HBL & KP & UK & LG2)
                   | (Hcf & Hres & Hmod & HNS & HNI & KP & UK & OLD2 & l1 & l2 & HLR & HNIN & LG2)].
  - subst res.
    assert (E2L : forall a, realloc_writes buf cap 0 a -> a < alloc_ceiling).
    { intros a Ha. destruct Ha as [Ha|[(Hb0 & Ha)|(Hr0 & Ha)]].
      - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. lia.
      - destruct (Z.eq_dec cap 0) as [C0|Cn]; [destruct (BUF0 C0); lia | lia].
      - lia. }
    assert (REC2 : pj_rec mem2 o buf len cap 0 pad).
    { unfold pj_rec in *. eapply rw_cells_hi; [exact CPK | exact HM1 | exact REC1 | lia | rewrite SPx; lia
        | cbn [cells_size csize]; unfold off_errno in EO; lia | exact E2L]. }
    assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs - 48) [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18);
                    C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { eapply rw_cells_hi; [exact CPK | exact HM1 | exact FR1 | lia | rewrite SPx; lia
        | cbn [cells_size csize]; unfold off_errno in ES; lia | exact E2L]. }
    eapply kA_lift; [exact Hh2 | exact Hl2 | |].
    { unfold mkR_of. rewrite K2, K3, K4, K8, K10, K20, K21, K22, K23, K24, K25, K26, K27.
      eapply put_after_realloc_null; [exact REC2 | rewrite SP2; unfold PUT_FRAME; exact STK2
        | rewrite SP2; unfold PUT_FRAME; lia | rewrite SP2; unfold PUT_FRAME; exact FR2 | right; rewrite SP2; exact SPO]. }
    intros x2 y2 HQ2 HEQ2 HRM2.
    destruct HQ2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & Ey2 & MU3 & WM3 & ST3 & REC3).
    subst y2.
    destruct (post_shape _ _ _ x2 md' HEQ2 PC) as [CF XM2]. rewrite XM2 in HRM2.
    apply SR_ret. unfold put_ret. cbv zeta.
    assert (Hst : put1 (mkW 0 text cap cnt fail calls) bs = mkW 1 text cap ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) (calls ++ [C])).
    { unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls]. change (0 =? 0) with true. cbn [negb].
      rewrite LT, LN. destruct (Z.leb_spec (len + n + 1) cap); [lia|]. rewrite Hcf, Z.eqb_refl. reflexivity. }
    rewrite Hst. cbn [w_text w_cap w_failed w_cnt w_fail]. rewrite LT.
    exists L', A', (ms_regs x2), m3, md', buf, Lam, peak, b.
    split; [exact CF|].
    split; [rewrite SEGS; apply (ro_munch_hi _ _ mem2 m3 RO2 MU3); unfold IMG_TOP; lia|].
    split.
    { apply (guard_trans B mem mem2 m3).
      - apply (guard_trans B mem m1 mem2); [|exact GK2].
        apply (guard_munch B API L A mem md _ mem m1 HM MU1). intros i Hi.
        destruct (got_low B API L A mem md i HM Hi) as [_ GL]. cbn [outside]. split; [lia | exact I].
      - apply (guard_munch B API L A mem md _ mem2 m3 HM MU3). intros i Hi.
        destruct (got_low B API L A mem md i HM Hi) as [_ GL]. cbn [outside]. split; [lia | exact I]. }
    split; [exact INIT|].
    split; [exact STR|].
    split.
    { apply (pj_out_of _ _ _ _ _ _ _ _ pad REC3 H8 Rb Rl Rc (or_intror eq_refl) BOt LT).
      destruct CAP as [C0|(Hj & Hin & Hst' & Hlt & Hz)]; [left; exact C0|right].
      split; [exact Hj|]. split; [exact Hin|]. split; [exact Hst'|]. split; [exact Hlt|].
      assert (Cn : cap <> 0) by (destruct Hj as (j & Hj & ->); pose proof (Z.pow_pos_nonneg 2 j); lia).
      destruct (lblock_of _ _ _ _ _ _ _ _ _ LG Hin) as (_ & Bbuf & _).
      eapply bytes_at_eqm; [exact (proj1 (zbytes_iff mem buf (text ++ [0]) ltac:(lia) ltac:(rewrite length_app; cbn; lia)) Hz)|].
      intros i Hi. rewrite length_map, length_app in Hi. cbn in Hi.
      rewrite <- TXT1 by lia.
      transitivity (mbyte rsegs mem2 (buf + i)).
      - apply raw_mbyte. apply (munch_raw _ _ _ _ MU3); [lia | cbn [outside]; split; [lia | exact I]].
      - pose proof (KP (buf - 16) (cap + 16) (i + 16) Bbuf ltac:(lia) ltac:(lia)) as KPi. rewrite SEGS in KPi.
        replace (buf - 16 + (i + 16)) with (buf + i) in KPi by lia. exact KPi. }
    split.
    { eapply (ledger_munch B API); [exact HM2 | exact LG2 | exact MU3 | |].
      - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. cbn [outside]. split; [lia | exact I].
      - intros x0 k i Hin Hi. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hin).
        pose proof (lblock_of _ _ _ _ _ _ _ _ _ LG2 Hin) as (Hk0 & _). cbn [outside]. split; [lia | exact I]. }
    split; [exact RSb|].
    right. right. left.
    split; [reflexivity|]. split; [exact HC|]. split; [exact Hcf|].
    do 4 (split; [reflexivity|]). split; [exact HBL|].
    split.
    { eapply (keeps_trans B L A mem m1 m3 0).
      - eapply (keeps_munch B API); [exact HM | exact MU1 |]. intros a k i Ha _ Hi.
        pose proof (block_range B API _ _ _ _ _ _ HM Ha). cbn [outside]. split; [lia | exact I].
      - eapply (keeps_trans B L A m1 mem2 m3 0); [exact KP|].
        eapply (keeps_munch B API); [exact HM | exact MU3 |]. intros a k i Ha _ Hi.
        pose proof (block_range B API _ _ _ _ _ _ HM Ha). cbn [outside]. split; [lia | exact I]. }
    split; [exact UK|].
    eapply (post_call B API SEGS PUT_K _ 0 L A regs mem md _ m1 (ms_regs x) (REALLOC_STACK + 48)); [exact PRE | exact MU1 | exact WM1 | | rewrite SPx; unfold PUT_K, REALLOC_STACK, ALLOC_STACK; lia
      | rewrite SPx; lia | | exact E2L | exact CPK | exact UK | exact MU3 | exact WM3 | exact HRM2 | | |].
    + intros z Hz Hn. destruct (WS1 z Hz Hn) as [H|[]]. left. exact H.
    + intros a Ha. unfold null_writes. destruct Ha as [Ha|[(Hb0 & Ha)|(Hr0 & Ha)]]; [right; left; exact Ha | | lia].
      right. right. split; [|lia]. intros C0. destruct (BUF0 C0). lia.
    + intros z Hz Hn. cbn [outside] in Hn. right. unfold null_writes. left. lia.
    + intros a Ha. pose proof (owned_low B API _ _ _ _ _ HM2 Ha). cbn [outside]. split; [lia | exact I].
    + eapply regs_kept; [exact HEQ2|]. unfold mkR_of. callee_cases.
  - assert (Hin' : In (res, C) ((res, C) :: l1 ++ l2)) by (left; reflexivity).
    pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hin') as RR.
    destruct (lblock_of _ _ _ _ _ _ _ _ _ LG2 Hin') as (_ & Bnew & _).
    assert (PRS2 : forall i, 0 <= i < C -> present mem2 (res + i))
      by (intros i Hi; exact (ledger_block_present B API _ _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hin' Hi)).
    assert (E2L : forall a, realloc_writes buf cap res a -> a < alloc_ceiling).
    { intros a Ha. destruct Ha as [Ha|[(Hb0 & Ha)|(Hr0 & Ha)]].
      - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. lia.
      - destruct (Z.eq_dec cap 0) as [C0|Cn]; [destruct (BUF0 C0); lia | lia].
      - lia. }
    assert (REC2 : pj_rec mem2 o buf len cap 0 pad).
    { unfold pj_rec in *. eapply rw_cells_hi; [exact CPK | exact HM1 | exact REC1 | lia | rewrite SPx; lia
        | cbn [cells_size csize]; unfold off_errno in EO; lia | exact E2L]. }
    assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs - 48) [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18);
                    C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { eapply rw_cells_hi; [exact CPK | exact HM1 | exact FR1 | lia | rewrite SPx; lia
        | cbn [cells_size csize]; unfold off_errno in ES; lia | exact E2L]. }
    assert (B0C : buf = 0 -> cap = 0) by (intros B0; destruct (Z.eq_dec cap 0) as [C0|Cn]; [exact C0 | destruct BR as (_ & _ & BR3); specialize (BR3 Cn); lia]).
    assert (LAMR : forall x0 y0, In (x0, y0) Lam -> x0 <> buf -> In (x0, y0) (l1 ++ l2)).
    { intros x0 y0 Hx0 Hne. destruct HLR as [(_ & -> & -> & _)|(_ & ELam & _)]; [exact Hx0|].
      rewrite ELam in Hx0. apply (in_app_skip _ _ _ _ Hx0). congruence. }
    assert (PRE2 : bytes_at rsegs mem2 res (map (Z_to_bv 8) text)).
    { apply zbytes_core; [lia | lia |]. intros i Hi. rewrite LT in Hi.
      assert (Cn : cap <> 0) by (intros C0; destruct (BUF0 C0); lia).
      destruct (CAPNZ Cn) as (Hin & _ & Hlt & Hz).
      pose proof (OLD2 i ltac:(lia)) as O2. rewrite SEGS in O2. rewrite O2.
      pose proof (OLD i ltac:(lia)) as O1. rewrite SEGS in O1. rewrite <- O1, TXT1 by lia.
      unfold zbytes_at in Hz. rewrite SEGS in Hz. rewrite (Hz i) by (rewrite length_app; cbn; lia).
      rewrite app_nth1 by lia. reflexivity. }
    assert (SRC2 : bytes_at rsegs mem2 s (map (Z_to_bv 8) bs)).
    { eapply bytes_at_eqm; [exact SRC|]. intros i Hi. rewrite length_map, LN in Hi.
      transitivity (mbyte rsegs m1 (s + i)).
      2:{ apply raw_mbyte. apply (munch_raw _ _ _ _ MU1); [lia | cbn [outside]; split; [lia | exact I]]. }
      destruct SW as [[SW1 SW2]|[[_ HR]|(x0 & y0 & Hx0 & Hne & H1 & H2)]].
      - apply (xport_hi _ _ _ _ _ _ _ _ _ _ _ _ CPK HM1); [lia | rewrite SPx; lia | unfold off_errno in SW2; lia | exact E2L].
      - apply mbyte_ro; [exact RO1 | exact RO2 | apply HR; lia].
      - destruct (lblock_of _ _ _ _ _ _ _ _ _ LG Hx0) as (Hy0 & Bx0 & _).
        pose proof (KP (x0 - 16) (y0 + 16) (s + i - (x0 - 16)) Bx0 ltac:(lia) ltac:(lia)) as KPi.
        rewrite SEGS in KPi. replace (x0 - 16 + (s + i - (x0 - 16))) with (s + i) in KPi by lia. exact KPi. }
    destruct (bytes_list mem2 (res + len) n ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; replace (res + len + i) with (res + (len + i)) by lia; apply PRS2; lia)) as (junkb & LJ & JB).
    assert (LJ' : length junkb = length bs) by lia.
    assert (SDJ : n = 0 \/ C = 0 \/ s + n <= res \/ res + C <= s).
    { apply (s_target L' A' mem2 md' _ _ _ _ res C s n HM2 LG2 Hin' ltac:(lia)).
      destruct SW as [[SW1 _]|[[_ HR]|(x0 & y0 & Hx0 & Hne & H1 & H2)]]; [left; lia | right; left; exact HR |].
      right. right. exists x0, y0. split; [right; exact (LAMR x0 y0 Hx0 Hne)|]. split; [|lia].
      intros E0. subst x0. apply HNIN. apply in_map_iff. exists (res, y0). split; [reflexivity | exact (LAMR res y0 Hx0 Hne)]. }
    assert (HN2 : mem_rel rsegs mem2 (normalize rsegs mem2)) by exact (mem_rel_normalize rsegs mem2 RO2).
    assert (NIr : forall i, 0 <= i < C -> ro_addr rsegs (wa (res + i)) = false).
    { intros i Hi. apply (ro_false_noimg B SEGS); [lia|].
      replace (res + i) with (res - 16 + (i + 16)) by lia. apply HNI. lia. }
    assert (REC2n : pj_rec (normalize rsegs mem2) o buf len cap 0 pad).
    { unfold pj_rec in *. apply (rw_cells_norm _ _ _ RO2 REC2). intros i Hi. cbn [cells_size csize] in Hi.
      apply ro_false_hi. unfold IMG_TOP. lia. }
    assert (STK2n := stk_norm _ _ _ RO2 STK2 ltac:(intros a Ha; apply ro_false_hi; unfold IMG_TOP; lia)).
    assert (FR2n := rw_cells_norm _ _ _ RO2 FR2
                      ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply ro_false_hi; unfold IMG_TOP; lia)).
    eapply kA_lift; [exact Hh2 | exact Hl2 | |].
    { unfold mkR_of. rewrite K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. rewrite <- LN.
      eapply put_post_norm; [exact RO2|].
      eapply put_after_realloc; [exact MC | exact REC2n | lia | lia | exact LT | lia
        | apply (wr_at_norm rsegs mem2 _ res C HN2); [apply present_wr_at; [lia | lia | exact PRS2] | exact NIr]
        | exact (bytes_at_normalize rsegs mem2 _ _ RO2 PRE2) | exact (bytes_at_normalize rsegs mem2 _ _ RO2 SRC2) | lia
        | exact (bytes_at_normalize rsegs mem2 _ _ RO2 JB) | exact LJ' | exact (mem_inv_normalize rsegs mem2)
        | rewrite SP2; unfold PUT_FRAME; exact STK2n | rewrite SP2; unfold PUT_FRAME; lia
        | rewrite SP2; unfold PUT_FRAME; exact FR2n
        | right; rewrite SP2; exact SPO | left; lia | left; lia | lia | lia]. }
    intros x3 y3 [HQ3 RO3] HEQ3 HRM3.
    destruct HQ3 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & Ey3 & MU3 & WM3 & ST3 & REC3 & TXT3).
    subst y3. rewrite LN in MU3, REC3.
    destruct (post_shape _ _ _ x3 md' HEQ3 PC) as [CF XM3]. rewrite XM3 in HRM3.
    apply SR_ret. unfold put_ret. cbv zeta.
    assert (Hst : put1 (mkW 0 text cap cnt fail calls) bs = mkW 0 (text ++ bs) C ((cnt + 1) mod 2 ^ 64) fail (calls ++ [C])).
    { unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls]. change (0 =? 0) with true. cbn [negb].
      rewrite LT, LN. destruct (Z.leb_spec (len + n + 1) cap); [lia|]. rewrite (proj2 (Z.eqb_neq cnt fail) Hcf). reflexivity. }
    rewrite Hst. cbn [w_text w_cap w_failed w_cnt w_fail].
    exists L', A', (ms_regs x3), m3, md', res, ((res, C) :: l1 ++ l2), (Z.max peak (lsum (l1 ++ l2) + C)),
      (wstep RF b cap C).
    split; [exact CF|].
    split; [rewrite SEGS; change (ro_agree rsegs m3) in RO3; exact RO3|].
    split.
    { apply (guard_trans B mem mem2 m3).
      - apply (guard_trans B mem m1 mem2); [|exact GK2].
        apply (guard_munch B API L A mem md _ mem m1 HM MU1). intros i Hi.
        destruct (got_low B API L A mem md i HM Hi) as [_ GL]. cbn [outside]. split; [lia | exact I].
      - apply (guard_munch B API L' A' mem2 md' _ mem2 m3 HM2 MU3). intros i Hi.
        destruct (got_low B API L' A' mem2 md' i HM2 Hi) as [GO GL].
        cbn [outside]. split; [lia|]. split; [|exact I].
        intros Hr. destruct (block_facts B API _ _ _ _ _ _ (ms_got_guard B + i - (res - 16)) HM2 Bnew ltac:(lia))
          as (_ & _ & _ & NO).
        apply NO. replace (res - 16 + (ms_got_guard B + i - (res - 16))) with (ms_got_guard B + i) by lia. exact GO. }
    split; [exact INIT|].
    split; [exact STR|].
    split.
    { assert (LTB : Z.of_nat (length (text ++ bs)) = len + n) by (rewrite length_app; lia).
      rewrite LTB. apply (pj_out_of _ _ _ _ _ _ _ _ pad REC3 H8 ltac:(lia) ltac:(lia) ltac:(lia) (or_introl eq_refl)).
      - unfold bytes_ok in *. apply Forall_app. split; assumption.
      - exact LTB.
      - right. split; [exists jn; split; [lia | exact NCE]|]. split; [exact Hin'|]. split; [exact HNS|]. split; [lia|].
        rewrite <- app_assoc. exact TXT3. }
    split.
    { eapply (ledger_munch B API); [exact HM2 | exact LG2 | exact MU3 | |].
      - intros a Ha. cbn [outside]. pose proof Ha as Ha'. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha'.
        split; [lia|]. split; [|exact I].
        intros Hr. apply (HNS (a - res + 16)); [lia|]. replace (res - 16 + (a - res + 16)) with a by lia. exact Ha.
      - intros x0 k i Hx0 Hi. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hx0).
        pose proof (lblock_of _ _ _ _ _ _ _ _ _ LG2 Hx0) as (Hk0 & Bx0 & _).
        cbn [outside]. split; [lia|]. split; [|exact I].
        destruct (Z.eq_dec x0 res) as [->|Hne]; [lia|].
        destruct (blocks_disj B API _ _ _ _ _ _ _ _ HM2 Bx0 Bnew ltac:(lia)); lia. }
    split.
    { unfold wstep. destruct (Z.eqb_spec cap 0) as [C0|Cn].
      - destruct HLR as [(_ & _ & _ & RSm & _)|(Bn & _)]; [exact RSm | destruct (BUF0 C0) as [Hb0 _]; exact (False_ind _ (Bn Hb0))].
      - destruct HLR as [(B0 & _)|(_ & _ & RSr & _)]; [destruct (Cn (B0C B0)) | exact RSr]. }
    right. right. right.
    split; [reflexivity|]. split; [exact HC|]. split; [exact Hcf|]. split; [exact Hres|]. split; [reflexivity|].
    assert (BLR : exists c1 c2, blocks L' A' = c1 ++ (res - 16, C + 16) :: c2 /\
                    forall a k, In (a, k) (blocks L A) -> a <> buf - 16 -> In (a, k) (c1 ++ c2)).
    { destruct HLR as [(_ & _ & _ & _ & b1 & b2 & E1 & E2)|(_ & _ & _ & b1 & b2 & c1 & c2 & E1 & E2 & E3)].
      - exists b1, b2. split; [exact E1|]. intros a k Ha _. rewrite E2 in Ha. exact Ha.
      - exists c1, c2. split; [exact E2|]. intros a k Ha Hne. rewrite E3. rewrite E1 in Ha.
        apply (in_app_skip _ _ _ _ Ha). congruence. }
    destruct BLR as (cc1 & cc2 & EB & INB).
    split.
    { eapply (keeps_trans B L A mem m1 m3 (buf - 16)).
      - eapply (keeps_munch B API); [exact HM | exact MU1 |]. intros a k i Ha _ Hi.
        pose proof (block_range B API _ _ _ _ _ _ HM Ha). cbn [outside]. split; [lia | exact I].
      - eapply (keeps_trans B L A m1 mem2 m3 (buf - 16)); [exact KP|].
        eapply (keeps_munch B API); [exact HM | exact MU3 |]. intros a k i Ha Hne Hi.
        pose proof (block_range B API _ _ _ _ _ _ HM Ha).
        destruct (newblock_disj _ _ _ _ _ _ _ _ _ _ HM2 EB (INB a k Ha Hne)).
        + cbn [outside]. split; [lia|]. split; [lia | exact I].
        + cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    split; [exact UK|].
    split.
    { eapply (post_call B API SEGS PUT_K _ (buf - 16) L A regs mem md _ m1 (ms_regs x) (REALLOC_STACK + 48));
        [exact PRE | exact MU1 | exact WM1 | | rewrite SPx; unfold PUT_K, REALLOC_STACK, ALLOC_STACK; lia
        | rewrite SPx; lia | | exact E2L | exact CPK | exact UK | exact MU3 | exact WM3 | exact HRM3 | | |].
      - intros z Hz Hn. destruct (WS1 z Hz Hn) as [H|[]]. left. exact H.
      - intros a Ha. unfold grow_writes. destruct Ha as [Ha|[(Hb0 & Ha)|(Hr0 & Ha)]].
        + right. left. exact Ha.
        + right. right. left. split; [|lia]. intros C0. destruct (BUF0 C0). lia.
        + right. right. right. lia.
      - intros z Hz Hn. cbn [outside] in Hn. right. unfold grow_writes.
        destruct (Z_le_gt_dec o z); destruct (Z_lt_ge_dec z (o + 24)); [left; lia | ..]; right; right; right; lia.
      - intros a Ha. pose proof (owned_low B API _ _ _ _ _ HM2 Ha). cbn [outside]. split; [lia|]. split; [|exact I].
        intros Hr. destruct (block_facts B API _ _ _ _ _ _ (a - (res - 16)) HM2 Bnew ltac:(lia)) as (_ & _ & _ & NO).
        apply NO. replace (res - 16 + (a - (res - 16))) with a by lia. exact Ha.
      - eapply regs_kept; [exact HEQ3|]. unfold mkR_of. callee_cases. }
    split.
    { destruct HLR as [(B0 & _ & _ & _ & b1 & b2 & E1 & E2)|(Bn & _ & _ & b1 & b2 & c1 & c2 & E1 & E2 & E3)].
      - exists b1, b2. split; [exact E1|]. left. split; [exact (B0C B0)|]. symmetry. exact E2.
      - exists c1, c2. split; [exact E2|]. right. split; [intros C0; destruct (BUF0 C0); lia|].
        exists b1, b2. split; [exact E1 | exact E3]. }
    exists l1, l2. split; [|split; reflexivity].
    destruct HLR as [(B0 & -> & -> & _)|(Bn & ELam & _)].
    + left. split; [exact (B0C B0)|]. split; reflexivity.
    + right. split; [intros C0; destruct (BUF0 C0); lia | exact ELam].
Qed.

End P.

Section Q.
Context {fx : FPState} {rc : RunCeil}.

Theorem put_holds : forall (B : malloc_syms) (API : AllocAPI B) (F : ResForm),
  fuzz_realloc_contract B API F -> memcpy_contract -> put_contract B API F.
Proof using.
  intros B API F RE MC. unfold put_contract.
  intros L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail calls
    SEGS PRE MI R10 R11 R12 PJ LG SPO EO ES ZB LN BO RS RSN SW SO NEED RES ROOM.
  assert (PP : ppre B API F L A regs mem md b o s n buf len cap failed text bs Lam peak cnt fail).
  { unfold ppre. rewrite SEGS in MI. repeat (split; [assumption|]). exact ROOM. }
  rewrite SEGS.
  change (pgoal B API F L A regs mem md b o n buf len cap failed text bs Lam peak cnt fail calls).
  destruct (Z.eq_dec failed 0) as [F0|F1].
  - destruct (Z_le_gt_dec (len + n + 1) cap) as [HC|HC].
    + exact (arm_fast B API F SEGS MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PP F0 HC).
    + exact (arm_grow B API F SEGS RE MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PP F0 ltac:(lia)).
  - exact (arm_failed B API F SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PP F1).
Qed.

End Q.
