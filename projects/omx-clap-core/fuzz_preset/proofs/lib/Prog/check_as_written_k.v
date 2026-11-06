From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ReaderRes strtod_c ex_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_as_written_c check_as_written_s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_as_written_r13 check_as_written_r2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_as_written_g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require LedgerCells GIInit fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11.
Import ListNotations.
Local Open Scope Z_scope.

Ltac caw_ret_ok := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Lemma caw_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma caw_bvid : forall x : word, Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma caw_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma caw_ret_pc : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof. exact kb_ret_pc. Qed.

Lemma caw_json : forall x : list byte, json_read jr_strtod (zb x) =
  match ex_V 0 (map bv_unsigned x) with
  | Some (u, r) => match skip r with [] => Some u | _ :: _ => None end
  | None => None
  end.
Proof.
  intros x. unfold json_read, jr_run, ex_V. change (Z.to_nat 0) with 0%nat.
  assert (E : zb x = map bv_unsigned x) by reflexivity. rewrite E.
  change ex_sm with jr_strtod.
  destruct (jr_value jr_strtod 0 (map bv_unsigned x) []) as [[[[u r]|] tr] ok]; reflexivity.
Qed.

Lemma caw_agree_V : forall rcv x t, caw_agree rcv x t ->
  match ex_V 0 (map bv_unsigned x) with
  | None => rcv <> 0
  | Some (u, r) => (rcv = 0 <-> caw_pe r = true) /\ (rcv = 0 -> t = u)
  end.
Proof.
  intros rcv x t H. unfold caw_agree in H. rewrite caw_json in H. unfold caw_pe.
  destruct (ex_V 0 (map bv_unsigned x)) as [[u r]|].
  - destruct (skip r) as [|c r'].
    + destruct H as [[H1 H2]|[H1 H2]]; [|discriminate].
      injection H2 as H2. subst u. split; [split; intros _; [reflexivity | exact H1] | intros _; reflexivity].
    + destruct H as [[H1 H2]|[H1 H2]]; [discriminate|].
      split; [split; intros E; [exfalso; exact (H1 E) | discriminate] | intros E; exfalso; exact (H1 E)].
  - destruct H as [[H1 H2]|[H1 H2]]; [discriminate | exact H1].
Qed.

Lemma caw_not_outside : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [outside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (l & h & Hin & Hr); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists l, h. split; [right; exact Hin | exact Hr].
  - destruct (IH x) as (l & h & Hin & Hr); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists l, h. split; [right; exact Hin | exact Hr].
Qed.

Lemma caw_stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H1 & H2 & H) Hl Hh Hlh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

Lemma caw_stk_present : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> present m a) ->
  stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha. destruct (HP a Ha) as [v Hv].
  unfold wa. split.
  - unfold wview. rewrite Hv. discriminate.
  - exists v. unfold mrd. rewrite Hv. reflexivity.
Qed.

Definition caw_kr (ra rb : bvmap 5 word) : Prop :=
  forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr rb (Z_to_bv 5 r) = getr ra (Z_to_bv 5 r).

Lemma caw_kr_trans : forall r1 r2 r3, caw_kr r1 r2 -> caw_kr r2 r3 -> caw_kr r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma caw_kr_pres : forall r1 r2, regs_preserved r1 r2 -> caw_kr r1 r2.
Proof. intros r1 r2 H r Hr. apply H. unfold callee_saved. lia. Qed.

Lemma caw_pres : forall r0 r5, getr r5 2 = getr r0 2 -> getr r5 8 = getr r0 8 -> getr r5 9 = getr r0 9 ->
  getr r5 18 = getr r0 18 -> caw_kr r0 r5 -> regs_preserved r0 r5.
Proof.
  intros r0 r5 H2 H8 H9 H18 K r Hr. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - exact H2.
  - apply K. lia.
  - apply K. lia.
  - exact H8.
  - exact H9.
  - destruct (Z.eq_dec r 18) as [->|Hne]; [exact H18 | apply K; lia].
Qed.

Ltac caw_kr_tac HG :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr;
  assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; rewrite HG; reflexivity.

Lemma caw_fk : forall (f : YK11.FPState) F' fc', ex_fkeep (@fp_regs f) F' -> fregs_kept f (mkFP F' fc').
Proof.
  intros f F' fc' H r Hr. cbn [fp_regs]. apply H.
  assert (E : bv_unsigned (Z_to_bv 5 r) = r).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. unfold bv_modulus. change (2 ^ Z.of_N 5) with 32. lia. }
  rewrite E. cbn [In]. lia.
Qed.

Lemma caw_apart_le : forall a k b k', 0 <= k -> 0 <= k' -> (a + k <= b \/ b + k' <= a) -> ex_apart a k b k'.
Proof. intros a k b k' _ _ H. unfold ex_apart. lia. Qed.

(* an image byte the loaded segments hold: whatever the memory holds there is one byte g *)
Lemma caw_img_byte : forall m a, Mem.mrd rsegs (fun _ => None) (Mem.wa a) <> None -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  exists g, 0 <= g < 2 ^ 8 /\ bytes_at rsegs m a (le1 (Z_to_bv 64 g)).
Proof.
  intros m a HR H0 H1.
  assert (E : exists b, Mem.mrd rsegs m (Mem.wa a) = Some b).
  { unfold Mem.mrd in *. cbv beta iota in HR. destruct (m (Mem.wa a)) as [b|]; [exists b; reflexivity|].
    match goal with |- exists b, ?t = Some b => destruct t as [b|] eqn:Et; [exists b; reflexivity | congruence] end. }
  destruct E as (b & E). exists (bv_unsigned b).
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  split; [exact Hb|].
  change (Z_to_bv 64 (bv_unsigned b)) with (zxb b). rewrite le1_zxb.
  split; [exact H0|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. destruct i as [|i]; [cbn [Z.of_nat nth_error]; rewrite Z.add_0_r; exact E | cbn [length] in Hi; lia].
Qed.

Lemma caw_glob_own : in_globals GIInit.omx_G LedgerCells.GL_OWN_RAN_OUT.
Proof.
  exists LedgerCells.GL_OWN_RAN_OUT, 8. split; [|lia].
  unfold GIInit.omx_G. cbn [In]. repeat first [left; reflexivity | right].
Qed.

Lemma caw_glob_ran : in_globals GIInit.omx_G fuzz_alloc_ran_out_c.G_RAN_OUT.
Proof.
  exists LedgerCells.GL_RAN_OUT, 8. split; [|unfold LedgerCells.GL_RAN_OUT, fuzz_alloc_ran_out_c.G_RAN_OUT; lia].
  unfold GIInit.omx_G. cbn [In]. repeat first [left; reflexivity | right].
Qed.

Section K.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis ERU : errno_unowned B API.
Hypothesis HERR : errno_addr B = STRTOD_ERRNO.
Hypothesis HTP : ms_tp B = STRTOD_TP.
Hypothesis HGG : ms_got_guard B = STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = STRTOD_GUARD.
Hypothesis HMAL : ms_malloc B = 0x178d8.
Hypothesis HFREE : ms_free B = 0x17798.
Hypothesis MALLOC : forall fx : YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis EXV : ex_value_contract.
Hypothesis HG : globals_free B API GIInit.omx_G.
Hypothesis RANC : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract.

Lemma caw_seg_in_img : forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HS; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma caw_mbyte_raw : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> mbyte (ms_segs B) m a = m (Z_to_bv 64 a).
Proof.
  intros m a Ha Hn. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  unfold YK11.seg_rom, memory_read. rewrite caw_uns by lia. change (Z.of_N 1) with 1.
  destruct (find_segment (ms_segs B) a 1) as [s|] eqn:E; [exfalso; exact (Hn (caw_seg_in_img a s E)) | reflexivity].
Qed.

Lemma caw_present_of_writable : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  writable_at (ms_segs B) m a -> present m a.
Proof.
  intros m a Ha Hn W. unfold writable_at, wview in W. unfold present.
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [exists x; reflexivity|]. exfalso.
  rewrite caw_uns in W by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:Fs; [|apply W; reflexivity].
  exact (Hn (caw_seg_in_img a seg Fs)).
Qed.

Lemma caw_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold ro_addr. rewrite caw_uns by lia. rewrite <- HS.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (caw_seg_in_img a seg E)) | reflexivity].
Qed.

Lemma caw_ro_agree_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> ~ in_img B a) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (caw_ro_false (bv_unsigned a) Hr (HW _ Hr Ho)) as E. rewrite caw_bvid in E. congruence.
Qed.

Lemma caw_bytes_frame : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). pose proof (Hm (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E. rewrite HS in E.
  exact E.
Qed.

Lemma caw_rw_frame : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte (ms_segs B) m' (A + i) = mbyte (ms_segs B) m (A + i) /\ writable_at (ms_segs B) m' (A + i)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs ((Hwf & Hb) & (Hw0 & Hw1 & Hw)) H.
  split; [split; [exact Hwf|] | split; [exact Hw0 | split; [exact Hw1|]]].
  - apply (caw_bytes_frame m m' A _ Hb). intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf.
    exact (proj1 (H i Hi)).
  - intros i Hi. pose proof (proj2 (H i Hi)) as W. unfold writable_at in W. rewrite HS in W. exact W.
Qed.

Lemma caw_norm_mbyte : forall m a, 0 <= a < 2 ^ 47 -> a < 65536 \/ 143360 <= a ->
  mbyte (ms_segs B) (normalize_cj rsegs m) a = mbyte (ms_segs B) m a.
Proof.
  intros m a H1 H2. unfold mbyte, normalize_cj. rewrite (caw_keep a H1 H2). reflexivity.
Qed.

Lemma caw_rw_C8 : forall m a v, word_mem (ms_segs B) m a v -> 0 <= v < 2 ^ 64 -> stk rsegs m a (a + Z.of_nat 8) ->
  rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hw Hv (S0 & S1 & S). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- HS. apply word_mem_le8; [exact Hw | exact Hv | lia | lia].
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Lemma caw_rd_cells : forall L A m md, MR L A m md -> ro_agree (ms_segs B) m -> rd_cells B m.
Proof.
  intros L A m md HM RA. destruct (ax_statics AX L A m md HM) as (G1 & (g & _ & G2) & _).
  split; [exact RA|]. split; [exact G1|]. exists g. exact G2.
Qed.

Lemma caw_cp_hi : forall Kc L A regs m md Ec L' A' regs' m' md' a,
  call_post_k B MR Kc L A regs m md Ec L' A' regs' m' md' -> MR L A m md ->
  YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B Kc regs a -> ~ Ec a ->
  mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a /\ (writable_at (ms_segs B) m a <-> writable_at (ms_segs B) m' a).
Proof.
  intros Kc L A regs m md Ec L' A' regs' m' md' a CP HM Ha Hs He.
  destruct CP as (HM' & _ & _ & _ & _ & _ & _ & HFR & _).
  apply (HFR a (or_introl Ha)); [| | exact Hs | exact He].
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
Qed.

Lemma caw_sep_new : forall L A m md b1 b2 q n p kk, MR L A m md -> blocks L A = b1 ++ (q, n) :: b2 ->
  In (p, kk) (b1 ++ b2) -> q + n <= p \/ p + kk <= q.
Proof.
  intros L A m md b1 b2 q n p kk HM EB Hin.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM) as PW. rewrite EB in PW.
  destruct (caw_pairwise_mid _ b1 (q, n) b2 PW (p, kk) Hin) as [H|H];
    unfold YO0f.ranges_disjoint in H; cbn [fst snd] in H; lia.
Qed.

Lemma caw_new_notin : forall L A m md b1 b2 q n, MR L A m md -> blocks L A = b1 ++ (q, n) :: b2 -> 0 < n ->
  ~ In (q, n) (b1 ++ b2).
Proof. intros L A m md b1 b2 q n HM EB Hn Hin. destruct (caw_sep_new L A m md b1 b2 q n q n HM EB Hin); lia. Qed.

Lemma caw_fresh_side : forall q n, 0 < n -> (forall i, 0 <= i < n -> ~ in_img B (q + i)) ->
  q + n <= 0x10000 \/ 0x56000 <= q.
Proof.
  intros q n Hn H. destruct (Z_le_gt_dec (q + n) 0x10000) as [E|E]; [left; exact E|right].
  destruct (Z_le_gt_dec 0x56000 q) as [E'|E']; [exact E'|exfalso].
  destruct (Z_le_gt_dec q 0x10000).
  - apply (H (0x10000 - q)); [lia|]. apply (caw_img_iff B HS). lia.
  - apply (H 0); [lia|]. apply (caw_img_iff B HS). lia.
Qed.

Lemma caw_apart_img : forall a k b k', (forall i, 0 <= i < k -> ~ in_img B (a + i)) ->
  (forall j, 0 <= j < k' -> in_img B (b + j)) -> ex_apart a k b k'.
Proof.
  intros a k b k' H H'. unfold ex_apart.
  destruct (Z_le_gt_dec k 0); [left; lia|]. destruct (Z_le_gt_dec k' 0); [right; left; lia|].
  destruct (Z_le_gt_dec (a + k) b); [right; right; left; lia|].
  destruct (Z_le_gt_dec (b + k') a); [right; right; right; lia|]. exfalso.
  destruct (Z_le_gt_dec a b).
  - apply (H (b - a)); [lia|]. replace (a + (b - a)) with (b + 0) by lia. apply H'. lia.
  - apply (H 0); [lia|]. replace (a + 0) with (b + (a - b)) by lia. apply H'. lia.
Qed.

Lemma caw_kA : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  evt rsegs Q (MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz HE HSh HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite HS. eapply evt_mono; [exact HE|]. intros ms' HQ. destruct (HSh ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma caw_kF : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> ro_agree rsegs mem1 ->
  evt rsegs Q (MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize_cj rsegs mem1) (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R Fr pc' fc m', ms' = MS R Fr pc' fc None m' (seg_rom rsegs)) ->
  (forall R Fr pc' fc m0 mem' regs', Q (MS R Fr pc' fc None m0 (seg_rom rsegs)) ->
     mem_rel_cj rsegs mem' m0 -> cj_same rsegs mem1 mem' -> (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP Fr fc) regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz Hro HE HSh HK.
  pose proof (evt_normalize_cj rsegs Q (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)
    caw_wx Hro HE) as HE'.
  rewrite HS in HK |- *.
  apply (evt_SR_canon rsegs (@mkst fx1 regs1 pc mem1 (seg_rom rsegs))
    (fun s => exists s0, Q s0 /\ ms_rel_cj rsegs s s0 /\ cj_same rsegs mem1 (ms_mem s)) md1 P HE' Hh Hz).
  intros ms' (s & (s0 & HQ & Hrel & Hsame) & Heq).
  destruct (HSh s0 HQ) as (R & Fr & pc' & fc & m0 & Es0). subst s0.
  destruct s as [r1 f1 p1 sv1 rv1 fc1 m1 ro1].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in E1, E2, E3, E4, E5, E6, E7, HR, Hsame.
  subst r1 f1 p1 sv1 rv1 fc1 ro1.
  destruct Heq as (HRg & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in HRg, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom.
  subst fr' pcv' svc' rv' fc' m' ro'.
  exact (HK R Fr pc' fc m0 m1 regs' HQ HR Hsame (kb_getr_eqv _ _ HRg)).
Qed.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CAW_K L0 A0 regs0 mem0 md0.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : STRTOD_GLOBALS_TOP <= spZ regs0 - CAW_K.

Let J := cj B API L0 A0 regs0 mem0 md0.

Lemma caw_sp : YM05.alloc_ceiling + CAW_K <= spZ regs0 /\ spZ regs0 mod 16 = 0 /\ spZ regs0 <= 2 ^ 47 /\
  140735332483072 <= YM05.alloc_ceiling /\ CAW_K = 13232 /\ ex_value_K 0 = 13152.
Proof.
  pose proof PRE0 as (_ & _ & _ & _ & H16 & HK & _). pose proof YM05.alloc_ceiling_value as Hc.
  split; [exact HK|]. split; [exact H16|]. split; [exact HSP47|]. split; [lia|]. split; reflexivity.
Qed.

Lemma caw_auxv : forall L A m md, J L A m md -> st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs0 - 80) m.
Proof.
  intros L A m md Jc Hf.
  pose proof Jc as (HM & _ & _ & (_ & Hsec & _) & HI & HLB & _ & _ & _ & HHI & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _ & _ & _ & HAUX).
  assert (Hf0 : st_init_done A0 = false).
  { destruct (st_init_done A0) eqn:E; [rewrite (HI eq_refl) in Hf; discriminate | reflexivity]. }
  destruct (HAUX Hf0) as (av & ar & W1 & W2 & W3 & W4 & H5 & H6 & H7 & H8 & H9 & H10).
  pose proof caw_k_val as HKv. pose proof YM05.alloc_ceiling_value as Hc.
  assert (HE : errno_addr B + 4 <= YM05.alloc_ceiling) by (rewrite HERR; unfold STRTOD_ERRNO; lia).
  assert (HIx : forall a v, spZ regs0 <= a -> a + 8 <= 2 ^ 63 -> word_mem (ms_segs B) mem0 a v ->
            word_mem (ms_segs B) m a v).
  { intros a v H1 H2 Hw. apply (word_mem_frame (ms_segs B) mem0 m a v Hw). intros k Hk.
    refine (proj1 (HHI (a + k) _ _)); [lia | intros [Hs|Hs]; lia]. }
  rewrite Hsec. exists av, ar.
  split; [intros k Hk; rewrite (HLB Hf (Z.of_nat k)) by lia; exact (W1 k Hk)|].
  split; [intros k Hk; apply HIx; [lia | lia | exact (W2 k Hk)]|].
  split; [apply HIx; [lia | lia | exact W3]|].
  split; [apply HIx; [lia | lia | exact W4]|].
  lia.
Qed.

Lemma caw_call_pre : forall L A regs m md K,
  J L A m md -> spZ regs = spZ regs0 - 80 -> 0 <= K -> 80 + K <= CAW_K ->
  getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  call_pre_k B MR K L A regs m md.
Proof.
  intros L A regs m md K Jc Hsp HK0 HKK Htp Hra.
  pose proof Jc as (HM & HWF & HBD & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  pose proof PRE0 as (_ & _ & _ & _ & HSP16 & HK & HK63 & _ & HTP0 & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  rewrite Hsp. split; [clear -HSP16; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSC; left; lia|]. split; [rewrite Htp; exact HTP0|].
  split; [intros a Ha; apply HSC; right; exact Ha|].
  intros Hf. exact (caw_auxv L A m md Jc Hf).
Qed.

Lemma caw_call_malloc : forall (fx : YK11.FPState) L A regs m md b n (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 80 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = Z_to_bv 64 n -> rf_ok F A b -> rf_room F b n ->
  (forall L' A' regs' m' md' q,
     J L' A' m' md' ->
     call_post_k B MR ALLOC_STACK L A regs m md (fun _ => False) L' A' regs' m' md' ->
     getr regs' 10 = Z_to_bv 64 q -> fresh_block B q n ->
     (exists b1 b2, blocks L' A' = b1 ++ (q, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     st_init_done A' = true -> rf_ok F A' (rf_malloc F b n) ->
     SR (ms_segs B) (mkCfg (@mkst fx regs' (getr regs 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 0x178d8) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md b n P Jc Hsp Htp Hra R10 HRES HROOM K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & _ & HRA).
  pose proof caw_k_val as HKv.
  rewrite <- HMAL.
  eapply SR_bind; [apply (MALLOC fx L A regs m md n b) |].
  - apply (proj2 (call_pre_k_alloc B MR L A regs m md)).
    apply (caw_call_pre L A regs m md ALLOC_STACK Jc Hsp); [unfold ALLOC_STACK; lia | unfold ALLOC_STACK; lia | exact Htp | exact Hra].
  - exact HRA.
  - exact R10.
  - exact HRES.
  - exact HROOM.
  - intros c' (L' & A' & regs' & m' & md' & q & -> & CP & R10' & Hq & Hq16 & FR & BL & BK & RA' & GK & SURV & INIT & LEN & RES').
    apply (K L' A' regs' m' md' q); try assumption.
    apply (cj_callpost B API L0 A0 regs0 mem0 md0 PRE0 L A m md ALLOC_STACK regs (fun _ => False) L' A' regs' m' md' Jc CP).
    + unfold ALLOC_STACK. lia.
    + lia.
    + intros a [].
    + intros p k Hp. exact (SURV p k (proj1 (HUB p k Hp))).
    + exact INIT.
    + exact LEN.
    + exact RA'.
Qed.

Lemma caw_pairwise_map : forall {T U : Type} (R : U -> U -> Prop) (f : T -> U) l x y,
  pairwise R (map f l) -> In x l -> In y l -> x <> y -> R (f x) (f y) \/ R (f y) (f x).
Proof.
  intros T U R f l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. apply in_map. exact Hy.
  - right. apply Hz. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma caw_call_free : forall (fx : YK11.FPState) L A regs m md b p n (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 80 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall q k, In (q, k) (user_blocks A0) -> q <> p) ->
  rf_ok F A b ->
  (forall L' A' regs' m' md',
     J L' A' m' md' ->
     call_post_k B MR ALLOC_STACK L A regs m md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' m' md' ->
     (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     st_init_done A' = true -> rf_ok F A' (rf_free F b n) ->
     SR (ms_segs B) (mkCfg (@mkst fx regs' (getr regs 1) m' (seg_rom (ms_segs B))) md') P) ->
  st_init_done A = true ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 0x17798) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md b p n P Jc Hsp Htp Hra Hp R10 HNS HRES K INIT.
  pose proof Jc as (HM & HWF & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & _ & HRA).
  pose proof caw_k_val as HKv.
  rewrite <- HFREE.
  eapply SR_bind; [apply (FREE fx L A regs m md p n b) |].
  - apply (proj2 (call_pre_k_alloc B MR L A regs m md)).
    apply (caw_call_pre L A regs m md ALLOC_STACK Jc Hsp); [unfold ALLOC_STACK; lia | unfold ALLOC_STACK; lia | exact Htp | exact Hra].
  - exact HRA.
  - exact Hp.
  - exact R10.
  - exact HRES.
  - intros c' (L' & A' & regs' & m' & md' & -> & CP & BL & BK & RA' & GK & SURV & INIT' & LEN & RES').
    pose proof (proj1 (call_post_k_alloc B MR L A regs m md _ L' A' regs' m' md') CP) as CPk.
    apply (K L' A' regs' m' md'); [| exact CPk | exact BL | exact (INIT' INIT) | exact RES'].
    apply (cj_callpost B API L0 A0 regs0 mem0 md0 PRE0 L A m md ALLOC_STACK regs _ L' A' regs' m' md' Jc CPk).
    + unfold ALLOC_STACK. lia.
    + lia.
    + intros a Ha. pose proof (caw_ub_blocks L A p n Hp) as Hb.
      destruct (caw_block_facts B API AX L A m md _ n (a - ptr_addr L p) HM Hb ltac:(lia)) as (_ & _ & H3 & _ & H5).
      replace (ptr_addr L p + (a - ptr_addr L p)) with a in H5 by lia.
      split; [lia|]. split; [exact H5|].
      intros p0 n0 Hp0 Ha0. destruct (HUB p0 n0 Hp0) as (Hp0A & Hptr).
      assert (Hne : (p, n) <> (p0, n0)) by (intros E; injection E as E1 E2; exact (HNS p0 n0 Hp0 (eq_sym E1))).
      pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM) as PW. unfold blocks in PW.
      destruct (caw_pairwise_map _ _ _ _ _ PW Hp Hp0A Hne) as [D|D];
        unfold YO0f.ranges_disjoint in D; cbn [fst snd] in D; rewrite Hptr in D; lia.
    + intros q k Hq. apply SURV; [exact (proj1 (HUB q k Hq)) | exact (HNS q k Hq)].
    + exact (INIT' INIT).
    + exact LEN.
    + exact RA'.
Qed.

Lemma caw_data : forall L A m md data x, J L A m md -> bytes_at rsegs mem0 data x ->
  (x <> [] -> caw_inside L0 A0 data (Z.of_nat (length x))) -> bytes_at rsegs m data x.
Proof.
  intros L A m md data x Jc Hb Hin.
  destruct x as [|c x'].
  - destruct Hb as (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn in Hi. lia.
  - destruct (Hin ltac:(discriminate)) as (p & k & Hpk & H1 & H2).
    apply (caw_bytes_frame mem0 m data (c :: x') Hb). intros i Hi.
    replace (data + i) with (p + (data + i - p)) by lia.
    apply (cj_mem0 B API L0 A0 regs0 mem0 md0 L A m md p k (data + i - p) Jc Hpk). lia.
Qed.

Lemma caw_inside_blk : forall a k, caw_inside L0 A0 a k -> exists p kk, In (p, kk) (blocks L0 A0) /\ p <= a /\
  a + k <= p + kk /\ 4096 <= p /\ p + kk <= YM05.alloc_ceiling /\ (forall i, 0 <= i < kk -> ~ in_img B (p + i)).
Proof.
  intros a k (p & kk & Hin & H1 & H2). pose proof PRE0 as (HM0 & _).
  destruct (caw_block_range B API L0 A0 mem0 md0 p kk HM0 Hin) as (H3 & H4).
  exists p, kk. split; [exact Hin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  intros i Hi. exact (proj2 (proj2 (proj2 (proj2 (caw_block_facts B API AX L0 A0 mem0 md0 p kk i HM0 Hin Hi))))).
Qed.

Lemma caw_stk_cj : forall L A m md, J L A m md -> stk rsegs m (spZ regs0 - CAW_K) (spZ regs0).
Proof.
  intros L A m md Jc. pose proof Jc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  pose proof caw_sp as (Hs1 & _ & Hs47 & Hc & HKv & _).
  apply caw_stk_present; [lia | lia |]. intros a Ha.
  apply (caw_present_of_writable m a); [lia | rewrite (caw_img_iff B HS); lia |].
  apply HSC. left. exact Ha.
Qed.

Lemma caw_rw_cp : forall Kc L A regs m md Ec L' A' regs' m' md' Ad cs,
  call_post_k B MR Kc L A regs m md Ec L' A' regs' m' md' -> MR L A m md -> J L' A' m' md' ->
  rw_cells rsegs m Ad cs -> spZ regs <= Ad -> spZ regs0 - CAW_K <= spZ regs ->
  Ad + Z.of_nat (cells_size cs) <= spZ regs0 ->
  (forall a, Ad <= a < Ad + Z.of_nat (cells_size cs) -> ~ Ec a) ->
  rw_cells rsegs m' Ad cs.
Proof.
  intros Kc L A regs m md Ec L' A' regs' m' md' Ad cs CP HM Jc RW H1 H2 H3 HE.
  pose proof Jc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  pose proof caw_sp as (Hs1 & _ & Hs47 & Hc & HKv & _).
  assert (Herr : errno_addr B + 4 <= YM05.alloc_ceiling) by (rewrite HERR; unfold STRTOD_ERRNO; lia).
  apply (caw_rw_frame m m' Ad cs RW). intros i Hi. split.
  - refine (proj1 (caw_cp_hi Kc L A regs m md Ec L' A' regs' m' md' (Ad + i) CP HM _ _ _)); [lia | | apply HE; lia].
    intros [Hs|Hs]; lia.
  - apply HSC. left. lia.
Qed.

Lemma caw_doc_norm : forall L A m md lblk doc t D,
  J L A m md -> pj_node rsegs mem0 lblk doc t D -> spZ regs0 <= doc -> doc + 56 <= 2 ^ 47 ->
  Forall (fun ak => caw_inside L0 A0 (fst ak) (snd ak)) D ->
  pj_node rsegs (normalize_cj rsegs m) (fun a k => In (a, k) D) doc t D.
Proof.
  intros L A m md lblk doc t D Jc HN H1 H2 HD.
  pose proof Jc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HHI & _).
  pose proof caw_sp as (Hs1 & _ & Hs47 & Hc & HKv & _). pose proof PRE0 as (HM0 & _).
  apply (pj_node_frame rsegs t mem0 lblk (normalize_cj rsegs m) (fun a k => In (a, k) D) doc D HN);
    [intros a k Hak; exact Hak|].
  intros w Hw. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
  rewrite <- (caw_bvid w). set (z := bv_unsigned w) in *.
  assert (KEY : (0 <= z < 2 ^ 47 /\ (z < 65536 \/ 143360 <= z)) /\
                mbyte (ms_segs B) m z = mbyte (ms_segs B) mem0 z /\ ~ in_img B z).
  { destruct Hw as [Hz | ((a, k) & Hin & Hz)].
    - assert (Hni : ~ in_img B z) by (rewrite (caw_img_iff B HS); lia).
      split; [split; lia|]. split; [|exact Hni].
      refine (proj1 (HHI z _ _)); [lia | intros [Hs|Hs]; [lia | rewrite HERR in Hs; unfold STRTOD_ERRNO in Hs; lia]].
    - unfold pj_holds in Hz. cbn [fst snd] in Hz.
      rewrite Forall_forall in HD. destruct (HD (a, k) Hin) as (p & kk & Hpk & Hp1 & Hp2). cbn [fst snd] in Hp1, Hp2.
      destruct (caw_block_facts B API AX L0 A0 mem0 md0 p kk (z - p) HM0 Hpk ltac:(lia)) as (_ & Hb1 & Hb2 & _ & Hni).
      replace (p + (z - p)) with z in Hni by lia.
      split; [split; [lia | rewrite (caw_img_iff B HS) in Hni; lia]|]. split; [|exact Hni].
      replace z with (p + (z - p)) by lia. apply (cj_mem0 B API L0 A0 regs0 mem0 md0 L A m md p kk (z - p) Jc Hpk). lia. }
  destruct KEY as ((Hz1 & Hz2) & Hmb & Hni).
  unfold normalize_cj. rewrite (caw_keep z Hz1 Hz2).
  rewrite <- (caw_mbyte_raw m z ltac:(lia) Hni), <- (caw_mbyte_raw mem0 z ltac:(lia) Hni). exact Hmb.
Qed.

(* g_own_ran_out and g_ran_out (omx_G cells, so no allocator state owns them) keep their bytes *)
Lemma caw_flag_keep : forall L A m md a bs, J L A m md -> in_globals GIInit.omx_G a ->
  bytes_at rsegs mem0 a bs -> Z.of_nat (length bs) = 1 -> bytes_at rsegs m a bs.
Proof.
  intros L A m md a bs Jc Hg Hb Hl.
  pose proof Jc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIM & _).
  pose proof caw_sp as (Hs1 & _).
  destruct (HG a Hg) as (GIMG & GLO & _ & GERR & GNO).
  apply (caw_bytes_frame mem0 m a bs Hb). intros i Hi. rewrite Hl in Hi.
  replace (a + i) with a by lia.
  refine (proj1 (HIM a GIMG _ _)).
  - intros L1 A1 m1 md1 HM1. exact (proj1 (GNO L1 A1 m1 md1 HM1)).
  - intros [Hs|Hs]; [lia | exact (GERR Hs)].
Qed.

Lemma caw_main : forall (fx : YK11.FPState) data rcv doc (x : list byte) lblk t D (b : rf_R F),
  frm_zero (@fp_csr fx) -> rd_cells B mem0 ->
  getr regs0 10 = Z_to_bv 64 data -> getr regs0 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
  getr regs0 12 = Z_to_bv 64 rcv -> getr regs0 13 = Z_to_bv 64 doc ->
  0 <= rcv < 2 ^ 64 -> 0 <= doc < 2 ^ 64 ->
  Z.of_nat (length x) <= 3 * 2 ^ 20 -> 0 < data -> data + Z.of_nat (length x) < 2 ^ 62 ->
  bytes_at rsegs mem0 data x -> (x <> [] -> caw_inside L0 A0 data (Z.of_nat (length x))) ->
  (rcv = 0 -> pj_node rsegs mem0 lblk doc t D /\ spZ regs0 <= doc /\ doc + 56 <= 2 ^ 47 /\
     Forall (fun ak => caw_inside L0 A0 (fst ak) (snd ak)) D) ->
  caw_agree rcv x t -> rf_ok F A0 b -> rf_room F b (Z.of_nat (length x) + 1) ->
  SR (ms_segs B) (mkCfg (@mkst fx regs0 (Z_to_bv 64 CHECK_AS_WRITTEN) mem0 (seg_rom (ms_segs B))) md0)
    (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md',
       c' = mkCfg (@mkst fx' regs' (getr regs0 1) mem' (seg_rom (ms_segs B))) md' /\
       frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
       rpost B API CAW_K L0 A0 regs0 mem0 md0 (fun _ => False) (fun _ _ => False) L' A' regs' mem' md' /\
       rd_cells B mem' /\ st_init_done A' = true /\ blocks L' A' = blocks L0 A0 /\
       bytes_at (ms_segs B) mem' data x /\
       rf_ok F A' (rf_free F (rf_malloc F b (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1)) /\
       caw_ran_out B mem0 mem' (getr regs' 10)).
Proof.
  intros fx data rcv doc x lblk t D b HFZ HRD R10 R11 R12 R13 Hrcv Hdoc Hlen Hd0 Hd1 HDB HDI HDOC HAG HRES HROOM.
  match goal with |- SR _ _ ?Q => set (POST := Q) end.
  pose proof caw_sp as (Hs1 & Hs16 & Hs47 & Hc & HKv & HK0v).
  pose proof PRE0 as (HM0 & _ & _ & Hra0 & _ & _ & _ & _ & HTP0 & _).
  pose proof YM05.alloc_ceiling_lt as Hclt.
  assert (Herr4 : STRTOD_ERRNO + 4 <= YM05.alloc_ceiling) by (unfold STRTOD_ERRNO; lia).
  destruct (kb_md B API L0 A0 mem0 md0 HM0) as (Hh0 & Hz0).
  pose proof (proj1 HRD) as HRA0.
  pose proof (cj_init B API L0 A0 regs0 mem0 md0 PRE0 HRA0) as J0.
  pose proof (kb_stk B API (caw_img_low B HS) CAW_K L0 A0 regs0 mem0 md0 PRE0 ltac:(lia)) as Hstk0.
  rewrite HS in Hstk0.
  assert (DG : Z.of_nat (length x) = 0 \/ exists p kk, In (p, kk) (blocks L0 A0) /\ p <= data /\
     data + Z.of_nat (length x) <= p + kk /\ 4096 <= p /\ p + kk <= YM05.alloc_ceiling /\
     (forall i, 0 <= i < kk -> ~ in_img B (p + i))).
  { destruct x as [|c x']; [left; reflexivity | right]. apply caw_inside_blk. apply HDI. discriminate. }
  (* g_own_ran_out = go and g_ran_out = gr on entry *)
  destruct (caw_img_byte mem0 LedgerCells.GL_OWN_RAN_OUT
    ltac:(unfold LedgerCells.GL_OWN_RAN_OUT; vm_compute; discriminate)
    ltac:(unfold LedgerCells.GL_OWN_RAN_OUT; lia) ltac:(unfold LedgerCells.GL_OWN_RAN_OUT; lia)) as (go & Hgo & BO0).
  destruct (caw_img_byte mem0 fuzz_alloc_ran_out_c.G_RAN_OUT
    ltac:(unfold fuzz_alloc_ran_out_c.G_RAN_OUT; vm_compute; discriminate)
    ltac:(unfold fuzz_alloc_ran_out_c.G_RAN_OUT; lia) ltac:(unfold fuzz_alloc_ran_out_c.G_RAN_OUT; lia)) as (gr & Hgr & BR0).
  (* run 1: entry to the malloc call *)
  eapply (caw_kA fx regs0 _ mem0 md0 _ _ Hh0 Hz0).
  { unfold rmk.
    apply (caw_run1 (getr regs0 1) (getr regs0 2) (getr regs0 3) (getr regs0 4) (getr regs0 5) (getr regs0 6) (getr regs0 7) (getr regs0 8) (getr regs0 9) (getr regs0 10) (getr regs0 11) (getr regs0 12) (getr regs0 13) (getr regs0 14) (getr regs0 15) (getr regs0 16) (getr regs0 17) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24) (getr regs0 25) (getr regs0 26) (getr regs0 27) (getr regs0 28) (getr regs0 29) (getr regs0 30) (getr regs0 31) (@fp_regs fx) (@fp_csr fx) mem0 data (Z.of_nat (length x)) (spZ regs0 - CAW_K));
      [exact R10 | exact R11 | lia | lia | lia | exact Hstk0 | unfold spZ in *; lia]. }
  { intros ms' (m' & j0 & j1 & j2 & E & _). eexists _, _, _. exact E. }
  intros R1 pc1 mem1 regs1 HQ1 HG1.
  destruct HQ1 as (m1 & j0 & j1 & j2 & E1 & MU1 & WM1 & RW1).
  pose proof (f_equal ms_regs E1) as ER. pose proof (f_equal ms_pc_val E1) as EP. pose proof (f_equal ms_mem E1) as EM.
  cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R1 pc1 mem1. clear E1.
  change (bv_unsigned (getr regs0 2)) with (spZ regs0) in MU1, RW1.
  assert (HRA1 : ro_agree rsegs m1).
  { apply (caw_ro_agree_munch [(spZ regs0 - 80, spZ regs0)] mem0 m1); [rewrite <- HS; exact HRA0 | exact MU1 |].
    intros a Ha Ho. destruct (caw_not_outside _ a Ho) as (lo & hi & Hin & Hr). destruct Hin as [E|[]].
    injection E as <- <-. rewrite (caw_img_iff B HS). lia. }
  assert (J1 : J L0 A0 m1 md0).
  { apply (cj_kindA B API HS AX ERU HERR L0 A0 regs0 mem0 md0 PRE0 L0 A0 mem0 md0 m1 _ J0 MU1);
      [rewrite HS; exact WM1 | rewrite HS; exact HRA1 |].
    intros z Hz Ho. destruct (caw_not_outside _ z Ho) as (lo & hi & Hin & Hr). destruct Hin as [E|[]].
    injection E as <- <-. left. lia. }
  assert (G1_1 : getr regs1 1 = Z_to_bv 64 CAW_AFTER_MALLOC) by (rewrite HG1; reflexivity).
  assert (G1_2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 80)) by (rewrite HG1; reflexivity).
  assert (G1_4 : getr regs1 4 = getr regs0 4) by (rewrite HG1; reflexivity).
  assert (G1_8 : getr regs1 8 = Z_to_bv 64 rcv) by (rewrite HG1; exact R12).
  assert (G1_9 : getr regs1 9 = Z_to_bv 64 doc) by (rewrite HG1; exact R13).
  assert (G1_10 : getr regs1 10 = Z_to_bv 64 (Z.of_nat (length x) + 1)) by (rewrite HG1; reflexivity).
  assert (K1 : caw_kr regs0 regs1) by caw_kr_tac HG1.
  assert (Hsp1 : spZ regs1 = spZ regs0 - 80) by (unfold spZ at 1; rewrite G1_2; apply caw_uns; lia).
  pose proof J1 as (HMa & _).
  (* malloc *)
  apply (caw_call_malloc fx L0 A0 regs1 m1 md0 b (Z.of_nat (length x) + 1) _ J1 Hsp1 G1_4);
    [rewrite G1_1; caw_ret_ok | exact G1_10 | exact HRES | exact HROOM |].
  intros L1 A1 regs2 m2 md1 q J2 CP2 R10q FRq BLq INIT1 RES1.
  rewrite G1_1.
  pose proof CP2 as (HM1 & HWF1 & _ & _ & _ & RP2 & _).
  destruct FRq as (Hq0 & Hq1 & Hq2).
  destruct BLq as (b1 & b2 & EB1 & EB0).
  assert (Hn0 : 0 < (Z.of_nat (length x) + 1)) by lia.
  assert (QIN : In (q, (Z.of_nat (length x) + 1)) (blocks L1 A1)) by (rewrite EB1; apply in_or_app; right; left; reflexivity).
  pose proof (caw_new_notin L1 A1 m2 md1 b1 b2 q _ HM1 EB1 Hn0) as QNEW.
  destruct (kb_md B API L1 A1 m2 md1 HM1) as (Hh1 & Hz1).
  pose proof J2 as (_ & _ & _ & _ & _ & _ & _ & HUB2 & _ & _ & _ & _ & HSC2 & HRA2).
  assert (HRA2' : ro_agree rsegs m2) by (rewrite <- HS; exact HRA2).
  assert (G2_2 : getr regs2 2 = Z_to_bv 64 (spZ regs0 - 80)) by (rewrite <- G1_2; apply (RP2 2); unfold callee_saved; lia).
  assert (G2_4 : getr regs2 4 = Z_to_bv 64 STRTOD_TP).
  { rewrite <- HTP, <- HTP0, <- G1_4. apply (RP2 4). unfold callee_saved. lia. }
  assert (G2_8 : getr regs2 8 = Z_to_bv 64 rcv) by (rewrite <- G1_8; apply (RP2 8); unfold callee_saved; lia).
  assert (G2_9 : getr regs2 9 = Z_to_bv 64 doc) by (rewrite <- G1_9; apply (RP2 9); unfold callee_saved; lia).
  assert (K2 : caw_kr regs1 regs2) by (apply caw_kr_pres; exact RP2).
  (* run 2 premises *)
  destruct (caw_r2_rw_app m1 (spZ regs0 - 80) [CB 8 j0; C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (data + Z.of_nat (length x))); C8 (Z_to_bv 64 0); CB 8 j1; CB 8 j2] [C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)] RW1) as [RWa RWb].
  cbn [cells_size csize Nat.add] in RWb. replace (spZ regs0 - 80 + Z.of_nat 48) with (spZ regs0 - 32) in RWb by lia.
  assert (RWa2 : rw_cells rsegs m2 (spZ regs0 - 80) [CB 8 j0; C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (data + Z.of_nat (length x))); C8 (Z_to_bv 64 0); CB 8 j1; CB 8 j2]).
  { apply (caw_rw_cp ALLOC_STACK L0 A0 regs1 m1 md0 (fun _ => False) L1 A1 regs2 m2 md1 _ _ CP2 HMa J2 RWa);
      [rewrite Hsp1; lia | rewrite Hsp1; lia | cbn [cells_size csize Nat.add]; lia | intros a _ []]. }
  assert (RWb2 : rw_cells rsegs m2 (spZ regs0 - 32) [C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)]).
  { apply (caw_rw_cp ALLOC_STACK L0 A0 regs1 m1 md0 (fun _ => False) L1 A1 regs2 m2 md1 _ _ CP2 HMa J2 RWb);
      [rewrite Hsp1; lia | rewrite Hsp1; lia | cbn [cells_size csize Nat.add]; lia | intros a _ []]. }
  assert (P8 : rw_cells rsegs (normalize_cj rsegs m2) (spZ regs0 - 80) [CB 8 j0; C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (data + Z.of_nat (length x))); C8 (Z_to_bv 64 0); CB 8 j1; CB 8 j2]).
  { apply (caw_rw_norm_cj m2 _ _ HRA2' RWa2); [cbn [cells_size csize Nat.add]; unfold TASK_SIZE; lia |].
    intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply caw_keep; lia. }
  assert (P11 : stk rsegs (normalize_cj rsegs m2) (spZ regs0 - CAW_K) (spZ regs0 - 80)).
  { apply caw_stk_norm_cj; [| intros a Ha; apply caw_keep; lia].
    apply (caw_stk_sub m2 (spZ regs0 - CAW_K) (spZ regs0)); [exact (caw_stk_cj L1 A1 m2 md1 J2) | lia | lia | lia]. }
  assert (P14 : bytes_at rsegs (normalize_cj rsegs m2) data x).
  { destruct DG as [E0|(p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & _)].
    - destruct x as [|c x']; [|cbn in E0; lia].
      split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - apply (bytes_at_normalize_cj_low rsegs m2 data x HRA2'); [unfold TASK_SIZE; lia |].
      exact (caw_data L1 A1 m2 md1 data x J2 HDB HDI). }
  assert (P18 : stk rsegs (normalize_cj rsegs m2) q (q + Z.of_nat (length x) + 1)).
  { apply caw_stk_norm_cj.
    - apply caw_stk_present; [lia | lia |]. intros a Ha.
      destruct (caw_block_facts B API AX L1 A1 m2 md1 q _ (a - q) HM1 QIN ltac:(lia)) as (Hp & _).
      replace (q + (a - q)) with a in Hp by lia. exact Hp.
    - intros a Ha. pose proof (Hq2 (a - q) ltac:(lia)) as Hni. replace (q + (a - q)) with a in Hni by lia.
      rewrite (caw_img_iff B HS) in Hni. apply caw_keep; lia. }
  assert (P20 : q + Z.of_nat (length x) + 1 <= STRTOD_IMG_LO \/ STRTOD_GLOBALS_TOP <= q).
  { unfold STRTOD_IMG_LO, STRTOD_GLOBALS_TOP.
    replace (q + Z.of_nat (length x) + 1) with (q + (Z.of_nat (length x) + 1)) by lia.
    exact (caw_fresh_side q _ Hn0 Hq2). }
  destruct (ax_statics AX L1 A1 m2 md1 HM1) as (GW1 & (g & Hg & GW2) & _).
  rewrite HGG, HGD in GW1. rewrite HGD in GW2.
  assert (P29 : rw_cells rsegs (normalize_cj rsegs m2) STRTOD_GOT_GUARD [C8 (Z_to_bv 64 STRTOD_GUARD)]).
  { apply caw_rw_C8; [| unfold STRTOD_GUARD; lia | apply caw_got_stk].
    apply (word_mem_frame (ms_segs B) m2); [exact GW1|]. intros k Hk. apply caw_norm_mbyte; unfold STRTOD_GOT_GUARD; lia. }
  assert (P30 : rw_cells rsegs (normalize_cj rsegs m2) STRTOD_GUARD [C8 (Z_to_bv 64 g)]).
  { apply caw_rw_C8; [| exact Hg | apply caw_guard_stk].
    apply (word_mem_frame (ms_segs B) m2); [exact GW2|]. intros k Hk. apply caw_norm_mbyte; unfold STRTOD_GUARD; lia. }
  destruct (caw_stk_C4 (normalize_cj rsegs m2) STRTOD_ERRNO (caw_errno_stk _)) as (ev & P31).
  assert (P24 : ex_apart (spZ regs0 - 80 + 8) 40 data (Z.of_nat (length x))).
  { unfold ex_apart. destruct DG as [E0|(p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & _)]; lia. }
  assert (P25 : ex_apart (spZ regs0 - 80 + 8) 40 q (Z.of_nat (length x) + 1)) by (unfold ex_apart; lia).
  assert (P26 : ex_apart data (Z.of_nat (length x)) q (Z.of_nat (length x) + 1)).
  { unfold ex_apart. destruct DG as [E0|(p & kk & Hin & Hp1 & Hp2 & _)]; [lia|].
    rewrite EB0 in Hin. destruct (caw_sep_new L1 A1 m2 md1 b1 b2 q _ p kk HM1 EB1 Hin); lia. }
  assert (P27 : ex_apart data (Z.of_nat (length x)) (spZ regs0 - 80 - ex_value_K 0) (ex_value_K 0)).
  { unfold ex_apart. destruct DG as [E0|(p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & _)]; lia. }
  assert (P28 : ex_apart data (Z.of_nat (length x)) STRTOD_ERRNO 4).
  { destruct DG as [E0|(p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & Hni)]; [unfold ex_apart; lia|].
    apply caw_apart_img.
    - intros i Hi. replace (data + i) with (p + (data + i - p)) by lia. apply Hni. lia.
    - intros j Hj. apply (caw_img_iff B HS). unfold STRTOD_ERRNO. lia. }
  assert (P22 : caw_v rcv doc = 0 \/ pj_node rsegs (normalize_cj rsegs m2) (fun a k => In (a, k) D) (caw_v rcv doc) t D /\
     Forall (fun ak => 0 < fst ak) D).
  { unfold caw_v. destruct (Z.eqb_spec rcv 0) as [E0|E0]; [|left; reflexivity].
    destruct (HDOC E0) as (HN & Hd1' & Hd2' & HDin). right. split.
    - exact (caw_doc_norm L1 A1 m2 md1 lblk doc t D J2 HN Hd1' Hd2' HDin).
    - rewrite Forall_forall in HDin |- *. intros [a k] Hak.
      destruct (caw_inside_blk a k (HDin (a, k) Hak)) as (p & kk & _ & Hp1 & _ & Hp3 & _). cbn [fst]. lia. }
  assert (P23 : caw_v rcv doc <> 0 ->
     ex_off (caw_v rcv doc) D (spZ regs0 - 80 + 8) 40 /\ ex_off (caw_v rcv doc) D q (Z.of_nat (length x) + 1) /\
     ex_off (caw_v rcv doc) D (spZ regs0 - 80 - ex_value_K 0) (ex_value_K 0) /\ ex_off (caw_v rcv doc) D STRTOD_ERRNO 4).
  { unfold caw_v. destruct (Z.eqb_spec rcv 0) as [E0|E0]; [|intros H; exfalso; exact (H eq_refl)].
    intros _. destruct (HDOC E0) as (HN & Hd1' & Hd2' & HDin).
    assert (HDB2 : forall a k, In (a, k) D -> exists p kk, In (p, kk) (blocks L0 A0) /\ p <= a /\ a + k <= p + kk /\
       4096 <= p /\ p + kk <= YM05.alloc_ceiling /\ (forall i, 0 <= i < kk -> ~ in_img B (p + i))).
    { intros a k Hak. rewrite Forall_forall in HDin. exact (caw_inside_blk a k (HDin (a, k) Hak)). }
    unfold ex_off. rewrite !Forall_forall.
    split; [split; [unfold ex_apart; lia | intros [a k] Hak; cbn [fst snd];
      destruct (HDB2 a k Hak) as (p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & _); unfold ex_apart; lia]|].
    split; [split; [unfold ex_apart; lia | intros [a k] Hak; cbn [fst snd];
      destruct (HDB2 a k Hak) as (p & kk & Hin & Hp1 & Hp2 & _); rewrite EB0 in Hin;
      destruct (caw_sep_new L1 A1 m2 md1 b1 b2 q _ p kk HM1 EB1 Hin); unfold ex_apart; lia]|].
    split; [split; [unfold ex_apart; lia | intros [a k] Hak; cbn [fst snd];
      destruct (HDB2 a k Hak) as (p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & _); unfold ex_apart; lia]|].
    split; [unfold ex_apart, STRTOD_ERRNO; lia|].
    intros [a k] Hak. cbn [fst snd]. destruct (HDB2 a k Hak) as (p & kk & _ & Hp1 & Hp2 & Hp3 & Hp4 & Hni).
    apply caw_apart_img.
    - intros i Hi. replace (a + i) with (p + (a + i - p)) by lia. apply Hni. lia.
    - intros j Hj. apply (caw_img_iff B HS). unfold STRTOD_ERRNO. lia. }
  (* run 2: after malloc to the free call *)
  eapply (caw_kF fx regs2 _ m2 md1 _ _ Hh1 Hz1 HRA2').
  { unfold rmk.
    apply (caw_run2 EXV (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) (@fp_regs fx) (@fp_csr fx) (normalize_cj rsegs m2) (spZ regs0 - 80) data rcv doc q
      (spZ regs0 - CAW_K) x j0 j1 j2 (fun a k => In (a, k) D) t D (Z_to_bv 64 g) ev).
    - exact G2_2.
    - exact G2_8.
    - exact G2_9.
    - exact R10q.
    - exact G2_4.
    - exact Hrcv.
    - exact Hdoc.
    - exact P8.
    - clear -Hs16. Z.div_mod_to_equations. lia.
    - lia.
    - exact P11.
    - lia.
    - lia.
    - exact P14.
    - exact Hd0.
    - exact Hd1.
    - exact Hlen.
    - exact P18.
    - exact Hq0.
    - exact P20.
    - lia.
    - exact P22.
    - exact P23.
    - exact P24.
    - exact P25.
    - exact P26.
    - exact P27.
    - exact P28.
    - exact P29.
    - exact P30.
    - exact P31.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact HFZ. }
  { intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & _). eexists _, _, _, _, _. exact E. }
  intros R3 Fr3 pc3 fc3 m30 m3 regs3 HQ3 HREL3 HSAME3 HG3.
  destruct HQ3 as (ra' & t0' & t1' & t2' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    F3 & fc3' & m3' & dl & E3 & FK3 & FRM3 & MU3 & WM3 & RW3 & DL3 & MATCH3).
  pose proof (f_equal ms_regs E3) as ER. pose proof (f_equal ms_fregs E3) as EF. pose proof (f_equal ms_pc_val E3) as EP.
  pose proof (f_equal ms_fcsr E3) as EC. pose proof (f_equal ms_mem E3) as EM.
  cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_mem MS] in ER, EF, EP, EC, EM. subst R3 Fr3 pc3 fc3 m30. clear E3.
  pose proof (mem_rel_cj_normalize rsegs m2 HRA2') as HN2.
  pose proof (munch_rel_cj rsegs _ m2 _ m3 m3' HN2 HREL3 HSAME3 MU3) as MU3r.
  pose proof (wmono_rel_cj rsegs m2 _ m3 m3' HN2 HREL3 HSAME3 WM3) as WM3r.
  pose proof (ro_agree_same_cj rsegs m2 m3 HRA2' HSAME3) as HRA3.
  pose proof (caw_rw_rel_cj m3 m3' _ _ HREL3 RW3) as RW3r.
  assert (J3 : J L1 A1 m3 md1).
  { apply (cj_kindA B API HS AX ERU HERR L0 A0 regs0 mem0 md0 PRE0 L1 A1 m2 md1 m3 _ J2 MU3r);
      [rewrite HS; exact WM3r | rewrite HS; exact HRA3 |].
    intros z Hz Ho. destruct (caw_not_outside _ z Ho) as (lo & hi & Hin & Hr).
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
    - left. lia.
    - left. lia.
    - right. right. exists q, (Z.of_nat (length x) + 1). split; [exact QIN|]. split; [rewrite EB0; exact QNEW|]. split; [lia|].
      destruct (caw_block_facts B API AX L1 A1 m2 md1 q _ (z - q) HM1 QIN ltac:(lia)) as ((v & Hv) & _).
      replace (q + (z - q)) with z in Hv by lia.
      pose proof (Hq2 (z - q) ltac:(lia)) as Hni. replace (q + (z - q)) with z in Hni by lia.
      apply (caw_present_of_writable m3 z); [lia | exact Hni |].
      unfold writable_at. rewrite HS. apply WM3r. unfold wview. rewrite Hv. discriminate.
    - right. left. rewrite HERR. lia. }
  assert (G3_1 : getr regs3 1 = ra') by (rewrite HG3; reflexivity).
  assert (G3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs0 - 80)) by (rewrite HG3; reflexivity).
  assert (G3_4 : getr regs3 4 = getr regs2 4) by (rewrite HG3; reflexivity).
  assert (G3_8 : getr regs3 8 = Z_to_bv 64 rcv) by (rewrite HG3; exact G2_8).
  assert (G3_9 : getr regs3 9 = s1') by (rewrite HG3; reflexivity).
  assert (G3_10 : getr regs3 10 = Z_to_bv 64 q) by (rewrite HG3; reflexivity).
  assert (G3_18 : getr regs3 18 = getr regs2 18) by (rewrite HG3; reflexivity).
  assert (K3 : caw_kr regs2 regs3) by caw_kr_tac HG3.
  assert (Hsp3 : spZ regs3 = spZ regs0 - 80) by (unfold spZ at 1; rewrite G3_2; apply caw_uns; lia).
  pose proof J3 as (HM1' & _).
  (* free *)
  destruct (caw_in_blocks L1 A1 q _ QIN) as (p & Hp & Ep).
  assert (HNS : forall q0 k0, In (q0, k0) (user_blocks A0) -> q0 <> p).
  { intros q0 k0 Hin E0. subst q0. destruct (HUB2 p k0 Hin) as (Hin1 & Hpa).
    pose proof (caw_nodup_fst _ p _ _ (YO10.user_block_ptrs_NoDup A1 HWF1) Hin1 Hp) as Ek. subst k0.
    apply QNEW. rewrite <- EB0. rewrite <- Ep, Hpa. apply caw_ub_blocks. exact Hin. }
  assert (RA3 : ra' = Z_to_bv 64 CAW_RET_REFUSE \/ ra' = Z_to_bv 64 CAW_RET_ACCEPT).
  { revert MATCH3. destruct (ex_V 0 (map bv_unsigned x)) as [[u r]|]; intros MATCH3;
      [right; exact (proj1 MATCH3) | left; exact MATCH3]. }
  apply (caw_call_free (mkFP F3 fc3') L1 A1 regs3 m3 md1 (rf_malloc F b (Z.of_nat (length x) + 1)) p (Z.of_nat (length x) + 1) _ J3 Hsp3);
    [rewrite G3_4, G2_4, HTP0, HTP; reflexivity | rewrite G3_1; destruct RA3 as [-> | ->]; caw_ret_ok |
     exact Hp | rewrite Ep; exact G3_10 | exact HNS | exact RES1 | | exact INIT1].
  intros L2 A2 regs4 m4 md2 J4 CP4 BL4 INIT2 RES2.
  rewrite G3_1.
  pose proof CP4 as (HM2 & _ & _ & _ & _ & RP4 & _).
  destruct (kb_md B API L2 A2 m4 md2 HM2) as (Hh2 & Hz2).
  pose proof J4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRA4).
  assert (EBL : blocks L2 A2 = blocks L0 A0).
  { destruct BL4 as (c1 & c2 & EC1 & EC2). rewrite Ep, EB1 in EC1.
    assert (N1 : ~ In (q, (Z.of_nat (length x) + 1)) b1) by (intros H; apply QNEW; apply in_or_app; left; exact H).
    assert (N2 : ~ In (q, (Z.of_nat (length x) + 1)) b2) by (intros H; apply QNEW; apply in_or_app; right; exact H).
    destruct (caw_mid_unique b1 b2 c1 c2 _ EC1 N1 N2) as [<- <-]. rewrite EC2, EB0. reflexivity. }
  assert (G4_2 : getr regs4 2 = Z_to_bv 64 (spZ regs0 - 80)) by (rewrite <- G3_2; apply (RP4 2); unfold callee_saved; lia).
  assert (G4_8 : getr regs4 8 = Z_to_bv 64 rcv) by (rewrite <- G3_8; apply (RP4 8); unfold callee_saved; lia).
  assert (G4_9 : getr regs4 9 = s1') by (rewrite <- G3_9; apply (RP4 9); unfold callee_saved; lia).
  assert (G4_18 : getr regs4 18 = getr regs2 18) by (rewrite <- G3_18; apply (RP4 18); unfold callee_saved; lia).
  assert (K4 : caw_kr regs3 regs4) by (apply caw_kr_pres; exact RP4).
  assert (RWb3 : rw_cells rsegs m3 (spZ regs0 - 32) [C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ RWb2 MU3r WM3r).
    cbn [cells_size csize Nat.add disjoint_from]. repeat split; lia. }
  assert (RWb4 : rw_cells rsegs m4 (spZ regs0 - 32) [C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)]).
  { apply (caw_rw_cp ALLOC_STACK L1 A1 regs3 m3 md1 _ L2 A2 regs4 m4 md2 _ _ CP4 HM1' J4 RWb3);
      [rewrite Hsp3; lia | rewrite Hsp3; lia | cbn [cells_size csize Nat.add]; lia |
       intros a Ha Hq; cbv beta in Hq; rewrite Ep in Hq; lia]. }
  destruct (caw_r2_rw_app m3 (spZ regs0 - 80 + 32) [C8 (Z_to_bv 64 q)] [C4 (Z_to_bv 64 dl)] RW3r) as [_ RWd].
  cbn [cells_size csize Nat.add] in RWd. replace (spZ regs0 - 80 + 32 + Z.of_nat 8) with (spZ regs0 - 40) in RWd by lia.
  assert (RWd4 : rw_cells rsegs m4 (spZ regs0 - 40) [C4 (Z_to_bv 64 dl)]).
  { apply (caw_rw_cp ALLOC_STACK L1 A1 regs3 m3 md1 _ L2 A2 regs4 m4 md2 _ _ CP4 HM1' J4 RWd);
      [rewrite Hsp3; lia | rewrite Hsp3; lia | cbn [cells_size csize Nat.add]; lia |
       intros a Ha Hq; cbv beta in Hq; rewrite Ep in Hq; lia]. }
  assert (BS4 : bytes_at rsegs m4 (spZ regs0 - 80 + 48)
     (le8 (getr regs0 18) ++ le8 (getr regs0 9) ++ le8 (getr regs0 8) ++ le8 (getr regs0 1))).
  { destruct RWb4 as ((_ & Hb) & _). replace (spZ regs0 - 80 + 48) with (spZ regs0 - 32) by lia.
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (BD4 : bytes_at rsegs m4 (spZ regs0 - 80 + 40) (le4 (Z_to_bv 64 dl))).
  { destruct RWd4 as ((_ & Hb) & _). replace (spZ regs0 - 80 + 40) with (spZ regs0 - 40) by lia.
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (BO4 : bytes_at rsegs m4 LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 go)))
    by exact (caw_flag_keep L2 A2 m4 md2 _ _ J4 caw_glob_own BO0 ltac:(rewrite length_le1; reflexivity)).
  assert (BR4 : bytes_at rsegs m4 fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 gr)))
    by exact (caw_flag_keep L2 A2 m4 md2 _ _ J4 caw_glob_ran BR0 ltac:(rewrite length_le1; reflexivity)).
  assert (FL4 : caw_flags m4 go gr) by (split; [exact Hgo|]; split; [exact Hgr|]; split; [exact BO4 | exact BR4]).
  assert (FIN : forall regs5, getr regs5 2 = Z_to_bv 64 (spZ regs0 - 80 + 80) -> getr regs5 8 = getr regs0 8 ->
      getr regs5 9 = getr regs0 9 -> getr regs5 18 = getr regs0 18 -> caw_kr regs4 regs5 ->
      getr regs5 10 = Z_to_bv 64 (caw_rv go gr) ->
      POST (mkCfg (@mkst (mkFP F3 fc3') regs5 (getr regs0 1) m4 (seg_rom (ms_segs B))) md2)).
  { intros regs5 H2 H8 H9 H18 K5 H10. unfold POST. exists (mkFP F3 fc3'), L2, A2, regs5, m4, md2.
    split; [reflexivity|]. split; [exact FRM3|]. split; [apply caw_fk; exact FK3|].
    split.
    { apply (cj_final B API L0 A0 regs0 mem0 md0 L2 A2 m4 md2 regs5 J4).
      apply (caw_pres regs0 regs5); [| exact H8 | exact H9 | exact H18 |].
      - rewrite H2. replace (spZ regs0 - 80 + 80) with (spZ regs0) by lia. unfold spZ. apply caw_bvid.
      - exact (caw_kr_trans _ _ _ K1 (caw_kr_trans _ _ _ K2 (caw_kr_trans _ _ _ K3 (caw_kr_trans _ _ _ K4 K5)))). }
    split; [exact (caw_rd_cells L2 A2 m4 md2 HM2 HRA4)|].
    split; [exact INIT2|]. split; [exact EBL|].
    split; [rewrite HS; exact (caw_data L2 A2 m4 md2 data x J4 HDB HDI)|].
    split; [exact RES2|].
    exists go, gr. split; [exact Hgo|]. split; [exact Hgr|]. rewrite HS.
    split; [exact BO0|]. split; [exact BR0|]. split; [exact BO4|]. split; [exact BR4|].
    rewrite H10. unfold caw_rv.
    destruct (Z.eqb_spec go 0) as [E0|E0]; destruct (Z.eqb_spec gr 0) as [E1|E1]; cbn [andb].
    - left. split; [exact E0|]. split; [exact E1 | reflexivity].
    - right. split; [right; exact E1 | reflexivity].
    - right. split; [left; exact E0 | reflexivity].
    - right. split; [left; exact E0 | reflexivity]. }
  pose proof (caw_agree_V rcv x t HAG) as AGV.
  revert MATCH3 AGV. destruct (ex_V 0 (map bv_unsigned x)) as [[u r]|]; intros MATCH3 AGV.
  - (* accepted value: run 3b *)
    destruct MATCH3 as (Era & Es1 & Edl).
    rewrite Era.
    eapply (caw_kA (mkFP F3 fc3') regs4 _ m4 md2 _ _ Hh2 Hz2).
    { unfold rmk.
      apply (caw_run3b RANC (getr regs4 1) (getr regs4 2) (getr regs4 3) (getr regs4 4) (getr regs4 5) (getr regs4 6) (getr regs4 7) (getr regs4 8) (getr regs4 9) (getr regs4 10) (getr regs4 11) (getr regs4 12) (getr regs4 13) (getr regs4 14) (getr regs4 15) (getr regs4 16) (getr regs4 17) (getr regs4 18) (getr regs4 19) (getr regs4 20) (getr regs4 21) (getr regs4 22) (getr regs4 23) (getr regs4 24) (getr regs4 25) (getr regs4 26) (getr regs4 27) (getr regs4 28) (getr regs4 29) (getr regs4 30) (getr regs4 31) (@fp_regs (mkFP F3 fc3')) (@fp_csr (mkFP F3 fc3')) m4
        (spZ regs0 - 80) rcv dl go gr (caw_pe r) (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18)).
      - exact G4_2.
      - lia.
      - lia.
      - exact G4_8.
      - exact Hrcv.
      - rewrite G4_9. exact Es1.
      - exact (proj1 AGV).
      - exact DL3.
      - intros H0. destruct DL3 as [E|E]; [exact E|]. exfalso. apply (proj1 Edl) in E.
        destruct E as (_ & Htu). exact (Htu (proj2 AGV H0)).
      - exact FL4.
      - exact BD4.
      - exact BS4. }
    { intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E). eexists _, _, _. exact E. }
    intros R5 pc5 mem5 regs5 HQ5 HG5.
    destruct HQ5 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E5).
    pose proof (f_equal ms_regs E5) as ER5. pose proof (f_equal ms_pc_val E5) as EP5. pose proof (f_equal ms_mem E5) as EM5.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER5, EP5, EM5. subst R5 pc5 mem5. clear E5.
    rewrite (caw_ret_pc (getr regs0 1) Hra0). apply SR_ret.
    apply FIN; [rewrite HG5; reflexivity | rewrite HG5; reflexivity | rewrite HG5; reflexivity |
                rewrite HG5; reflexivity | caw_kr_tac HG5 | rewrite HG5; reflexivity].
  - (* refused text: run 3a *)
    rewrite MATCH3.
    eapply (caw_kA (mkFP F3 fc3') regs4 _ m4 md2 _ _ Hh2 Hz2).
    { unfold rmk.
      apply (caw_run3a RANC (getr regs4 1) (getr regs4 2) (getr regs4 3) (getr regs4 4) (getr regs4 5) (getr regs4 6) (getr regs4 7) (getr regs4 8) (getr regs4 9) (getr regs4 10) (getr regs4 11) (getr regs4 12) (getr regs4 13) (getr regs4 14) (getr regs4 15) (getr regs4 16) (getr regs4 17) (getr regs4 18) (getr regs4 19) (getr regs4 20) (getr regs4 21) (getr regs4 22) (getr regs4 23) (getr regs4 24) (getr regs4 25) (getr regs4 26) (getr regs4 27) (getr regs4 28) (getr regs4 29) (getr regs4 30) (getr regs4 31) (@fp_regs (mkFP F3 fc3')) (@fp_csr (mkFP F3 fc3')) m4
        (spZ regs0 - 80) rcv go gr (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18)).
      - exact G4_2.
      - lia.
      - lia.
      - exact G4_8.
      - exact Hrcv.
      - exact AGV.
      - exact FL4.
      - exact BS4. }
    { intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E). eexists _, _, _. exact E. }
    intros R5 pc5 mem5 regs5 HQ5 HG5.
    destruct HQ5 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E5).
    pose proof (f_equal ms_regs E5) as ER5. pose proof (f_equal ms_pc_val E5) as EP5. pose proof (f_equal ms_mem E5) as EM5.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER5, EP5, EM5. subst R5 pc5 mem5. clear E5.
    rewrite (caw_ret_pc (getr regs0 1) Hra0). apply SR_ret.
    apply FIN; [rewrite HG5; reflexivity | rewrite HG5; reflexivity | rewrite HG5; reflexivity |
                rewrite HG5; reflexivity | caw_kr_tac HG5 | rewrite HG5; reflexivity].
Qed.

End K.
