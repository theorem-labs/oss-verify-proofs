(* Batch b2 helpers of the fuzz_ctrl LLVMFuzzerTestOneInput slot proof (plain) for the machine side of segments
   R09-R18: memory slices, register keeps, the round-trip bundles across a call. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcFrag RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- Byte slices ---- *)

Lemma b2_at_slice : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H1 & H2 & H3) Hk.
  assert (L : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n) as [_|]; [|lia].
  rewrite nth_error_skipn. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H3. lia.
Qed.

Lemma b2_fr50_eq : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma b2_fr50_at : forall m a bs, bytes_at rsegs m a bs -> (50 <= length bs)%nat -> bytes_at rsegs m a (fr50 bs).
Proof.
  intros m a bs H L. rewrite (b2_fr50_eq bs L).
  pose proof (b2_at_slice m a bs 0 50 H ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma b2_bsl_at : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (bsl bs k n).
Proof.
  intros m a bs k n H Hk Hn L. unfold bsl.
  pose proof (b2_at_slice m a bs (Z.to_nat k) (Z.to_nat n) H ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma b2_bsl_len : forall bs k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  length (bsl bs k n) = Z.to_nat n.
Proof. intros bs k n Hk Hn L. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

(* A stack slot holding known bytes is a writable cell of them. *)
Lemma b2_rw_at : forall m lo hi a bs, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  bytes_at rsegs m a bs -> rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m lo hi a bs ST H1 H2 HB.
  destruct (sl_rw_of_stk m lo hi a (length bs) ST H1 H2) as (junk & _ & HW).
  split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - exact HW.
Qed.

Lemma b2_stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' ->
  stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H) E1 E2 E3. split; [exact E3|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma b2_mod : forall s k d, s mod 16 = 0 -> 0 < d -> 16 mod d = 0 -> k mod d = 0 -> (s + k) mod d = 0.
Proof.
  intros s k d Hs Hd H16 Hk.
  apply (proj2 (Z.mod_divide (s + k) d ltac:(lia))). apply Z.divide_add_r.
  - apply (Z.divide_trans d 16 s).
    + apply (proj1 (Z.mod_divide 16 d ltac:(lia))). exact H16.
    + apply (proj1 (Z.mod_divide s 16 ltac:(lia))). exact Hs.
  - apply (proj1 (Z.mod_divide k d ltac:(lia))). exact Hk.
Qed.

(* ---- The reply's result on a frame with IR ---- *)

Lemma b2_reply_ok : forall fr len pa pp pn g, fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ir len g = true ->
  reply_ok fr len pa pp pn g = true /\ reply_ret fr len pa pp pn g = 1.
Proof.
  intros fr len pa pp pn g H1 H2 H3 H4 Hir. unfold reply_ok, reply_ret, reply_args.
  rewrite (proj2 (Z.eqb_neq fr 0) H1), (proj2 (Z.eqb_neq pa 0) H2), (proj2 (Z.eqb_neq pp 0) H3),
    (proj2 (Z.eqb_neq pn 0) H4), Hir.
  split; reflexivity.
Qed.

(* ---- Registers and the round-trip bundles across a run ---- *)

Definition b2_kr (regs' regs : bvmap 5 word) : Prop :=
  b1_kr regs' regs /\ YK11.getr regs' 20 = YK11.getr regs 20 /\ YK11.getr regs' 22 = YK11.getr regs 22.

(* RB with the id and frag the run leaves (each shown by the caller), OUR kept. *)
Lemma b2_RB_new : forall g b idb fgb idb' fgb' regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  Frame.disjoint_from W (spk g 76) 6 -> b1_kr regs' regs -> RB g b idb fgb regs mem ->
  IDB g m' idb' -> FGB g m' fgb' -> RB g b idb' fgb' regs' m'.
Proof.
  intros g b idb fgb idb' fgb' regs regs' mem m0 m' W Hro MU Hrel HD
    (E8 & E9 & E18 & E19 & E21 & E23 & E24 & E25 & E26 & E27)
    (Hb & (Hc & H21 & H27) & HO & (H8 & H18 & H19 & H23 & H24 & H25 & H26) & H9 & _ & _) HI HF.
  unfold RB, CUR, RT, rg, OURb in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite E21; exact H21 | rewrite E27; exact H27]|].
  split.
  { apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HO]. rewrite OUR_length. exact HD. }
  split; [rewrite E8, E18, E19, E23, E24, E25, E26; auto 8|].
  split; [rewrite E9; exact H9|].
  split; [exact HI | exact HF].
Qed.

(* RFx across a run that writes neither [sp+76, sp+192) nor the block. *)
Lemma b2_RFx_keep : forall g b idb fgb phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat -> Frame.disjoint_from W (spk g 76) 116 ->
  Frame.disjoint_from W phi (rnb g b) -> b2_kr regs' regs ->
  RFx g b idb fgb phi regs mem -> RFx g b idb fgb phi regs' m'.
Proof.
  intros g b idb fgb phi regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD HDp (KR & E20 & E22)
    ((HRB & Hnz & H20 & HF) & H22).
  destruct (b1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HB & HL).
  unfold RFx, RFb, rg in *. rewrite E20, E22.
  split; [split; [|split; [exact Hnz|]; split; [exact H20|]]|exact H22].
  - exact (b1_RB_keep g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD KR HRB).
  - apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
    unfold rFb, rnb in *. rewrite HL, Z2Nat.id by lia. exact HDp.
Qed.

(* RFx with the id and frag the run leaves (each shown by the caller), OUR, the block and the registers kept. *)
Lemma b2_RFx_new : forall g b idb fgb idb' fgb' phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  Frame.disjoint_from W (spk g 76) 6 -> Frame.disjoint_from W phi (rnb g b) -> b2_kr regs' regs ->
  RFx g b idb fgb phi regs mem -> IDB g m' idb' -> FGB g m' fgb' -> RFx g b idb' fgb' phi regs' m'.
Proof.
  intros g b idb fgb idb' fgb' phi regs regs' mem m0 m' W Hro MU Hrel HD HDp (KR & E20 & E22)
    ((HRB & Hnz & H20 & HF) & H22) HI HG.
  destruct (b1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HB & HL).
  unfold RFx, RFb, rg in *. rewrite E20, E22.
  split; [split; [|split; [exact Hnz|]; split; [exact H20|]]|exact H22].
  - exact (b2_RB_new g b idb fgb idb' fgb' regs regs' mem m0 m' W Hro MU Hrel HD KR HRB HI HG).
  - apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
    unfold rFb, rnb in *. rewrite HL, Z2Nat.id by lia. exact HDp.
Qed.

(* ---- Loads ---- *)

Lemma b2_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  rewrite Z.add_0_r, skipn_O, firstn_all in E. exact E.
Qed.

Lemma b2_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma b2_reply_addr : forall g, reply_addr g = le2 (Z_to_bv 64 (r_addr g)).
Proof. intros g. unfold reply_addr, r_addr. symmetry. apply RcParseLib.rc_le2_pair. Qed.

Lemma b2_r_addr_rng : forall g, 0 <= r_addr g < 65536.
Proof.
  intros g. unfold r_addr. pose proof (cp_v_range' g 36). pose proof (cp_v_range' g 37). lia.
Qed.

Lemma b2_wr_of_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) E1 E2 E3. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(* ---- The fragment call (sp+82, Φ, n, sp+1824, sp+1688, sp+40) of R11 and R18 ---- *)

Lemma b2_fg_class : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  fg_class f fr pa pp pn len st g = fcls len st g.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. unfold fcls, fg_class.
  rewrite (proj2 (Z.eqb_neq f 0) H1), (proj2 (Z.eqb_neq fr 0) H2), (proj2 (Z.eqb_neq pa 0) H3),
    (proj2 (Z.eqb_neq pp 0) H4), (proj2 (Z.eqb_neq pn 0) H5). reflexivity.
Qed.

Lemma b2_frag_call : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n : Z) (st g : list byte) (c : fg_case),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (spv + 82) -> a1 = Z_to_bv 64 phi -> a2 = Z_to_bv 64 n ->
    a3 = Z_to_bv 64 (spv + 1824) -> a4 = Z_to_bv 64 (spv + 1688) -> a5 = Z_to_bv 64 (spv + 40) ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 80 -> 50 <= n < 2 ^ 64 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m -> length g = 50%nat -> length st = 72%nat ->
    bytes_at rsegs m phi g -> rw_cells rsegs m (spv + 82) [CB 72 st] ->
    wr_at rsegs m (spv + 1824) 2 -> wr_at rsegs m (spv + 1688) 8 -> wr_at rsegs m (spv + 40) 8 ->
    fcls n st g = c ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret c))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp 80 (spv + 82) (spv + 1824) (spv + 1688) (spv + 40) spv c) m m' /\ wmono rsegs m m' /\
         fg_mem (spv + 82) (spv + 1824) (spv + 1688) (spv + 40) st g c m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n st g c -> -> -> -> -> -> -> Hsp0 Hsp H16 Hph0 Hph Hn ST MI Lg Ls HG HF WA WP WN Hc.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply unsigned_lit; lia).
  pose proof (b2_fg_class (spv + 82) phi (spv + 1824) (spv + 1688) (spv + 40) n st g ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia)) as EC.
  eapply evt_mono.
  { eapply (FRAG ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 _ _ _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m (spv + 82) phi n (spv + 1824) (spv + 1688) (spv + 40) st g).
    all: rewrite ?Hspu; unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME.
    all: first [ reflexivity | exact ST | exact Lg | exact Ls | exact MI
               | intros _ _ _ _ _ _; exact HG
               | intros _ _ _ _ _;
                 split; [exact HF|];
                 split; [apply b2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
                 split; [apply b2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
                 split; [apply b2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
                 split; [exact WA|]; split; [exact WP|]; split; [exact WN|];
                 cbn [all_dj dj_from]; repeat split; lia
               | lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _ & _ & HM).
  rewrite Hspu, EC, Hc in *.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM | exact HM].
Qed.

(* ---- CONFIG (b = 0): RFb across a run, the image row, ports_ok, bcmp ---- *)

Lemma b2_RFb_keep : forall g b idb fgb phi regs regs' mem m0 m' W,
  ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  length idb = 38%nat -> length fgb = 72%nat -> Frame.disjoint_from W (spk g 76) 116 ->
  Frame.disjoint_from W phi (rnb g b) -> b1_kr regs' regs -> YK11.getr regs' 20 = YK11.getr regs 20 ->
  RFb g b idb fgb phi regs mem -> RFb g b idb fgb phi regs' m'.
Proof.
  intros g b idb fgb phi regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD HDp KR E20 (HRB & Hnz & H20 & HF).
  destruct (b1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HB & HL).
  unfold RFb, rg in *. rewrite E20.
  split; [exact (b1_RB_keep g b idb fgb regs regs' mem m0 m' W Hro MU Hrel L1 L2 HD KR HRB)|].
  split; [exact Hnz|]. split; [exact H20|].
  apply (b1_keep W mem m0 m' _ _ Hro MU Hrel); [|exact HF].
  unfold rFb, rnb in *. rewrite HL, Z2Nat.id by lia. exact HDp.
Qed.

Lemma b2_ro_norm : forall m, ro_agree rsegs (normalize rsegs m).
Proof. intros m a Ha. unfold Mem.mrd, normalize. rewrite Ha. reflexivity. Qed.

Lemma b2_memcmp_refl : forall l n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|a l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma b2_neqb_refl : forall x : word, negb (bv_eqb x x) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma b2_eqb0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma b2_mrow_rng : forall inp, CAT <= mrow inp <= CAT + CAT_ROW * 10 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. pose proof (b2_istar_range inp) as H. unfold mrow, CAT, CAT_ROW in *. split; [lia|].
  replace (126256 + 296 * istar inp) with ((15782 + 37 * istar inp) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma b2_row_io : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 16 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_ic (rowb i))) /\
  firstn 4 (skipn 20 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_oc (rowb i))) /\
  -2 ^ 31 <= RcDecl.box_ic (rowb i) < 2 ^ 31 /\ -2 ^ 31 <= RcDecl.box_oc (rowb i) < 2 ^ 31.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute;
    (split; [reflexivity|]); (split; [reflexivity|]); split; split; first [reflexivity | intro H; discriminate H].
Qed.

Lemma b2_ports_ok : forall p q bs, p <> 0 -> q <> 0 -> RcLeaf.decl bs = true -> RcLeaf.ports_ok p q bs = true.
Proof.
  intros p q bs Hp Hq Hd. unfold RcLeaf.ports_ok.
  rewrite (proj2 (Z.eqb_neq p 0) Hp), (proj2 (Z.eqb_neq q 0) Hq), Hd. reflexivity.
Qed.

(* ---- The block sum loops (bytes 18 .. 49 of the frame) ---- *)

Lemma b2_psum_S : forall bs i,
  RcModel.psum bs (S i) = RcModel.psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

Lemma b2_psum_rng : forall bs i, 0 <= RcModel.psum bs i <= 255 * Z.of_nat i.
Proof.
  intros bs i. induction i as [|i IH]; cbn [RcModel.psum]; [lia|].
  pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma b2_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as H.
  unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma b2_bv_eqb_u : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma b2_first1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma b2_rd_blk : forall m phi F j, bytes_at rsegs m phi F -> (50 <= length F)%nat -> (j < 32)%nat ->
  ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j (skipn 18 (fr50 F)) (Z_to_bv 8 0)].
Proof.
  intros m phi F j HB HL Hj. rewrite <- Z.add_assoc.
  rewrite (bytes_at_read rsegs m phi F (18 + Z.of_nat j) 1 HB) by lia.
  replace (Z.to_nat (18 + Z.of_nat j)) with (18 + j)%nat by lia.
  rewrite (b2_first1 F (18 + j) (Z_to_bv 8 0)) by lia.
  rewrite nth_skipn. rewrite (b2_fr50_eq F HL). rewrite nth_firstn.
  destruct (Nat.ltb_spec (18 + j) 50); [reflexivity | lia].
Qed.

(* Stack addresses lie above every image segment. *)
Lemma b2_rom_none : forall a, SL_TOP <= a < 2 ^ 64 -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha. destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:Ef.
  - apply sl_find_top in Ef. unfold SL_TOP in *. rewrite wa_unsigned in Ef by lia. lia.
  - exact (seg_rom_unmapped rsegs (wa a) Ef).
Qed.

Section B2R.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The RELRO bytes (the catalogue among them) read through the normalized memory are the image's. *)
Lemma b2_relro_mrd : forall mem a, relro B mem -> 0x1ed20 <= a < 0x1fb80 ->
  Mem.mrd rsegs (normalize rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof.
  intros mem a HR Ha. unfold relro, G_img_c in HR.
  pose proof (HR a (b1_in_relro a Ha)) as E. rewrite (sl_segs B APIf ra empty FF) in E.
  unfold Mem.mrd, normalize. destruct (Mem.ro_addr rsegs (wa a)); [reflexivity|].
  unfold mbyte in E. unfold wa. exact E.
Qed.

End B2R.
