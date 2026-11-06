From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strlen_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition rp_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fd : word) (Q : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x17b28) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 Q) fd
                  fd (Z_to_bv 64 Q) (Z_to_bv 64 (Z.of_nat (length str) + 1)) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x173a8) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [CB 8 junk; C8 s1; C8 s0; C8 ra]
    /\ bytes_at rsegs m' Q (str ++ Z_to_bv 8 0 :: slack).

Lemma rp_run1 : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Q lo : Z) (str slack : list byte),
  bytes_at rsegs m Q (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  (Z.of_nat (length str) <= 4096)%Z ->
  ((- (Q + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z ->
  (Q + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= Q)%Z ->
  mem_inv rsegs m ->
  evt rsegs (rp_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 Q str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 Q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17af8) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q lo str slack BS NONUL LMX PAD ST LO DISJ MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB, DISJ. cbn [length] in SB, DISJ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (US : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  1-4: rewrite ?US; first [eassumption | lia].
  cbv delta [mkR].
  do 4 step.
  assert (A2 : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length str))) + 1))
               = Z_to_bv 64 (Z.of_nat (length str) + 1)).
  { rewrite unsigned_lit by lia. change (bv_swrap 32 ?z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z.
    rewrite Z.mod_small by lia. f_equal. lia. }
  rewrite A2. replace (bv_unsigned sp + -32)%Z with (bv_unsigned sp - 32)%Z by lia.
  apply evt_done. unfold rp_mid.
  do 14 eexists. split; [reflexivity|].
  do 4 (split; [eassumption|]). eassumption.
Qed.

Lemma rp_run2 :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 : word) (junk : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 junk; C8 s01; C8 s00; C8 ra0] ->
  (32 <= bv_unsigned sp0)%Z ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 s0 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x188cc) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b28) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 junk FR SPR.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YN03 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import snprintf_c socket_send_c reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsB.
Local Open Scope Z_scope.

Lemma pairwise_In2 : forall {X} (Rl : X -> X -> Prop) l x y,
  pairwise Rl l -> In x l -> In y l -> x <> y -> Rl x y \/ Rl y x.
Proof.
  intros X Rl l x y HP Hx Hy Hne. destruct (in_split x l Hx) as (l1 & l2 & ->).
  apply (pairwise_app_mid' Rl l1 x l2 y HP). apply in_app_or in Hy. apply in_or_app.
  destruct Hy as [Hy|[Hy|Hy]]; [left; exact Hy | congruence | right; exact Hy].
Qed.

Lemma same_start : forall l a k k', pairwise ranges_disjoint l -> In (a, k) l -> In (a, k') l ->
  0 < k -> 0 < k' -> k = k'.
Proof.
  intros l a k k' HP H1 H2 P1 P2. destruct (Z.eq_dec k k') as [E|E]; [exact E|].
  destruct (pairwise_In2 _ l (a, k) (a, k') HP H1 H2 ltac:(congruence)) as [D|D];
    unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma mid_not_side : forall b1 x b2, pairwise ranges_disjoint (b1 ++ x :: b2) -> 0 < snd x -> ~ In x (b1 ++ b2).
Proof.
  intros b1 x b2 HP Hx Hin. destruct (pairwise_app_mid' _ b1 x b2 x HP Hin) as [D|D];
    unfold ranges_disjoint in D; lia.
Qed.

Lemma le_at_bytes : forall (B : malloc_syms) m a bs, VerbsB.le_at B m a bs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at (ms_segs B) m a bs.
Proof.
  unfold VerbsB.le_at, blk_data. intros B m a bs H Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. exact E.
Qed.

Lemma bytes_le_at : forall (B : malloc_syms) m a bs, bytes_at (ms_segs B) m a bs -> VerbsB.le_at B m a bs.
Proof.
  unfold VerbsB.le_at, blk_data. intros B m a bs H i Hi. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  apply (mbyte_of_bytes_at _ _ _ _ _ H). lia.
Qed.

Lemma present_bytes : forall segs m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> present m (a + i)) -> exists bs, length bs = k /\ bytes_at segs m a bs.
Proof.
  intros segs m a k Ha Hk H. destruct (present_rw_cells segs m a k Ha Hk H) as [junk [[Hwf Hb] _]].
  exists junk. cbn in Hwf. split; [tauto|]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma room_sb : forall b n', room_slots (VerbsB.sb_n b 1) 8194 -> 0 <= n' <= 8194 -> room_slots (sb_malloc b n') n'.
Proof.
  intros b n' R Hn. apply (room_slots_mono (sb_malloc b n') (VerbsB.sb_n b 1) n' 8194); [|lia|exact R].
  unfold sb_le, sb_malloc, VerbsB.sb_n, VerbsB.SB_REQ. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

Lemma res_sb : forall s b n k, 0 <= k -> n <= 8194 -> sb_live b + 2 <= sb_cap b ->
  res_ok_slots s (sb_free (sb_malloc b n) k) -> res_ok_slots s (VerbsB.sb_n b 1).
Proof.
  intros s b n k Hk Hn Hc H. apply (res_ok_slots_le s (sb_free (sb_malloc b n) k)); [| |exact H];
    unfold sb_le, sb_free, sb_malloc, VerbsB.sb_n, VerbsB.SB_REQ; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Lemma call_at_blk : forall segs bl mem a c P pn, call_at segs bl mem a c P -> In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
  intros segs bl mem a c P pn (Hfn & Hn & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Hk1].
  assert (Hkl : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Hk1; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Hk1) as (_ & _ & Hb & Hsz & _). split; [exact Hb | lia].
Qed.

Lemma rec_rep_O : forall segs gr sc L A mem R O, rec_rep segs gr sc L A mem R O ->
  forall pn, In pn O -> In pn (blocks L A) /\ 1 <= snd pn.
Proof.
  intros segs gr sc L A mem R O (Q & HR & HO) pn Hpn. apply HO in Hpn.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hpn. apply in_app_or in Hpn as [Hpn|Hpn].
  - apply in_concat in Hpn as (P & HP1 & HP2).
    destruct (In_nth_error _ _ HP1) as [i Hi].
    assert (Hil : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (C4 i c P Ec Hi) as [Hc _]. exact (call_at_blk _ _ _ _ _ _ _ Hc HP2).
  - apply in_app_or in Hpn as [Hpn|Hpn]; [exact (call_at_blk _ _ _ _ _ _ _ C5 Hpn)|].
    apply in_app_or in Hpn as [Hpn|Hpn].
    + unfold answer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn'|]; cbn [oblk In] in Hpn;
        try contradiction.
      destruct Hpn as [<-|[]]. destruct HA as (_ & _ & Hin & Hsz & _). split; [exact Hin | lia].
    + unfold reply_at in HP. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [pn'|]; cbn [oblk In] in Hpn;
        try contradiction.
      destruct Hpn as [<-|[]]. destruct HP as (_ & _ & _ & Hne & Hin & Hsz & _). split; [exact Hin|].
      destruct x as [|x0 x]; [contradiction|]. cbn [length] in Hsz. lia.
Qed.

Lemma wr_static : forall m a, (0x22a68 <= a < 0x22a70 \/ 0x54450 <= a < 0x54458) -> writable_at rsegs m a.
Proof.
  intros m a Ha. unfold writable_at, wview. destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  assert (C : a = 0x22a68 \/ a = 0x22a69 \/ a = 0x22a6a \/ a = 0x22a6b \/ a = 0x22a6c \/ a = 0x22a6d \/
              a = 0x22a6e \/ a = 0x22a6f \/ a = 0x54450 \/ a = 0x54451 \/ a = 0x54452 \/ a = 0x54453 \/
              a = 0x54454 \/ a = 0x54455 \/ a = 0x54456 \/ a = 0x54457) by lia.
  repeat (destruct C as [C|C]; [subst a; intro H; vm_compute in H; discriminate H|]).
  subst a; intro H; vm_compute in H; discriminate H.
Qed.

Lemma f18_of_le : forall m (can : word),
  (forall i, 0 <= i < 8 -> mbyte rsegs m (0x22a68 + i) = nth_error (le8 (Z_to_bv 64 0x54450)) (Z.to_nat i)) ->
  (forall i, 0 <= i < 8 -> mbyte rsegs m (0x54450 + i) = nth_error (le8 can) (Z.to_nat i)) ->
  f18_words rsegs m.
Proof.
  intros m can H1 H2. unfold f18_words, GOT_GUARD, GUARD. split; [|exists can];
    (split; [split; [cbn; tauto|] | split; [lia|]; split; [cbn; lia|]; intros i Hi; apply wr_static; cbn in Hi; lia]);
    cbn [cells_bytes cbytes]; rewrite app_nil_r; (split; [lia|]); rewrite length_le8; (split; [lia|]);
    intros i Hi; [pose proof (H1 (Z.of_nat i) ltac:(lia)) as E | pose proof (H2 (Z.of_nat i) ltac:(lia)) as E];
    rewrite Nat2Z.id in E; exact E.
Qed.

Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma word_le_at : forall (B : malloc_syms) m a v, word_mem (ms_segs B) m a v -> 0 <= v < 2 ^ 64 ->
  VerbsB.le_at B m a (le8 (Z_to_bv 64 v)).
Proof.
  unfold VerbsB.le_at, blk_data. intros B m a v Hw Hv i Hi. rewrite length_le8 in Hi.
  unfold le8, word_to_le_bytes. rewrite nth_le_bytes by lia. rewrite unsigned_lit by lia.
  rewrite <- le_byte_bv by exact Hv.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. exact (Hw (Z.to_nat i) ltac:(lia)).
Qed.

Lemma with_vmmaps_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 [] ; reflexivity. Qed.

Definition zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x188cc.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GUARDV : ms_guard B = 0x54450.
Hypothesis GFRAME : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BSP : block_slack_present B API.
Hypothesis CTXO : ctx_owned B API.
Hypothesis SLEN : strlen_contract.
Hypothesis SSEND : socket_send_contract B API.
Hypothesis FREE : free_contract B API.

Lemma rec_area_G : forall a, rec_area a -> in_globals frame_G a.
Proof using.
  intros a Ha. exists 0x33d10, 1020. split; [left; reflexivity|].
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia.
Qed.

Lemma not_owned_mid : forall L A mem md L1 A1 mem1 md1 a, aa_MR API L A mem md -> aa_MR API L1 A1 mem1 md1 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L1 A1 a.
Proof using AX CTXO.
  intros L A mem md L1 A1 mem1 md1 a HM HM1 Ha NO HO. pose proof (aa_laws API) as LAWS.
  destruct Ha as [Ha|Ha].
  - destruct (owned_low B _ LAWS _ _ _ _ _ HM1 HO). lia.
  - destruct HO as [HO|HO].
    + apply NO. apply (CTXO L A mem md a HM). exact (ax_img AX L1 A1 mem1 md1 a HM1 Ha HO).
    + apply NO. right. exact HO.
Qed.

Theorem reply_holds : reply_contract B API.
Proof using SEGS FREE_PC ERRNO_LOW GOTG GUARDV GFRAME GOWN AX BSP CTXO SLEN SSEND FREE.
  unfold reply_contract, REPLY, RP_K, RP_MALLOCS, RP_REQ.
  intros L A regs mem md b R O q nq X can PRE RA A1R INQ NOQ HX NZX LXN LX4 GR NREP SSP RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  destruct PRE as ((HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX) & HTS).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (Nat2Z.is_nonneg (length X)) as L0.
  set (l := Z.of_nat (length X)) in *.
  destruct (proj1 (in_map_iff _ _ _) INQ) as ([qs nq'] & Eq & Hqs). cbn [fst snd] in Eq. injection Eq as EQ1 EQ2. subst nq'.
  pose proof (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR INQ ltac:(lia)) as (_ & Q4 & QC & _).
  pose proof (mr_blocks_aligned B _ LAWS L A mem md qs nq HMR Hqs) as QAL. rewrite EQ1 in QAL.
  assert (QO : ~ In q (map fst O)).
  { intros Hin. apply in_map_iff in Hin as ([q' k'] & Eq' & Hin). cbn in Eq'. subst q'.
    destruct (rec_rep_O _ _ _ _ _ _ _ _ GR (q, k') Hin) as [Hb Hk]. cbn in Hk.
    pose proof (same_start _ q k' nq (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR) Hb INQ ltac:(lia) ltac:(lia)) as E.
    subst k'. exact (NOQ Hin). }
  set (pad := (- (q + l + 1)) mod 8).
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADE : (q + l + 1 + pad) mod 8 = 0) by (unfold pad; rewrite Z.add_mod, Z.mod_mod, <- Z.add_mod by lia;
    replace (q + l + 1 + - (q + l + 1)) with 0 by ring; reflexivity).
  destruct (present_bytes rsegs mem (q + l + 1) (Z.to_nat pad)) as (slack & SLL & SLB); [lia | lia | |].
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (Z_lt_ge_dec (q + l + 1 + i) (q + nq)) as [D|D].
    - destruct (block_facts B _ LAWS _ _ _ _ _ _ (l + 1 + i) HMR INQ ltac:(lia)) as (P & _).
      replace (q + l + 1 + i) with (q + (l + 1 + i)) by ring. exact P.
    - apply (BSP L A mem md q nq (q + l + 1 + i) HMR INQ). split; [lia|].
      pose proof (Z.mod_pos_bound (q + nq + 7) 8 ltac:(lia)).
      pose proof (Z.div_mod (q + nq + 7) 8 ltac:(lia)).
      pose proof (Z.div_mod (q + l + 1 + pad) 8 ltac:(lia)). lia. }
  assert (SLZ : Z.of_nat (length slack) = pad) by (rewrite SLL; lia).
  clear SLL.
  assert (HXB : bytes_at rsegs mem q (X ++ [Z_to_bv 8 0])).
  { rewrite <- SEGS. apply le_at_bytes; [exact HX | lia | rewrite length_app; cbn [length]; lia]. }
  assert (BSX : bytes_at rsegs mem q (X ++ Z_to_bv 8 0 :: slack)).
  { replace (X ++ Z_to_bv 8 0 :: slack) with ((X ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact HXB|]. rewrite length_app. cbn [length].
    replace (q + Z.of_nat (length X + 1)) with (q + l + 1) by lia. exact SLB. }
  assert (NZ0 : ~ In (Z_to_bv 8 0) X).
  { intros Hin. rewrite Forall_forall in NZX. apply (NZX _ Hin). reflexivity. }
  assert (LALL : Z.of_nat (length (X ++ Z_to_bv 8 0 :: slack)) = l + 1 + pad)
    by (rewrite length_app; cbn [length]; lia).
  rewrite SEGS in RA, HWS, HERR.
  pose proof (bytes_at_normalize rsegs mem q _ RA BSX) as BSN.
  assert (ST : stk rsegs (normalize rsegs mem) (bv_unsigned sp - 8448) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 q) by exact A1R. rewrite R11.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (rp_run1 SLEN) with (lo := bv_unsigned sp - 8448);
      [exact BSN | exact NZ0 | lia | rewrite SLZ; unfold pad; lia | exact ST | lia | rewrite LALL; lia
      | apply mem_inv_normalize]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1').
  destruct Q1 as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & junk
    & -> & MU1n & WM1n & MI1n & FR1n & BS1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1'. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1'. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r FR1n) as FR1.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR1r) BS1n) as BS1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1' eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17b28) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_12 : getr R1 12 = Z_to_bv 64 (l + 1))
    by (rewrite (getr_of_eqv _ _ 12 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp) ->
            Frame.outside [(bv_unsigned sp - 32, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  rewrite <- SEGS in WM1.
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (GR1m : g_rec_rep (ms_segs B) L A m1 R O).
  { unfold g_rec_rep in *. apply (rec_rep_frame (ms_segs B) G_REC REC_SC L A mem R O L A m1 GR).
    - intros a Ha. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha.
      split; [eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia]|].
      intros W. apply (munch_writable _ _ _ _ a MU1 ltac:(lia) ltac:(apply OUT1; lia)). exact W.
    - intros p n i Hin Hi. destruct (rec_rep_O _ _ _ _ _ _ _ _ GR (p, n) Hin) as [Hb _].
      destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hb Hi) as (_ & Hp4 & Hpc & _).
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros pn Hin. exact (proj1 (rec_rep_O _ _ _ _ _ _ _ _ GR pn Hin)). }
  destruct SSP as [S1 S2]. unfold VerbsB.le_at, blk_data, VerbsB.SSP_GOT_B, VerbsB.SSP_GUARD_B in S1, S2.
  rewrite SEGS in S1, S2.
  assert (F18m : f18_words rsegs m1).
  { apply (f18_of_le m1 can).
    - intros i Hi. rewrite (munch_mbyte rsegs _ _ _ (0x22a68 + i) MU1 ltac:(lia) ltac:(apply OUT1; lia)).
      apply S1. rewrite length_le8. lia.
    - intros i Hi. rewrite (munch_mbyte rsegs _ _ _ (0x54450 + i) MU1 ltac:(lia) ltac:(apply OUT1; lia)).
      apply S2. rewrite length_le8. lia. }
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (SSEND L A R1 m1 md q (l + 1) (X ++ [Z_to_bv 8 0]) R O b).
    - split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP1; replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP1; unfold SOCKET_SEND_K; change ALLOC_STACK with 8192; lia|].
      split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; unfold SOCKET_SEND_K in Ha; change ALLOC_STACK with 8192 in Ha;
              apply WM1; rewrite SEGS; apply HWS; lia|].
      split; [rewrite E1_4; exact HTP|].
      split; [intros a Ha; apply WM1; rewrite SEGS; apply HERR; exact Ha|].
      intros HI. specialize (HAUX HI). rewrite SP1.
      destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & LL1 & LL2).
      exists av, ar.
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
        assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
        destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
      split.
      { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
        split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
      lia.
    - exact E1_11.
    - exact E1_12.
    - lia.
    - exact GR1m.
    - exact NREP.
    - intros _. split; [unfold LMAX; lia|]. split; [rewrite length_app; cbn [length]; lia|].
      split.
      { rewrite SEGS. replace (X ++ Z_to_bv 8 0 :: slack) with ((X ++ [Z_to_bv 8 0]) ++ slack) in BS1
          by (rewrite <- app_assoc; reflexivity).
        exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BS1)). }
      split; [left; rewrite SP1; unfold SOCKET_SEND_K; change ALLOC_STACK with 8192; lia|].
      split; [right; left; exists q, nq; split; [exact INQ|]; split; [exact QO | lia]|].
      split.
      { intros a Ha HR. apply rec_area_G in HR. destruct (GFRAME a HR) as [IMG _].
        apply (ax_blocks_img AX L A mem md qs nq (a - q) HMR Hqs ltac:(lia)). rewrite EQ1.
        replace (q + (a - q)) with a by ring. exact IMG. }
      apply room_sb; [exact ROOM | lia].
    - intros H. lia.
    - rewrite SEGS. exact RA1.
    - rewrite SEGS. exact F18m.
    - exact RES. }
  intros c2 RET.
  destruct RET as (L1 & A1 & R2 & m2 & md1 & R' & O1 & r0 & qn & bl1 & bl2 & -> & POST1 & A0' & ER' & GR1 & HR0 & HRR
    & HNEG & HPOS & HACC & HOK & RA2 & F18' & INIT1 & REG1 & RES1).
  destruct POST1 as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  destruct (HPOS ltac:(lia)) as ((c1 & c2 & BLK1 & CC) & FRESHN & QNAL & HO1).
  clear HNEG HPOS.
  destruct (HOK qs nq Hqs ltac:(rewrite EQ1; exact NOQ)) as (Hqs1 & EQ1q & KQ).
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 q) by exact (eq_trans (HPRES1 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (NOWN : forall L' A' mem' md' a, aa_MR API L' A' mem' md' -> alloc_ceiling <= a -> ~ owned B L' A' a).
  { intros L' A' mem' md' a HM Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HM Ho). lia. }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp - 32) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. apply HFRAME1; [left; exact Ha | exact (NOWN _ _ _ _ a MR1 (proj1 Ha))
      | exact (NOWN _ _ _ _ a HMR1 (proj1 Ha)) | | ].
    - unfold scratch_k. rewrite SP1. unfold SOCKET_SEND_K. change ALLOC_STACK with 8192. intros [H|H]; lia.
    - unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY. lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [CB 8 junk; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 32 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  assert (WS2 : forall a, bv_unsigned sp - 8448 <= a < bv_unsigned sp -> writable_at (ms_segs B) m2 a).
  { intros a Ha.
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 32)) as [D|D];
      [destruct (Z_lt_ge_dec a (bv_unsigned sp - 8256)) as [D'|D']|].
    - apply (proj1 (proj2 (HI2 a ltac:(lia) ltac:(lia)))). apply WM1. rewrite SEGS. apply HWS. lia.
    - apply HSCR1. left. rewrite SP1. unfold SOCKET_SEND_K. change ALLOC_STACK with 8192. lia.
    - apply (proj1 (proj2 (HI2 a ltac:(lia) ltac:(lia)))). apply WM1. rewrite SEGS. apply HWS. lia. }
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_2, SEGS.
    eapply rp_run2; [exact FR2 | lia]. }
  intros ms3 (can3 & Q3 & EQ3). subst can3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = reg_get regs 1) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_4 : getr R3 4 = reg_get R2 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = reg_get R2 8) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (SP3 : spZ R3 = bv_unsigned sp) by (unfold spZ; rewrite E3_2; reflexivity).
  pose proof FREE as FRE. unfold free_contract in FRE. rewrite FREE_PC in FRE.
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (FRE L1 A1 R3 m2 md1 qs nq (sb_malloc b (l + 1))).
    - split; [exact HMR1|]. split; [exact HWF1|]. split; [exact HBD1|].
      split; [rewrite E3_1; exact HRA|].
      split; [rewrite SP3; exact HAL|].
      split; [rewrite SP3; change ALLOC_STACK with 8192; lia|].
      split; [rewrite SP3; lia|].
      split; [intros a Ha; rewrite SP3 in Ha; change ALLOC_STACK with 8192 in Ha; apply WS2; lia|].
      split; [rewrite E3_4, E2_4; exact HTP|].
      split; [intros a Ha; apply HSCR1; right; exact Ha|].
      intros HI. exfalso. rewrite (YI04.init_done_of_block A1 (qs, nq) HWF1 Hqs1) in HI. discriminate.
    - exact RA2.
    - exact Hqs1.
    - rewrite E3_10, E2_8, EQ1q, EQ1. reflexivity.
    - destruct RES1 as (LE1 & RS1). rewrite (proj2 (Z.ltb_lt 0 (l + 1)) ltac:(lia)) in LE1.
      apply (res_ok_slots_le A1 _ _ LE1); [|exact RS1].
      destruct ROOM as (_ & RC & _). unfold VerbsB.sb_n in RC. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap] in *. lia. }
  intros c3 RET2.
  destruct RET2 as (L2 & A2 & R4 & m4 & md2 & -> & POST2 & BLK2 & KEPT2 & RA4 & GK4 & SURV2 & INIT2 & REG2 & RES2).
  destruct POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HPRES2 & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
  rewrite E3_1.
  apply SR_ret.
  exists L2, A2, R4, m4, md2, O1, 1%nat.
  split; [reflexivity|].
  destruct BLK2 as (b1 & b2 & BL1 & BL2). rewrite EQ1q, EQ1 in BL1.
  pose proof (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR1) as DJ1.
  assert (QNOT2 : ~ In (q, nq) (blocks L2 A2)).
  { rewrite BL2. apply mid_not_side; [rewrite <- BL1; exact DJ1 | cbn; lia]. }
  assert (INB1 : In (q, nq) (blocks L1 A1)) by (rewrite BL1; apply in_or_app; right; left; reflexivity).
  assert (NNEW : ~ In (qn, l + 1) (bl1 ++ bl2)).
  { rewrite <- CC. apply mid_not_side; [rewrite <- BLK1; exact DJ1 | cbn; lia]. }
  assert (QINbl : In (q, nq) (bl1 ++ bl2)).
  { destruct (r_reply R).
    - destruct HRR as (k0 & Hk0 & EB). rewrite EB in INQ. apply in_app_or in INQ. apply in_or_app.
      destruct INQ as [H|[H|H]]; [left; exact H | exfalso; apply NOQ; rewrite <- H; exact Hk0 | right; exact H].
    - destruct HRR as [_ EB]. rewrite <- EB. exact INQ. }
  assert (QNO1 : ~ In (q, nq) O1).
  { intros H. apply HO1 in H as [[H _]|H]; [exact (NOQ H)|].
    apply NNEW. rewrite <- H. exact QINbl. }
  assert (O1B : forall pn, In pn O1 -> In pn (blocks L1 A1) /\ 1 <= snd pn).
  { intros pn H. rewrite ER' in GR1. unfold g_rec_rep in GR1. exact (rec_rep_O _ _ _ _ _ _ _ _ GR1 pn H). }
  assert (O1q : forall pn, In pn O1 -> fst pn <> q).
  { intros [a k] H E. cbn in E. subst a. destruct (O1B _ H) as [Hb Hk]. cbn in Hk.
    pose proof (same_start _ q k nq DJ1 Hb INB1 ltac:(lia) ltac:(lia)) as E. subst k. exact (QNO1 H). }
  assert (O1in2 : forall pn, In pn O1 -> In pn (blocks L2 A2)).
  { intros pn H. destruct (O1B pn H) as [Hb _]. rewrite BL1 in Hb. rewrite BL2.
    apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|[Hb|Hb]]; [left; exact Hb| |right; exact Hb].
    exfalso. apply (O1q pn H). rewrite <- Hb. reflexivity. }
  assert (OWNS : forall pn, In pn O1 -> In pn O \/ ~ In pn (blocks L A)).
  { intros pn H. apply HO1 in H as [[H _]|H]; [left; exact H|]. subst pn.
    destruct (in_dec zz_dec (qn, l + 1) (blocks L A)) as [Hin|Hin]; [|right; exact Hin].
    destruct (r_reply R).
    - destruct HRR as (k0 & Hk0 & EB). rewrite EB in Hin. apply in_app_or in Hin.
      destruct Hin as [H|[H|H]]; [exfalso; apply NNEW; apply in_or_app; left; exact H | left; rewrite <- H; exact Hk0
        | exfalso; apply NNEW; apply in_or_app; right; exact H].
    - destruct HRR as [_ EB]. exfalso. apply NNEW. rewrite <- EB. exact Hin. }
  assert (NOUT : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (q <= a < q + nq)).
  { intros a HA Ha. destruct HA as [HA|HA]; [lia|].
    apply (ax_blocks_img AX L1 A1 m2 md1 qs nq (a - q) HMR1 Hqs1 ltac:(lia)). rewrite EQ1q, EQ1.
    replace (q + (a - q)) with a by ring. exact HA. }
  split.
  { split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
    destruct HLE1 as (C1 & C2 & C3 & C4). destruct HLE2 as (D1 & D2 & D3 & D4).
    split.
    { split; [rewrite D1, C1; reflexivity|]. split; [rewrite D2, C2; reflexivity|].
      split; [rewrite D3, C3; reflexivity|]. intros r Hr. rewrite (D4 r ltac:(lia)). exact (C4 r Hr). }
    split.
    { intros p n Hp _. destruct (YN03.block_region A p n HWF Hp) as (k & o & rg & -> & Hrg & _).
      unfold region_of in Hrg. assert (Hk : (k < length (st_regions A))%nat)
        by (apply nth_error_Some; rewrite Hrg; discriminate).
      unfold ptr_addr, loc_addr. rewrite (D4 k ltac:(lia)), (C4 k Hk). reflexivity. }
    split.
    { intros r Hr. rewrite (HPRES2 r Hr). unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct C as [C|C]; [subst r|]); [..|subst r];
      match goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
        rewrite (getr_of_eqv _ _ (Z_to_bv 5 n) X3 eq_refl); simp_regs;
        first [ reflexivity
              | transitivity (getr R1 (Z_to_bv 5 n));
                [ exact (HPRES1 n ltac:(unfold callee_saved; lia))
                | rewrite (getr_of_eqv _ _ (Z_to_bv 5 n) X1 eq_refl); simp_regs; reflexivity ] ] end. }
    split.
    { destruct HVM1 as [v1 ->]. destruct HVM2 as [v2 ->]. exists v2. apply with_vmmaps_twice. }
    split.
    { intros a HA NO NO2 NS NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8448 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      pose proof (not_owned_mid L A mem md L1 A1 m2 md1 a HMR HMR1 HA NO) as NO1.
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFRAME1; [exact HA | exact NO | exact NO1 | |].
        - unfold scratch_k. rewrite SP1. unfold SOCKET_SEND_K. change ALLOC_STACK with 8192.
          intros [H|H]; [lia | exact (NER H)].
        - intros H. apply NE. unfold socket_send_writes, rp_writes, OFF_NREPLIES, OFF_REPLY, REC_SIZE in *. lia. }
      assert (H24 : mbyte (ms_segs B) m4 a = mbyte (ms_segs B) m2 a /\
                    (writable_at (ms_segs B) m2 a <-> writable_at (ms_segs B) m4 a)).
      { apply HFRAME2; [exact HA | exact NO1 | exact NO2 | |].
        - unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)].
        - cbn beta. rewrite EQ1q, EQ1. exact (NOUT a HA). }
      split; [rewrite (proj1 H24), (proj1 H12), E01; reflexivity | rewrite W01, (proj2 H12), (proj2 H24); tauto]. }
    split.
    { intros p n i Hp Hp2 Hex Hi.
      assert (HnO : ~ In (ptr_addr L p, n) O).
      { intros HinO. apply Hex. apply in_map_iff. exists (ptr_addr L p, n). split; [reflexivity | exact HinO]. }
      destruct (HOK p n Hp HnO) as (Hp1 & EQp & KP).
      destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hp Hi) as (_ & Hlo & Hhi & _).
      pose proof (HBLKS2 p n i Hp1 Hp2 Hi) as E24. rewrite EQp in E24. rewrite E24, (KP i Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k in Ha. change (spZ regs) with (bv_unsigned sp) in Ha.
    destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 8192)) as [D|D]; [|apply HSCR2; left; rewrite SP3; change ALLOC_STACK with 8192; lia].
    apply (proj1 (proj2 (HFRAME2 a ltac:(left; lia) (NOWN _ _ _ _ a HMR1 ltac:(lia)) (NOWN _ _ _ _ a HMR2 ltac:(lia))
             ltac:(unfold scratch; rewrite SP3; change ALLOC_STACK with 8192; intros [H|H]; lia)
             ltac:(cbn beta; rewrite EQ1q, EQ1; lia)))).
    apply WS2. lia. }
  split; [exact RA4|].
  split.
  { rewrite ER' in GR1. unfold g_rec_rep in *.
    apply (rec_rep_frame (ms_segs B) G_REC REC_SC L1 A1 m2 _ O1 L2 A2 m4 GR1).
    - intros a Ha.
      assert (HG : in_globals frame_G a).
      { exists 0x33d10, 1020. split; [left; reflexivity|]. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha. lia. }
      destruct (GFRAME a HG) as (IMG & _ & _ & NER).
      assert (AR : 0 <= a < 2 ^ 21) by exact (in_img_low B SEGS a IMG).
      destruct (HFRAME2 a (or_intror IMG) (GOWN _ _ _ _ a HMR1 HG) (GOWN _ _ _ _ a HMR2 HG)) as [E W].
      + unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)].
      + cbn beta. rewrite EQ1q, EQ1. exact (NOUT a (or_intror IMG)).
      + split; [exact E | apply W].
    - intros p n i Hin Hi. destruct (O1B (p, n) Hin) as [Hb _].
      apply (KEPT2 p n i Hb); [| exact Hi]. rewrite EQ1q, EQ1. exact (O1q (p, n) Hin).
    - exact O1in2. }
  split; [exact QNOT2|].
  split.
  { intros [a k] Hpn HnO Hne. apply in_map_iff in Hpn as ([p k'] & Ep & Hp). cbn [fst snd] in Ep.
    injection Ep as Ea Ek. subst k'.
    destruct (HOK p k Hp ltac:(rewrite Ea; exact HnO)) as (Hp1 & EQp & _).
    assert (Hb1 : In (a, k) (blocks L1 A1)).
    { apply in_map_iff. exists (p, k). split; [cbn [fst snd]; rewrite EQp, Ea; reflexivity | exact Hp1]. }
    rewrite BL1 in Hb1. rewrite BL2. apply in_app_or in Hb1. apply in_or_app.
    destruct Hb1 as [H|[H|H]]; [left; exact H | exfalso; apply Hne; rewrite <- H; reflexivity | right; exact H]. }
  split.
  { intros pn Hpn.
    assert (Hb1 : In pn (blocks L1 A1)).
    { rewrite BL2 in Hpn. rewrite BL1. apply in_app_or in Hpn. apply in_or_app.
      destruct Hpn as [H|H]; [left; exact H | right; right; exact H]. }
    destruct (HACC pn Hb1) as [[H1 H2]|H]; [left|right; exact H].
    split; [exact H1|]. split; [exact H2|]. intros E. subst pn. exact (QNOT2 Hpn). }
  split; [exact OWNS|].
  split.
  { intros pn H1 H2 H3. destruct (OWNS pn H3) as [H|H]; contradiction. }
  split; [lia|].
  split.
  { intros a k i Hin Hgone Hi. apply in_map_iff in Hin as ([p k'] & Ep & Hp). cbn [fst snd] in Ep.
    injection Ep as Ea Ek. subst k'.
    assert (HnO : ~ In (ptr_addr L p, k) O) by (intros H; apply Hgone; left; exists k; rewrite <- Ea; exact H).
    destruct (HOK p k Hp HnO) as (Hp1 & EQp & KP).
    destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hp Hi) as (_ & Hlo & Hhi & _).
    assert (Hb1 : In (a, k) (blocks L1 A1)).
    { apply in_map_iff. exists (p, k). split; [cbn [fst snd]; rewrite EQp, Ea; reflexivity | exact Hp1]. }
    rewrite (KEPT2 a k i Hb1 ltac:(rewrite EQ1q, EQ1; intro E; apply Hgone; right; exact E) Hi).
    rewrite <- Ea. rewrite (KP i Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split.
  { destruct (ax_statics AX L2 A2 m4 md2 HMR2) as (WG & (g & Hg & WGD) & _).
    exists (Z_to_bv 64 g). unfold VerbsB.ssp_b, VerbsB.SSP_GOT_B, VerbsB.SSP_GUARD_B. split.
    - rewrite <- GOTG, <- GUARDV. apply word_le_at; [exact WG | rewrite GUARDV; lia].
    - rewrite <- GUARDV. apply word_le_at; [exact WGD | exact Hg]. }
  split; [lia|].
  apply (res_sb A2 b (l + 1) nq); [lia | lia | | exact RES2].
  destruct ROOM as (_ & RC & _). unfold VerbsB.sb_n in RC. cbn [sb_live sb_bytes sb_cap] in RC. lia.
Qed.

End R.
