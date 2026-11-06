From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YO0u YO0x YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq answer_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma tail_owns_blocks : forall (bl bl1 bl' O O1 O' c1 c2 : list (Z * Z)) old kold p1 p2 n,
  (forall pn, In pn O1 -> In pn O \/ ~ In pn bl) ->
  (forall pn, In pn bl1 -> (In pn bl /\ ~ In pn O) \/ In pn O1) ->
  (forall pn, In pn bl -> ~ In pn bl1 -> In pn O) ->
  ((old = 0 /\ bl1 = c1 ++ c2) \/ (old <> 0 /\ In (old, kold) O1 /\ bl1 = c1 ++ (old, kold) :: c2)) ->
  ~ In (p1, n) (c1 ++ c2) ->
  (forall pn, In pn O' <-> (In pn O1 /\ fst pn <> old) \/ pn = (p1, n)) ->
  (forall pn, In pn bl' -> (In pn bl1 /\ ~ In pn O1) \/ In pn O' \/ pn = (p2, n)) ->
  (forall pn, In pn O' -> In pn O \/ ~ In pn bl) /\
  (forall pn, In pn bl' -> (In pn bl /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)).
Proof.
  intros bl bl1 bl' O O1 O' c1 c2 old kold p1 p2 n P1 P2 P5 HB Hp1 HO' HC.
  split.
  - intros pn Hpn. apply HO' in Hpn as [[H1 _] | ->]; [exact (P1 pn H1)|].
    destruct (in_dec pair_dec (p1, n) bl) as [Hin|Hin]; [|right; exact Hin].
    destruct (in_dec pair_dec (p1, n) bl1) as [Hin1|Hin1]; [|left; exact (P5 _ Hin Hin1)].
    destruct HB as [[_ E]|(_ & Ho & E)]; rewrite E in Hin1; [contradiction|].
    apply in_app_or in Hin1 as [H|[H|H]].
    + exfalso. apply Hp1. apply in_or_app. left. exact H.
    + rewrite <- H. destruct (P1 _ Ho) as [H'|H']; [left; exact H'|].
      rewrite H in H'. contradiction.
    + exfalso. apply Hp1. apply in_or_app. right. exact H.
  - intros pn Hpn. destruct (HC pn Hpn) as [[H1 H2]|H]; [|right; exact H].
    destruct (P2 pn H1) as [H|H]; [left; exact H | contradiction].
Qed.

Lemma tail_q_distinct : forall (bl bl1 O O1 c1 c2 : list (Z * Z)) old kold q n x,
  (forall pn, In pn O1 -> In pn O \/ ~ In pn bl) ->
  ((old = 0 /\ bl1 = c1 ++ c2) \/ (old <> 0 /\ In (old, kold) O1 /\ bl1 = c1 ++ (old, kold) :: c2)) ->
  ~ In (q, n) (c1 ++ c2) ->
  In x bl -> ~ In x O -> In x bl1 -> x <> (q, n).
Proof.
  intros bl bl1 O O1 c1 c2 old kold q n x P1 HB Hq Hx Hxo Hx1 ->.
  destruct HB as [[_ E]|(_ & Ho & E)]; rewrite E in Hx1; [contradiction|].
  apply in_app_or in Hx1 as [H|[H|H]].
  - apply Hq. apply in_or_app. left. exact H.
  - rewrite <- H in Hxo, Hx. destruct (P1 _ Ho) as [H'|H']; contradiction.
  - apply Hq. apply in_or_app. right. exact H.
Qed.

Section Tail.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.

Lemma blocks_same_addr : forall L A mem md a k k', MR L A mem md ->
  In (a, k) (blocks L A) -> In (a, k') (blocks L A) -> 0 < k -> 0 < k' -> k = k'.
Proof using LAWS.
  intros L A mem md a k k' HM H1 H2 Hk Hk'. destruct (Z.eq_dec k k') as [E|E]; [exact E|].
  assert (Ne : (a, k) <> (a, k')) by congruence.
  destruct (YI04.pairwise_in2 _ _ (a, k) (a, k') (mr_blocks_disjoint B MR LAWS L A mem md HM) H1 H2 Ne) as [D|D];
    unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma user_in_blocks : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact H]. Qed.

Lemma others_kept_tail : forall segs L A mem L1 A1 mem1 md1 L' A' mem' O O1 old kold,
  MR L1 A1 mem1 md1 ->
  others_kept segs L A mem L1 A1 mem1 O ->
  (forall pn, In pn O1 -> In pn O \/ ~ In pn (blocks L A)) ->
  (old <> 0 -> In (old, kold) O1 /\ In (old, kold) (blocks L1 A1) /\ 0 < kold) ->
  (forall q k, In (q, k) (user_blocks A1) -> ~ In (ptr_addr L1 q, k) O1 -> In (q, k) (user_blocks A')) ->
  (forall p n, In (p, n) (user_blocks A1) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L1 p) ->
  (forall p n i, In (p, n) (user_blocks A1) -> In (p, n) (user_blocks A') -> ~ (ptr_addr L1 p = old) ->
     0 <= i < n -> mbyte segs mem' (ptr_addr L1 p + i) = mbyte segs mem1 (ptr_addr L1 p + i)) ->
  others_kept segs L A mem L' A' mem' O.
Proof using LAWS.
  intros segs L A mem L1 A1 mem1 md1 L' A' mem' O O1 old kold HM1 OK P1 HOLD HK HP HB.
  intros p k Hu Hno.
  destruct (OK p k Hu Hno) as (Hu1 & Hp1 & Hb1).
  assert (Hno1 : ~ In (ptr_addr L1 p, k) O1).
  { rewrite Hp1. intros H. destruct (P1 _ H) as [H'|H']; [exact (Hno H')|].
    exact (H' (user_in_blocks L A p k Hu)). }
  pose proof (HK p k Hu1 Hno1) as Hu'.
  split; [exact Hu'|]. split; [rewrite (HP p k Hu1 Hu'); exact Hp1|].
  intros i Hi.
  assert (Hne : ptr_addr L1 p <> old).
  { intros E. destruct (Z.eq_dec old 0) as [Z0|Z0].
    - pose proof (mr_blocks_range B MR LAWS L1 A1 mem1 md1 p k HM1 Hu1). lia.
    - destruct (HOLD Z0) as (Ho & Hob & Hk0).
      pose proof (user_in_blocks L1 A1 p k Hu1) as Hb. rewrite E in Hb.
      assert (Ek : k = kold) by exact (blocks_same_addr L1 A1 mem1 md1 old k kold HM1 Hb Hob ltac:(lia) Hk0).
      apply Hno1. rewrite E, Ek. exact Ho. }
  rewrite <- (Hb1 i Hi). rewrite <- Hp1. exact (HB p k i Hu1 Hu' Hne Hi).
Qed.

Lemma q_apart_tail : forall segs L A mem L' A' mem' md' O q n,
  MR L' A' mem' md' ->
  others_kept segs L A mem L' A' mem' O ->
  In (q, n) (blocks L' A') ->
  (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O -> (ptr_addr L p, k) <> (q, n)) ->
  forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
    ptr_addr L p + k <= q \/ q + n <= ptr_addr L p.
Proof using LAWS.
  intros segs L A mem L' A' mem' md' O q n HM' OK Hq HD p k Hu Hno.
  destruct (OK p k Hu Hno) as (Hu' & Hp' & _).
  pose proof (user_in_blocks L' A' p k Hu') as Hb. rewrite Hp' in Hb.
  destruct (YI04.pairwise_in2 _ _ _ _ (mr_blocks_disjoint B MR LAWS L' A' mem' md' HM') Hb Hq (HD p k Hu Hno))
    as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

End Tail.

Lemma rec_rep_pos : forall segs gr sc L A mem R O pn, rec_rep segs gr sc L A mem R O -> In pn O -> 0 < snd pn.
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. apply HO in Hin.
  destruct HR as (_ & HC & HA & HP & _ & _). destruct HC as (_ & C2 & _ & C4 & C5 & _).
  assert (CP : forall a c P, call_at segs (blocks L A) mem a c P -> In pn P -> 0 < snd pn).
  { intros a c P (_ & _ & Hl & _ & _ & _ & Hk) Hp.
    destruct (In_nth_error P pn Hp) as [k Ek].
    assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
    destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (Hk k s pn Es Ek) as (_ & _ & _ & Hs & _). lia. }
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (CP _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (CP _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold answer_at.
      destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin;
        try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & _ & H4 & _). lia.
    + revert HP Hin. unfold reply_at.
      destruct (r_reply R) as [y|]; destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin;
        try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & H4 & _ & H6 & _).
      destruct y as [|y0 y']; [exfalso; exact (H4 eq_refl)|]. cbn [length] in H6. lia.
Qed.

Lemma rec_rep_size : forall segs gr sc L A mem R O pn, rec_rep segs gr sc L A mem R O -> In pn O ->
  0 < snd pn <= LMAX + 2.
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. apply HO in Hin.
  destruct HR as (_ & HC & HA & HP & _ & _). destruct HC as (_ & C2 & _ & C4 & C5 & _).
  assert (CP : forall a c P, call_at segs (blocks L A) mem a c P -> In pn P -> 0 < snd pn <= LMAX + 2).
  { intros a c P (_ & _ & Hl & _ & _ & _ & Hk) Hp.
    destruct (In_nth_error P pn Hp) as [k Ek].
    assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
    destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (Hk k s pn Es Ek) as (_ & _ & _ & Hs & _). lia. }
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (CP _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (CP _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold answer_at.
      destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin;
        try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & _ & H4 & _). lia.
    + revert HP Hin. unfold reply_at.
      destruct (r_reply R) as [y|]; destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin;
        try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & H4 & _ & H6 & _).
      destruct y as [|y0 y']; [exfalso; exact (H4 eq_refl)|]. cbn [length] in H6. lia.
Qed.

Section AnsTail.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTXO : forall L A mem md a, MR L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE -> owned B L A a.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis ANS : answer_contract B API.
Hypothesis SLACK : block_slack_present B API.

Definition tail_ret (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (R1 : rstate) (e : rcall) (x : list byte) (chg : bool) (b bpre : sbound) (c' : config) : Prop :=
  let t := snd (rec_answer R1 e x chg) in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' q,
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B MR K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep segs L' A' mem' (fst (rec_answer R1 e x chg)) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at segs mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept segs L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    ro_agree segs mem' /\ f18_words segs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre (Z.of_nat (length t) + 1)) (Z.of_nat (length t) + 1)) /\
    res_ok_slots A' (sb_shift b A A').

Lemma answer_tail : forall K L A regs mem md (O : list (Z * Z)) L1 A1 regs1 mem1 md1 (R1 : rstate)
    (O1 : list (Z * Z)) b bpre b1 c sh e x chg,
  call_pre_t B API K L A regs mem md -> ANSWER_K <= K ->
  rjr B MR K (spZ regs) rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 ->
  getr regs1 1 = getr regs 1 -> spZ regs1 = spZ regs -> regs_preserved regs regs1 ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  g_rec_rep segs L1 A1 mem1 R1 O1 ->
  (r_refuse R1 = 0 -> ans_shape segs mem1 sh x) ->
  (r_refuse R1 = 0 -> chg = true -> ans_entry R1 c e) ->
  frm_zero fp_csr -> f18_words segs mem1 -> ro_agree segs mem1 ->
  res_ok_slots A1 b1 -> b1 = sb_shift b A A1 -> sb_le b1 bpre ->
  room_slots (sb_malloc (sb_malloc b1 (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) ->
  owns_new L A O O1 ->
  (forall pn, In pn (blocks L1 A1) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O1) ->
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks L1 A1) -> In pn O) ->
  SR segs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mem1 (seg_rom segs)) md1) (tail_ret K L A regs mem md O R1 e x chg b bpre).
Proof using SEGS AX CTXO ERRNO_LOW ANS SLACK.
  intros K L A regs mem md O L1 A1 regs1 mem1 md1 R1 O1 b bpre b1 c sh e x chg
    PRE KA R RA1 SP1 RP1 A10 A11 ACH GREP1 SHAPE ENTRY FRM F18 RO1 RES1 EB1 BLE ROOM1 P1 P2 P5.
  pose proof (aa_laws API) as LAWS.
  pose proof R as R0.
  destruct R0 as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  pose proof PRE as ((HM & _ & _ & HRA & HAL & _ & _ & _ & HTP & _) & HTS).
  assert (PRE1 : call_pre_t B API ANSWER_K L1 A1 regs1 mem1 md1).
  { split; [|rewrite SP1; exact HTS].
    apply (call_pre_k_of_rjr B MR K (spZ regs) rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 ANSWER_K regs1 R).
    - rewrite RA1. exact HRA.
    - rewrite SP1. exact HAL.
    - apply Z.leb_le. vm_compute. reflexivity.
    - rewrite SP1. lia.
    - rewrite SP1. lia.
    - exact (eq_trans (RP1 4 ltac:(unfold callee_saved; lia)) HTP). }
  eapply SR_mono.
  { apply (ANS L1 A1 regs1 mem1 md1 R1 O1 c sh e x chg b1 PRE1 A10 A11 ACH GREP1 SHAPE); [|exact FRM | exact F18 | exact RES1 | exact ROOM1 | exact RO1].
    intros Hr Hc. split; [exact (ENTRY Hr Hc)|]. intros q k a Hq Ha. exact (SLACK L1 A1 mem1 md1 q k a HM1 Hq Ha). }
  intros c' RET. unfold answer_ret in RET.
  destruct RET as (fx' & L' & A' & regs' & mem' & md' & p1 & p2 & old & O' & EC & FPK & OLDB & POST & A0 & NE12 & AL1 & AL2
    & FR1 & FR2 & (c1 & c2 & HB & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & RA' & F18' & GK
    & INIT & REG & GR' & RES').
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  set (n := Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) in *.
  assert (HB' : exists kold, (old = 0 /\ blocks L1 A1 = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) O1 /\ blocks L1 A1 = c1 ++ (old, kold) :: c2)).
  { destruct HB as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B MR K (spZ regs) rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 p k R Hu Hno)|].
    exact (ptr_addr_stable A L L1 p k HWA Hu HL). }
  assert (R2 : rjr B MR K (spZ regs) rec_area (fun pn => In pn O) L A mem md L' A' mem' md').
  { apply (rjr_post B MR SEGS LAWS AX ERRNO_LOW K (spZ regs) rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1
             ANSWER_K regs1 ans_writes (fun a => a = old) L' A' regs' mem' md' R POST).
    - rewrite SP1. lia.
    - rewrite SP1. lia.
    - intros a Ha _. pose proof alloc_ceiling_val as AC.
      unfold ans_writes, rec_area, G_REC, REC_SC, OFF_ANSWER, OFF_STATE, SC_SIZE, REC_SIZE in *.
      split; [lia|]. lia.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B MR LAWS L A mem md p k HM Hu) as Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks L1 A1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks L1 A1 p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos segs G_REC REC_SC L1 A1 mem1 R1 O1 (old, kold) GREP1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B MR LAWS L1 A1 mem1 md1 old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (P1 _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L L1 p k HWA Hu HL). intros Ho.
      destruct (P1 _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG.
    - rewrite INIT. discriminate. }
  assert (RP : regs_preserved regs regs').
  { intros r Hr. rewrite (PR r Hr). exact (RP1 r Hr). }
  pose proof (rjr_final B MR CTXO K rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
                L' A' regs' mem' md' (proj1 PRE) R2 RP ltac:(intros a k G; exact (in_map fst O (a, k) G))) as FIN.
  pose proof (rjr_others_kept B MR K (spZ regs) rec_area (fun pn => In pn O) L A mem md L' A' mem' md' O R2
                (fun pn H => H)) as OK.
  destruct (tail_owns_blocks (blocks L A) (blocks L1 A1) (blocks L' A') O O1 O' c1 c2 old kold p1 p2 n
              P1 P2 P5 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L' A')) by (apply HIFF; right; right; reflexivity).
  exists fx', L', A', regs', mem', md', O', p2.
  split; [rewrite EC, RA1; reflexivity|].
  split; [exact FPK|]. split; [exact FIN|]. split; [exact A0|]. split; [exact GREP'|]. split; [exact OWN|].
  split; [exact BLK|]. split; [exact Hq|]. split; [exact FR2|].
  split; [intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn)|].
  split; [exact BY2|]. split; [exact OK|].
  split.
  { intros p0 k0 Hu0 Hno0.
    enough (D : ptr_addr L p0 + k0 <= p2 \/ p2 + n <= ptr_addr L p0) by (unfold n in D; lia).
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B MR LAWS segs L A mem L' A' mem' md' O p2 n PM OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks L1 A1) O O1 c1 c2 old kold p2 n (ptr_addr L p, k) P1 HB' NI2).
    - exact (user_in_blocks L A p k Hu).
    - exact Hno.
    - rewrite <- Ep. exact (user_in_blocks L1 A1 p k Hu1). }
  split; [exact RA'|]. split; [exact F18'|]. split; [exact INIT|]. split; [lia|].
  rewrite <- (sb_shift_trans b A A1 A'), <- EB1.
  split; [eapply sb_le_trans; [exact GR' | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE] | exact RES'].
Qed.

End AnsTail.
