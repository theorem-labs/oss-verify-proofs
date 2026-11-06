(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-pieces S_MF_KIGNP (KIGN 0x145a0) and S_MF_KKNOCKP
    (KKNOCK 0x145dc) of one line (Prog/mf_cuts.v, family F3).
    - KIGN: ieq(k, kl, "ignore" 0x1054f) 0x145b0; a miss goes to KKNOCK (the premise H_MF_KKNOCK). A hit tests the
      value: "yes" 0x145c8, "true" 0x14660, the one byte '1' (0x14670-0x1467c), "no" 0x14690, "false" 0x146a8, the
      one byte '0' (0x1472c-0x14738). A match stores ignore (s5) 0x146b8 and ignore_set 0x146c0 in entry gi and
      calls snprintf(g->ignore_file, 96, "%s", c->reading) 0x146d8; no match calls m_refuse 0x14744. Every path
      restores s8 = 0x1ff and s7 = 9 (0x14594-0x14598) and joins the tail 0x143d4.
    - KKNOCK: ieq(k, kl, "knock" 0x102a3) 0x145ec; a miss is the unknown key (m_refuse 0x143a8, knock = false). A
      hit reads n_kept 0x145f8 and, when n_kept <= 7, stores kept_knock[n_kept] = 1 at 0x1461c (the pending flag of
      seg_spec.mconf_encp), then m_refuse 0x143d0 with knock = true. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Image Arr ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  mfu_facts mf_common mfp_mconf mfp_facts ieq_c snprintf_c m_refuse_c printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

(** * Generic facts *)
Lemma ki_unsigned8 : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 8 b) = b.
Proof. intros b H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma ki_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. f_equal; [apply ki_unsigned8; exact Hx | exact (IH Hl)].
Qed.

Lemma ki_length_zb : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma ki_In_fs : forall (l : list Z) a b x, In x (firstn a (skipn b l)) -> In x l.
Proof.
  intros l a b x H. assert (H1 : In x (skipn b l)).
  { rewrite <- (firstn_skipn a (skipn b l)). apply in_or_app. left. exact H. }
  rewrite <- (firstn_skipn b l). apply in_or_app. right. exact H1.
Qed.

Lemma ki_Forall_fs : forall (P : Z -> Prop) (l : list Z) a b, Forall P l -> Forall P (firstn a (skipn b l)).
Proof. intros P l a b H. rewrite Forall_forall in *. intros x Hx. apply H. eapply ki_In_fs. exact Hx. Qed.

Lemma ki_nth_fs : forall (l : list Z) a b i, (i < a)%nat -> nth i (firstn a (skipn b l)) 0 = nth (b + i) l 0.
Proof.
  intros l a b. revert l a. induction b as [|b IH]; intros l a i H.
  - cbn [skipn Nat.add]. revert a i H. induction l as [|x l IHl]; intros a i H; [destruct a, i; reflexivity|].
    destruct a as [|a]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IHl. lia.
  - destruct l as [|x l]; [destruct a, i; reflexivity|]. cbn [skipn]. rewrite (IH l a i H). reflexivity.
Qed.

Lemma ki_upd_nth_comp {A} : forall (f g : A -> A) l i, upd_nth i g (upd_nth i f l) = upd_nth i (fun x => g (f x)) l.
Proof. intros f g l. induction l as [|x r IH]; intros i; destruct i; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma ki_upd_nth_ext {A} : forall (f g : A -> A) l i, (forall x, f x = g x) -> upd_nth i f l = upd_nth i g l.
Proof. intros f g l. induction l as [|x r IH]; intros i H; destruct i; cbn; try reflexivity; f_equal; auto. Qed.

Lemma ki_m_upd_comp : forall c0 i f g, m_upd (m_upd c0 i f) i g = m_upd c0 i (fun x => g (f x)).
Proof.
  intros. unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  rewrite ki_upd_nth_comp. reflexivity.
Qed.

Lemma ki_m_upd_ext : forall c0 i f g, (forall x, f x = g x) -> m_upd c0 i f = m_upd c0 i g.
Proof. intros c0 i f g H. unfold m_upd. f_equal. apply ki_upd_nth_ext. exact H. Qed.

Lemma ki_m_upd_len : forall c0 i f, length (mc_seg (m_upd c0 i f)) = length (mc_seg c0).
Proof. intros. unfold m_upd, m_set_segs. cbn [mc_seg]. apply upd_nth_length. Qed.

Lemma ki_ro : forall m a l, mem_inv rsegs m ->
  ((0 <=? a) && (a + Z.of_nat (length l) <=? 2 ^ 64) && ro_bytes_b rsegs a l)%bool = true -> bytes_at rsegs m a l.
Proof.
  intros m a l MI H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply ro_bytes_at; [exact MI | lia | lia |]. apply ro_bytes_b_sound. exact H3.
Qed.

Lemma ki_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma ki_span_rd : forall c0 s, c0 mod 16 = 0 -> (length s < 96)%nat ->
  1 <= cstr_span (c0 + MC_READING) s /\ c0 + MC_READING + cstr_span (c0 + MC_READING) s <= c0 + SEG_M_SIZE + 4.
Proof.
  intros c0 s H L. unfold cstr_span, MC_READING, SEG_M_SIZE.
  pose proof (Z.mod_pos_bound (- (c0 + 9140 + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
  Z.div_mod_to_equations. split; lia.
Qed.

Lemma ki_penv : forall m fc lo sp0 lo' sp', printf_env m fc lo sp0 -> lo <= lo' -> sp' <= sp0 -> printf_env m fc lo' sp'.
Proof. intros m fc lo sp0 lo' sp' (A & B & C & D & E) H1 H2. refine (conj A (conj B (conj C (conj _ _)))); lia. Qed.

Lemma ki_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

Lemma ki_lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2 ^ 63))) by lia. rewrite (proj2 (Z.ltb_lt y (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma ki_rd_bytes : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma ki_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 x; cbn [app outside].
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - rewrite IH. tauto.
Qed.

Lemma ki_sub_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x Hx. apply ki_outside_app in Hx. exact (proj1 Hx). Qed.
Lemma ki_sub_r : forall W1 W2, sub_fp W2 (W1 ++ W2).
Proof. intros W1 W2 x Hx. apply ki_outside_app in Hx. exact (proj2 Hx). Qed.

Lemma ki_noimg_sub : forall c0 N a n0, blk_noimg rsegs c0 N -> c0 <= a -> a + n0 <= c0 + N -> blk_noimg rsegs a n0.
Proof.
  intros c0 N a n0 H H1 H2 i Hi s Hs. replace (a + i) with (c0 + (a - c0 + i)) by lia. apply H; [lia | exact Hs].
Qed.

Lemma ki_firstn_all : forall (l : list Z) n, (length l <= n)%nat -> firstn n l = l.
Proof.
  induction l as [|x l IH]; intros [|n] H; cbn [length] in H; try reflexivity; [lia|].
  cbn [firstn]. f_equal. apply IH. lia.
Qed.

(** * The .rodata literals of this piece *)
Definition KI_IGNORE : Z := 0x1054f.
Definition KI_YES : Z := 0x1042f.
Definition KI_TRUE : Z := 0x10517.
Definition KI_NO : Z := 0x10711.
Definition KI_FALSE : Z := 0x1029d.
Definition KI_KNOCK : Z := 0x102a3.

(** The image bytes after a literal's NUL (cstr_at's slack is at most 7). *)
Definition ki_sl (A : Z) (len : nat) : list byte :=
  match image_bytes rsegs (A + Z.of_nat len + 1) 7 with Some l => l | None => [] end.

(** The witness bytes are given explicitly: a vm_compute on a goal that still holds an evar normalizes the
    stuck term, image included. *)
Ltac ki_lit_tac A w len :=
  intros m MI; exists (zb w), (ki_sl A len);
  split; [apply ki_ro; [exact MI | vm_compute; reflexivity]|];
  split; [vm_compute; reflexivity|];
  split; [intros H; vm_compute in H; repeat (destruct H as [H|H]; [discriminate H|]); exact H|];
  apply Z.leb_le; vm_compute; reflexivity.

Lemma ki_at_ignore : forall m, mem_inv rsegs m -> cstr_at rsegs m KI_IGNORE S_ignore.
Proof. ki_lit_tac KI_IGNORE S_ignore 6%nat. Qed.
Lemma ki_at_yes : forall m, mem_inv rsegs m -> cstr_at rsegs m KI_YES S_yes.
Proof. ki_lit_tac KI_YES S_yes 3%nat. Qed.
Lemma ki_at_true : forall m, mem_inv rsegs m -> cstr_at rsegs m KI_TRUE S_true.
Proof. ki_lit_tac KI_TRUE S_true 4%nat. Qed.
Lemma ki_at_no : forall m, mem_inv rsegs m -> cstr_at rsegs m KI_NO S_no.
Proof. ki_lit_tac KI_NO S_no 2%nat. Qed.
Lemma ki_at_false : forall m, mem_inv rsegs m -> cstr_at rsegs m KI_FALSE S_false.
Proof. ki_lit_tac KI_FALSE S_false 5%nat. Qed.
Lemma ki_at_knock : forall m, mem_inv rsegs m -> cstr_at rsegs m KI_KNOCK S_knock.
Proof. ki_lit_tac KI_KNOCK S_knock 5%nat. Qed.

(** * The model at KIGN and KKNOCK *)
Lemma ki_mk_ign : forall c gi k v line,
  ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = true ->
  mk_disp c gi k v line =
    (if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)) then
       m_upd c gi (ms_with_ignore true (snprintf_s 96 F_s [AS (mc_reading c)]))
     else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)) then
       m_upd c gi (ms_with_ignore false (snprintf_s 96 F_s [AS (mc_reading c)]))
     else m_refuse c line false).
Proof. intros c gi k v line H1 H2 H3. unfold mk_disp. rewrite H1, H2, H3. reflexivity. Qed.

Lemma ki_mk_knock : forall c gi k v line,
  ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = false -> ieq k S_knock = true ->
  mk_disp c gi k v line = m_refuse c line true.
Proof. intros c gi k v line H1 H2 H3 H4. unfold mk_disp. rewrite H1, H2, H3, H4. reflexivity. Qed.

Lemma ki_mk_other : forall c gi k v line,
  ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = false -> ieq k S_knock = false ->
  mk_disp c gi k v line = m_refuse c line false.
Proof. intros c gi k v line H1 H2 H3 H4. unfold mk_disp. rewrite H1, H2, H3, H4. reflexivity. Qed.

Ltac ki_unf := unfold mseg_addr, apart, M_FILE_STACK, M_REFUSE_STACK, M_FILE_FRAME, PRINTF_K, SEG_M_SIZE, MSEG_SIZE,
  IEQ_STACK, MC_READING, MC_KNOCK, MC_NKEPT, MC_N, MS_IGNORE, MS_IGNORE_SET, MS_IGNORE_FILE in *.
Ltac nlia := ki_unf; lia.

(** * The walk *)
Section KI.
Variables (sp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F0 : bvmap 5 word) (fc0 : bv 32)
  (m0 : word -> option byte) (lo c p line : Z) (mc : mconf) (gi k0 : nat) (rest : list Z)
  (ok kl ov vl : nat) (k v : list Z) (n : nat).
Hypothesis HIEQ : ieq_contract.
Hypothesis HSN : snprintf_contract.
Hypothesis HMR : m_refuse_contract.
Hypothesis HT : H_MF_TAIL n.
Hypothesis HKK : H_MF_KKNOCK n.
Hypothesis Hn : (length rest <= n)%nat.
Hypothesis Hne : rest <> [].
Hypothesis HC0 : mf_ctx m0 fc0 (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HX0 : mf_text m0 (bv_unsigned sp0) lo c p rest.
Hypothesis HS0 : mf_st m0 (bv_unsigned sp) c mc (Some gi) k0 line rest.
Hypothesis HKV : mk_kv rest ok kl ov vl k v.
Hypothesis Hrole : ieq k S_role = false.
Hypothesis Hmodel : ieq k S_model = false.

Local Abbreviation Sp := (bv_unsigned sp).
Local Abbreviation Sp0 := (bv_unsigned sp0).
Local Abbreviation QP mf := (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F0 m0 lo c k0 mf).
Local Abbreviation KS pc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 s7 s8
       (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Local Abbreviation Wst := [(Sp0 - M_FILE_STACK, Sp0)].

(** The loop facts the walk keeps. *)
Definition ki_inv (m : word -> option byte) (fc : bv 32) (mcx : mconf) (pend : bool) : Prop :=
  mf_ctx m fc Sp0 Sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 /\ mf_text m Sp0 lo c p rest /\
  mconf_atp rsegs pend m c mcx /\ cell8 m (Sp + 0x20) (mseg_addr c gi).

Lemma ki_inv0 : ki_inv m0 fc0 mc false.
Proof. destruct HS0 as (HM & HQ & _). exact (conj HC0 (conj HX0 (conj HM HQ))). Qed.

Lemma ki_ctx_facts : forall m fc, mf_ctx m fc Sp0 Sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  Sp + 208 = Sp0 /\ 341736 <= lo /\ lo + 6160 <= Sp0 /\ Sp0 < 2 ^ 63 /\
  (c + 9240 <= lo \/ Sp0 <= c) /\ 0 < c /\ c + 9244 <= 2 ^ 64 /\ c mod 16 = 0 /\ Sp mod 16 = 0.
Proof.
  intros m fc H. pose proof H as H'. apply mf_ctx_bounds in H'. destruct H' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  destruct H as (E & _ & _ & _ & _ & _ & C16 & _). unfold M_FILE_FRAME in E.
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in B2. unfold SEG_M_SIZE in B6, B8.
  change (sa_img_end SA) with 341736 in B1.
  refine (conj _ (conj B1 (conj _ (conj B3 (conj _ (conj B7 (conj _ (conj C16 B5)))))))); lia.
Qed.

Lemma ki_text_facts : forall m, mf_text m Sp0 lo c p rest ->
  ~ In 0 rest /\ Forall (fun x => 0 <= x < 256) rest /\ 0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\
  (p + Z.of_nat (length rest) + 8 <= lo \/ Sp0 <= p).
Proof.
  intros m HX. pose proof HX as HX'. apply mf_text_props in HX'. destruct HX' as (A & B & C & D & E).
  destruct HX as (_ & _ & _ & AP & _). unfold apart in AP.
  assert (G : Z.of_nat (length rest) + 1 <= cstr_span p rest).
  { unfold cstr_span. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia. }
  refine (conj A (conj B (conj C (conj _ _)))); lia.
Qed.

Lemma ki_line_le : (length (mf_line rest) <= length rest)%nat.
Proof.
  destruct (mf_line_rest rest) as [[E _]|[E _]].
  - apply (f_equal (@length Z)) in E. rewrite length_app in E. cbn [length] in E. lia.
  - apply (f_equal (@length Z)) in E. lia.
Qed.

Lemma ki_st_facts : (gi < length (mc_seg mc))%nat /\ (k0 <= length (mc_kept mc))%nat /\ 0 <= line /\
  line + Z.of_nat (length rest) <= 65535 /\ mc_refused mc + Z.of_nat (length rest) < 2 ^ 32 /\
  mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32 /\ (length (mc_kept mc) <= 8)%nat /\ (1 <= length rest)%nat.
Proof.
  destruct HS0 as (HM & _ & HG & HK & HL0 & HL1 & HR & HO).
  destruct (mconf_atp_bytes rsegs false m0 c mc HM) as (bs & _ & E & _).
  destruct (mconf_enc_bounds false mc bs E) as (_ & _ & B8 & _).
  assert (L1 : (1 <= length rest)%nat).
  { destruct (length rest) eqn:EL; [|lia]. apply length_zero_iff_nil in EL. congruence. }
  cbn [cur_ok] in HG. repeat split; assumption.
Qed.

Lemma ki_seg32 : (length (mc_seg mc) <= 32)%nat.
Proof.
  destruct HS0 as (HM & _).
  destruct (mconf_atp_bytes rsegs false m0 c mc HM) as (bs & _ & E & _).
  destruct (mconf_enc_bounds false mc bs E) as (_ & B32 & _). exact B32.
Qed.

Lemma ki_mc_facts : (length (mc_reading mc) < 96)%nat /\ ~ In 0 (mc_reading mc) /\
  Forall (fun x => 0 <= x < 256) (mc_reading mc).
Proof.
  destruct HS0 as (HM & _).
  destruct (mconf_atp_bytes rsegs false m0 c mc HM) as (bs & _ & E & _).
  destruct (mconf_enc_bounds false mc bs E) as (_ & _ & _ & _ & _ & _ & R1 & R2 & R3 & _).
  exact (conj R1 (conj R2 R3)).
Qed.

Lemma ki_kv : (ok + kl <= length rest)%nat /\ (ov + vl <= length rest)%nat /\ length k = kl /\ length v = vl /\
  Forall (fun x => 0 <= x < 256) k /\ Forall (fun x => 0 <= x < 256) v /\ ~ In 0 v.
Proof.
  destruct HKV as (H1 & H2 & Ek & Ev). pose proof ki_line_le as LL.
  pose proof (ki_text_facts m0 HX0) as (NZ & FB & _ & _ & _).
  assert (L1 : (ok + kl <= length rest)%nat) by lia. assert (L2 : (ov + vl <= length rest)%nat) by lia.
  refine (conj L1 (conj L2 (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite <- Ek, length_firstn, length_skipn. lia.
  - rewrite <- Ev, length_firstn, length_skipn. lia.
  - rewrite <- Ek. apply ki_Forall_fs. exact FB.
  - rewrite <- Ev. apply ki_Forall_fs. exact FB.
  - rewrite <- Ev. intros H. apply NZ. eapply ki_In_fs. exact H.
Qed.

Lemma ki_stack_ok : forall m fc mcx pend d, ki_inv m fc mcx pend -> d <= 16 + PRINTF_K -> stack_ok rsegs m lo Sp d.
Proof.
  intros m fc mcx pend d (HC & _) Hd. pose proof (ki_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & STL & STA & STR) & _).
  unfold PRINTF_K in Hd. destruct (stk_split rsegs m lo Sp Sp0 STK ltac:(lia)) as [S1 _].
  refine (conj S1 (conj _ (conj F9 _))); [lia|]. intros a Ha. apply STR. lia.
Qed.

Lemma ki_stack_pf : forall m fc mcx pend, ki_inv m fc mcx pend -> stack_ok rsegs m (Sp - PRINTF_K) Sp PRINTF_K.
Proof.
  intros m fc mcx pend (HC & _). pose proof (ki_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & STL & STA & STR) & _).
  unfold PRINTF_K. destruct (stk_split rsegs m lo Sp Sp0 STK ltac:(lia)) as [S1 _].
  destruct (stk_split rsegs m lo (Sp - 5936) Sp S1 ltac:(lia)) as [_ S2].
  refine (conj S2 (conj _ (conj F9 _))); [lia|]. intros a Ha. apply STR. lia.
Qed.

(** A callee that writes only below sp. *)
Lemma ki_inv_call : forall m m' fc fc' mcx pend W,
  ki_inv m fc mcx pend -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm0 fc' -> stk rsegs m' lo Sp ->
  sub_fp W [(lo, Sp)] -> disjoint_from W Sp (Sp0 - Sp) -> disjoint_from W c SEG_M_SIZE ->
  disjoint_from W (Sp + 0x20) 8 -> ki_inv m' fc' mcx pend.
Proof.
  intros m m' fc fc' mcx pend W (HC & HX & HM & HQ) MU WM MI FR ST SF D1 D2 D3.
  pose proof (ki_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & _) & _).
  assert (SF3 : sub_fp W [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. apply SF. cbn [outside] in *. destruct Hx as (X1 & _ & _ & _). split; [exact X1 | exact I]. }
  assert (TM : MemNorm.task_mem rsegs m') by (eapply mf_task_mem; [exact HC | exact HM | exact MU | exact SF3]).
  assert (STK' : stk rsegs m' lo Sp0).
  { eapply mf_stk_after; [exact STK | exact MU | exact WM | exact ST | lia | exact D1]. }
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; [exact HC | exact MU | exact WM | exact MI | exact TM | exact FR | exact STK' | exact SF3].
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. apply SF. cbn [outside] in *.
    destruct Hx as (X1 & _ & _). split; [lia | exact I].
  - eapply mconf_atp_transport; [exact HM | exact MU | exact D2].
  - eapply cell8_transport; [exact HQ | exact MU | exact D3].
Qed.

(** A store into c. *)
Lemma ki_inv_wc : forall m fc mcx mcx' pend pend' a nb,
  ki_inv m fc mcx pend -> c <= a -> a + Z.of_nat (length nb) <= c + SEG_M_SIZE ->
  store_ok rsegs m (wa a) (length nb) = true ->
  (forall bs, mconf_encp pend mcx bs -> mconf_encp pend' mcx' (upd_bytes bs (Z.to_nat (a - c)) nb)) ->
  ki_inv (write_to_mem m (wa a) nb) fc mcx' pend'.
Proof.
  intros m fc mcx mcx' pend pend' a nb (HC & HX & HM & HQ) H1 H2 HS ENC.
  pose proof (ki_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & (STK & _) & MI).
  unfold SEG_M_SIZE in H2.
  assert (MU : munch [(a, a + Z.of_nat (length nb))] m (write_to_mem m (wa a) nb)).
  { apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia]. }
  assert (WM : wmono rsegs m (write_to_mem m (wa a) nb)) by (apply wmono_write; apply wmono_refl).
  assert (MI' : mem_inv rsegs (write_to_mem m (wa a) nb)) by (apply mem_inv_store; assumption).
  assert (SF3 : sub_fp [(a, a + Z.of_nat (length nb))] [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx. destruct Hx as (X1 & X2 & X3 & _).
    split; [lia | exact I]. }
  assert (TM : MemNorm.task_mem rsegs (write_to_mem m (wa a) nb)) by (eapply mf_task_mem; eassumption).
  assert (STK' : stk rsegs (write_to_mem m (wa a) nb) lo Sp0) by (apply stk_write; [exact STK | lia | lia]).
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; eassumption.
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx.
    destruct Hx as (X1 & X2 & _). split; [lia | exact I].
  - eapply mconf_atp_store; [exact HM | lia | unfold SEG_M_SIZE; lia | exact ENC].
  - eapply cell8_transport; [exact HQ | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** The step facts of a store into c. *)
Lemma ki_wc_step : forall m W mcx mcx' pend pend' a nb,
  ki_inv m fc0 mcx pend -> munch W m0 m -> wmono rsegs m0 m -> inside W a (Z.of_nat (length nb)) ->
  c <= a -> a + Z.of_nat (length nb) <= c + SEG_M_SIZE -> store_ok rsegs m (wa a) (length nb) = true ->
  (forall bs, mconf_encp pend mcx bs -> mconf_encp pend' mcx' (upd_bytes bs (Z.to_nat (a - c)) nb)) ->
  ki_inv (write_to_mem m (Z_to_bv 64 a) nb) fc0 mcx' pend' /\ munch W m0 (write_to_mem m (Z_to_bv 64 a) nb) /\
  wmono rsegs m0 (write_to_mem m (Z_to_bv 64 a) nb).
Proof.
  intros m W mcx mcx' pend pend' a nb INV MU WM IN H1 H2 HS ENC. pose proof INV as (HC & _).
  pose proof (ki_ctx_facts m fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  unfold SEG_M_SIZE in H2. change (Z_to_bv 64 a) with (wa a).
  refine (conj _ (conj _ _)).
  - eapply ki_inv_wc; [exact INV | lia | unfold SEG_M_SIZE; lia | exact HS | exact ENC].
  - apply munch_write; [exact MU | lia | lia | exact IN].
  - apply wmono_write. exact WM.
Qed.

(** With kept full the pending flag says nothing. *)
Lemma ki_pend_full : forall m mcx pend pend', mconf_atp rsegs pend m c mcx -> (length (mc_kept mcx) = 8)%nat ->
  mconf_atp rsegs pend' m c mcx.
Proof.
  intros m mcx pend pend' HM HL. destruct (mconf_atp_bytes rsegs pend m c mcx HM) as (bs & HB & HE & _).
  exists bs. split; [exact HB|]. eapply mconf_encp_full; [exact HL | exact HE].
Qed.

(** ** The tail 0x143d4 *)
Lemma ki_tail : forall mt Ft fct mcx W (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 w7 w8 t3 t4 t5 t6 : word),
  w7 = Z_to_bv 64 9 -> w8 = Z_to_bv 64 0x1ff ->
  ki_inv mt fct mcx false -> munch W m0 mt -> wmono rsegs m0 mt -> sub_fp W (M_FILE_W Sp0 c k0 mcx) ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F0 r) ->
  (gi < length (mc_seg mcx))%nat -> (k0 <= length (mc_kept mcx))%nat ->
  mc_refused mcx <= mc_refused mc + 1 -> mc_overflow mcx <= mc_overflow mc + 1 ->
  evt rsegs (QP (mf_fin (mcx, Some gi) line rest))
    (KS 0x143d4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 w7 w8 t3 t4 t5 t6 Ft fct mt).
Proof.
  intros mt Ft fct mcx W ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 w7 w8 t3 t4 t5 t6 E7 E8 (HC & HX & HM & HQ)
    MU WM SF FF Hg Hk Hr Ho. subst w7 w8.
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  eapply mf_post_back; [exact FF | exact MU | exact WM | |].
  { eapply sub_fp_trans; [exact SF | apply mf_W_fin; exact Hg]. }
  unfold mf_post, mf_fin. pose proof HT as HT'. unfold H_MF_TAIL in HT'.
  eapply HT' with (rest := mf_rest rest) (p := mf_next p rest) (line := line + 1) (mc := mcx) (cur := Some gi)
                  (k0 := k0).
  - pose proof (mf_rest_lt rest Hne). lia.
  - eapply mf_tail_loop; [exact HC | exact HX | exact Hne | exact HM | exact HQ | exact Hg | exact Hk | lia | lia | |].
    + eapply mf_cnt_next; [exact Hne | exact S5 | lia].
    + eapply mf_cnt_next; [exact Hne | exact S6 | lia].
  - unfold m_file_regs. repeat split; reflexivity.
Qed.

(** ** The unknown key 0x143a0: m_refuse(c, line + 1) with knock = false, then 0x14594 and the tail. *)
Lemma ki_unknown : forall mk W (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word),
  ki_inv mk fc0 mc false -> munch W m0 mk -> wmono rsegs m0 mk ->
  sub_fp W (M_FILE_W Sp0 c k0 (m_refuse mc (line + 1) false)) ->
  evt rsegs (QP (mf_fin (m_refuse mc (line + 1) false, Some gi) line rest))
    (KS 0x143a0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk W ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 INV MU WM SF.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  step. step. step.
  eapply (mf_refuse_call HMR 0x143a8) with (lo := lo) (sp0 := Sp0) (p := p) (rest := rest) (w := mseg_addr c gi)
    (mc := mc) (knock := false) (ra0 := ra0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11).
  - lia.
  - lia.
  - reflexivity.
  - exact HC.
  - exact HX.
  - exact HQ.
  - exact HM.
  - lia.
  - lia.
  - intros m' F' fc' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HC' HX' HQ' HM' MU' WM' FF'.
    replace (Z_to_bv 64 (0x143a8 + 4)) with (Z_to_bv 64 0x143ac) by reflexivity.
    step. step. step. step.
    destruct (m_refuse_sizes mc (line + 1) false) as (Eseg & Ekept).
    eapply ki_tail with (mcx := m_refuse mc (line + 1) false) (W := W ++ m_refuse_W Sp c mc).
    + reflexivity.
    + reflexivity.
    + exact (conj HC' (conj HX' (conj HM' HQ'))).
    + eapply munch_trans.
      * eapply munch_weaken; [apply ki_sub_l | exact MU].
      * eapply munch_weaken; [apply ki_sub_r | exact MU'].
    + eapply wmono_trans; eassumption.
    + apply sub_fp_app; [exact SF|].
      apply mf_W_refuse; [unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK, PRINTF_K; lia | lia | exact S2].
    + exact FF'.
    + rewrite Eseg. exact S1.
    + lia.
    + unfold m_refuse. cbn [mc_refused]. lia.
    + unfold m_refuse. cbn [mc_overflow]. lia.
Qed.

(** ** The knock refusal 0x143c8: m_refuse(c, line + 1) with knock = true, straight into the tail. *)
Lemma ki_kn_refuse : forall mk W (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word),
  ki_inv mk fc0 mc true -> munch W m0 mk -> wmono rsegs m0 mk ->
  sub_fp W (M_FILE_W Sp0 c k0 (m_refuse mc (line + 1) true)) ->
  evt rsegs (QP (mf_fin (m_refuse mc (line + 1) true, Some gi) line rest))
    (KS 0x143c8 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk W ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 INV MU WM SF.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  step. step. step.
  eapply (mf_refuse_call HMR 0x143d0) with (lo := lo) (sp0 := Sp0) (p := p) (rest := rest) (w := mseg_addr c gi)
    (mc := mc) (knock := true) (ra0 := ra0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11).
  - lia.
  - lia.
  - reflexivity.
  - exact HC.
  - exact HX.
  - exact HQ.
  - exact HM.
  - lia.
  - lia.
  - intros m' F' fc' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HC' HX' HQ' HM' MU' WM' FF'.
    replace (Z_to_bv 64 (0x143d0 + 4)) with (Z_to_bv 64 0x143d4) by reflexivity.
    destruct (m_refuse_sizes mc (line + 1) true) as (Eseg & Ekept).
    eapply ki_tail with (mcx := m_refuse mc (line + 1) true) (W := W ++ m_refuse_W Sp c mc).
    + reflexivity.
    + reflexivity.
    + exact (conj HC' (conj HX' (conj HM' HQ'))).
    + eapply munch_trans.
      * eapply munch_weaken; [apply ki_sub_l | exact MU].
      * eapply munch_weaken; [apply ki_sub_r | exact MU'].
    + eapply wmono_trans; eassumption.
    + apply sub_fp_app; [exact SF|].
      apply mf_W_refuse; [unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK, PRINTF_K; lia | lia | exact S2].
    + exact FF'.
    + rewrite Eseg. exact S1.
    + lia.
    + unfold m_refuse. cbn [mc_refused]. lia.
    + unfold m_refuse. cbn [mc_overflow]. lia.
Qed.

(** ** KKNOCK 0x145dc: ieq(k, kl, "knock"); the hit marks kept_knock[n_kept] and refuses with knock = true. *)
Lemma ki_kn_main : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  ieq k S_ignore = false ->
  evt rsegs (QP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (KS 0x145dc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
        (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
        t3 t4 t5 t6 F0 fc0 m0).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hign.
  pose proof ki_inv0 as INV. pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts m0 fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (ki_text_facts m0 HX) as (T1 & T2 & T3 & T4 & T5).
  destruct ki_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  pose proof HC as (_ & _ & HC8 & HC10 & _ & _ & _ & _ & HWR & _ & _ & (FR & _) & _ & _ & _ & MI).
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HIEQ with (l := zb k) (w := S_knock) (lo := lo). unfold ieq_pre. rewrite !unsigned_lit by nlia.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    - nlia.
    - destruct HKV as (_ & _ & Ek & _). rewrite <- Ek. apply (mf_text_bytes m0 Sp0 lo c p rest ok kl HX). lia.
    - rewrite ki_length_zb. lia.
    - nlia.
    - unfold KI_KNOCK. lia.
    - exact (ki_at_knock m0 MI).
    - change (length S_knock) with 5%nat. unfold KI_KNOCK. nlia.
    - apply (ki_stack_ok m0 fc0 mc false); [exact INV | unfold IEQ_STACK, PRINTF_K; lia].
    - exact MI. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MU & WM &
              MI1 & ST1 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (ki_zs_zb k K5).
  assert (INV1 : ki_inv m1 fc0 mc false).
  { eapply ki_inv_call; [exact INV | exact MU | exact WM | exact MI1 | exact FR | exact ST1 | | | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _). unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK, SEG_M_SIZE. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I]. }
  assert (MU1 : munch Wst m0 m1).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _).
    unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *. split; [lia | exact I]. }
  assert (SFst : forall mf, sub_fp Wst (M_FILE_W Sp0 c k0 mf))
    by (intros mf; apply mf_W_frame; unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia).
  destruct (ieq k S_knock) eqn:EQ; unfold b2z.
  - (* the knock key *)
    rewrite (ki_mk_knock mc gi k v (line + 1) Hrole Hmodel Hign EQ).
    pose proof INV1 as (HC1 & HX1 & HM1 & HQ1).
    pose proof HC1 as (_ & _ & HK8 & HK10 & _ & _ & _ & _ & HWR1 & _ & _ & _ & _ & _ & _ & MI1').
    pose proof (ki_rd_bytes _ _ _ HK10) as RD10. rewrite length_le8 in RD10.
    pose proof (ki_rd_bytes _ _ _ HK8) as RD8. rewrite length_le8 in RD8.
    assert (RN : ov_read_bytes rsegs m1 (wa (c + MC_N + 0x3ac)) 4
                 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)))))).
    { replace (c + MC_N + 0x3ac) with (c + MC_NKEPT) by (unfold MC_N, MC_NKEPT; lia).
      apply (mconf_rd_nkept rsegs false m1 c mc HM1). }
    step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    step. step.
    rewrite (ki_sx32_small (Z.of_nat (length (mc_kept mc)))) by lia.
    step. step. step. step.
    rewrite (ki_lts_small 7 (Z.of_nat (length (mc_kept mc)))) by lia.
    destruct (Z.ltb_spec 7 (Z.of_nat (length (mc_kept mc)))) as [H8|H8]; cbv iota.
    + (* n_kept = 8: the flag says nothing *)
      eapply (ki_kn_refuse m1 Wst); [| exact MU1 | exact WM | apply SFst].
      refine (conj HC1 (conj HX1 (conj _ HQ1))).
      eapply ki_pend_full; [exact HM1 | lia].
    + (* n_kept <= 7: kept_knock[n_kept] = 1 *)
      step.
      try rewrite (unsigned_lit (Z.of_nat (length (mc_kept mc)))) by lia.
      replace (Z.shiftl (Z.of_nat (length (mc_kept mc))) 2) with (4 * Z.of_nat (length (mc_kept mc)))
        by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      step. step. step.
      assert (HS : store_ok rsegs m1 (wa (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)))) 4 = true).
      { replace (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)))
          with (c + (MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)))) by lia.
        apply (wr_at_store_ok rsegs m1 c SEG_M_SIZE (MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc))) 4 HWR1);
          unfold MC_KNOCK, SEG_M_SIZE; lia. }
      step.
      assert (MUk : munch [(Sp0 - M_FILE_STACK, Sp0);
                           (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)),
                            c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)) + 4)] m0 m1).
      { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _ & _).
        split; [exact X1 | exact I]. }
      pose proof (ki_wc_step m1 _ mc mc false true (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)))
         (le4 (Z_to_bv 64 1)) INV1 MUk WM
         ltac:(rewrite length_le4; cbn [inside]; right; left; lia) ltac:(nlia) ltac:(rewrite length_le4; nlia)
         ltac:(rewrite length_le4; exact HS)
         ltac:(intros bs E; replace (Z.to_nat (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)) - c))
                 with (Z.to_nat MC_KNOCK + 4 * length (mc_kept mc))%nat by (unfold MC_KNOCK; lia);
               apply mconf_enc_knock; [exact E | lia])) as (INV2 & MU2 & WM2).
      set (m2 := write_to_mem m1 (Z_to_bv 64 (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc))))
                   (le4 (Z_to_bv 64 1))) in *. clearbody m2.
      step.
      eapply (ki_kn_refuse m2 _); [exact INV2 | exact MU2 | exact WM2 |].
      change [(Sp0 - M_FILE_STACK, Sp0);
              (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)),
               c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)) + 4)]
        with ([(Sp0 - M_FILE_STACK, Sp0)] ++
              [(c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)),
                c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)) + 4)]).
      apply sub_fp_app; [apply SFst|].
      apply mf_W_knock. rewrite mfc_refuse_kept by lia. lia.
  - (* an unknown key *)
    rewrite (ki_mk_other mc gi k v (line + 1) Hrole Hmodel Hign EQ).
    step. if_cases K; cbv iota; [|exfalso; vm_compute in K; discriminate K].
    eapply (ki_unknown m1 Wst); [exact INV1 | exact MU1 | exact WM | apply SFst].
Qed.

(** ** KIGN: the value of the "ignore" key *)
Local Abbreviation Whit := [(Sp0 - M_FILE_STACK, Sp0); (mseg_addr c gi, mseg_addr c gi + 256)].

Definition ki_rd : list Z := snprintf_s 96 F_s [AS (mc_reading mc)].
Definition ki_set (b : bool) : mconf := m_upd mc gi (ms_with_ignore b ki_rd).
Definition ki_vt : bool := ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)).
Definition ki_vf : bool := ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)).
Definition ki_res : mconf :=
  if ki_vt then ki_set true else if ki_vf then ki_set false else m_refuse mc (line + 1) false.

Lemma ki_disp_ign : ieq k S_ignore = true -> mk_disp mc gi k v (line + 1) = ki_res.
Proof.
  intros H. rewrite (ki_mk_ign mc gi k v (line + 1) Hrole Hmodel H).
  unfold ki_res, ki_vt, ki_vf, ki_set, ki_rd. reflexivity.
Qed.

Lemma ki_res_t : ki_vt = true -> ki_res = ki_set true.
Proof. intros H. unfold ki_res. rewrite H. reflexivity. Qed.
Lemma ki_res_f : ki_vt = false -> ki_vf = true -> ki_res = ki_set false.
Proof. intros H1 H2. unfold ki_res. rewrite H1, H2. reflexivity. Qed.
Lemma ki_res_n : ki_vt = false -> ki_vf = false -> ki_res = m_refuse mc (line + 1) false.
Proof. intros H1 H2. unfold ki_res. rewrite H1, H2. reflexivity. Qed.

Lemma ki_hd0 : (1 <= vl)%nat -> hd0 v = nth ov rest 0.
Proof.
  intros H. destruct HKV as (_ & _ & _ & Ev). rewrite <- Ev.
  change (hd0 (firstn vl (skipn ov rest))) with (hd0 (skipn 0 (firstn vl (skipn ov rest)))).
  rewrite hd0_skipn. rewrite (ki_nth_fs rest vl ov 0) by lia. f_equal. lia.
Qed.

Lemma ki_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ki_zxb : forall b, 0 <= b < 256 -> zxb (Z_to_bv 8 b) = Z_to_bv 64 b.
Proof. intros b H. unfold zxb. rewrite ki_unsigned8 by exact H. reflexivity. Qed.

Lemma ki_nth_byte : forall (l : list Z) i, Forall (fun x => 0 <= x < 256) l -> 0 <= nth i l 0 < 256.
Proof.
  intros l i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. lia.
Qed.

(** The encoding of an edit of entry gi at offset off. *)
Lemma ki_enc_upd : forall mcx (f : mseg -> mseg) off nb, 0 <= off ->
  (gi < length (mc_seg mcx))%nat -> (Z.to_nat off + length nb <= 256)%nat ->
  (forall fb, mseg_enc (nth gi (mc_seg mcx) mseg_d) fb ->
              mseg_enc (f (nth gi (mc_seg mcx) mseg_d)) (upd_bytes fb (Z.to_nat off) nb)) ->
  forall bs, mconf_encp false mcx bs ->
    mconf_encp false (m_upd mcx gi f) (upd_bytes bs (Z.to_nat (mseg_addr c gi + off - c)) nb).
Proof.
  intros mcx f off nb H0 Hg Hk Hf bs E.
  replace (Z.to_nat (mseg_addr c gi + off - c)) with (256 * gi + Z.to_nat off)%nat
    by (unfold mseg_addr, MSEG_SIZE; lia).
  apply mconf_enc_seg; assumption.
Qed.

(** snprintf(D, 96, "%s", reading) with D inside c and its stack [lo', sp). *)
Lemma ki_inv_snp : forall m m' fc fc' mcx mcx' lo' D L nb,
  ki_inv m fc mcx false -> lo <= lo' -> lo' <= Sp -> c <= D -> D + L <= c + SEG_M_SIZE -> Z.of_nat (length nb) = L ->
  munch [(lo', Sp); (D, D + L)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  frm0 fc' -> stk rsegs m' lo' Sp -> bytes_at rsegs m' D nb ->
  (forall bs, mconf_encp false mcx bs -> mconf_encp false mcx' (upd_bytes bs (Z.to_nat (D - c)) nb)) ->
  ki_inv m' fc' mcx' false.
Proof.
  intros m m' fc fc' mcx mcx' lo' D L nb (HC & HX & HM & HQ) L1 L2 D1 D2 EL MU WM MI TM FR ST BA ENC.
  pose proof (ki_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & _) & _).
  unfold SEG_M_SIZE in D2.
  assert (Lnn : 0 <= L) by lia.
  assert (ST0 : stk rsegs m' lo Sp).
  { destruct (stk_split rsegs m lo lo' Sp0 STK ltac:(lia)) as [S1 _].
    eapply stk_merge; [| exact ST | lia]. eapply stk_transport_disjoint; [exact S1 | exact MU | exact WM |].
    cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (STK' : stk rsegs m' lo Sp0).
  { eapply mf_stk_after; [exact STK | exact MU | exact WM | exact ST0 | lia |].
    cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (SF3 : sub_fp [(lo', Sp); (D, D + L)] [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx. destruct Hx as (X1 & X2 & X3 & _).
    split; [lia|]. split; [lia | exact I]. }
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; eassumption.
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx.
    destruct Hx as (X1 & X2 & _). split; [lia|]. split; [lia | exact I].
  - eapply mconf_atp_upd; [exact HM | exact MU | | exact BA | lia | unfold SEG_M_SIZE; lia | exact ENC].
    intros x Hx Hn'. unfold SEG_M_SIZE in Hx. rewrite EL.
    destruct (Z.le_gt_cases D x); destruct (Z.lt_ge_cases x (D + L)); try (split; assumption);
      exfalso; apply Hn'; cbn [outside]; repeat split; try exact I; lia.
  - eapply cell8_transport; [exact HQ | exact MU |]. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

(** 0x146b4: ignore = s5 (0x146b8), ignore_set = 1 (0x146c0), snprintf of ignore_file (0x146d8), the tail. *)
Lemma ki_store : forall (b : bool) mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 t3 t4 t5 t6 : word),
  ki_res = ki_set b -> ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x146b4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (if b then 1 else 0)) s6 s7
        (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros b mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 t3 t4 t5 t6 HRES INV MU WM.
  rewrite HRES.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct ki_mc_facts as (R1 & R2 & R3).
  pose proof ki_seg32 as S9.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HNI & HWR & _ & _ & _ & _ & _ & _ & MI).
  pose proof (ki_rd_bytes _ _ _ HQ) as RC. rewrite length_le8 in RC.
  assert (MUh : munch Whit m0 mk).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _ & _).
    split; [exact X1 | exact I]. }
  assert (HS1 : store_ok rsegs mk (wa (mseg_addr c gi + 24)) 4 = true).
  { replace (mseg_addr c gi + 24) with (c + (256 * Z.of_nat gi + 24)) by (unfold mseg_addr, MSEG_SIZE; lia).
    apply (wr_at_store_ok rsegs mk c SEG_M_SIZE (256 * Z.of_nat gi + 24) 4 HWR); unfold SEG_M_SIZE; lia. }
  step. step.
  pose proof (ki_wc_step mk Whit mc (m_upd mc gi (ms_set_ignore b)) false false (mseg_addr c gi + 24)
     (le4 (Z_to_bv 64 (if b then 1 else 0)))
     INV MUh WM ltac:(rewrite length_le4; cbn [inside]; right; left; nlia) ltac:(nlia) ltac:(rewrite length_le4; nlia)
     ltac:(rewrite length_le4; exact HS1)
     (ki_enc_upd mc (ms_set_ignore b) 24 (le4 (Z_to_bv 64 (if b then 1 else 0))) ltac:(lia) S1
        ltac:(rewrite length_le4; lia) (fun fb Ef => mseg_enc_ignore _ fb b Ef))) as (INV1 & MU1 & WM1).
  set (mk1 := write_to_mem mk (Z_to_bv 64 (mseg_addr c gi + 24)) (le4 (Z_to_bv 64 (if b then 1 else 0)))) in *.
  clearbody mk1.
  clear HQ HM HC HX RC HS1.
  set (mc1 := m_upd mc gi (ms_set_ignore b)) in *.
  assert (G1 : (gi < length (mc_seg mc1))%nat) by (unfold mc1; rewrite ki_m_upd_len; exact S1).
  pose proof INV1 as (HC1 & _ & _ & _).
  pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & HWR1 & _).
  assert (HS2 : store_ok rsegs mk1 (wa (mseg_addr c gi + 28)) 4 = true).
  { replace (mseg_addr c gi + 28) with (c + (256 * Z.of_nat gi + 28)) by (unfold mseg_addr, MSEG_SIZE; lia).
    apply (wr_at_store_ok rsegs mk1 c SEG_M_SIZE (256 * Z.of_nat gi + 28) 4 HWR1); unfold SEG_M_SIZE; lia. }
  step. step.
  pose proof (ki_wc_step mk1 Whit mc1 (m_upd mc1 gi (ms_set_ignore_set true)) false false (mseg_addr c gi + 28)
     (le4 (Z_to_bv 64 1))
     INV1 MU1 WM1 ltac:(rewrite length_le4; cbn [inside]; right; left; nlia) ltac:(nlia) ltac:(rewrite length_le4; nlia)
     ltac:(rewrite length_le4; exact HS2)
     (ki_enc_upd mc1 (ms_set_ignore_set true) 28 (le4 (Z_to_bv 64 1)) ltac:(lia) G1
        ltac:(rewrite length_le4; lia) (fun fb Ef => mseg_enc_ignore_set _ fb true Ef))) as (INV2 & MU2 & WM2).
  set (mk2 := write_to_mem mk1 (Z_to_bv 64 (mseg_addr c gi + 28)) (le4 (Z_to_bv 64 1))) in *. clearbody mk2.
  clear INV1 MU1 WM1 HC1 HWR1 HS2.
  set (mc2 := m_upd mc1 gi (ms_set_ignore_set true)) in *.
  assert (G2 : (gi < length (mc_seg mc2))%nat) by (unfold mc2; rewrite ki_m_upd_len; exact G1).
  pose proof INV2 as (HC2 & HX2 & HM2 & HQ2).
  pose proof HC2 as (_ & _ & _ & _ & HR8 & _ & _ & _ & HWR2 & HSL2 & _ & HPE2 & _ & _ & _ & MI2).
  pose proof (ki_rd_bytes _ _ _ HR8) as RR8. rewrite length_le8 in RR8.
  step. step. step. step. step. step.
  destruct (mconf_field_cells rsegs false mk2 c mc2 (256 * Z.of_nat gi + 156) HM2 HWR2 ltac:(lia) ltac:(nlia))
    as [junk HJ].
  pose proof (mconf_reading_cstr rsegs false mk2 c mc2 HM2 HSL2 (ki_mod8 c F8)) as CR.
  change (mc_reading mc2) with (mc_reading mc) in CR.
  pose proof (ki_span_rd c (mc_reading mc) F8 R1) as (SP1 & SP2).
  eapply evt_cut.
  { eapply (mf_snprintf_s HSN) with (lo := Sp - PRINTF_K) (s := mc_reading mc) (junk := junk);
      rewrite ?unsigned_lit by nlia.
    - reflexivity.
    - reflexivity.
    - nlia.
    - exact CR.
    - lia.
    - nlia.
    - nlia.
    - replace (mseg_addr c gi + 156) with (c + (256 * Z.of_nat gi + 156)) by (unfold mseg_addr, MSEG_SIZE; lia).
      exact HJ.
    - nlia.
    - nlia.
    - apply (ki_noimg_sub c SEG_M_SIZE); [exact HNI | nlia | nlia].
    - eapply ki_penv; [exact HPE2 | unfold PRINTF_K; lia | lia].
    - exact (ki_stack_pf mk2 fc0 mc2 false INV2).
    - exact MI2. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & Fq & fc3 & m3 & -> &
              MU3 & WM3 & MI3 & TM3 & FR3 & FF3 & ST3 & BA3).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (ki_firstn_all (mc_reading mc) 95) in MU3, BA3 by lia.
  assert (PB : pf_bytes (mc_reading mc ++ [0]) = zb (mc_reading mc) ++ [ZERO])
    by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
  rewrite PB in BA3.
  rewrite (unsigned_lit (mseg_addr c gi + 156)) in MU3, BA3 by nlia.
  replace (mseg_addr c gi + 156 + Z.of_nat (length (mc_reading mc)) + 1)
    with (mseg_addr c gi + 156 + (Z.of_nat (length (mc_reading mc)) + 1)) in MU3 by lia.
  set (mc3 := m_upd mc2 gi (ms_set_ignore_file (mc_reading mc))).
  assert (G3 : (gi < length (mc_seg mc3))%nat) by (unfold mc3; rewrite ki_m_upd_len; exact G2).
  pose proof (ki_inv_snp mk2 m3 fc0 fc3 mc2 mc3 (Sp - PRINTF_K) (mseg_addr c gi + 156)
     (Z.of_nat (length (mc_reading mc)) + 1) (zb (mc_reading mc) ++ [ZERO]) INV2 ltac:(unfold PRINTF_K; lia)
     ltac:(unfold PRINTF_K; lia) ltac:(nlia) ltac:(nlia)
     ltac:(rewrite length_app, ki_length_zb; cbn [length]; lia) MU3 WM3 MI3 TM3 FR3 ST3 BA3
     (ki_enc_upd mc2 (ms_set_ignore_file (mc_reading mc)) 156 (zb (mc_reading mc) ++ [ZERO]) ltac:(lia) G2
        ltac:(rewrite length_app, ki_length_zb; cbn [length]; lia)
        (fun fb Ef => mseg_enc_ignore_file _ fb (mc_reading mc) Ef R1 R2 R3))) as INV3.
  assert (MU3' : munch Whit m0 m3).
  { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *.
    unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K, mseg_addr, MSEG_SIZE in *. destruct Hx as (X1 & X2 & _).
    split; [lia|]. split; [lia | exact I]. }
  assert (WM3' : wmono rsegs m0 m3) by (eapply wmono_trans; eassumption).
  assert (EQM : ki_set b = mc3).
  { unfold ki_set, ki_rd, mc3, mc2, mc1. rewrite (mf_snprintf_s_model _ R2 R1). rewrite !ki_m_upd_comp.
    apply ki_m_upd_ext. intros x. apply ms_with_ignore_eq. }
  rewrite EQM.
  step. step. step.
  eapply ki_tail with (mcx := mc3) (W := Whit).
  - reflexivity.
  - reflexivity.
  - exact INV3.
  - exact MU3'.
  - exact WM3'.
  - change Whit with ([(Sp0 - M_FILE_STACK, Sp0)] ++ [(mseg_addr c gi, mseg_addr c gi + 256)]).
    apply sub_fp_app; [apply mf_W_frame; lia |].
    pose proof (mf_W_seg Sp0 c k0 mc3 gi 0 256 G3 ltac:(lia) ltac:(unfold MSEG_SIZE; lia)) as H.
    rewrite !Z.add_0_r in H. exact H.
  - exact FF3.
  - exact G3.
  - exact S2.
  - unfold mc3, mc2, mc1, m_upd, m_set_segs. cbn [mc_refused]. lia.
  - unfold mc3, mc2, mc1, m_upd, m_set_segs. cbn [mc_overflow]. lia.
Qed.

(** 0x146b0: s5 = 0, then the stores with ignore = false. *)
Lemma ki_zero : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 t3 t4 t5 t6 : word),
  ki_res = ki_set false -> ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x146b0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 t3 t4 t5 t6 HRES INV MU WM.
  step. eapply (ki_store false); [exact HRES | exact INV | exact MU | exact WM].
Qed.

(** 0x1473c: no word matched; m_refuse(c, line + 1), then 0x14598 and the tail. *)
Lemma ki_refuse_v : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 t3 t4 t5 t6 : word),
  ki_res = m_refuse mc (line + 1) false -> ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x1473c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 t3 t4 t5 t6 HRES INV MU WM.
  rewrite HRES.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  step. step. step.
  eapply (mf_refuse_call HMR 0x14744) with (lo := lo) (sp0 := Sp0) (p := p) (rest := rest) (w := mseg_addr c gi)
    (mc := mc) (knock := false) (ra0 := ra0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11).
  - lia.
  - lia.
  - reflexivity.
  - exact HC.
  - exact HX.
  - exact HQ.
  - exact HM.
  - lia.
  - lia.
  - intros m' F' fc' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HC' HX' HQ' HM' MU' WM' FF'.
    replace (Z_to_bv 64 (0x14744 + 4)) with (Z_to_bv 64 0x14748) by reflexivity.
    step. step. step.
    destruct (m_refuse_sizes mc (line + 1) false) as (Eseg & Ekept).
    eapply ki_tail with (mcx := m_refuse mc (line + 1) false) (W := Wst ++ m_refuse_W Sp c mc).
    + reflexivity.
    + reflexivity.
    + exact (conj HC' (conj HX' (conj HM' HQ'))).
    + eapply munch_trans.
      * eapply munch_weaken; [apply ki_sub_l | exact MU].
      * eapply munch_weaken; [apply ki_sub_r | exact MU'].
    + eapply wmono_trans; eassumption.
    + apply sub_fp_app; [apply mf_W_frame; lia |].
      apply mf_W_refuse; [unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK, PRINTF_K; lia | lia | exact S2].
    + exact FF'.
    + rewrite Eseg. exact S1.
    + lia.
    + unfold m_refuse. cbn [mc_refused]. lia.
    + unfold m_refuse. cbn [mc_overflow]. lia.
Qed.

(** An ieq(v, vl, w) call at X (`jal ieq` at X) from the value chain: the facts after it. *)
Lemma ki_ieq_v : forall mk A wl (R : Z) (Qg : machine_state -> Prop)
    (ra t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word),
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  ra = Z_to_bv 64 R -> 0 <= R < 2 ^ 64 -> R mod 2 = 0 ->
  (forall m, mem_inv rsegs m -> cstr_at rsegs m A wl) -> 0 < A -> A + Z.of_nat (length wl) + 1 <= 0x20000 ->
  (forall m1 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     ki_inv m1 fc0 mc false -> munch Wst m0 m1 -> wmono rsegs m0 m1 ->
     evt rsegs Qg
       (MS (mkR ra sp gp tp x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) (Z_to_bv 64 (b2z (ieq v wl)))
                x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 s7 s8
                (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) x28 x29 x30 x31)
           F0 (Z_to_bv 64 R) fc0 None m1 (seg_rom rsegs))) ->
  evt rsegs Qg
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) (Z_to_bv 64 (p + Z.of_nat ov))
             (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 A) a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 s7 s8
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F0 (Z_to_bv 64 IEQ) fc0 None mk (seg_rom rsegs)).
Proof.
  intros mk A wl R Qg ra t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 INV MU WM ER HR0 HR2 HLIT HA0 HA1 K.
  subst ra.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (ki_text_facts mk HX) as (T1 & T2 & T3 & T4 & T5).
  destruct ki_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & _ & MI).
  eapply evt_cut.
  { eapply HIEQ with (l := zb v) (w := wl) (lo := lo). unfold ieq_pre. rewrite !unsigned_lit by nlia.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    - nlia.
    - destruct HKV as (_ & _ & _ & Ev). rewrite <- Ev. apply (mf_text_bytes mk Sp0 lo c p rest ov vl HX). lia.
    - rewrite ki_length_zb. lia.
    - nlia.
    - lia.
    - exact (HLIT mk MI).
    - nlia.
    - apply (ki_stack_ok mk fc0 mc false); [exact INV | unfold IEQ_STACK, PRINTF_K; lia].
    - exact MI. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MU1 & WM1 &
              MI1 & ST1 & _).
  rewrite ret_pc_even by (first [lia | exact HR2]).
  rewrite (ki_zs_zb v K6).
  assert (INV1 : ki_inv m1 fc0 mc false).
  { eapply ki_inv_call; [exact INV | exact MU1 | exact WM1 | exact MI1 | exact FR | exact ST1 | | | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _). unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK, SEG_M_SIZE. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I]. }
  assert (MU2 : munch Wst m0 m1).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *.
    destruct Hx as (X1 & _). unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *. split; [lia | exact I]. }
  eapply K; [exact INV1 | exact MU2 | eapply wmono_trans; eassumption].
Qed.

(** 0x14728: the one byte '0'. *)
Lemma ki_one0 : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
  ki_vt = false -> ieq v S_no = false -> ieq v S_false = false ->
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x14728 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 1) s6
        (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 HVT HNO HFA INV MU WM.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (ki_text_facts mk HX) as (T1 & T2 & T3 & T4 & T5).
  destruct ki_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  assert (Hb : 0 <= nth ov rest 0 < 256) by (apply ki_nth_byte; exact T2).
  pose proof (mf_text_byte mk Sp0 lo c p rest ov HX ltac:(lia)) as RD.
  step. step.
  rewrite (ki_eqb_lit (Z.of_nat vl) 1) by lia.
  if_cases K; cbv iota; zify_cond K.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1473c) _ _ _ _) =>
      eapply ki_refuse_v; [| exact INV | exact MU | exact WM];
      apply ki_res_n; [exact HVT|];
      unfold ki_vf; rewrite HNO, HFA; cbn [orb];
      destruct (Nat.eqb_spec (length v) 1); [lia | reflexivity]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14730) _ _ _ _) =>
      assert (Hv1 : vl = 1%nat) by lia;
      step; rewrite (ki_zxb (nth ov rest 0) Hb); step; step;
      rewrite (ki_eqb_lit (nth ov rest 0) 48) by lia;
      if_cases KB; cbv iota; zify_cond KB;
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x146b0) _ _ _ _) =>
          eapply ki_zero; [| exact INV | exact MU | exact WM];
          apply ki_res_f; [exact HVT|];
          unfold ki_vf; rewrite HNO, HFA; cbn [orb];
          rewrite (ki_hd0 ltac:(lia)); apply andb_true_iff; split; [apply Nat.eqb_eq; lia | apply Z.eqb_eq; lia]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1473c) _ _ _ _) =>
          eapply ki_refuse_v; [| exact INV | exact MU | exact WM];
          apply ki_res_n; [exact HVT|];
          unfold ki_vf; rewrite HNO, HFA; cbn [orb];
          rewrite (ki_hd0 ltac:(lia)); apply andb_false_iff; right; apply Z.eqb_neq; lia
      end
  end.
Qed.

(** 0x14698: ieq(v, vl, "false"). *)
Lemma ki_false : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
  ki_vt = false -> ieq v S_no = false ->
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x14698 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 1) s6
        (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 HVT HNO INV MU WM.
  step. step. step. step. step.
  eapply (ki_ieq_v mk KI_FALSE S_false 0x146ac); [exact INV | exact MU | exact WM | reflexivity | lia | reflexivity
    | exact ki_at_false | unfold KI_FALSE; lia | change (length S_false) with 5%nat; unfold KI_FALSE; lia |].
  intros m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV1 MU1 WM1.
  destruct (ieq v S_false) eqn:EF; unfold b2z.
  - step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    eapply ki_zero; [| exact INV1 | exact MU1 | exact WM1].
    apply ki_res_f; [exact HVT|]. unfold ki_vf. rewrite HNO, EF. reflexivity.
  - step. if_cases K; cbv iota; [|exfalso; vm_compute in K; discriminate K].
    eapply ki_one0; [exact HVT | exact HNO | exact EF | exact INV1 | exact MU1 | exact WM1].
Qed.

(** 0x14680: ieq(v, vl, "no"). *)
Lemma ki_no : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
  ki_vt = false ->
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x14680 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 1) s6
        (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 HVT INV MU WM.
  step. step. step. step. step.
  eapply (ki_ieq_v mk KI_NO S_no 0x14694); [exact INV | exact MU | exact WM | reflexivity | lia | reflexivity
    | exact ki_at_no | unfold KI_NO; lia | change (length S_no) with 2%nat; unfold KI_NO; lia |].
  intros m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV1 MU1 WM1.
  destruct (ieq v S_no) eqn:EN; unfold b2z.
  - step. if_cases K; cbv iota; [|exfalso; vm_compute in K; discriminate K].
    eapply ki_zero; [| exact INV1 | exact MU1 | exact WM1].
    apply ki_res_f; [exact HVT|]. unfold ki_vf. rewrite EN. reflexivity.
  - step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    eapply ki_false; [exact HVT | exact EN | exact INV1 | exact MU1 | exact WM1].
Qed.

(** 0x1466c: the one byte '1'. *)
Lemma ki_one1 : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
  ieq v S_yes = false -> ieq v S_true = false ->
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x1466c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 1) s6
        (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 0x1ff) t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 HYES HTRUE INV MU WM.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (ki_text_facts mk HX) as (T1 & T2 & T3 & T4 & T5).
  destruct ki_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  assert (Hb : 0 <= nth ov rest 0 < 256) by (apply ki_nth_byte; exact T2).
  pose proof (mf_text_byte mk Sp0 lo c p rest ov HX ltac:(lia)) as RD.
  step. step.
  rewrite (ki_eqb_lit (Z.of_nat vl) 1) by lia.
  if_cases K; cbv iota; zify_cond K.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14680) _ _ _ _) =>
      eapply ki_no; [| exact INV | exact MU | exact WM];
      unfold ki_vt; rewrite HYES, HTRUE; cbn [orb];
      destruct (Nat.eqb_spec (length v) 1); [lia | reflexivity]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14674) _ _ _ _) =>
      assert (Hv1 : vl = 1%nat) by lia;
      step; rewrite (ki_zxb (nth ov rest 0) Hb); step; step;
      rewrite (ki_eqb_lit (nth ov rest 0) 49) by lia;
      if_cases KB; cbv iota; zify_cond KB;
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x146b4) _ _ _ _) =>
          eapply (ki_store true); [| exact INV | exact MU | exact WM];
          apply ki_res_t; unfold ki_vt; rewrite HYES, HTRUE; cbn [orb];
          rewrite (ki_hd0 ltac:(lia)); apply andb_true_iff; split; [apply Nat.eqb_eq; lia | apply Z.eqb_eq; lia]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14680) _ _ _ _) =>
          eapply ki_no; [| exact INV | exact MU | exact WM];
          unfold ki_vt; rewrite HYES, HTRUE; cbn [orb];
          rewrite (ki_hd0 ltac:(lia)); apply andb_false_iff; right; apply Z.eqb_neq; lia
      end
  end.
Qed.

(** 0x14650: ieq(v, vl, "true"), s8 = 0x1ff. *)
Lemma ki_true : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 t3 t4 t5 t6 : word),
  ieq v S_yes = false ->
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x14650 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 1) s6
        (Z_to_bv 64 (Z.of_nat vl)) s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 t3 t4 t5 t6 HYES INV MU WM.
  step. step. step. step. step.
  eapply (ki_ieq_v mk KI_TRUE S_true 0x14664); [exact INV | exact MU | exact WM | reflexivity | lia | reflexivity
    | exact ki_at_true | unfold KI_TRUE; lia | change (length S_true) with 4%nat; unfold KI_TRUE; lia |].
  intros m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV1 MU1 WM1.
  step.
  destruct (ieq v S_true) eqn:ET; unfold b2z.
  - step. if_cases K; cbv iota; [|exfalso; vm_compute in K; discriminate K].
    eapply (ki_store true); [| exact INV1 | exact MU1 | exact WM1].
    apply ki_res_t. unfold ki_vt. rewrite ET. apply orb_true_iff. left. apply orb_true_iff. right. reflexivity.
  - step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    eapply ki_one1; [exact HYES | exact ET | exact INV1 | exact MU1 | exact WM1].
Qed.

(** 0x145b8: ieq(v, vl, "yes"), s5 = 1. *)
Lemma ki_yes : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word),
  ki_inv mk fc0 mc false -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (ki_res, Some gi) line rest))
    (KS 0x145b8 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) s5 s6
        (Z_to_bv 64 (Z.of_nat vl)) s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 INV MU WM.
  step. step. step. step. step.
  eapply (ki_ieq_v mk KI_YES S_yes 0x145cc); [exact INV | exact MU | exact WM | reflexivity | lia | reflexivity
    | exact ki_at_yes | unfold KI_YES; lia | change (length S_yes) with 3%nat; unfold KI_YES; lia |].
  intros m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV1 MU1 WM1.
  step.
  destruct (ieq v S_yes) eqn:EY; unfold b2z.
  - step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    step. step.
    eapply (ki_store true); [| exact INV1 | exact MU1 | exact WM1].
    apply ki_res_t. unfold ki_vt. rewrite EY. reflexivity.
  - step. if_cases K; cbv iota; [|exfalso; vm_compute in K; discriminate K].
    eapply ki_true; [exact EY | exact INV1 | exact MU1 | exact WM1].
Qed.

(** KKNOCK 0x145dc reached from KIGN: the premise H_MF_KKNOCK. *)
Lemma ki_kknock : forall m1 (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  ieq k S_ignore = false -> ki_inv m1 fc0 mc false -> munch Wst m0 m1 -> wmono rsegs m0 m1 ->
  evt rsegs (QP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (KS 0x145dc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
        (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl)) t3 t4 t5 t6
        F0 fc0 m1).
Proof.
  intros m1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EQ (HC & HX & HM & HQ) MU WM.
  pose proof (ki_ctx_facts m1 fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  eapply mf_post_back; [intros r _; reflexivity | exact MU | exact WM | apply mf_W_frame; lia |].
  pose proof HKK as HK. unfold H_MF_KKNOCK, H_MF_KAT, MF_PC_KKNOCK in HK.
  eapply HK; [exact Hn | exact Hne | | | exact HKV |].
  - apply mf_loop_iff. refine (conj HC (conj HX _)). unfold mf_st. refine (conj HM (conj HQ _)).
    cbn [cur_ok]. repeat split; lia.
  - unfold mk_regs. repeat split; reflexivity.
  - constructor; [exact Hrole|]. constructor; [exact Hmodel|]. constructor; [exact EQ | constructor].
Qed.

(** ** KIGN 0x145a0: ieq(k, kl, "ignore"). *)
Lemma ki_main : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs (QP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (KS 0x145a0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
        (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
        t3 t4 t5 t6 F0 fc0 m0).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof ki_inv0 as INV. pose proof INV as (HC & HX & HM & HQ).
  pose proof (ki_ctx_facts m0 fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (ki_text_facts m0 HX) as (T1 & T2 & T3 & T4 & T5).
  destruct ki_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  destruct ki_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & _ & MI).
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HIEQ with (l := zb k) (w := S_ignore) (lo := lo). unfold ieq_pre. rewrite !unsigned_lit by nlia.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    - nlia.
    - destruct HKV as (_ & _ & Ek & _). rewrite <- Ek. apply (mf_text_bytes m0 Sp0 lo c p rest ok kl HX). lia.
    - rewrite ki_length_zb. lia.
    - nlia.
    - unfold KI_IGNORE. lia.
    - exact (ki_at_ignore m0 MI).
    - change (length S_ignore) with 6%nat. unfold KI_IGNORE. nlia.
    - apply (ki_stack_ok m0 fc0 mc false); [exact INV | unfold IEQ_STACK, PRINTF_K; lia].
    - exact MI. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MU & WM &
              MI1 & ST1 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (ki_zs_zb k K5).
  assert (INV1 : ki_inv m1 fc0 mc false).
  { eapply ki_inv_call; [exact INV | exact MU | exact WM | exact MI1 | exact FR | exact ST1 | | | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _). unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK, SEG_M_SIZE. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I]. }
  assert (MU1 : munch Wst m0 m1).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _).
    unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *. split; [lia | exact I]. }
  destruct (ieq k S_ignore) eqn:EQ; unfold b2z.
  - rewrite (ki_disp_ign EQ).
    step. if_cases K; cbv iota; try (exfalso; vm_compute in K; discriminate K).
    eapply ki_yes; [exact INV1 | exact MU1 | exact WM].
  - step. if_cases K; cbv iota; try (exfalso; vm_compute in K; discriminate K).
    eapply ki_kknock; [exact EQ | exact INV1 | exact MU1 | exact WM].
Qed.

End KI.

Lemma mf_kknockp_holds : ieq_contract -> m_refuse_contract -> S_MF_KKNOCKP.
Proof.
  intros HIEQ HMR n HT. unfold H_MF_KKNOCK, H_MF_KAT, MF_PC_KKNOCK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v Hlen Hne HL HR HKV HM.
  destruct HR as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  apply mf_loop_iff in HL. destruct HL as (HC & HX & HS).
  inversion HM as [|w1 r1 Hr HM1]; subst.
  inversion HM1 as [|w2 r2 Hmo HM2]; subst.
  inversion HM2 as [|w3 r3 Hig HM3]; subst.
  eapply ki_kn_main; eassumption.
Qed.

Lemma mf_kignp_holds : ieq_contract -> snprintf_contract -> m_refuse_contract -> S_MF_KIGNP.
Proof.
  intros HIEQ HSN HMR n HT HKK. unfold H_MF_KIGN, H_MF_KAT, MF_PC_KIGN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v Hlen Hne HL HR HKV HM.
  destruct HR as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  apply mf_loop_iff in HL. destruct HL as (HC & HX & HS).
  inversion HM as [|w1 r1 Hr HM1]; subst.
  inversion HM1 as [|w2 r2 Hmo HM2]; subst.
  eapply ki_main; eassumption.
Qed.
