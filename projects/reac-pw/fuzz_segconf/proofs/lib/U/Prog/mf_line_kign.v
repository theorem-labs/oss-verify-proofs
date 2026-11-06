(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the sub-pieces S_MFU_KIGNP and S_MFU_KKNOCKP of S_MF_LINE
    (U/Prog/mfu_cuts.v; family F3, U/Prog/m_file_c.v).

    KIGN 0x1477c (m_key after "role" and "model" missed: s6 = kl, s5 = vl, the cells 0xa0(sp) = k and 0x90(sp) = v,
    cur = Some gi): ieq(k, kl, "ignore") (0x1478c). A miss goes to KKNOCK 0x147cc; this file walks KKNOCK as well
    (kk_walk, from any memory the line has reached), so mfu_kignp_holds does not use its H_MFU_KKNOCK premise. A hit
    tests v: ieq "yes" (0x147a4), ieq "true" (0x14830), vl = 1 and v[0] = '1' (0x14840-0x14854; the NULL trap 0x14844
    is dead: v lies in the text), ieq "no" (0x14864), ieq "false" (0x1487c), vl = 1 and v[0] = '0' (0x14960-0x14978,
    trap 0x14968 dead). A yes-word goes to 0x14888 with s1 = 1, a no-word to 0x14884 (s1 = 0), anything else to the
    refusal 0x146a8. At 0x14888: the g & 3 trap 0x14890 (g = c + 256 gi, c 16-aligned), g->ignore = s1 (`sw`
    0x14898), g->ignore_set = 1 (`sw` 0x148a0), snprintf(g->ignore_file, 96, "%s", c->reading) (0x148b8), the tail.
    The model: mk_disp's ignore branch (ieq k "role" = ieq k "model" = false by the cut's premise).
    KKNOCK 0x147cc: ieq(k, kl, "knock") (0x147dc). A miss refuses at 0x148c8 (mk_disp's last branch). A hit reads
    n_kept (0x147e8): n_kept = 8 refuses with no store (0x147f4 -> 0x146a8: m_refuse adds no kept entry then, so
    knock = false and knock = true give the same model); n_kept <= 7 passes the traps 0x147fc (n_kept >= 8) and 0x14808
    (c + 0x238c + 4 n_kept wraps), stores kept_knock[n_kept] = 1 (0x14818: the block then holds mconf_atp true) and
    refuses with knock = true (0x146b0).
    Every path ends at the tail 0x146b4 through mfu_tail. The current memory is tracked by [kst]: mfu_mid since the
    cut, the frame cells the walk and the tail read ([kc]), frm0 and the FP registers of the cut. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_refuse_c ieq_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists, bytes, words *)
Lemma kg_map_skipn : forall {A B} (f : A -> B) a l, map f (skipn a l) = skipn a (map f l).
Proof. intros A B f. induction a as [|a IH]; intros [|x l]; cbn [skipn map]; auto. Qed.

Lemma kg_map_firstn : forall {A B} (f : A -> B) b l, map f (firstn b l) = firstn b (map f l).
Proof. intros A B f. induction b as [|b IH]; intros [|x l]; cbn [firstn map]; auto. f_equal. apply IH. Qed.

Lemma kg_bat_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

(** The bytes [ok, ok + kl) of a C string: a byte list at p + ok. *)
Lemma kg_text : forall m p rest ok kl k, cstr_at rsegs m p rest -> (ok + kl <= length rest)%nat ->
  firstn kl (skipn ok rest) = k ->
  exists lk, bytes_at rsegs m (p + Z.of_nat ok) lk /\ zs lk = k /\ length lk = kl.
Proof.
  intros m p rest ok kl k (bs & sl & HB & HZ & _ & _) Hk E.
  assert (LB : length bs = length rest) by (rewrite <- HZ; unfold zs; symmetry; apply length_map).
  apply bytes_at_app in HB as [HB _].
  exists (firstn kl (skipn ok bs)). split; [apply kg_bat_sub; [exact HB | lia]|]. split.
  - rewrite <- E, <- HZ. unfold zs. rewrite kg_map_firstn, kg_map_skipn. reflexivity.
  - rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia.
Qed.

Lemma kg_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - rewrite E at 2. rewrite length_app. cbn [length]. lia.
  - rewrite E at 2. lia.
Qed.

Lemma kg_len_pos : forall (l : list Z), l <> [] -> (1 <= length l)%nat.
Proof. intros [|x l] H; [congruence | cbn; lia]. Qed.

Lemma kg_list1 : forall (l : list byte), length l = 1%nat -> l = [nth 0 l ZERO].
Proof. intros [|x [|y r]] H; cbn in H; try lia. reflexivity. Qed.

Lemma kg_len_concat_le8 : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn [map concat length]; [reflexivity|]. rewrite length_app, length_le8, IH. lia. Qed.

Lemma kg_disj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H3 H4]. split; [lia | eapply IH; [exact H4 | exact H1 | exact H2]].
Qed.

Lemma kg_outside_app : forall A B x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof. induction A as [|[lo hi] A IH]; intros B x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

Lemma kg_inside_app : forall A B a n, inside (A ++ B) a n <-> inside A a n \/ inside B a n.
Proof. induction A as [|[lo hi] A IH]; intros B a n; cbn [app inside]; [tauto|]. rewrite IH. tauto. Qed.

Lemma kg_cell_rd : forall m a v, cell8 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold cell8 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as R.
  replace (a + Z.of_nat 0) with a in R by lia. rewrite R. f_equal.
  all: try (cbn [skipn]; apply firstn_all2; rewrite length_le8; lia).
Qed.

Lemma kg_signed_lit : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia. Qed.

Lemma kg_sx32_small : forall x, 0 <= x < 2 ^ 31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

Lemma kg_land3 : forall t, t mod 16 = 0 -> Z.land t 3 = 0.
Proof.
  intros t H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

(** ** The model *)
Lemma kg_mk_ign : forall mc gi k v L, ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = true ->
  mk_disp mc gi k v L =
  if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49))
  then m_upd mc gi (ms_with_ignore true (snprintf_s 96 F_s [AS (mc_reading mc)]))
  else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48))
  then m_upd mc gi (ms_with_ignore false (snprintf_s 96 F_s [AS (mc_reading mc)]))
  else m_refuse mc L false.
Proof. intros mc gi k v L H1 H2 H3. unfold mk_disp. rewrite H1, H2, H3. reflexivity. Qed.

Lemma kg_mk_knock : forall mc gi k v L, ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = false ->
  mk_disp mc gi k v L = if ieq k S_knock then m_refuse mc L true else m_refuse mc L false.
Proof. intros mc gi k v L H1 H2 H3. unfold mk_disp. rewrite H1, H2, H3. reflexivity. Qed.

(** With kept full, m_refuse adds no entry: the knock flag is moot. *)
Lemma kg_refuse_full : forall mc L, length (mc_kept mc) = 8%nat -> m_refuse mc L false = m_refuse mc L true.
Proof. intros mc L H. unfold m_refuse. rewrite H. reflexivity. Qed.

Lemma kg_upd_comp : forall {A} (f g : A -> A) l i, upd_nth i g (upd_nth i f l) = upd_nth i (fun x => g (f x)) l.
Proof. intros A f g. induction l as [|x r IH]; intros [|i]; cbn [upd_nth]; try reflexivity. f_equal. apply IH. Qed.

Lemma kg_upd_ext : forall {A} (f g : A -> A) l i d, (i < length l)%nat -> f (nth i l d) = g (nth i l d) ->
  upd_nth i f l = upd_nth i g l.
Proof.
  intros A f g. induction l as [|x r IH]; intros [|i] d Hi E; cbn [length nth upd_nth] in *; try lia.
  - rewrite E. reflexivity.
  - f_equal. apply (IH i d); [lia | exact E].
Qed.

Lemma kg_ign_eq : forall b g, ms_set_ignore_set true (ms_set_ignore b g) = ms_with_ignore b (ms_ignore_file g) g.
Proof. intros b []. reflexivity. Qed.

(** The two stores 0x14898 / 0x148a0 are ms_with_ignore with the old file field. *)
Lemma kg_upd_ign : forall mc gi b, (gi < length (mc_seg mc))%nat ->
  m_upd (m_upd mc gi (ms_set_ignore b)) gi (ms_set_ignore_set true) =
  m_upd mc gi (ms_with_ignore b (ms_ignore_file (nth gi (mc_seg mc) mseg_d))).
Proof.
  intros mc gi b Hi. unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  f_equal. rewrite kg_upd_comp. apply (kg_upd_ext _ _ _ _ mseg_d Hi). cbv beta. apply kg_ign_eq.
Qed.

Lemma kg_W_upd : forall sp0 c k0 mf i f pend, mfu_W sp0 c k0 (m_upd mf i f) pend = mfu_W sp0 c k0 mf pend.
Proof. intros. unfold mfu_W, M_FILE_W, m_upd, m_set_segs. cbn [mc_seg mc_kept]. rewrite upd_nth_length. reflexivity. Qed.

Lemma kg_upd_len : forall mf i f, length (mc_seg (m_upd mf i f)) = length (mc_seg mf).
Proof. intros. unfold m_upd, m_set_segs. cbn [mc_seg]. apply upd_nth_length. Qed.

(** ** Tactics *)
Ltac kunf := unfold MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING,
  SEG_M_SIZE, MSEG_SIZE, MS_IGNORE, MS_IGNORE_SET, MS_IGNORE_FILE, M_FILE_FRAME, M_FILE_SAVE, M_FILE_STACK,
  M_REFUSE_STACK, PRINTF_K, IEQ_STACK, mseg_addr, kept_addr in *.
Ltac kcond K := zify_cond K; rewrite ?unsigned_lit in K by (kunf; lia).
(** A branch not taken (ntk) or taken (tkn), the other side refuted by arithmetic. *)
Ltac ntk := let K := fresh "K" in if_cases K; [exfalso; kcond K; kunf; Z.div_mod_to_equations; lia | clear K].
Ltac tkn := let K := fresh "K" in if_cases K; [clear K | exfalso; kcond K; kunf; Z.div_mod_to_equations; lia].
Ltac klit := first [ intros mm MI; pose proof (mfu_lits mm MI) as LL; tauto
                   | unfold RO_LO; lia
                   | apply Z.leb_le; vm_compute; reflexivity ].
Ltac kret := rewrite ret_pc_even by (try lia; reflexivity).

(** ** The walk *)
Section Kign.
Hypothesis HIEQ : ieq_contract.
Hypothesis HSNP : snprintf_contract.
Hypothesis HREF : m_refuse_contract.
Variable n : nat.
Hypothesis HT : H_MF_TAIL n.
Variables (sp gp tp : word) (Fc : bvmap 5 word) (fcc : bv 32) (mcut : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (gi k0 : nat)
  (rest : list Z) (ok kl ov vl : nat) (k v : list Z) (lk lv : list byte).
Hypothesis HLEN : (length rest <= n)%nat.
Hypothesis HNE : rest <> [].
Hypothesis HL : m_file_loop mcut fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc (Some gi) line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HCK : cell8 mcut (bv_unsigned sp + 0xa0) (p + Z.of_nat ok).
Hypothesis HCV : cell8 mcut (bv_unsigned sp + 0x90) (p + Z.of_nat ov).
Hypothesis HOK : (ok + kl <= length rest)%nat.
Hypothesis HOV : (ov + vl <= length rest)%nat.
Hypothesis HLK : bytes_at rsegs mcut (p + Z.of_nat ok) lk.
Hypothesis HZK : zs lk = k.
Hypothesis HKL : length lk = kl.
Hypothesis HLV : bytes_at rsegs mcut (p + Z.of_nat ov) lv.
Hypothesis HZV : zs lv = v.
Hypothesis HVL : length lv = vl.
Hypothesis HROLE : ieq k S_role = false.
Hypothesis HMODEL : ieq k S_model = false.

Local Abbreviation KPost mf := (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 Fc mcut lo c k0
  (mf_fin (mf, Some gi) line rest)).
Local Abbreviation RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (mf_next p rest))
       (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK)
       (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6).

(** The bounds the walk needs, from the loop facts of the cut. *)
Lemma kg_facts :
  0 < c /\ c mod 16 = 0 /\ c + 9236 <= 2 ^ 64 /\
  bv_unsigned sp + 272 = bv_unsigned sp0 /\ lo + 6224 <= bv_unsigned sp0 /\ 0 <= lo /\ bv_unsigned sp0 < 2 ^ 63 /\
  (c + 9240 <= lo \/ bv_unsigned sp0 <= c) /\
  0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\
  (p + Z.of_nat (length rest) + 8 <= lo \/ bv_unsigned sp0 <= p) /\
  (p + Z.of_nat (length rest) + 1 <= c \/ c + 9236 <= p) /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
  (gi < length (mc_seg mc))%nat /\ (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat /\
  mc_refused mc + 1 < 2 ^ 32 /\ (1 <= length rest)%nat.
Proof.
  pose proof HL as (E1 & _ & _ & _ & _ & _ & _ & _ & Hc0 & Hc16 & _ & HMC & _ & _ & HAP & HCUR & _ & Hl0 & Hl1 &
                    Href & _ & Hp0 & _ & HCS & HAPp & HAPpc & HPE & _ & _ & HSO & _).
  destruct HMC as (bs & HB & Lbs & Lseg & _ & _ & _ & _ & Lkept & _).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  destruct HCS as (rb & sl & HRB & HZR & _ & _). pose proof (bytes_at_bound _ _ _ _ HRB) as RB.
  rewrite length_app in RB. cbn [length] in RB.
  assert (LR : length rb = length rest) by (rewrite <- HZR; unfold zs; symmetry; apply length_map).
  destruct HSO as ((Hlo & Hhi & _) & Hdep & _ & _).
  destruct HPE as (_ & _ & _ & _ & Hsp63).
  unfold apart in HAP, HAPp, HAPpc. cbv [cur_ok] in HCUR. unfold cstr_span in HAPpc.
  unfold M_FILE_FRAME in E1. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in Hdep. unfold SEG_M_SIZE in Lbs, HAP, HAPpc.
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)) as MB.
  pose proof (kg_len_pos rest HNE) as Hr1.
  repeat split; lia.
Qed.

Ltac kfacts := pose proof kg_facts as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 &
  KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19).

(** The frame cells the walk reads and the tail asks for. *)
Definition kc (m : word -> option byte) : Prop :=
  saved_at rsegs m (bv_unsigned sp + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 m (bv_unsigned sp + 0x8) (- 1 - c) /\ cell8 m (bv_unsigned sp + 0x10) (c + MC_KNOCK) /\
  cell8 m (bv_unsigned sp + 0x18) (- 1 - (c + MC_KNOCK)) /\ cell8 m (bv_unsigned sp + 0x20) (c + MC_READING) /\
  cell8 m (bv_unsigned sp + 0x28) (c + MC_N) /\ cell8 m (bv_unsigned sp + 0x30) (mseg_addr c gi) /\
  cell8 m (bv_unsigned sp + 0xa0) (p + Z.of_nat ok) /\ cell8 m (bv_unsigned sp + 0x90) (p + Z.of_nat ov).

(** The state of the line at memory m: mfu_mid since the cut (model mf, pending knock pend), the cells, frm0 and the
    FP registers of the cut (but fa0). *)
Definition kst (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (mf : mconf) (pend : bool) : Prop :=
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 mf pend /\ kc m /\ frm0 fc /\
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F r = reg_get Fc r).

Lemma kc_transport : forall m m' W, kc m -> munch W m m' -> disjoint_from W (bv_unsigned sp) 272 -> kc m'.
Proof.
  intros m m' W (SV & C8 & C10 & C18 & C20 & C28 & C30 & CA0 & C90) MU D.
  assert (T : forall a bs, bytes_at rsegs m a bs -> bv_unsigned sp <= a ->
              a + Z.of_nat (length bs) <= bv_unsigned sp + 272 -> bytes_at rsegs m' a bs)
    by (intros a bs H H1 H2; eapply bytes_at_transport; [exact H | exact MU | eapply kg_disj_sub; [exact D | exact H1 | exact H2]]).
  unfold kc, cell8, saved_at, M_FILE_SAVE in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))));
    (apply T; [assumption | lia | rewrite ?kg_len_concat_le8, ?length_le8; cbn [length]; lia]).
Qed.

Lemma kc_write : forall m a bs, kc m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (a + Z.of_nat (length bs) <= bv_unsigned sp \/ bv_unsigned sp + 272 <= a) -> kc (write_to_mem m (wa a) bs).
Proof.
  intros m a bs (SV & C8 & C10 & C18 & C20 & C28 & C30 & CA0 & C90) H0 H1 D.
  assert (T : forall a' bs', bytes_at rsegs m a' bs' -> bv_unsigned sp <= a' ->
              a' + Z.of_nat (length bs') <= bv_unsigned sp + 272 -> bytes_at rsegs (write_to_mem m (wa a) bs) a' bs')
    by (intros a' bs' H H2 H3; apply bytes_at_write_other; [exact H | lia | lia | lia]).
  unfold kc, cell8, saved_at, M_FILE_SAVE in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))));
    (apply T; [assumption | lia | rewrite ?kg_len_concat_le8, ?length_le8; cbn [length]; lia]).
Qed.

Lemma kst_init : kst mcut Fc fcc mc false.
Proof.
  pose proof HL as (_ & SV & C8 & C10 & C18 & C20 & C28 & C30 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & _ & _ & _ & _ & (FR & _) & _).
  split; [eapply mfu_mid_init; exact HL|]. split; [|split; [exact FR | intros r _; reflexivity]].
  unfold kc. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.
Qed.

Lemma kst_rd : forall m F fc mf pend, kst m F fc mf pend ->
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 0x10)) 8 = Some (le8 (Z_to_bv 64 (c + MC_KNOCK))) /\
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 0x18)) 8 = Some (le8 (Z_to_bv 64 (- 1 - (c + MC_KNOCK)))) /\
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 0x20)) 8 = Some (le8 (Z_to_bv 64 (c + MC_READING))) /\
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 0x30)) 8 = Some (le8 (Z_to_bv 64 (mseg_addr c gi))) /\
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 0xa0)) 8 = Some (le8 (Z_to_bv 64 (p + Z.of_nat ok))) /\
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 0x90)) 8 = Some (le8 (Z_to_bv 64 (p + Z.of_nat ov))).
Proof.
  intros m F fc mf pend (_ & (_ & _ & C10 & C18 & C20 & _ & C30 & CA0 & C90) & _).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); apply kg_cell_rd; assumption.
Qed.

Lemma kst_kbytes : forall m F fc mf pend, kst m F fc mf pend -> bytes_at rsegs m (p + Z.of_nat ok) lk.
Proof.
  intros m F fc mf pend (MID & _). kfacts.
  eapply mfu_cut_bytes; [exact HL | exact MID | exact HLK | |]; unfold apart, SEG_M_SIZE; rewrite HKL; lia.
Qed.

Lemma kst_vbytes : forall m F fc mf pend, kst m F fc mf pend -> bytes_at rsegs m (p + Z.of_nat ov) lv.
Proof.
  intros m F fc mf pend (MID & _). kfacts.
  eapply mfu_cut_bytes; [exact HL | exact MID | exact HLV | |]; unfold apart, SEG_M_SIZE; rewrite HVL; lia.
Qed.

Lemma kg_vlen : length v = vl.
Proof. rewrite <- HZV, <- HVL. unfold zs. apply length_map. Qed.

Lemma kg_vhd : vl = 1%nat -> hd0 v = bv_unsigned (nth 0 lv ZERO).
Proof.
  intros H1. rewrite <- HZV.
  assert (E : lv = [nth 0 lv ZERO]) by (apply kg_list1; rewrite HVL; exact H1).
  rewrite E at 1. reflexivity.
Qed.

Lemma kst_vbyte : forall m F fc mf pend, kst m F fc mf pend -> vl = 1%nat ->
  ov_read_bytes rsegs m (wa (p + Z.of_nat ov)) 1 = Some [nth 0 lv ZERO].
Proof.
  intros m F fc mf pend KS H1. pose proof (kst_vbytes _ _ _ _ _ KS) as HB.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 1 HB ltac:(rewrite HVL; lia)) as R.
  replace (p + Z.of_nat ov + Z.of_nat 0) with (p + Z.of_nat ov) in R by lia. rewrite R. f_equal.
  assert (E : lv = [nth 0 lv ZERO]) by (apply kg_list1; rewrite HVL; exact H1).
  rewrite E at 1. reflexivity.
Qed.

Lemma kst_store_ok : forall m F fc mf pend a, kst m F fc mf pend -> c <= a -> a + 4 <= c + 9236 ->
  store_ok rsegs m (wa a) 4 = true.
Proof.
  intros m F fc mf pend a ((_ & WM & _) & _) H1 H2.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWR & _).
  pose proof (wr_at_transport rsegs _ _ _ _ HWR WM) as HW.
  replace a with (c + (a - c)) by lia.
  apply (wr_at_store_ok rsegs m c SEG_M_SIZE (a - c) 4 HW); unfold SEG_M_SIZE; lia.
Qed.

(** A 4-byte store into field [off] of seg[gi] (0x14898, 0x148a0). *)
Lemma kst_seg_store_k : forall (P : machine_state -> Prop) R F pc fc rv ro m mf (f : mseg -> mseg) off nb,
  kst m F fc mf false -> (gi < length (mc_seg mf))%nat -> 0 <= off -> off + 4 <= 256 -> length nb = 4%nat ->
  (forall fb, mseg_enc (nth gi (mc_seg mf) mseg_d) fb ->
     mseg_enc (f (nth gi (mc_seg mf) mseg_d)) (upd_bytes fb (Z.to_nat off) nb)) ->
  (forall m', kst m' F fc (m_upd mf gi f) false -> evt rsegs P (MS R F pc fc rv m' ro)) ->
  evt rsegs P (MS R F pc fc rv (write_to_mem m (wa (mseg_addr c gi + off)) nb) ro).
Proof.
  intros P R F pc fc rv ro m mf f off nb KS Hgi Ho1 Ho2 Hnb HENC K.
  pose proof KS as ((MU & WM & MI & ST & MA) & KC & FR & FA). kfacts.
  destruct (mconf_atp_bytes _ _ _ _ _ MA) as (bs0 & _ & HE0 & _).
  destruct (mconf_enc_bounds _ _ _ HE0) as (_ & Lseg & _).
  assert (HS : store_ok rsegs m (wa (mseg_addr c gi + off)) (length nb) = true)
    by (rewrite Hnb; eapply kst_store_ok; [exact KS | unfold mseg_addr, MSEG_SIZE; lia | unfold mseg_addr, MSEG_SIZE; lia]).
  apply K. split; [|split; [|split; [exact FR | exact FA]]].
  - unfold mfu_mid. rewrite kg_W_upd. split; [|split; [|split; [|split]]].
    + apply munch_write; [exact MU | unfold mseg_addr, MSEG_SIZE; lia | rewrite Hnb; unfold mseg_addr, MSEG_SIZE; lia |].
      unfold mfu_W, M_FILE_W. cbn [app inside]. right; left. rewrite Hnb. unfold mseg_addr, MSEG_SIZE. lia.
    + apply wmono_write. exact WM.
    + apply mem_inv_store; [exact MI | exact HS].
    + apply stk_write; [exact ST | unfold mseg_addr, MSEG_SIZE; lia | rewrite Hnb; unfold mseg_addr, MSEG_SIZE; lia].
    + eapply mconf_atp_store;
        [exact MA | unfold mseg_addr, MSEG_SIZE; lia | rewrite Hnb; unfold mseg_addr, MSEG_SIZE, SEG_M_SIZE; lia |].
      intros bs HE.
      replace (Z.to_nat (mseg_addr c gi + off - c)) with (256 * gi + Z.to_nat off)%nat
        by (unfold mseg_addr, MSEG_SIZE; lia).
      apply mconf_enc_seg; [exact HE | exact Hgi | rewrite Hnb; lia | exact HENC].
  - apply kc_write; [exact KC | unfold mseg_addr, MSEG_SIZE; lia | rewrite Hnb; unfold mseg_addr, MSEG_SIZE; lia |].
    rewrite Hnb. unfold mseg_addr, MSEG_SIZE. lia.
Qed.

(** kept_knock[n_kept] = 1 (0x14818), n_kept <= 7: the pending flag. *)
Lemma kst_knock_store_k : forall (P : machine_state -> Prop) R F pc fc rv ro m,
  kst m F fc mc false -> (length (mc_kept mc) < 8)%nat ->
  (forall m', kst m' F fc mc true -> evt rsegs P (MS R F pc fc rv m' ro)) ->
  evt rsegs P (MS R F pc fc rv
    (write_to_mem m (wa (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)))) (le4 (Z_to_bv 64 1))) ro).
Proof.
  intros P R F pc fc rv ro m KS Hn K.
  pose proof KS as ((MU & WM & MI & ST & MA) & KC & FR & FA). kfacts.
  assert (HS : store_ok rsegs m (wa (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc))))
                 (length (le4 (Z_to_bv 64 1))) = true)
    by (rewrite length_le4; eapply kst_store_ok; [exact KS | unfold MC_KNOCK; lia | unfold MC_KNOCK; lia]).
  apply K. split; [|split; [|split; [exact FR | exact FA]]].
  - unfold mfu_mid. split; [|split; [|split; [|split]]].
    + apply munch_write; [ | unfold MC_KNOCK; lia | rewrite length_le4; unfold MC_KNOCK; lia | ].
      * eapply munch_weaken; [|exact MU]. unfold mfu_W, sub_fp. intros x Hx.
        apply kg_outside_app in Hx as [Hx _]. apply kg_outside_app. split; [exact Hx | exact I].
      * unfold mfu_W. apply kg_inside_app. right. cbn [inside]. left. rewrite length_le4. lia.
    + apply wmono_write. exact WM.
    + apply mem_inv_store; [exact MI | exact HS].
    + apply stk_write; [exact ST | unfold MC_KNOCK; lia | rewrite length_le4; unfold MC_KNOCK; lia].
    + eapply mconf_atp_store; [exact MA | unfold MC_KNOCK; lia | rewrite length_le4; unfold MC_KNOCK, SEG_M_SIZE; lia |].
      intros bs HE.
      replace (Z.to_nat (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)) - c))
        with (Z.to_nat MC_KNOCK + 4 * length (mc_kept mc))%nat by (unfold MC_KNOCK; lia).
      apply mconf_enc_knock; [exact HE | exact Hn].
  - apply kc_write; [exact KC | unfold MC_KNOCK; lia | rewrite length_le4; unfold MC_KNOCK; lia |].
    rewrite length_le4. unfold MC_KNOCK. lia.
Qed.

Lemma kg_refuse_disj : disjoint_from (m_refuse_W (bv_unsigned sp) c mc) (bv_unsigned sp) 272.
Proof.
  kfacts. unfold m_refuse_W, M_REFUSE_STACK, PRINTF_K, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED.
  destruct (Z.ltb_spec (Z.of_nat (length (mc_kept mc))) 8); cbn [app disjoint_from]; repeat split; lia.
Qed.

(** `jal ieq` on a byte string of the text and a word literal, through mfu_ieq. *)
Lemma kg_ieq : forall (P : machine_state -> Prop)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mf : mconf) (pend : bool) (l : list byte)
    (a wv : Z) (w : list Z),
  kst m F fc mf pend ->
  bytes_at rsegs m a l -> 0 < a -> apart a (Z.of_nat (length l)) lo (bv_unsigned sp0) ->
  bv_unsigned a0 = a -> bv_unsigned a1 = Z.of_nat (length l) -> bv_unsigned a2 = wv ->
  (forall mm, mem_inv rsegs mm -> cstr_at rsegs mm wv w) -> RO_LO <= wv ->
  wv + Z.of_nat (length w) + 1 <= sa_ro_end SA ->
  (forall (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     kst m' F fc mf pend ->
     evt rsegs P (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b2z (ieq (zs l) w))) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 IEQ) fc None m (seg_rom rsegs)).
Proof.
  intros P ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mf pend l a wv w
    KS HB Ha HAP E0 E1 E2 HW HR1 HR2 K.
  pose proof KS as (MID & KC & FR & FA). pose proof MID as (_ & _ & MI & _).
  apply (mfu_ieq HIEQ) with (fcc := fcc) (mcut := mcut) (lo := lo) (ra0 := ra0) (sp0 := sp0) (e0 := e0) (e1 := e1)
    (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11)
    (c := c) (p := p) (line := line) (mc0 := mc) (cur := Some gi) (k0 := k0) (rest := rest) (mc := mf) (pend := pend)
    (l := l) (w := w).
  - exact HL.
  - exact MID.
  - lia.
  - rewrite E0. exact HB.
  - exact E1.
  - rewrite E0. exact HAP.
  - rewrite E2. unfold RO_LO in HR1. lia.
  - rewrite E2. apply HW. exact MI.
  - rewrite E2. exact HR1.
  - rewrite E2. exact HR2.
  - intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID' MU WM. apply K.
    split; [exact MID'|]. split; [|split; [exact FR | exact FA]].
    eapply kc_transport; [exact KC | exact MU |]. cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I].
Qed.

(** The tail 0x146b4 from any state of the line with model mf (no knock pending). *)
Lemma kg_tail : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (mf : mconf),
  kst m F fc mf false -> mf_grows mc mf -> (gi < length (mc_seg mf))%nat ->
  mc_refused mf <= mc_refused mc + 1 -> mc_overflow mf <= mc_overflow mc + 1 ->
  evt rsegs (KPost mf)
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s5 (Z_to_bv 64 0x1ff) t3 t4 t5 t6)
        F (Z_to_bv 64 M_FILE_TAIL) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc m mf (MID & KC & FR & FA) HG Hgi Hr Ho.
  destruct KC as (SV & C8 & C10 & C18 & C20 & C28 & C30 & _ & _).
  apply (mfu_tail n) with (fcc := fcc) (p := p) (mc := mc) (cur := Some gi).
  all: try assumption.
  all: unfold m_file_regs; repeat (split; [reflexivity|]); reflexivity.
Qed.

(** The refusal 0x146a8 (m_refuse(c, line + 1), knock = pend) and the tail. *)
Lemma kg_refuse : forall (pend : bool) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  kst m F fc mc pend ->
  evt rsegs (KPost (m_refuse mc (line + 1) pend))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s5 (Z_to_bv 64 0x1ff) t3 t4 t5 t6)
        F (Z_to_bv 64 0x146a8) fc None m (seg_rom rsegs)).
Proof.
  intros pend ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc m (MID & KC & FR & FA).
  kfacts.
  step. step. step.
  eapply (mfu_refuse HREF) with (fcc := fcc) (mcut := mcut) (p := p) (mc0 := mc) (cur := Some gi) (mc := mc)
    (pend := pend).
  - exact HL.
  - exact HNE.
  - exact MID.
  - apply mf_grows_refl.
  - reflexivity.
  - exact FR.
  - apply unsigned_lit. lia.
  - apply unsigned_lit. lia.
  - intros m' F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID' MU WM FR' FA'.
    kret.
    destruct (m_refuse_sizes mc (line + 1) pend) as [ES _].
    apply kg_tail.
    + split; [exact MID'|]. split; [eapply kc_transport; [exact KC | exact MU | apply kg_refuse_disj]|].
      split; [exact FR' | intros r Hr; rewrite FA' by exact Hr; apply FA; exact Hr].
    + apply m_refuse_grows.
    + rewrite ES. exact KF15.
    + unfold m_refuse. cbv zeta. cbn [mc_refused]. lia.
    + unfold m_refuse. cbv zeta. cbn [mc_overflow]. lia.
Qed.

(** 0x14888: g->ignore = b, g->ignore_set = 1, snprintf(g->ignore_file, 96, "%s", c->reading), the tail. *)
Lemma kg_store : forall (b : bool) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false ->
  evt rsegs (KPost (m_upd mc gi (ms_with_ignore b (snprintf_s 96 F_s [AS (mc_reading mc)]))))
    (MS (RG ra t0 t1 t2 (Z_to_bv 64 (if b then 1 else 0)) a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 (Z_to_bv 64 0x1ff)
            t3 t4 t5 t6)
        F (Z_to_bv 64 0x14888) fc None m (seg_rom rsegs)).
Proof.
  intros b ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 F fc m KS.
  kfacts.
  assert (HM16 : mseg_addr c gi mod 16 = 0) by (unfold mseg_addr, MSEG_SIZE; Z.div_mod_to_equations; lia).
  pose proof (kst_rd _ _ _ _ _ KS) as (_ & _ & _ & R30 & _ & _).
  step. step.
  match goal with |- context [Z.land ?x 3] =>
    replace (Z.land x 3) with 0
      by (rewrite unsigned_lit by (unfold mseg_addr, MSEG_SIZE; lia);
          first [symmetry; apply kg_land3; exact HM16 | apply kg_land3; exact HM16]) end.
  step. ntk.
  step. clear R30.
  pose proof (kst_store_ok _ _ _ _ _ (mseg_addr c gi + 24) KS ltac:(unfold mseg_addr, MSEG_SIZE; lia)
                ltac:(unfold mseg_addr, MSEG_SIZE; lia)) as HS1.
  step.
  eapply (kst_seg_store_k _ _ _ _ _ _ _ m mc (ms_set_ignore b) 24);
    [exact KS | exact KF15 | lia | lia | apply length_le4 | | ].
  { intros fb HE. exact (mseg_enc_ignore _ _ b HE). }
  intros m2 KS2. clear HS1.
  step.
  pose proof (kst_store_ok _ _ _ _ _ (mseg_addr c gi + 28) KS2 ltac:(unfold mseg_addr, MSEG_SIZE; lia)
                ltac:(unfold mseg_addr, MSEG_SIZE; lia)) as HS2.
  step.
  eapply (kst_seg_store_k _ _ _ _ _ _ _ m2 (m_upd mc gi (ms_set_ignore b)) (ms_set_ignore_set true) 28);
    [exact KS2 | rewrite kg_upd_len; exact KF15 | lia | lia | apply length_le4 | | ].
  { intros fb HE. exact (mseg_enc_ignore_set _ _ true HE). }
  intros m3 KS3. clear HS2.
  rewrite (kg_upd_ign mc gi b KF15) in KS3.
  set (f0 := ms_ignore_file (nth gi (mc_seg mc) mseg_d)) in KS3.
  pose proof KS3 as (MID3 & KC3 & FR3 & FA3).
  pose proof (kst_rd _ _ _ _ _ KS3) as (_ & _ & R20 & _ & _ & _).
  step. step. step. step. step. clear R20.
  step.
  apply (mfu_snprintf_file HSNP) with (fcc := fcc) (mcut := mcut) (lo := lo) (ra0 := ra0) (sp0 := sp0) (e0 := e0)
    (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10)
    (e11 := e11) (c := c) (p := p) (line := line) (mc0 := mc) (cur := Some gi) (k0 := k0) (rest := rest) (mcx := mc)
    (i := gi) (off := MS_IGNORE_FILE) (upd := ms_with_ignore b) (f0 := f0).
  - exact HL.
  - exact MID3.
  - right. split; [reflexivity | exists b; intros; reflexivity].
  - exact KF15.
  - exact FR3.
  - rewrite unsigned_lit by (unfold mseg_addr, MSEG_SIZE; lia). reflexivity.
  - apply unsigned_lit. lia.
  - apply unsigned_lit. lia.
  - apply unsigned_lit. unfold MC_READING. lia.
  - intros m' F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID' MU WM FR' FA'.
    kret. step.
    apply kg_tail.
    + split; [exact MID'|]. split; [eapply kc_transport; [exact KC3 | exact MU |]|].
      * cbn [disjoint_from]. unfold PRINTF_K, mseg_addr, MSEG_SIZE, MS_IGNORE_FILE. repeat split; lia.
      * split; [exact FR' | intros r Hr; rewrite FA' by exact Hr; apply FA3; exact Hr].
    + apply m_upd_grows.
    + rewrite kg_upd_len. exact KF15.
    + unfold m_upd, m_set_segs. cbn [mc_refused]. lia.
    + unfold m_upd, m_set_segs. cbn [mc_overflow]. lia.
Qed.

(** The ignore decision: v is a yes-word ([kg_y]) or a no-word ([kg_n]). *)
Local Abbreviation kg_y := (ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49))).
Local Abbreviation kg_n := (ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48))).

Lemma kg_eq_yes : ieq k S_ignore = true -> kg_y = true ->
  mk_disp mc gi k v (line + 1) = m_upd mc gi (ms_with_ignore true (snprintf_s 96 F_s [AS (mc_reading mc)])).
Proof. intros HI HY. rewrite (kg_mk_ign mc gi k v (line + 1) HROLE HMODEL HI), HY. reflexivity. Qed.

Lemma kg_eq_no : ieq k S_ignore = true -> kg_y = false -> kg_n = true ->
  mk_disp mc gi k v (line + 1) = m_upd mc gi (ms_with_ignore false (snprintf_s 96 F_s [AS (mc_reading mc)])).
Proof. intros HI HY HN. rewrite (kg_mk_ign mc gi k v (line + 1) HROLE HMODEL HI), HY, HN. reflexivity. Qed.

Lemma kg_eq_bad : ieq k S_ignore = true -> kg_y = false -> kg_n = false ->
  mk_disp mc gi k v (line + 1) = m_refuse mc (line + 1) false.
Proof. intros HI HY HN. rewrite (kg_mk_ign mc gi k v (line + 1) HROLE HMODEL HI), HY, HN. reflexivity. Qed.

(** 0x14960: neither word matched; vl = 1 and v[0] = '0' is the last no-word. *)
Lemma kg_zero : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false -> ieq k S_ignore = true -> kg_y = false -> ieq v S_no = false -> ieq v S_false = false ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 0x1ff)
            t3 t4 t5 t6)
        F (Z_to_bv 64 0x14960) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m KS HI HY Hno Hfa.
  kfacts.
  step. if_cases K.
  - (* vl <> 1 *)
    kcond K.
    rewrite (kg_eq_bad HI HY) by (rewrite Hno, Hfa, kg_vlen; replace (vl =? 1)%nat with false
                                   by (symmetry; apply Nat.eqb_neq; lia); reflexivity).
    apply kg_refuse. exact KS.
  - kcond K. assert (H1 : vl = 1%nat) by (Z.div_mod_to_equations; lia).
    pose proof (kst_rd _ _ _ _ _ KS) as (_ & _ & _ & _ & _ & R90).
    pose proof (kst_vbyte _ _ _ _ _ KS H1) as RB.
    step. clear R90. step. ntk.
    step. clear RB.
    step. step. step.
    pose proof (bv_unsigned_in_range 8 (nth 0 lv ZERO)) as Rb. change (bv_modulus 8) with 256 in Rb.
    if_cases K2.
    + (* v[0] <> '0' *)
      kcond K2.
      rewrite (kg_eq_bad HI HY)
        by (rewrite Hno, Hfa, kg_vlen, (kg_vhd H1), H1; cbn [Nat.eqb andb orb];
            apply Z.eqb_neq; Z.div_mod_to_equations; lia).
      apply kg_refuse. exact KS.
    + kcond K2.
      rewrite (kg_eq_no HI HY)
        by (rewrite Hno, Hfa, kg_vlen, (kg_vhd H1), H1; cbn [Nat.eqb andb orb];
            apply Z.eqb_eq; Z.div_mod_to_equations; lia).
      step. step.
      apply (kg_store false). exact KS.
Qed.

(** 0x14858: a0 = v, ieq "no", then ieq "false". *)
Lemma kg_no : forall (ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false -> ieq k S_ignore = true -> kg_y = false ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 (Z_to_bv 64 (p + Z.of_nat ov)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1)
            (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 0x1ff) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14858) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m KS HI HY.
  kfacts.
  step. step. step. step.
  eapply kg_ieq with (l := lv) (a := p + Z.of_nat ov) (wv := 0x10711) (w := S_no) (mf := mc) (pend := false).
  - exact KS.
  - exact (kst_vbytes _ _ _ _ _ KS).
  - lia.
  - unfold apart. rewrite HVL. lia.
  - apply unsigned_lit. lia.
  - rewrite unsigned_lit by lia. rewrite HVL. reflexivity.
  - apply unsigned_lit. lia.
  - klit.
  - klit.
  - klit.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KS1.
    kret. rewrite HZV.
    destruct (ieq v S_no) eqn:Hno; cbn [b2z].
    + step. tkn. step.
      rewrite (kg_eq_no HI HY) by (rewrite Hno; reflexivity).
      apply (kg_store false). exact KS1.
    + step. ntk.
      pose proof (kst_rd _ _ _ _ _ KS1) as (_ & _ & _ & _ & _ & R90).
      step. clear R90. step. step. step. step.
      eapply kg_ieq with (l := lv) (a := p + Z.of_nat ov) (wv := 0x1029d) (w := S_false) (mf := mc) (pend := false).
      * exact KS1.
      * exact (kst_vbytes _ _ _ _ _ KS1).
      * lia.
      * unfold apart. rewrite HVL. lia.
      * apply unsigned_lit. lia.
      * rewrite unsigned_lit by lia. rewrite HVL. reflexivity.
      * apply unsigned_lit. lia.
      * klit.
      * klit.
      * klit.
      * intros m2 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' KS2.
        kret. rewrite HZV.
        destruct (ieq v S_false) eqn:Hfa; cbn [b2z].
        -- step. ntk. step.
           rewrite (kg_eq_no HI HY) by (rewrite Hno, Hfa; reflexivity).
           apply (kg_store false). exact KS2.
        -- step. tkn.
           eapply kg_zero; [exact KS2 | exact HI | exact HY | exact Hno | exact Hfa].
Qed.

(** 0x14820: "yes" missed; ieq "true", then vl = 1 and v[0] = '1'. *)
Lemma kg_true : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false -> ieq k S_ignore = true -> ieq v S_yes = false ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat vl))
            (Z_to_bv 64 (Z.of_nat kl)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14820) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m KS HI Hy.
  kfacts.
  pose proof (kst_rd _ _ _ _ _ KS) as (_ & _ & _ & _ & _ & R90).
  step. clear R90. step. step. step. step.
  eapply kg_ieq with (l := lv) (a := p + Z.of_nat ov) (wv := 0x10517) (w := S_true) (mf := mc) (pend := false).
  - exact KS.
  - exact (kst_vbytes _ _ _ _ _ KS).
  - lia.
  - unfold apart. rewrite HVL. lia.
  - apply unsigned_lit. lia.
  - rewrite unsigned_lit by lia. rewrite HVL. reflexivity.
  - apply unsigned_lit. lia.
  - klit.
  - klit.
  - klit.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KS1.
    kret. rewrite HZV.
    step.
    destruct (ieq v S_true) eqn:Ht; cbn [b2z].
    + step. tkn.
      rewrite kg_eq_yes by (exact HI || (rewrite Hy, Ht; reflexivity)).
      apply (kg_store true). exact KS1.
    + step. ntk.
      pose proof (kst_rd _ _ _ _ _ KS1) as (_ & _ & _ & _ & _ & R90).
      step. clear R90.
      step. if_cases K.
      * (* vl <> 1: to "no" *)
        kcond K.
        apply kg_no; [exact KS1 | exact HI |].
        rewrite Hy, Ht, kg_vlen. replace (vl =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
      * kcond K. assert (H1 : vl = 1%nat) by (Z.div_mod_to_equations; lia).
        pose proof (kst_vbyte _ _ _ _ _ KS1 H1) as RB.
        step. ntk.
        step. clear RB. step. step.
        pose proof (bv_unsigned_in_range 8 (nth 0 lv ZERO)) as Rb. change (bv_modulus 8) with 256 in Rb.
        step. if_cases K2.
        -- (* v[0] = '1' *)
           kcond K2.
           rewrite kg_eq_yes by (exact HI || (rewrite Hy, Ht, kg_vlen, (kg_vhd H1), H1; cbn [Nat.eqb andb orb];
                                              apply Z.eqb_eq; Z.div_mod_to_equations; lia)).
           apply (kg_store true). exact KS1.
        -- kcond K2.
           apply kg_no; [exact KS1 | exact HI |].
           rewrite Hy, Ht, kg_vlen, (kg_vhd H1), H1. cbn [Nat.eqb andb orb].
           apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

(** 0x14794: "ignore" hit; ieq "yes". *)
Lemma kg_hit : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false -> ieq k S_ignore = true ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
            t3 t4 t5 t6)
        F (Z_to_bv 64 0x14794) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m KS HI.
  kfacts.
  pose proof (kst_rd _ _ _ _ _ KS) as (_ & _ & _ & _ & _ & R90).
  step. clear R90. step. step. step. step.
  eapply kg_ieq with (l := lv) (a := p + Z.of_nat ov) (wv := 0x1042f) (w := S_yes) (mf := mc) (pend := false).
  - exact KS.
  - exact (kst_vbytes _ _ _ _ _ KS).
  - lia.
  - unfold apart. rewrite HVL. lia.
  - apply unsigned_lit. lia.
  - rewrite unsigned_lit by lia. rewrite HVL. reflexivity.
  - apply unsigned_lit. lia.
  - klit.
  - klit.
  - klit.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KS1.
    kret. rewrite HZV.
    step. step.
    destruct (ieq v S_yes) eqn:Hy; cbn [b2z].
    + step. ntk. step. step.
      rewrite kg_eq_yes by (exact HI || (rewrite Hy; reflexivity)).
      apply (kg_store true). exact KS1.
    + step. tkn.
      eapply kg_true; [exact KS1 | exact HI | exact Hy].
Qed.

(** KKNOCK 0x147cc from any memory of the line: ieq "knock", then the refusals. *)
Lemma kk_walk : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false -> ieq k S_ignore = false ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
            t3 t4 t5 t6)
        F (Z_to_bv 64 0x147cc) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m KS HI.
  kfacts.
  rewrite (kg_mk_knock mc gi k v (line + 1) HROLE HMODEL HI).
  pose proof (kst_rd _ _ _ _ _ KS) as (_ & _ & _ & _ & RA0 & _).
  step. clear RA0. step. step. step. step.
  eapply kg_ieq with (l := lk) (a := p + Z.of_nat ok) (wv := 0x102a3) (w := S_knock) (mf := mc) (pend := false).
  - exact KS.
  - exact (kst_kbytes _ _ _ _ _ KS).
  - lia.
  - unfold apart. rewrite HKL. lia.
  - apply unsigned_lit. lia.
  - rewrite unsigned_lit by lia. rewrite HKL. reflexivity.
  - apply unsigned_lit. lia.
  - klit.
  - klit.
  - klit.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KS1.
    kret. rewrite HZK.
    step.
    pose proof KS1 as (MID1 & KC1 & FR1 & FA1).
    destruct (ieq k S_knock) eqn:Hk; cbn [b2z].
    + (* knock: n_kept *)
      step. ntk.
      pose proof MID1 as (_ & _ & _ & _ & MA1).
      assert (RN : ov_read_bytes rsegs m1 (wa (c + MC_N + 940)) 4 =
                   Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))))
        by (replace (c + MC_N + 940) with (c + MC_NKEPT) by (unfold MC_N, MC_NKEPT; lia);
            eapply mconf_rd_nkept; exact MA1).
      step. clear RN.
      rewrite (kg_sx32_small (Z.of_nat (length (mc_kept mc)))) by lia.
      step. step. step.
      if_cases K.
      * (* n_kept = 8: no store *)
        kcond K. rewrite ?kg_signed_lit in K by lia.
        assert (H8 : length (mc_kept mc) = 8%nat) by lia.
        rewrite <- (kg_refuse_full mc (line + 1) H8).
        apply kg_refuse. exact KS1.
      * kcond K. rewrite ?kg_signed_lit in K by lia.
        step. step. ntk.
        step.
        match goal with |- context [Z.shiftl ?x 2] =>
          replace (Z.shiftl x 2) with (4 * Z.of_nat (length (mc_kept mc)))
            by (rewrite ?unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia) end.
        pose proof (kst_rd _ _ _ _ _ KS1) as (R10 & R18 & _ & _ & _ & _).
        step. clear R18. step. ntk.
        step. clear R10.
        step. step.
        pose proof (kst_store_ok _ _ _ _ _ (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc))) KS1
                      ltac:(unfold MC_KNOCK; lia) ltac:(unfold MC_KNOCK; lia)) as HS.
        step.
        apply kst_knock_store_k; [exact KS1 | lia |].
        intros m2 KS2. clear HS.
        step.
        apply kg_refuse. exact KS2.
    + (* any other key: m_refuse at 0x148c8 *)
      step. tkn.
      step. step. step.
      eapply (mfu_refuse HREF) with (fcc := fcc) (mcut := mcut) (p := p) (mc0 := mc) (cur := Some gi) (mc := mc)
        (pend := false).
      * exact HL.
      * exact HNE.
      * exact MID1.
      * apply mf_grows_refl.
      * reflexivity.
      * exact FR1.
      * apply unsigned_lit. lia.
      * apply unsigned_lit. lia.
      * intros m' F' fc' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' MID' MU WM FR' FA'.
        kret. step. step.
        destruct (m_refuse_sizes mc (line + 1) false) as [ES _].
        apply kg_tail.
        -- split; [exact MID'|]. split; [eapply kc_transport; [exact KC1 | exact MU | apply kg_refuse_disj]|].
           split; [exact FR' | intros r Hr; rewrite FA' by exact Hr; apply FA1; exact Hr].
        -- apply m_refuse_grows.
        -- rewrite ES. exact KF15.
        -- unfold m_refuse. cbv zeta. cbn [mc_refused]. lia.
        -- unfold m_refuse. cbv zeta. cbn [mc_overflow]. lia.
Qed.

(** KIGN 0x1477c from any memory of the line: ieq "ignore". *)
Lemma kg_main : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  kst m F fc mc false ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
            t3 t4 t5 t6)
        F (Z_to_bv 64 0x1477c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m KS.
  kfacts.
  pose proof (kst_rd _ _ _ _ _ KS) as (_ & _ & _ & _ & RA0 & _).
  step. clear RA0. step. step. step. step.
  eapply kg_ieq with (l := lk) (a := p + Z.of_nat ok) (wv := 0x1054f) (w := S_ignore) (mf := mc) (pend := false).
  - exact KS.
  - exact (kst_kbytes _ _ _ _ _ KS).
  - lia.
  - unfold apart. rewrite HKL. lia.
  - apply unsigned_lit. lia.
  - rewrite unsigned_lit by lia. rewrite HKL. reflexivity.
  - apply unsigned_lit. lia.
  - klit.
  - klit.
  - klit.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KS1.
    kret. rewrite HZK.
    destruct (ieq k S_ignore) eqn:HI; cbn [b2z].
    + step. ntk. eapply kg_hit; [exact KS1 | exact HI].
    + step. tkn. eapply kk_walk; [exact KS1 | exact HI].
Qed.

(** The two cuts. *)
Lemma kign_cut : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
            t3 t4 t5 t6)
        Fc (Z_to_bv 64 MFU_PC_KIGN) fcc None mcut (seg_rom rsegs)).
Proof. intros. apply kg_main. exact kst_init. Qed.

Lemma kknock_cut : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  ieq k S_ignore = false ->
  evt rsegs (KPost (mk_disp mc gi k v (line + 1)))
    (MS (RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
            t3 t4 t5 t6)
        Fc (Z_to_bv 64 MFU_PC_KKNOCK) fcc None mcut (seg_rom rsegs)).
Proof. intros. apply kk_walk; [exact kst_init | assumption]. Qed.

End Kign.

(** ** The sub-pieces *)
Lemma mfu_kignp_holds : ieq_contract -> snprintf_contract -> m_refuse_contract -> S_MFU_KIGNP.
Proof.
  intros HIEQ HSNP HREF n HT _. unfold H_MFU_KIGN, H_MFU_KAT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v
    HLEN HNE HL HR HS6 HS5 HCK HCV _ HKV HW.
  destruct HR as (E0 & E2 & E3 & E7 & E8 & E9 & E10 & E11). subst s0 s2 s3 s5 s6 s7 s8 s9 s10 s11.
  pose proof (Forall_inv HW) as HROLE. pose proof (Forall_inv (Forall_inv_tail HW)) as HMODEL.
  cbv beta in HROLE, HMODEL.
  destruct HKV as (Hok & Hov & Ek & Ev).
  pose proof (kg_line_le rest) as Lle.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    HCS & _).
  destruct (kg_text _ _ _ ok kl k HCS ltac:(lia) Ek) as (lk & HLK & HZK & HKL).
  destruct (kg_text _ _ _ ov vl v HCS ltac:(lia) Ev) as (lv & HLV & HZV & HVL).
  eapply kign_cut with (lk := lk) (lv := lv) (ok := ok) (ov := ov).
  all: first [eassumption | lia].
Qed.

Lemma mfu_kknockp_holds : ieq_contract -> m_refuse_contract -> S_MFU_KKNOCKP.
Proof.
  intros HIEQ HREF n HT. unfold H_MFU_KKNOCK, H_MFU_KAT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v
    HLEN HNE HL HR HS6 HS5 HCK HCV _ HKV HW.
  destruct HR as (E0 & E2 & E3 & E7 & E8 & E9 & E10 & E11). subst s0 s2 s3 s5 s6 s7 s8 s9 s10 s11.
  pose proof (Forall_inv HW) as HROLE. pose proof (Forall_inv (Forall_inv_tail HW)) as HMODEL.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HW))) as HIGN. cbv beta in HROLE, HMODEL, HIGN.
  destruct HKV as (Hok & Hov & Ek & Ev).
  pose proof (kg_line_le rest) as Lle.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    HCS & _).
  destruct (kg_text _ _ _ ok kl k HCS ltac:(lia) Ek) as (lk & HLK & HZK & HKL).
  destruct (kg_text _ _ _ ov vl v HCS ltac:(lia) Ev) as (lv & HLV & HZV & HVL).
  eapply kknock_cut with (lk := lk) (lv := lv) (ok := ok) (ov := ov).
  all: first [eassumption | lia].
Qed.
