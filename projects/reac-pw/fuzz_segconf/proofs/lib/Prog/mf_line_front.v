(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-pieces S_MF_FRONT and S_MF_LONGP of the line piece
    S_MF_LINE (Prog/mf_cuts.v, family F3). Segment lemmas of m_file's walk; Prog/mf_line.v composes them into
    S_MF_LINE.

    Code (the plain build's disassembly):
      HEAD 0x1407c  s5 = p; nl = strchr(p, '\n') (0x14088, s4 = s6 = nl); nl = 0: s6 = p + strlen(p) (0x1409c);
                    s2 = nl + 1 or s6 (= mf_next p rest); JOIN 0x140b0 a0 = s6 - s5; s3 = line + 1 (`addiw`);
                    `bge s8, a0` 0x140b8: 511 >= |l| goes to the short line 0x140e0, else LONG 0x140bc.
      0x140e0       |l| = 0 skips to the strip; the comment scan 0x140ec-0x14114 (a0 = p + q, a1 = -q; a mark ';'
                    or '#' at q cuts when q = 0 or q[-1] is '\t' or ' '), CUTEND 0x14118 s6 = the cut end.
      STRIP 0x1411c forward over the blanks 0x14124-0x14144 (a0 counts down), BACK0 0x14148, backward 0x14154-0x14170.
      DISP 0x14174  s5 = s6: the empty stripped line goes to the tail 0x143d4; else '[' goes to HDR 0x14188, other
                    bytes to KEY 0x14200 (a2 = s6 - s5).
      LONG 0x140bc  the blank skip 0x140c0-0x140dc; a non-blank byte b (0x143b0-0x143c4): the cur cell 0x20(sp) &=
                    (b = '[' ? 0 : -1); 0x143c8 m_refuse(c, line + 1) (`jal` 0x143d0), then the tail 0x143d4.
    The callees' writes before a cut are strchr's frame [sp - 32, sp) only (strlen writes nothing); the long line
    adds the cur cell and m_refuse's footprint. Each is moved back to the cut's memory with mf_common.mf_post_back.
    The blank test is SegModel.blank on the shift mask 0x100002200 (fr_blank_mask0, fr_blank_mask1). *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c
  mf_cuts mfu_facts mf_common mfp_facts m_refuse_c strchr_c strlen_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Helpers *)
Definition fr_hide (P : Prop) : Prop := P.

Lemma fr_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.

Lemma fr_word : forall (x : word) e, bv_unsigned x = e -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- H. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma fr_signed : forall e, 0 <= e < 2 ^ 63 -> bv_signed (Z_to_bv 64 e) = e.
Proof. intros e He. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec e (2 ^ 63)); lia. Qed.

Lemma fr_swrap : forall x, 0 <= x < 2 ^ 31 -> Z_to_bv 64 (bv_swrap 32 x) = Z_to_bv 64 x.
Proof. intros x Hx. rewrite bv_swrap_small; [reflexivity|]. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma fr_negmod0 : forall q, 0 <= q < 2 ^ 64 -> ((- q) mod 2 ^ 64 = 0 <-> q = 0).
Proof.
  intros q Hq. split; intros H; [|subst; reflexivity].
  destruct (Z.eq_dec q 0) as [|Hn]; [assumption|]. exfalso.
  rewrite Z.mod_opp_l_nz in H by (try lia; rewrite Z.mod_small by lia; lia).
  rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma fr_negmod_step : forall q : nat, ((- Z.of_nat q) mod 2 ^ 64 + -1) mod 2 ^ 64 = (- Z.of_nat (S q)) mod 2 ^ 64.
Proof. intros q. rewrite Zplus_mod_idemp_l. f_equal. lia. Qed.

Lemma fr_len_pos : forall l : list Z, l <> [] -> (0 < length l)%nat.
Proof. intros [|x l] H; [congruence|]. cbn [length]. lia. Qed.

(** The blank test of the loops: `bltu 0x20, c`, then bit c of 0x100002200 = 2^32 + 2^13 + 2^9. *)
Lemma fr_blank_le32 : forall c, blank c = true -> c <= 32.
Proof.
  intros c H. unfold blank in H.
  destruct (c =? 32) eqn:E1; [apply Z.eqb_eq in E1; lia|].
  destruct (c =? 9) eqn:E2; [apply Z.eqb_eq in E2; lia|].
  destruct (c =? 13) eqn:E3; [apply Z.eqb_eq in E3; lia|]. discriminate.
Qed.

Lemma fr_blank_mask_b : forall c, 0 <= c <= 32 ->
  (Z.land (Z.shiftr 4294976000 (c mod 64)) 1 =? 0) = negb (blank c).
Proof.
  intros c Hc. destruct (Z_of_nat_complete c ltac:(lia)) as [k ->].
  assert (Hk : (k <= 32)%nat) by lia. clear Hc.
  do 33 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma fr_blank_mask0 : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr 4294976000 (c mod 64)) 1 = 0 -> blank c = false.
Proof.
  intros c Hc H. pose proof (fr_blank_mask_b c Hc) as E. apply Z.eqb_eq in H. rewrite H in E.
  destruct (blank c); [discriminate | reflexivity].
Qed.

Lemma fr_blank_mask1 : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr 4294976000 (c mod 64)) 1 <> 0 -> blank c = true.
Proof.
  intros c Hc H. pose proof (fr_blank_mask_b c Hc) as E. apply Z.eqb_neq in H. rewrite H in E.
  destruct (blank c); [reflexivity | discriminate].
Qed.

Lemma fr_gt32 : forall c, 32 < c -> blank c = false.
Proof. intros c H. destruct (blank c) eqn:E; [apply fr_blank_le32 in E; lia | reflexivity]. Qed.

(** The cur cell's mask (0x143b0-0x143c0): b = '[' clears it, any other byte keeps it. *)
Lemma fr_mask : forall b cp, 0 <= b < 256 -> 0 <= cp < 2 ^ 64 ->
  Z.land ((Z.b2z ((b + -91) mod 2 ^ 64 <? 1) + -1) mod 2 ^ 64) cp = if b =? 91 then 0 else cp.
Proof.
  intros b cp Hb Hc. destruct (Z.eqb_spec b 91) as [->|NE]; [reflexivity|].
  assert (E1 : ((b + -91) mod 2 ^ 64 <? 1) = false) by (apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  rewrite E1. replace ((Z.b2z false + -1) mod 2 ^ 64) with (Z.ones 64) by reflexivity.
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** ** Lists *)
Lemma fr_nth_firstn : forall (l : list Z) q k, (k < q)%nat -> nth k (firstn q l) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros [|q] [|k] H; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma fr_slice_firstn : forall (l : list Z) q i j, (j <= q)%nat -> slice i j (firstn q l) = slice i j l.
Proof. intros l q i j H. unfold slice. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia. Qed.

Lemma fr_slice_nil : forall (l : list Z) i, slice i i l = [].
Proof. intros. unfold slice. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma fr_hd0_fs : forall (l : list Z) i k, (0 < k)%nat -> (i < length l)%nat -> hd0 (firstn k (skipn i l)) = nth i l 0.
Proof.
  induction l as [|x l IH]; intros [|i] k Hk Hi; cbn [length] in Hi; try lia.
  - destruct k as [|k]; [lia|]. reflexivity.
  - cbn [skipn nth]. apply IH; lia.
Qed.

Lemma fr_hd0_slice : forall (l : list Z) i j, (i < j)%nat -> (j <= length l)%nat -> hd0 (slice i j l) = nth i l 0.
Proof. intros l i j H1 H2. unfold slice. apply fr_hd0_fs; lia. Qed.

Lemma fr_slice_ne : forall (l : list Z) i j, (i < j)%nat -> (j <= length l)%nat -> slice i j l <> [].
Proof.
  intros l i j H1 H2 E. pose proof (slice_length l i j ltac:(lia)) as L. rewrite E in L. cbn [length] in L. lia.
Qed.

Lemma fr_memchr_app : forall (l r : list Z) c, ~ In c l -> memchr (l ++ c :: r) c = Some (length l).
Proof.
  induction l as [|x l IH]; intros r c H; cbn.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec x c) as [E|E]; [exfalso; apply H; left; exact E|].
    rewrite IH by (intros Hi; apply H; right; exact Hi). reflexivity.
Qed.

Lemma fr_memchr_none : forall (l : list Z) c, ~ In c l -> memchr l c = None.
Proof.
  induction l as [|x l IH]; intros c H; cbn; [reflexivity|].
  destruct (Z.eqb_spec x c) as [E|E]; [exfalso; apply H; left; exact E|].
  rewrite IH by (intros Hi; apply H; right; exact Hi). reflexivity.
Qed.

Lemma fr_line_nonl : forall rest, ~ In NL (mf_line rest).
Proof.
  intros rest. exact (proj1 (break_nl_spec rest (mf_line rest) (mf_rest rest) (surjective_pairing _))).
Qed.

Lemma fr_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i H. destruct (mf_line_rest rest) as [[E _] | [E _]].
  - rewrite E at 1. rewrite app_nth1 by exact H. reflexivity.
  - rewrite E at 1. reflexivity.
Qed.

Lemma fr_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _] | [E _]].
  - rewrite E at 2. rewrite length_app. cbn [length]. lia.
  - rewrite E at 2. lia.
Qed.

Lemma fr_cut_at_eq : forall l q, cut_at l q =
  ((nth q l 0 =? 35) || (nth q l 0 =? 59)) && ((q =? 0)%nat || ((nth (q - 1) l 0 =? 32) || (nth (q - 1) l 0 =? 9))).
Proof. reflexivity. Qed.

(** ** The text *)
Lemma fr_byte : forall m sp0 lo c p rest i, mf_text m sp0 lo c p rest -> 0 <= nth i rest 0 < 256.
Proof.
  intros m sp0 lo c p rest i T. destruct (mf_text_props _ _ _ _ _ _ T) as (_ & FA & _).
  destruct (Nat.lt_ge_cases i (length rest)) as [Hi|Hi].
  - rewrite Forall_forall in FA. apply FA. apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. lia.
Qed.

Lemma fr_rd : forall m sp0 lo c p rest (i : nat) (x : word),
  mf_text m sp0 lo c p rest -> (i <= length rest)%nat -> bv_unsigned x = p + Z.of_nat i ->
  ov_read_bytes rsegs m x 1 = Some [Z_to_bv 8 (nth i rest 0)].
Proof.
  intros m sp0 lo c p rest i x T Hi Hx. rewrite <- (wa_of_var x (p + Z.of_nat i) Hx).
  apply (mf_text_byte m sp0 lo c p rest i T Hi).
Qed.

Lemma fr_rd1 : forall m sp0 lo c p rest (i : nat) (y : word),
  mf_text m sp0 lo c p rest -> (i < length rest)%nat -> bv_unsigned y = p + Z.of_nat (S i) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned y + -1)) 1 = Some [Z_to_bv 8 (nth i rest 0)].
Proof.
  intros m sp0 lo c p rest i y T Hi Hy.
  rewrite <- (wa_of_Z_to_bv (bv_unsigned y + -1) (p + Z.of_nat i)) by lia.
  apply (mf_text_byte m sp0 lo c p rest i T). lia.
Qed.

(** The C string at a with only the slack up to the next 8-byte boundary (strchr's premise keeps it apart from the
    stack). *)
Lemma fr_cstr : forall m a s, cstr_at rsegs m a s ->
  exists bs sl, bytes_at rsegs m a (bs ++ ZERO :: sl) /\ zs bs = s /\ ~ In ZERO bs /\ length bs = length s /\
    (length sl <= 7)%nat /\ fr_hide ((- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl)).
Proof.
  intros m a s (bs & sl0 & BY & ZS & NZ & SL).
  assert (LB : length bs = length s) by (rewrite <- ZS; unfold zs; rewrite length_map; reflexivity).
  rewrite <- LB in SL.
  set (k := Z.to_nat ((- (a + Z.of_nat (length bs) + 1)) mod 8)).
  assert (Hk8 : 0 <= (- (a + Z.of_nat (length bs) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  exists bs, (firstn k sl0). split; [|split; [exact ZS|split; [|split; [exact LB|split]]]].
  - assert (BY2 : bytes_at rsegs m a ((bs ++ ZERO :: firstn k sl0) ++ skipn k sl0))
      by (rewrite <- app_assoc; cbn [app]; rewrite firstn_skipn; exact BY).
    apply bytes_at_app in BY2. exact (proj1 BY2).
  - apply SegBridge.nul_free_bytes. rewrite ZS. exact NZ.
  - rewrite length_firstn. lia.
  - unfold fr_hide. rewrite length_firstn. lia.
Qed.

(** strchr(p, '\n') on the text left: the first '\n' is the end of the line, or there is none. *)
Lemma fr_strchr_nl : forall p rest (bs : list byte), zs bs = rest -> ~ In 0 rest -> 0 < p ->
  p + Z.of_nat (length rest) < 2 ^ 64 -> rest = mf_line rest ++ NL :: mf_rest rest ->
  strchr_val (bv_unsigned (Z_to_bv 64 p)) (bv_unsigned (Z_to_bv 64 10) mod 256) bs =
    p + Z.of_nat (length (mf_line rest)).
Proof.
  intros p rest bs ZS NZ Hp Hl E.
  rewrite (unsigned_lit p), (unsigned_lit 10), (Z.mod_small 10 256) by lia.
  rewrite SegBridge.bridge_strchr by (try lia; apply SegBridge.nul_free_bytes; rewrite ZS; exact NZ).
  rewrite ZS, strchr_memchr by (try exact NZ; lia).
  rewrite E at 1. rewrite fr_memchr_app by apply fr_line_nonl. reflexivity.
Qed.

Lemma fr_strchr_none : forall p rest (bs : list byte), zs bs = rest -> ~ In 0 rest -> 0 < p ->
  p + Z.of_nat (length rest) < 2 ^ 64 -> rest = mf_line rest ->
  strchr_val (bv_unsigned (Z_to_bv 64 p)) (bv_unsigned (Z_to_bv 64 10) mod 256) bs = 0.
Proof.
  intros p rest bs ZS NZ Hp Hl E.
  rewrite (unsigned_lit p), (unsigned_lit 10), (Z.mod_small 10 256) by lia.
  rewrite SegBridge.bridge_strchr by (try lia; apply SegBridge.nul_free_bytes; rewrite ZS; exact NZ).
  rewrite ZS, strchr_memchr by (try exact NZ; lia).
  rewrite fr_memchr_none; [reflexivity|]. rewrite E. apply fr_line_nonl.
Qed.

(** ** Memory *)
Lemma fr_bat_read : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H (le_n _)) as R.
  replace (a + Z.of_nat 0) with a in R by lia. rewrite R. f_equal. exact (firstn_all bs).
Qed.

Lemma fr_stk_store : forall m lo hi a (j : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok rsegs m (wa a) j = true.
Proof.
  intros m lo hi a j (H1 & H2 & H) Ha Hj.
  rewrite <- (Z.add_0_r a). apply (wr_at_store_ok rsegs m a (Z.of_nat j) 0 j); [|lia|lia].
  split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

(** The loop facts after a callee that writes only below sp (strchr's frame, strlen: nothing). *)
Lemma fr_loop_below : forall m m1 fc sp0 sp lo c p mc cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  munch [(lo, sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo sp ->
  m_file_loop m1 fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m m1 fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 HL MU WM MI ST.
  apply mf_loop_iff in HL. destruct HL as (CTX & TXT & MC & CELL & REST).
  pose proof CTX as CTX0.
  destruct CTX0 as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & PE & _ & _ & SO & _).
  unfold M_FILE_FRAME in Hsp.
  assert (W1 : sub_fp [(lo, sp)] [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)])
    by (intros x Hx; cbn [outside] in *; tauto).
  assert (TM : MemNorm.task_mem rsegs m1)
    by (eapply mf_task_mem with (pend := false); [exact CTX | exact MC | exact MU | exact W1]).
  assert (ST1 : stk rsegs m1 lo sp0).
  { eapply mf_stk_after; [exact (proj1 SO) | exact MU | exact WM | exact ST | lia |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CTX1 : mf_ctx m1 fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
    by (eapply mf_ctx_transport; [exact CTX | exact MU | exact WM | exact MI | exact TM | exact (proj1 PE)
                                  | exact ST1 | exact W1]).
  assert (TXT1 : mf_text m1 sp0 lo c p rest).
  { eapply mf_text_transport; [exact TXT | exact MU |].
    intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  apply mf_loop_iff. split; [exact CTX1|]. split; [exact TXT1|]. split; [|split; [|exact REST]].
  - destruct MC as (bs & BY & ENC). exists bs. split; [|exact ENC].
    eapply bytes_at_transport; [exact BY | exact MU |]. destruct ENC as (EL & _).
    unfold apart in Hap. cbn [disjoint_from]. split; [lia | exact I].
  - unfold cell8 in *. eapply bytes_at_transport; [exact CELL | exact MU |].
    cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
Qed.

Lemma fr_cur_range : forall m fc sp0 sp lo c mc cur ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 -> mconf_at rsegs m c mc -> cur_ok mc cur ->
  0 <= cur_ptr c cur < 2 ^ 64.
Proof.
  intros m fc sp0 sp lo c mc cur ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 CTX (bs & _ & ENC) CO.
  apply mf_ctx_bounds in CTX. destruct CTX as (_ & _ & _ & _ & _ & _ & C0 & C1).
  destruct ENC as (_ & S32 & _).
  destruct cur as [i|]; cbn [cur_ptr cur_ok] in *; [|lia].
  unfold mseg_addr, MSEG_SIZE. unfold SEG_M_SIZE in C1. lia.
Qed.

Lemma fr_loop_facts : forall m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\ (length (mf_line rest) <= length rest)%nat /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535.
Proof.
  intros m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 H.
  apply mf_loop_iff in H. destruct H as (_ & TXT & (_ & _ & _ & _ & L0 & L1 & _)).
  destruct (mf_text_props _ _ _ _ _ _ TXT) as (_ & _ & P0 & P1 & _).
  unfold cstr_span in P1. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)).
  pose proof (fr_line_len rest). repeat split; lia.
Qed.

Lemma fr_loop_text : forall m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text m sp0 lo c p rest.
Proof.
  intros m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 H.
  apply mf_loop_iff in H. exact (proj1 (proj2 H)).
Qed.

(** ** S_MF_LONGP *)
Section Long.
Variable n : nat.
Hypothesis HT : H_MF_TAIL n.
Hypothesis HMR : m_refuse_contract.

(** 0x143c8: m_refuse(c, line + 1) (knock false) at the `jal` 0x143d0, then the tail with the refused state. *)
Lemma fr_lref : forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z),
  (length rest <= n)%nat -> rest <> [] ->
  mf_ctx m fc (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text m (bv_unsigned sp0) lo c p rest ->
  mconf_at rsegs m c mc -> cell8 m (bv_unsigned sp + 0x20) (cur_ptr c cur) -> cur_ok mc cur ->
  (k0 <= length (mc_kept mc))%nat -> 0 <= line -> line + Z.of_nat (length rest) <= 65535 ->
  mc_refused mc + Z.of_nat (length rest) < 2 ^ 32 -> mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32 ->
  evt rsegs
    (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
       (mf_fin (m_refuse mc (line + 1) false, cur) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F (Z_to_bv 64 0x143c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6
    e7 e8 e9 e10 e11 c p line mc cur k0 rest HN HNE CTX TXT MC CELL CO K0 L0 L1 RF OV.
  pose proof (fr_len_pos rest HNE) as LP. pose proof (mf_rest_lt rest HNE) as RL.
  pose proof CTX as CTX0. destruct CTX0 as (Hsp & _). unfold M_FILE_FRAME in Hsp.
  destruct (m_refuse_sizes mc (line + 1) false) as [ES EK].
  assert (RF1 : mc_refused (m_refuse mc (line + 1) false) = mc_refused mc + 1) by reflexivity.
  assert (OV1 : mc_overflow (m_refuse mc (line + 1) false) = mc_overflow mc) by reflexivity.
  step. step. step.
  eapply (mf_refuse_call HMR 0x143d0) with (p := p) (rest := rest) (w := cur_ptr c cur) (knock := false);
    [lia | lia | reflexivity | exact CTX | exact TXT | exact CELL | exact MC | lia | lia |].
  intros m' F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CTX' TXT' CELL' MC' MU' WM' FR'.
  eapply (mf_post_back ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F F' m m' lo c k0 _
            (m_refuse_W (bv_unsigned sp) c mc)); [exact FR' | exact MU' | exact WM' | |].
  { apply (sub_fp_trans _ (M_FILE_W (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false))).
    - apply mf_W_refuse; [unfold M_FILE_STACK, M_REFUSE_STACK, M_FILE_FRAME; lia | lia | exact K0].
    - apply (mf_W_fin (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false, cur) line rest).
      cbn [fst snd]. unfold mf_cur_ok. destruct cur as [i|]; [|exact I]. cbn [cur_ok] in CO. rewrite ES. exact CO. }
  unfold mf_post, mf_fin.
  pose proof HT as HT'. unfold H_MF_TAIL in HT'.
  eapply HT'; [lia | |].
  - eapply mf_tail_loop; [exact CTX' | exact TXT' | exact HNE | exact MC' | exact CELL' | | | exact L0 | exact L1 | |].
    + destruct cur as [i|]; [|exact I]. cbn [cur_ok] in *. rewrite ES. exact CO.
    + lia.
    + rewrite RF1. lia.
    + rewrite OV1. lia.
  - unfold m_file_regs. repeat split.
Qed.

Section LongS.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
  (k0 : nat) (rest : list Z).
Hypothesis HN : (length rest <= n)%nat.
Hypothesis HNE : rest <> [].
Hypothesis HLP : fr_hide (m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11).
Hypothesis HLG : (512 <= length (mf_line rest))%nat.

Local Abbreviation POSTL cur' := (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
  (mf_fin (m_refuse mc (line + 1) false, cur') line rest)).
Local Abbreviation LST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 pc :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
         (Z_to_bv 64 4294976000) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(** 0x143c4: `sd a1, 0x20(sp)` stores the new cur, then 0x143c8. *)
Lemma fr_lst : forall (cur' : option nat) (ra t0 t1 t2 a0 x11 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word),
  x11 = Z_to_bv 64 (cur_ptr c cur') -> cur_ok mc cur' ->
  evt rsegs (POSTL cur') (LST ra t0 t1 t2 a0 x11 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 0x143c4).
Proof.
  intros cur' ra t0 t1 t2 a0 x11 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 E11 CO'. subst x11.
  pose proof HLP as H. unfold fr_hide in H. apply mf_loop_iff in H.
  destruct H as (CTX & TXT & MC & CELL & CO & K0 & L0 & L1 & RF & OV).
  pose proof CTX as CTX0.
  destruct CTX0 as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & PE & _ & _ & SO & MI).
  unfold M_FILE_FRAME in Hsp.
  pose proof (proj1 SO) as ST0.
  pose proof (proj1 (proj2 SO)) as DEEP. unfold M_FILE_STACK, PRINTF_K, M_FILE_FRAME in DEEP.
  assert (HS : store_ok rsegs m (wa (bv_unsigned sp + 32)) 8 = true)
    by (apply (fr_stk_store m lo (bv_unsigned sp0)); [exact ST0 | lia | cbn; lia]).
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. change (2 ^ Z.of_N 64) with (2 ^ 64) in RS.
  pose proof (bv_unsigned_in_range 64 sp0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2 ^ 64) in RS0.
  step.
  set (m1 := write_to_mem m (Z_to_bv 64 (bv_unsigned sp + 32)) (le8 (Z_to_bv 64 (cur_ptr c cur')))).
  assert (MU : munch [(bv_unsigned sp + 32, bv_unsigned sp + 40)] m m1).
  { unfold m1. change (Z_to_bv 64 (bv_unsigned sp + 32)) with (wa (bv_unsigned sp + 32)).
    apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    cbn [inside]. rewrite length_le8. left. lia. }
  assert (WM : wmono rsegs m m1) by (apply wmono_write; apply wmono_refl).
  assert (MI1 : mem_inv rsegs m1) by (apply mem_inv_store; [exact MI | rewrite length_le8; exact HS]).
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp0))
    by (apply stk_write; [exact ST0 | lia | rewrite length_le8; lia]).
  assert (W1 : sub_fp [(bv_unsigned sp + 32, bv_unsigned sp + 40)]
                 [(lo, bv_unsigned sp); (bv_unsigned sp + 0x20, bv_unsigned sp + 0x68); (c, c + SEG_M_SIZE)])
    by (intros x Hx; cbn [outside] in *; destruct Hx as (_ & H2 & _); split; [lia | exact I]).
  assert (TM : MemNorm.task_mem rsegs m1)
    by (eapply mf_task_mem with (pend := false); [exact CTX | exact MC | exact MU | exact W1]).
  assert (CTX1 : mf_ctx m1 fc (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
    by (eapply mf_ctx_transport; [exact CTX | exact MU | exact WM | exact MI1 | exact TM | exact (proj1 PE)
                                  | exact ST1 | exact W1]).
  assert (TXT1 : mf_text m1 (bv_unsigned sp0) lo c p rest).
  { eapply mf_text_transport; [exact TXT | exact MU |].
    intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. }
  assert (MC1 : mconf_at rsegs m1 c mc).
  { destruct MC as (bs & BY & ENC). exists bs. split; [|exact ENC].
    eapply bytes_at_transport; [exact BY | exact MU |]. destruct ENC as (EL & _).
    unfold apart in Hap. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CELL1 : cell8 m1 (bv_unsigned sp + 0x20) (cur_ptr c cur')).
  { unfold cell8, m1. change (Z_to_bv 64 (bv_unsigned sp + 32)) with (wa (bv_unsigned sp + 32)).
    apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
  eapply (mf_post_back ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F F m m1 lo c k0 _
            [(bv_unsigned sp + 32, bv_unsigned sp + 40)]);
    [intros k _; reflexivity | exact MU | exact WM | apply mf_W_frame; unfold M_FILE_STACK, PRINTF_K, M_FILE_FRAME; lia |].
  eapply fr_lref; [exact HN | exact HNE | exact CTX1 | exact TXT1 | exact MC1 | exact CELL1 | exact CO' | exact K0
                   | exact L0 | exact L1 | exact RF | exact OV].
Qed.

(** 0x143b0: the first non-blank byte b of the long line is at i (a0 = b): cur := b = '[' ? NULL : cur. *)
Lemma fr_lnb : forall (i : nat) (ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word),
  (i < length (mf_line rest))%nat -> all_blank (mf_line rest) 0 i -> blank (nth i (mf_line rest) 0) = false ->
  x10 = Z_to_bv 64 (nth i rest 0) ->
  evt rsegs (POSTL (if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur))
    (LST ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 0x143b0).
Proof.
  intros i ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 Hi B0 Bi E10. subst x10.
  pose proof HLP as H. unfold fr_hide in H. apply mf_loop_iff in H.
  destruct H as (CTX & TXT & MC & CELL & CO & K0 & L0 & L1 & RF & OV).
  pose proof (fr_byte _ _ _ _ _ _ i TXT) as Rb.
  pose proof (fr_line_nth rest i Hi) as EB.
  assert (CR : 0 <= cur_ptr c cur < 2 ^ 64) by (eapply fr_cur_range; eassumption).
  rewrite (dropwhile_blank_idx (mf_line rest) i); [|lia | exact B0 | right; exact Bi].
  rewrite hd0_skipn, <- EB.
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (_ & _ & SP63 & _).
  pose proof CTX as CTX0. destruct CTX0 as (Hsp & _). unfold M_FILE_FRAME in Hsp.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. change (2 ^ Z.of_N 64) with (2 ^ 64) in RS.
  assert (RD8 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 32)) 8 = Some (le8 (Z_to_bv 64 (cur_ptr c cur)))).
  { unfold cell8 in CELL. pose proof (fr_bat_read m _ _ CELL) as R. rewrite length_le8 in R.
    unfold wa in R. exact R. }
  zstep. zstep. zstep. zstep. zstep.
  eapply fr_lst; [ | destruct (nth i rest 0 =? 91); [exact I | exact CO]].
  replace (cur_ptr c (if nth i rest 0 =? 91 then None else cur)) with (if nth i rest 0 =? 91 then 0 else cur_ptr c cur)
    by (destruct (nth i rest 0 =? 91); reflexivity).
  rewrite <- (fr_mask (nth i rest 0) (cur_ptr c cur) Rb CR).
  reflexivity.
Qed.

(** The blank skip 0x140c0-0x140dc at byte i (s5 = p + i, the bytes before i blank, k + 1 bytes left). *)
Lemma fr_lskip_step : forall (k i : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  length (mf_line rest) = (i + S k)%nat -> all_blank (mf_line rest) 0 i ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x6 = p + Z.of_nat (length (mf_line rest)) ->
  (forall (a0' a1' x5' : word), (0 < k)%nat -> all_blank (mf_line rest) 0 (S i) ->
     bv_unsigned x5' = p + Z.of_nat (S i) ->
     evt rsegs (POSTL (if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur))
       (LST ra t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 x5' x6 t3 t4 t5 t6 0x140c0)) ->
  evt rsegs (POSTL (if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur))
    (LST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140c0).
Proof.
  intros k i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 HLk B0 H5 H6 NEXT.
  pose proof HLP as H. unfold fr_hide in H.
  pose proof H as FA. apply fr_loop_facts in FA. destruct FA as (P0 & P1 & LL & L0 & L1).
  apply mf_loop_iff in H. destruct H as (CTX & TXT & MC & CELL & CO & K0 & _ & _ & RF & OV).
  assert (Hi : (i < length (mf_line rest))%nat) by lia.
  pose proof (fr_byte _ _ _ _ _ _ i TXT) as Rb.
  pose proof (fr_line_nth rest i Hi) as EB.
  assert (RD : ov_read_bytes rsegs m x5 1 = Some [Z_to_bv 8 (nth i rest 0)])
    by (apply (fr_rd m _ lo c p rest i x5 TXT); lia).
  assert (STOP : blank (nth i rest 0) = false -> forall a0' a1' : word, a0' = Z_to_bv 64 (nth i rest 0) ->
     evt rsegs (POSTL (if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur))
       (LST ra t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x143b0)).
  { intros NB a0' a1' E0. eapply (fr_lnb i); [exact Hi | exact B0 | rewrite <- EB; exact NB | exact E0]. }
  zstep.
  zstep. if_cases K; zify_cond K; rewrite ?(fr_u8 _ Rb) in K.
  - eapply STOP; [apply fr_gt32; lia | rewrite ?(fr_u8 _ Rb); reflexivity].
  - zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?(fr_u8 _ Rb) in K2.
    + eapply STOP; [apply fr_blank_mask0; [lia | exact K2] | rewrite ?(fr_u8 _ Rb); reflexivity].
    + apply fr_blank_mask1 in K2; [|lia].
      assert (B1 : all_blank (mf_line rest) 0 (S i)).
      { intros t Ht. destruct (Nat.eq_dec t i) as [->|]; [rewrite <- EB; exact K2 | apply B0; lia]. }
      zstep. zstep. if_cases K3; zify_cond K3.
      * apply NEXT; [lia | exact B1 | rewrite unsigned_lit by lia; lia].
      * assert (Ek : k = 0%nat) by lia. subst k.
        zstep.
        assert (EC : (if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur) = cur).
        { rewrite (dropwhile_blank_idx (mf_line rest) (length (mf_line rest))); [| lia | | left; reflexivity].
          - rewrite skipn_all. reflexivity.
          - replace (length (mf_line rest)) with (S i) by lia. exact B1. }
        rewrite EC.
        eapply fr_lref; [exact HN | exact HNE | exact CTX | exact TXT | exact MC | exact CELL | exact CO | exact K0
                         | exact L0 | exact L1 | exact RF | exact OV].
Qed.

Lemma fr_lskip : forall (k i : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  length (mf_line rest) = (i + S k)%nat -> all_blank (mf_line rest) 0 i ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x6 = p + Z.of_nat (length (mf_line rest)) ->
  evt rsegs (POSTL (if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur))
    (LST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140c0).
Proof.
  induction k as [|k IH]; intros i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 HLk B0 H5 H6;
    (eapply fr_lskip_step; [exact HLk | exact B0 | exact H5 | exact H6 |]).
  - intros a0' a1' x5' Hk. lia.
  - intros a0' a1' x5' _ B1 H5'. eapply (IH (S i)); [lia | exact B1 | exact H5' | exact H6].
Qed.

End LongS.
End Long.

Lemma mf_longp_holds : m_refuse_contract -> S_MF_LONGP.
Proof.
  intros HMR n HT. unfold H_MF_LONG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest HN HNE HLP HRG E5 E6 HLG.
  destruct HRG as (-> & -> & -> & -> & -> & -> & -> & -> & ->). subst s5 s6.
  pose proof HLP as FA. apply fr_loop_facts in FA. destruct FA as (P0 & P1 & LL & L0 & L1).
  rewrite (m_line_long mc cur (line + 1) (mf_line rest) HLG).
  unfold MF_PC_LONG, BLANK_MASK.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  eapply fr_lskip with (k := (length (mf_line rest) - 1)%nat) (i := 0%nat);
    first [exact HT | exact HMR | exact HN | exact HNE | exact HLP | exact HLG | lia
          | (intros t Ht; lia) | (rewrite unsigned_lit by lia; lia)].
Qed.

(** ** S_MF_FRONT *)
Section Front.
Variable n : nat.
Hypothesis HT : H_MF_TAIL n.
Hypothesis HL : H_MF_LONG n.
Hypothesis HH : H_MF_HDR n.
Hypothesis HK : H_MF_KEY n.

(** The short line (0x140e0-0x14200): one memory, the loop facts of the head, s3 = line + 1. *)
Section Short.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
  (k0 : nat) (rest : list Z).
Hypothesis HN : (length rest <= n)%nat.
Hypothesis HNE : rest <> [].
Hypothesis HLP : fr_hide (m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11).
Hypothesis HSH : (length (mf_line rest) < 512)%nat.

Local Abbreviation POST := (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
  (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest)).
Local Abbreviation SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 pc :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 0x1ff)
         (Z_to_bv 64 4294976000) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Local Abbreviation CUTQ q := (h_cut_comment (mf_line rest) = firstn q (mf_line rest)).
Local Abbreviation CU q := (firstn q (mf_line rest)).

Ltac sfacts := pose proof HLP as HL0; unfold fr_hide in HL0; pose proof HL0 as FA; apply fr_loop_facts in FA;
  destruct FA as (P0 & P1 & LL & L0 & L1); pose proof HL0 as TXT; apply fr_loop_text in TXT.

(** DISP 0x14174: the stripped line is [i, j) of the line (s5 = p + i, s6 = p + j). *)
Lemma fr_disp : forall (i j q : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  (i <= j <= q)%nat -> (q <= length (mf_line rest))%nat -> CUTQ q ->
  h_strip (CU q) = slice i j (mf_line rest) ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x6 = p + Z.of_nat j ->
  evt rsegs POST (SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14174).
Proof.
  intros i j q ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hij Hq HC HS H5 H6.
  rewrite <- HC in HS. sfacts.
  zstep. if_cases K; zify_cond K.
  - assert (Eij : i = j) by lia. subst j. rewrite fr_slice_nil in HS.
    rewrite (m_line_empty mc cur (line + 1) (mf_line rest) HSH HS).
    unfold mf_post, mf_fin.
    pose proof HT as HT'. unfold H_MF_TAIL in HT'.
    pose proof (mf_rest_lt rest HNE) as RL.
    apply mf_loop_iff in HL0. destruct HL0 as (CTX & TXT' & MC & CELL & CO & K0 & _ & _ & RF & OV).
    eapply HT'; [lia | |].
    + eapply mf_tail_loop; [exact CTX | exact TXT' | exact HNE | exact MC | exact CELL | exact CO | exact K0
                           | exact L0 | exact L1 | lia | lia].
    + unfold m_file_regs. repeat split.
  - assert (Hlt : (i < j)%nat) by lia.
    pose proof (fr_byte _ _ _ _ _ _ i TXT) as Rb.
    assert (EB : nth i rest 0 = nth i (mf_line rest) 0) by (apply fr_line_nth; lia).
    assert (RD : ov_read_bytes rsegs m x5 1 = Some [Z_to_bv 8 (nth i rest 0)])
      by (apply (fr_rd m _ lo c p rest i x5 TXT); lia).
    assert (NE : h_strip (h_cut_comment (mf_line rest)) <> []) by (rewrite HS; apply fr_slice_ne; lia).
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?(fr_u8 _ Rb) in K2.
    + assert (NB : nth i (mf_line rest) 0 <> LBR) by (rewrite <- EB; exact K2).
      assert (HD : hd0 (h_strip (h_cut_comment (mf_line rest))) <> LBR)
        by (rewrite HS, fr_hd0_slice by lia; exact NB).
      rewrite (m_line_key mc cur (line + 1) (mf_line rest) HSH NE HD).
      pose proof HK as HK'. unfold H_MF_KEY in HK'.
      eapply HK' with (i := i) (j := j);
        [exact HN | exact HNE | exact HL0 | unfold m_file_regs; repeat split | exact HSH | lia | lia
        | symmetry; exact HS | exact NB | apply fr_word; lia | apply fr_word; lia | f_equal; lia].
    + assert (NB : nth i (mf_line rest) 0 = LBR) by (rewrite <- EB; exact K2).
      assert (HD : hd0 (h_strip (h_cut_comment (mf_line rest))) = LBR)
        by (rewrite HS, fr_hd0_slice by lia; exact NB).
      rewrite (m_line_hdr mc cur (line + 1) (mf_line rest) HSH HD).
      pose proof HH as HH'. unfold H_MF_HDR in HH'.
      eapply HH' with (i := i) (j := j);
        [exact HN | exact HNE | exact HL0 | unfold m_file_regs; repeat split | exact HSH | lia | lia
        | symmetry; exact HS | exact NB | apply fr_word; lia | apply fr_word; lia | f_equal; lia].
Qed.

(** The backward strip 0x14154-0x14170 at s6 = p + j (u[j, q) blank, u[i] not blank). *)
Lemma fr_back_step : forall (k i j q : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  j = (i + S k)%nat -> (j <= q)%nat -> (q <= length (mf_line rest))%nat -> CUTQ q ->
  all_blank (CU q) 0 i -> blank (nth i (mf_line rest) 0) = false -> all_blank (CU q) j q ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x6 = p + Z.of_nat j ->
  (forall (a1' x6' : word), (0 < k)%nat -> all_blank (CU q) (j - 1) q -> bv_unsigned x6' = p + Z.of_nat (j - 1) ->
     evt rsegs POST (SST ra t0 t1 t2 a0 a1' a2 a3 a4 a5 a6 a7 s4 x5 x6' t3 t4 t5 t6 0x14154)) ->
  evt rsegs POST (SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14154).
Proof.
  intros k i j q ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hj Hjq Hq HC B0 Bi Bj H5 H6 NEXT.
  sfacts.
  assert (LU : length (CU q) = q) by (rewrite length_firstn; lia).
  pose proof (fr_byte _ _ _ _ _ _ (j - 1) TXT) as Rb.
  assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned x6 + -1)) 1 = Some [Z_to_bv 8 (nth (j - 1) rest 0)])
    by (apply (fr_rd1 m _ lo c p rest (j - 1) x6 TXT); lia).
  assert (EB : nth (j - 1) rest 0 = nth (j - 1) (CU q) 0) by (rewrite fr_nth_firstn by lia; apply fr_line_nth; lia).
  assert (STOP : blank (nth (j - 1) rest 0) = false -> forall a1' : word,
     evt rsegs POST (SST ra t0 t1 t2 a0 a1' a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14174)).
  { intros NB a1'. eapply (fr_disp i j q); [lia | exact Hq | exact HC | | exact H5 | exact H6].
    rewrite <- (fr_slice_firstn (mf_line rest) q i j) by lia.
    apply h_strip_idx; rewrite ?LU;
      [lia | exact B0 | right; rewrite fr_nth_firstn by lia; exact Bi | exact Bj | right; rewrite <- EB; exact NB]. }
  zstep. zstep. if_cases K; zify_cond K; rewrite ?(fr_u8 _ Rb) in K.
  - apply STOP. apply fr_gt32. lia.
  - zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?(fr_u8 _ Rb) in K2.
    + apply STOP. apply fr_blank_mask0; [lia | exact K2].
    + apply fr_blank_mask1 in K2; [|lia].
      zstep. zstep. if_cases K3; zify_cond K3.
      * apply NEXT; [lia | | rewrite unsigned_lit by lia; lia].
        intros t Ht. destruct (Nat.eq_dec t (j - 1)) as [->|]; [rewrite <- EB; exact K2 | apply Bj; lia].
      * exfalso. assert (Ei : (j - 1)%nat = i) by lia. rewrite Ei, fr_line_nth in K2 by lia. congruence.
Qed.

Lemma fr_back : forall (k i j q : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  j = (i + S k)%nat -> (j <= q)%nat -> (q <= length (mf_line rest))%nat -> CUTQ q ->
  all_blank (CU q) 0 i -> blank (nth i (mf_line rest) 0) = false -> all_blank (CU q) j q ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x6 = p + Z.of_nat j ->
  evt rsegs POST (SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14154).
Proof.
  induction k as [|k IH]; intros i j q ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6
    Hj Hjq Hq HC B0 Bi Bj H5 H6;
    (eapply fr_back_step; [exact Hj | exact Hjq | exact Hq | exact HC | exact B0 | exact Bi | exact Bj | exact H5
                          | exact H6 |]).
  - intros a1' x6' Hk. lia.
  - intros a1' x6' _ Bj' H6'.
    eapply (IH i (j - 1)%nat q); [lia | lia | exact Hq | exact HC | exact B0 | exact Bi | exact Bj' | exact H5 | exact H6'].
Qed.

(** BACK0 0x14148: the forward strip stopped at i (i = q, or u[i] not blank). *)
Lemma fr_back0 : forall (i q : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  (i <= q)%nat -> (q <= length (mf_line rest))%nat -> CUTQ q -> all_blank (CU q) 0 i ->
  (i = q \/ blank (nth i (mf_line rest) 0) = false) ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x6 = p + Z.of_nat q ->
  evt rsegs POST (SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14148).
Proof.
  intros i q ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hiq Hq HC B0 HB H5 H6.
  sfacts.
  assert (LU : length (CU q) = q) by (rewrite length_firstn; lia).
  zstep. if_cases K; zify_cond K.
  - assert (Ei : i = q) by lia. subst i.
    eapply (fr_disp q q q); [lia | exact Hq | exact HC | | exact H5 | exact H6].
    rewrite fr_slice_nil.
    rewrite (h_strip_idx (CU q) q q); [apply fr_slice_nil | rewrite LU; lia | exact B0 | left; rewrite LU; reflexivity
                                      | rewrite LU; intros t Ht; lia | left; reflexivity].
  - assert (Hlt : (i < q)%nat) by lia. destruct HB as [HB|Bi]; [lia|].
    zstep. zstep.
    eapply (fr_back (q - i - 1) i q q);
      [lia | lia | exact Hq | exact HC | exact B0 | exact Bi | intros t Ht; lia | exact H5 | exact H6].
Qed.

(** The forward strip 0x14124-0x14144 at s5 = p + i (a0 = q - i bytes left, u[0, i) blank). *)
Lemma fr_fwd_step : forall (k i q : nat) (ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  q = (i + S k)%nat -> (q <= length (mf_line rest))%nat -> CUTQ q -> all_blank (CU q) 0 i ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x10 = Z.of_nat (S k) -> bv_unsigned x6 = p + Z.of_nat q ->
  (forall (x10' a1' x5' : word), (0 < k)%nat -> all_blank (CU q) 0 (S i) -> bv_unsigned x5' = p + Z.of_nat (S i) ->
     bv_unsigned x10' = Z.of_nat k ->
     evt rsegs POST (SST ra t0 t1 t2 x10' a1' a2 a3 a4 a5 a6 a7 s4 x5' x6 t3 t4 t5 t6 0x14124)) ->
  evt rsegs POST (SST ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14124).
Proof.
  intros k i q ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hqk Hq HC B0 H5 H10 H6 NEXT.
  sfacts.
  pose proof (fr_byte _ _ _ _ _ _ i TXT) as Rb.
  assert (EB : nth i rest 0 = nth i (CU q) 0) by (rewrite fr_nth_firstn by lia; apply fr_line_nth; lia).
  assert (EBl : nth i rest 0 = nth i (mf_line rest) 0) by (apply fr_line_nth; lia).
  assert (RD : ov_read_bytes rsegs m x5 1 = Some [Z_to_bv 8 (nth i rest 0)])
    by (apply (fr_rd m _ lo c p rest i x5 TXT); lia).
  assert (STOP : blank (nth i rest 0) = false -> forall a1' : word,
     evt rsegs POST (SST ra t0 t1 t2 x10 a1' a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14148)).
  { intros NB a1'. eapply (fr_back0 i q);
      [lia | exact Hq | exact HC | exact B0 | right; rewrite <- EBl; exact NB | exact H5 | exact H6]. }
  zstep. zstep. if_cases K; zify_cond K; rewrite ?(fr_u8 _ Rb) in K.
  - apply STOP. apply fr_gt32. lia.
  - zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?(fr_u8 _ Rb) in K2.
    + apply STOP. apply fr_blank_mask0; [lia | exact K2].
    + apply fr_blank_mask1 in K2; [|lia].
      assert (B1 : all_blank (CU q) 0 (S i)).
      { intros t Ht. destruct (Nat.eq_dec t i) as [->|]; [rewrite <- EB; exact K2 | apply B0; lia]. }
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      * apply NEXT; [lia | exact B1 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia].
      * zstep.
        eapply (fr_back0 q q); [lia | exact Hq | exact HC | | left; reflexivity | exact H6 | exact H6].
        replace q with (S i) at 2 by lia. exact B1.
Qed.

Lemma fr_fwd : forall (k i q : nat) (ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  q = (i + S k)%nat -> (q <= length (mf_line rest))%nat -> CUTQ q -> all_blank (CU q) 0 i ->
  bv_unsigned x5 = p + Z.of_nat i -> bv_unsigned x10 = Z.of_nat (S k) -> bv_unsigned x6 = p + Z.of_nat q ->
  evt rsegs POST (SST ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14124).
Proof.
  induction k as [|k IH]; intros i q ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hqk Hq HC B0 H5 H10 H6;
    (eapply fr_fwd_step; [exact Hqk | exact Hq | exact HC | exact B0 | exact H5 | exact H10 | exact H6 |]).
  - intros x10' a1' x5' Hk. lia.
  - intros x10' a1' x5' _ B1 H5' H10'.
    eapply (IH (S i) q); [lia | exact Hq | exact HC | exact B1 | exact H5' | exact H10' | exact H6].
Qed.

(** STRIP 0x1411c: the comment-cut line is [0, q) (s5 = p, s6 = p + q). *)
Lemma fr_strip : forall (q : nat) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  (q <= length (mf_line rest))%nat -> CUTQ q -> bv_unsigned x5 = p -> bv_unsigned x6 = p + Z.of_nat q ->
  evt rsegs POST (SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x1411c).
Proof.
  intros q ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hq HC H5 H6.
  sfacts.
  zstep. if_cases K; zify_cond K.
  - eapply (fr_back0 0 q); [lia | exact Hq | exact HC | intros t Ht; lia | left; lia | lia | exact H6].
  - zstep.
    eapply (fr_fwd (q - 1) 0 q);
      [lia | exact Hq | exact HC | intros t Ht; lia | lia | rewrite unsigned_lit by lia; lia | exact H6].
Qed.

(** CUTEND 0x14118: s6 = a0 = p + q, the comment cut at q. *)
Lemma fr_cutend : forall (q : nat) (ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  (q <= length (mf_line rest))%nat -> CUTQ q -> bv_unsigned x10 = p + Z.of_nat q -> bv_unsigned x5 = p ->
  evt rsegs POST (SST ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14118).
Proof.
  intros q ra t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 Hq HC H10 H5.
  zstep. eapply (fr_strip q); [exact Hq | exact HC | exact H5 | exact H10].
Qed.

(** The comment scan 0x140ec-0x14114 at q (a0 = p + q, a1 = -q; no cut before q). *)
Lemma fr_cut_step : forall (k q : nat) (ra t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  length (mf_line rest) = (q + S k)%nat -> (forall j, (j < q)%nat -> cut_at (mf_line rest) j = false) ->
  bv_unsigned x10 = p + Z.of_nat q -> bv_unsigned x11 = (- Z.of_nat q) mod 2 ^ 64 ->
  bv_unsigned x5 = p -> bv_unsigned x6 = p + Z.of_nat (length (mf_line rest)) ->
  (forall (x10' x11' a2' : word), (0 < k)%nat -> (forall j, (j < S q)%nat -> cut_at (mf_line rest) j = false) ->
     bv_unsigned x10' = p + Z.of_nat (S q) -> bv_unsigned x11' = (- Z.of_nat (S q)) mod 2 ^ 64 ->
     evt rsegs POST (SST ra t0 t1 t2 x10' x11' a2' a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140ec)) ->
  evt rsegs POST (SST ra t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140ec).
Proof.
  intros k q ra t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 HLq HC H10 H11 H5 H6 NEXT.
  sfacts.
  pose proof (fr_byte _ _ _ _ _ _ q TXT) as Rb.
  assert (EBq : nth q rest 0 = nth q (mf_line rest) 0) by (apply fr_line_nth; lia).
  assert (RD : ov_read_bytes rsegs m x10 1 = Some [Z_to_bv 8 (nth q rest 0)])
    by (apply (fr_rd m _ lo c p rest q x10 TXT); lia).
  assert (ADV : cut_at (mf_line rest) q = false -> forall a2' : word,
     evt rsegs POST (SST ra t0 t1 t2 x10 x11 a2' a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14108)).
  { intros NC a2'. zstep. zstep. zstep. if_cases K; zify_cond K.
    - apply NEXT; [lia | | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit_wrap, H11; apply fr_negmod_step].
      intros j Hj. destruct (Nat.eq_dec j q) as [->|]; [exact NC | apply HC; lia].
    - zstep.
      eapply (fr_cutend (length (mf_line rest))); [lia | | exact H6 | exact H5].
      apply h_cut_idx; [lia | | left; reflexivity].
      intros j Hj. destruct (Nat.eq_dec j q) as [->|]; [exact NC | apply HC; lia]. }
  assert (CUT : cut_at (mf_line rest) q = true -> forall a2' : word,
     evt rsegs POST (SST ra t0 t1 t2 x10 x11 a2' a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x14118)).
  { intros CT a2'. eapply (fr_cutend q); [lia | apply h_cut_idx; [lia | exact HC | right; exact CT] | exact H10 | exact H5]. }
  assert (MARK : is_mark (nth q rest 0) = true -> forall a2' : word,
     evt rsegs POST (SST ra t0 t1 t2 x10 x11 a2' a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140f8)).
  { intros IM a2'. zstep. if_cases K3; zify_cond K3.
    - rewrite H11 in K3. apply fr_negmod0 in K3; [|lia]. assert (Eq : q = 0%nat) by lia. subst q.
      apply CUT. unfold cut_at. rewrite <- EBq, IM. reflexivity.
    - rewrite H11 in K3.
      assert (Hq0 : (0 < q)%nat) by (destruct (Nat.eq_dec q 0) as [->|]; [exfalso; apply K3; reflexivity | lia]).
      pose proof (fr_byte _ _ _ _ _ _ (q - 1) TXT) as Rb1.
      assert (EBq1 : nth (q - 1) rest 0 = nth (q - 1) (mf_line rest) 0) by (apply fr_line_nth; lia).
      assert (RD1 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned x10 + -1)) 1 = Some [Z_to_bv 8 (nth (q - 1) rest 0)])
        by (apply (fr_rd1 m _ lo c p rest (q - 1) x10 TXT); lia).
      zstep. zstep. if_cases K4; zify_cond K4; rewrite ?(fr_u8 _ Rb1) in K4.
      + apply CUT. unfold cut_at, sp_tab. rewrite <- EBq, <- EBq1, IM, K4. destruct (q =? 0)%nat; reflexivity.
      + zstep. if_cases K5; zify_cond K5; rewrite ?(fr_u8 _ Rb1) in K5.
        * apply CUT. unfold cut_at, sp_tab. rewrite <- EBq, <- EBq1, IM, K5. destruct (q =? 0)%nat; reflexivity.
        * apply ADV. unfold cut_at, sp_tab. rewrite <- EBq, <- EBq1, IM.
          rewrite (proj2 (Nat.eqb_neq q 0)) by lia.
          rewrite (proj2 (Z.eqb_neq _ 32) K5), (proj2 (Z.eqb_neq _ 9) K4). reflexivity. }
  zstep. zstep. if_cases K1; zify_cond K1; rewrite ?(fr_u8 _ Rb) in K1.
  - apply MARK. unfold is_mark. rewrite K1. reflexivity.
  - zstep. if_cases K2; zify_cond K2; rewrite ?(fr_u8 _ Rb) in K2.
    + apply ADV. unfold cut_at, is_mark. rewrite <- EBq.
      rewrite (proj2 (Z.eqb_neq _ 35) K2), (proj2 (Z.eqb_neq _ 59) K1). reflexivity.
    + apply MARK. unfold is_mark. rewrite K2. reflexivity.
Qed.

Lemma fr_cut : forall (k q : nat) (ra t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  length (mf_line rest) = (q + S k)%nat -> (forall j, (j < q)%nat -> cut_at (mf_line rest) j = false) ->
  bv_unsigned x10 = p + Z.of_nat q -> bv_unsigned x11 = (- Z.of_nat q) mod 2 ^ 64 ->
  bv_unsigned x5 = p -> bv_unsigned x6 = p + Z.of_nat (length (mf_line rest)) ->
  evt rsegs POST (SST ra t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140ec).
Proof.
  induction k as [|k IH]; intros q ra t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 HLq HC H10 H11 H5 H6;
    (eapply fr_cut_step; [exact HLq | exact HC | exact H10 | exact H11 | exact H5 | exact H6 |]).
  - intros x10' x11' a2' Hk. lia.
  - intros x10' x11' a2' _ HC' H10' H11'.
    eapply (IH (S q)); [lia | exact HC' | exact H10' | exact H11' | exact H5 | exact H6].
Qed.

(** 0x140e0: the short line (s5 = p, s6 = p + |l|). *)
Lemma fr_short : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 : word),
  bv_unsigned x5 = p -> bv_unsigned x6 = p + Z.of_nat (length (mf_line rest)) ->
  evt rsegs POST (SST ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 0x140e0).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 x5 x6 t3 t4 t5 t6 H5 H6.
  sfacts.
  zstep. if_cases K; zify_cond K.
  - eapply (fr_strip (length (mf_line rest))); [lia | | exact H5 | exact H6].
    apply h_cut_idx; [lia | intros j Hj; lia | left; reflexivity].
  - zstep. zstep.
    eapply (fr_cut (length (mf_line rest) - 1) 0);
      [lia | intros j Hj; lia | lia | first [reflexivity | rewrite unsigned_lit by lia; reflexivity] | exact H5 | exact H6].
Qed.

End Short.

(** JOIN 0x140b0: s5 = p, s6 = p + |l|, s2 = the next line's address; s3 = line + 1 and the length test. *)
Lemma fr_join : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z),
  (length rest <= n)%nat -> rest <> [] ->
  m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  m_file_regs c (mf_next p rest) line s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
  s5 = Z_to_bv 64 p -> s6 = Z_to_bv 64 (p + Z.of_nat (length (mf_line rest))) ->
  evt rsegs
    (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
       (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest HN HNE HLP HRG E5 E6.
  destruct HRG as (-> & -> & -> & -> & -> & -> & -> & -> & ->). subst s5 s6.
  pose proof HLP as FA. apply fr_loop_facts in FA. destruct FA as (P0 & P1 & LL & L0 & L1).
  pose proof (fr_len_pos rest HNE) as LP.
  unfold BLANK_MASK.
  zstep. zstep. zstep.
  rewrite fr_swrap by lia.
  if_cases K; zify_cond K; rewrite ?fr_signed in K by lia.
  - eapply fr_short; first [exact HN | exact HNE | exact HLP | lia | (rewrite unsigned_lit by lia; lia)].
  - pose proof HL as HL'. unfold H_MF_LONG in HL'.
    eapply HL'; [exact HN | exact HNE | exact HLP | unfold m_file_regs; repeat split | reflexivity | reflexivity | lia].
Qed.

End Front.

Lemma mf_front_holds : strchr_contract -> strlen_contract -> S_MF_FRONT.
Proof.
  intros HSC HSL n HT HL HH HK. unfold H_MF_HEAD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest HLEN HNE HLP HRG.
  assert (HN : (length rest <= n)%nat) by lia.
  rewrite (mf_fin_head (mc, cur) line rest HNE).
  change (ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m
            (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest)) lo
            (fun m' => mconf_at rsegs m' c (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest)))
    with (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
            (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest)).
  pose proof HLP as FA. apply fr_loop_facts in FA. destruct FA as (P0 & P1 & LL & L0 & L1).
  pose proof (fr_len_pos rest HNE) as LP.
  pose proof HLP as H. apply mf_loop_iff in H. destruct H as (CTX & TXT & _).
  pose proof CTX as CTX0.
  destruct CTX0 as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SO & MI).
  unfold M_FILE_FRAME in Hsp. destruct SO as (ST0 & DEEP & _ & _).
  unfold M_FILE_STACK, PRINTF_K, M_FILE_FRAME in DEEP.
  pose proof TXT as TXT0. destruct TXT0 as (_ & _ & CS & PAP & _).
  destruct (fr_cstr _ _ _ CS) as (bs & sl & BY & ZS & NZB & LB & SL7 & SLK).
  destruct (mf_text_props _ _ _ _ _ _ TXT) as (NZ & _).
  destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp0) ST0 ltac:(lia)) as [STsp _].
  destruct HRG as (-> & -> & -> & -> & -> & -> & -> & -> & ->).
  unfold M_FILE_HEAD.
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSC with (str := bs) (slack := sl) (lo := lo); rewrite ?unsigned_lit by lia.
    - exact STsp.
    - exact BY.
    - exact NZB.
    - unfold fr_hide in SLK. exact SLK.
    - exact MI.
    - lia.
    - unfold apart in PAP. destruct PAP as [A|A]; [left | right]; lia. }
  intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1
              & ST1 & BY1).
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (MUb : munch [(lo, bv_unsigned sp)] m m1).
  { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  pose proof (fr_loop_below m m1 fc _ _ lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
                HLP MUb WM1 MI1 ST1) as HLP1.
  eapply (mf_post_back ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F F m m1 lo c k0 _
            [(bv_unsigned sp - 32, bv_unsigned sp)]);
    [intros k _; reflexivity | exact MU1 | exact WM1 | apply mf_W_frame; unfold M_FILE_STACK, PRINTF_K, M_FILE_FRAME; lia |].
  rewrite unsigned_lit in BY1 by lia.
  destruct (mf_line_rest rest) as [[EA EB] | [EA [EB EC]]].
  - (* a '\n' ends the line: s2 = nl + 1 *)
    rewrite (fr_strchr_nl p rest bs ZS NZ P0 ltac:(lia) EA).
    zstep. zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep.
    eapply fr_join; [exact HT | exact HL | exact HH | exact HK | exact HN | exact HNE | exact HLP1 | | reflexivity | reflexivity].
    unfold m_file_regs. repeat split. f_equal. unfold mf_next. lia.
  - (* no '\n': the line is the whole text, s2 = s6 = p + strlen(p) *)
    rewrite (fr_strchr_none p rest bs ZS NZ P0 ltac:(lia) EA).
    zstep. zstep. zstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K; zify_cond K; [exfalso; lia|]
    | _ => idtac
    end.
    zstep. zstep.
    eapply evt_cut.
    { eapply HSL with (str := bs) (slack := sl); rewrite ?unsigned_lit by lia;
        [exact BY1 | exact NZB | unfold fr_hide in SLK; exact SLK | exact MI1]. }
    intros ms' (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2
                & BY2).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (ST2 : stk rsegs m2 lo (bv_unsigned sp))
      by (eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | exact I]).
    assert (MUc : munch [(lo, bv_unsigned sp)] m1 m2) by (eapply munch_weaken; [|exact MU2]; intros x Hx; exact I).
    pose proof (fr_loop_below m1 m2 fc _ _ lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
                  HLP1 MUc WM2 MI2 ST2) as HLP2.
    eapply (mf_post_back ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F F m1 m2 lo c k0 _ []);
      [intros k _; reflexivity | exact MU2 | exact WM2 | intros x Hx; exact I |].
    zstep. zstep. zstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K2; zify_cond K2; [|exfalso; lia]
    | _ => idtac
    end.
    eapply fr_join; [exact HT | exact HL | exact HH | exact HK | exact HN | exact HNE | exact HLP2 | | reflexivity | ].
    + unfold m_file_regs. repeat split. f_equal. unfold mf_next. rewrite EB. cbn [length]. lia.
    + f_equal. rewrite LB, <- EA. reflexivity.
Qed.
