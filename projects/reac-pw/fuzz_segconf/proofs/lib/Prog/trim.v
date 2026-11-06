(** The walk of trim (reac_segconf.c:50-59, static) in the plain image 3776ca44d75c (Prog/trim_c.v), written new for
    reac-pw/fuzz_segconf on the pattern of Prog/strcasecmp.v (loops) and Prog/strtol_null.v (frame, callee).
    strlen is a premise (strlen_contract, Prog/strlen_c.v, 0x1ec30).

    Code (plain image; frame 16: ra at sp+8, s0 at sp+0):
      0x15660-0x1566c  frame, s0 = s; 0x15670-0x1567c a0 = 0x20, a1 = 0x800011 << 9 = 0x100002200
      LEAD 0x15680 lbu a2,0(s0); bltu a0,a2 -> 0x1569c; srl/andi (bit a2 of a1); beqz -> 0x1569c; s0++; j LEAD
      0x1569c a0 = s0; jal strlen; a1 = s0 + a0; beqz a0 -> 0x156d8; 0x156ac-0x156b8 a0 = 0x20, a2 = mask
      TRAIL 0x156bc lbu a3,-1(a1); bltu a0,a3 -> 0x156d8; srl/andi; beqz -> 0x156d8; a1--; bltu s0,a1 -> TRAIL
      0x156d8 sb zero,0(a1); a0 = s0; restore; ret
    The mask test is SegModel.blank on bytes (blank_mask_b); LEAD stops at trim_lead s; strlen gives |s1| for
    s1 = dropwhile blank s; TRAIL runs e = s0 + j down while e[-1] is blank, which is te s j = trim_end s1 j j;
    the NUL lands at trim_end_addr. cstr_at may name more slack than the 7 bytes trim_pre keeps apart from the
    stack: the walk keeps only the bytes up to the next 8-byte boundary (slack_cut), which strlen needs.
    TrimSpine holds the image-free lemmas; U/Prog/trim.v imports it. *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strlen_c trim_c.
Import ListNotations.
Open Scope Z_scope.

Module TrimSpine.

Definition hide (P : Prop) : Prop := P.

Lemma zb8 : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma zb_zs : forall bs, zb (zs bs) = bs.
Proof. unfold zb, zs. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite zb8, IH. reflexivity. Qed.

Lemma len_zs : forall bs, length (zs bs) = length bs.
Proof. intros. unfold zs. apply length_map. Qed.

Lemma zs_range : forall bs i, 0 <= nth i (zs bs) 0 < 256.
Proof.
  unfold zs. induction bs as [|b bs IH]; intros [|i]; cbn; try lia; [|apply IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma byte_at : forall bs sl i, (i <= length bs)%nat ->
  nth_error (bs ++ ZERO :: sl) i = Some (Z_to_bv 8 (nth i (zs bs) 0)).
Proof.
  intros bs sl i Hi. destruct (Nat.lt_ge_cases i (length bs)) as [Hl|Hg].
  - rewrite nth_error_app1 by exact Hl. unfold zs.
    rewrite (nth_indep _ 0 (bv_unsigned ZERO)) by (rewrite length_map; exact Hl).
    rewrite map_nth, zb8. apply nth_error_nth'. exact Hl.
  - assert (i = length bs) as -> by lia. rewrite nth_error_app2, Nat.sub_diag by lia. cbn.
    rewrite nth_overflow by (rewrite len_zs; lia). reflexivity.
Qed.

Lemma bytes_at_prefix : forall segs m a l1 l2, bytes_at segs m a (l1 ++ l2) -> bytes_at segs m a l1.
Proof. intros segs m a l1 l2 H. apply bytes_at_app in H. tauto. Qed.

(** The slack the contract names may run past the 7 bytes trim's callers keep apart from the stack: keep only the
    bytes up to the next 8-byte boundary. *)
Lemma slack_cut : forall segs m a bs sl,
  bytes_at segs m a (bs ++ ZERO :: sl) -> (- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl) ->
  exists sl', bytes_at segs m a (bs ++ ZERO :: sl') /\ (length sl' <= 7)%nat /\
    hide ((- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl')).
Proof.
  intros segs m a bs sl H Hk. set (k := Z.to_nat ((- (a + Z.of_nat (length bs) + 1)) mod 8)).
  assert (Hk8 : 0 <= (- (a + Z.of_nat (length bs) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  exists (firstn k sl). split; [|split].
  - apply (bytes_at_prefix segs m a _ (skipn k sl)). rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. exact H.
  - rewrite length_firstn. lia.
  - unfold hide. rewrite length_firstn. lia.
Qed.

Lemma cut_nul_nz : forall s, ~ In 0 s -> cut_nul s = s.
Proof.
  induction s as [|x s IH]; intros H; cbn; [reflexivity|].
  destruct (x =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst. exfalso. apply H. left. reflexivity.
  - f_equal. apply IH. intros Hi. apply H. right. exact Hi.
Qed.

Lemma tw_nth : forall P l i, (i < length (takewhile P l))%nat -> P (nth i l 0) = true.
Proof.
  intros P. induction l as [|x l IH]; intros i H; cbn in *; [lia|].
  destruct (P x) eqn:E; cbn in H; [|lia]. destruct i; [exact E|]. apply IH. lia.
Qed.

Lemma tw_len : forall P l, (length (takewhile P l) <= length l)%nat.
Proof. intros P. induction l as [|x l IH]; cbn; [lia|]. destruct (P x); cbn; lia. Qed.

Lemma tw_stop : forall P l, P 0 = false -> P (nth (length (takewhile P l)) l 0) = false.
Proof.
  intros P. induction l as [|x l IH]; intros H0; cbn; [exact H0|].
  destruct (P x) eqn:E; cbn; [apply IH; exact H0 | exact E].
Qed.

Lemma skipn_tw : forall P l, skipn (length (takewhile P l)) l = dropwhile P l.
Proof. intros P. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (P x); cbn; [exact IH | reflexivity]. Qed.

Lemma trim_end_le : forall s f e, (trim_end s e f <= e)%nat.
Proof.
  intros s f. induction f as [|f IH]; intros [|e].
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - change (trim_end s (S e) (S f)) with (if blank (nth e s 0) then trim_end s e f else S e).
    destruct (blank (nth e s 0)); [specialize (IH e); lia | apply Nat.le_refl].
Qed.

Definition s1_of (s : list Z) : list Z := dropwhile blank s.
Definition te (s : list Z) (j : nat) : nat := trim_end (s1_of s) j j.

Lemma te_S : forall s j, te s (S j) = if blank (nth j (s1_of s) 0) then te s j else S j.
Proof. reflexivity. Qed.

Lemma te_0 : forall s, te s 0 = 0%nat.
Proof. reflexivity. Qed.

Lemma te_le : forall s j, (te s j <= j)%nat.
Proof. intros. apply trim_end_le. Qed.

Lemma lead_eq : forall s, ~ In 0 s -> trim_lead s = length (takewhile blank s).
Proof. intros s H. unfold trim_lead. rewrite cut_nul_nz by exact H. reflexivity. Qed.

Lemma lead_le : forall s, ~ In 0 s -> (trim_lead s <= length s)%nat.
Proof. intros s H. rewrite lead_eq by exact H. apply tw_len. Qed.

Lemma lead_blank : forall s i, ~ In 0 s -> (i < trim_lead s)%nat -> blank (nth i s 0) = true.
Proof. intros s i H Hi. rewrite lead_eq in Hi by exact H. apply tw_nth. exact Hi. Qed.

Lemma lead_stop : forall s, ~ In 0 s -> blank (nth (trim_lead s) s 0) = false.
Proof. intros s H. rewrite lead_eq by exact H. apply tw_stop. reflexivity. Qed.

Lemma s1_skipn : forall s, ~ In 0 s -> s1_of s = skipn (trim_lead s) s.
Proof. intros s H. rewrite lead_eq by exact H. unfold s1_of. symmetry. apply skipn_tw. Qed.

Lemma s1_len : forall s, ~ In 0 s -> length (s1_of s) = (length s - trim_lead s)%nat.
Proof. intros s H. rewrite s1_skipn by exact H. apply length_skipn. Qed.

Lemma nth_skipn0 : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma s1_nth : forall s j, ~ In 0 s -> nth j (s1_of s) 0 = nth (trim_lead s + j) s 0.
Proof. intros s j H. rewrite s1_skipn by exact H. apply nth_skipn0. Qed.

Lemma rtrim_len : forall s, ~ In 0 s -> length (r_trim s) = te s (length (s1_of s)).
Proof.
  intros s H. unfold r_trim. rewrite cut_nul_nz by exact H. fold (s1_of s). fold (te s (length (s1_of s))).
  rewrite length_firstn. pose proof (te_le s (length (s1_of s))). lia.
Qed.

(** trim's blank test: `bltu 0x20, c` (out when c > 32), then bit c of 0x100002200 = 2^32 + 2^13 + 2^9. *)
Lemma blank_le32 : forall c, blank c = true -> c <= 32.
Proof.
  intros c H. unfold blank in H.
  destruct (c =? 32) eqn:E1; [apply Z.eqb_eq in E1; lia|].
  destruct (c =? 9) eqn:E2; [apply Z.eqb_eq in E2; lia|].
  destruct (c =? 13) eqn:E3; [apply Z.eqb_eq in E3; lia|]. discriminate.
Qed.

Lemma blank_mask_b : forall c, 0 <= c <= 32 ->
  (Z.land (Z.shiftr 4294976000 (c mod 64)) 1 =? 0) = negb (blank c).
Proof.
  intros c Hc. destruct (Z_of_nat_complete c ltac:(lia)) as [n ->].
  assert (Hn : (n <= 32)%nat) by lia. clear Hc.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma blank_mask0 : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr 4294976000 (c mod 64)) 1 = 0 -> blank c = false.
Proof.
  intros c Hc H. pose proof (blank_mask_b c Hc) as E. apply Z.eqb_eq in H. rewrite H in E.
  destruct (blank c); [discriminate | reflexivity].
Qed.

Lemma blank_mask1 : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr 4294976000 (c mod 64)) 1 <> 0 -> blank c = true.
Proof.
  intros c Hc H. pose proof (blank_mask_b c Hc) as E. apply Z.eqb_neq in H. rewrite H in E.
  destruct (blank c); [reflexivity | discriminate].
Qed.

Lemma u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.

Lemma in_skipn' : forall {A} (x : A) k l, In x (skipn k l) -> In x l.
Proof. intros A x k l H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.

Lemma nz_bytes : forall bs, ~ In 0 (zs bs) -> ~ In ZERO bs.
Proof. intros bs H Hin. apply H. unfold zs. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

Lemma bytes_at_skip : forall segs m a (l : list byte) k, (k <= length l)%nat -> bytes_at segs m a l ->
  bytes_at segs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros segs m a l k Hk H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia. exact H.
Qed.

Lemma skipn_app_le : forall {A} k (l1 l2 : list A), (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof. intros A k l1 l2 H. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity. Qed.

(** The bytes at p after trim's store: the kept prefix of s and the NUL. *)
Lemma upd_prefix : forall (bs sl : list byte) k, (k <= length bs)%nat ->
  upd_bytes (bs ++ ZERO :: sl) k [ZERO] = (firstn k bs ++ [ZERO]) ++ skipn (k + 1) (bs ++ ZERO :: sl).
Proof.
  intros bs sl k H. unfold upd_bytes. rewrite firstn_app. replace (k - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. cbn [length]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma zb_firstn : forall bs k, zb (firstn k (zs bs)) = firstn k bs.
Proof. intros bs k. unfold zb. rewrite <- firstn_map. fold (zb (zs bs)). rewrite zb_zs. reflexivity. Qed.

End TrimSpine.
Import TrimSpine.

Theorem trim_holds : strlen_contract -> trim_contract.
Proof.
  intros SL. unfold trim_contract, TRIM, trim_pre, TRIM_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
    (P0 & CS & WR & AP & SO & MI).
  destruct CS as (bs & sl0 & BY0 & ZS & NZ & SL80).
  assert (LB : length bs = length s) by (rewrite <- ZS; symmetry; apply len_zs).
  rewrite <- LB in SL80.
  destruct (slack_cut _ _ _ _ _ BY0 SL80) as (sl & BY & SL7 & SL8). clear BY0 SL80 sl0.
  destruct SO as (ST & D16 & AL & NR).
  unfold apart in AP.
  pose proof (bytes_at_bound _ _ _ _ BY) as B1. rewrite length_app in B1. cbn [length] in B1.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (lead_le s NZ) as LL.
  pose proof (s1_len s NZ) as S1L.
  pose proof (rtrim_len s NZ) as RTL.
  pose proof (te_le s (length (s1_of s))) as TEL.
  assert (HR : forall i, 0 <= nth i s 0 < 256) by (intros i; rewrite <- ZS; apply zs_range).
  assert (HB : forall i, (i <= length s)%nat -> nth_error (bs ++ ZERO :: sl) i = Some (Z_to_bv 8 (nth i s 0)))
    by (intros i Hi; rewrite <- ZS; apply byte_at; lia).
  assert (HE : trim_end_addr (bv_unsigned a0) s =
               bv_unsigned a0 + Z.of_nat (trim_lead s) + Z.of_nat (te s (length (s1_of s))))
    by (unfold trim_end_addr; rewrite RTL; lia).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp);
              (trim_end_addr (bv_unsigned a0) s, trim_end_addr (bv_unsigned a0) s + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mm _) => set (POST := QQ); rename mm into M1 end.
  (* 0x1569c: s0 = s + trim_lead s; strlen(s0); back over the trailing blanks; *e = 0; return s0. *)
  assert (AFTER : forall (x8 x12 : word), bv_unsigned x8 = bv_unsigned a0 + Z.of_nat (trim_lead s) ->
    evt rsegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 x8 s1 (Z_to_bv 64 32) (Z_to_bv 64 4294976000)
               x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1569c) fc None M1 (seg_rom rsegs))).
  { intros x8 x12 H8.
    zstep. zstep.
    assert (BYL : bytes_at rsegs M1 (bv_unsigned x8) (skipn (trim_lead s) bs ++ ZERO :: sl)).
    { rewrite H8, <- skipn_app_le by lia. apply bytes_at_skip; [rewrite length_app; lia | exact BY]. }
    assert (NZL : ~ In (Z_to_bv 8 0) (skipn (trim_lead s) bs)).
    { intros Hin. apply in_skipn' in Hin. revert Hin. apply nz_bytes. rewrite ZS. exact NZ. }
    assert (SLK : (- (bv_unsigned x8 + Z.of_nat (length (skipn (trim_lead s) bs)) + 1)) mod 8 <= Z.of_nat (length sl)).
    { unfold hide in SL8. rewrite length_skipn, H8.
      replace (bv_unsigned a0 + Z.of_nat (trim_lead s) + Z.of_nat (length bs - trim_lead s))
        with (bv_unsigned a0 + Z.of_nat (length bs)) by lia. exact SL8. }
    eapply evt_cut; [eapply SL; [exact BYL | exact NZL | exact SLK | exact MI] |].
    intros ms' PO. unfold strlen_post in PO.
    destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & M2 & -> & MUc & WMc & MIc & BYc).
    transport_after_call rsegs M1 M2 MUc WMc.
    clear MUc WMc BYc BYL MI. rename MIc into MI.
    try replace (ret_pc (Z_to_bv 64 0x156a4)) with (Z_to_bv 64 0x156a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (LN : length (skipn (trim_lead s) bs) = length (s1_of s)) by (rewrite length_skipn, LB, S1L; reflexivity).
    rewrite LN. clear LN NZL SLK.
    (* 0x156d8: *e = 0, epilogue. *)
    assert (FINAL : forall (y10 y11 y12 y13 : word), bv_unsigned y11 = trim_end_addr (bv_unsigned a0) s ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0x156a4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp u0 u1 u2 x8 s1 y10 y11 y12 y13
                 ua4 ua5 ua6 ua7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x156d8) fc None M2 (seg_rom rsegs))).
    { intros y10 y11 y12 y13 G11.
      assert (Y11 : y11 = wa (trim_end_addr (bv_unsigned a0) s))
        by (unfold wa; rewrite <- G11; symmetry; apply Z_to_bv_lit_self).
      subst y11. clear G11.
      assert (HS : store_ok rsegs M2 (wa (trim_end_addr (bv_unsigned a0) s)) 1 = true).
      { unfold trim_end_addr.
        apply (wr_at_store_ok rsegs M2 (bv_unsigned a0) (Z.of_nat (length s) + 1)
                 (Z.of_nat (trim_lead s + length (r_trim s))) 1 WR); lia. }
      zstep.
      replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
      assert (ZF : forall k, zb (firstn k s) = firstn k bs) by (intros k; rewrite <- ZS; apply zb_firstn).
      assert (NEW : bytes_at rsegs (write_to_mem M2 (wa (trim_end_addr (bv_unsigned a0) s)) [ZERO]) (bv_unsigned a0)
                      (zb (firstn (trim_lead s + length (r_trim s)) s) ++ [ZERO])).
      { rewrite ZF. unfold trim_end_addr.
        pose proof (bytes_at_write_inside rsegs M2 (bv_unsigned a0) (bs ++ ZERO :: sl)
                      (Z.of_nat (trim_lead s + length (r_trim s))) [ZERO] BY) as NW.
        specialize (NW ltac:(lia) ltac:(rewrite Nat2Z.id, length_app; cbn [length]; lia)).
        rewrite Nat2Z.id in NW. rewrite upd_prefix in NW by lia.
        apply bytes_at_prefix in NW. exact NW. }
      store_done.
      zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      replace x8 with (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (trim_lead s))) by (rewrite <- H8; apply Z_to_bv_lit_self).
      unfold POST. finish. }
    (* LOOP 0x156bc: e = s0 + j, the bytes at j and after blank up to s0 + |s1|. *)
    assert (LOOP2 : forall (j : nat) (y11 y13 : word), (1 <= j <= length (s1_of s))%nat ->
      te s j = te s (length (s1_of s)) -> bv_unsigned y11 = bv_unsigned x8 + Z.of_nat j ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0x156a4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp u0 u1 u2 x8 s1 (Z_to_bv 64 32) y11
                 (Z_to_bv 64 4294976000) y13 ua4 ua5 ua6 ua7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x156bc) fc None M2 (seg_rom rsegs))).
    { induction j as [|j IH]; intros y11 y13 Hj Hte G11; [lia|].
      pose proof (HR (trim_lead s + j)%nat) as Rc.
      pose proof (te_S s j) as TS. rewrite (s1_nth s j NZ) in TS.
      assert (RD : ov_read_bytes rsegs M2 (Z_to_bv 64 (bv_unsigned y11 + -1)) 1 =
                   Some [Z_to_bv 8 (nth (trim_lead s + j) s 0)]).
      { apply (u8ro_read rsegs M2 (bv_unsigned a0) (bs ++ ZERO :: sl) (Z.of_nat (trim_lead s + j)) _ _ BY);
          [rewrite Nat2Z.id; apply HB; lia | lia | unfold wa; f_equal; lia]. }
      zstep. zstep. if_cases K; zify_cond K; rewrite ?u8 in K by exact Rc.
      - destruct (blank (nth (trim_lead s + j) s 0)) eqn:Bc; [apply blank_le32 in Bc; lia|].
        eapply FINAL. rewrite HE, <- Hte, TS. lia.
      - zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?u8 in K2 by exact Rc.
        + apply blank_mask0 in K2; [|lia]. rewrite K2 in TS.
          eapply FINAL. rewrite HE, <- Hte, TS. lia.
        + apply blank_mask1 in K2; [|lia]. rewrite K2 in TS.
          zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
          * eapply IH; [lia | rewrite <- TS; exact Hte | rewrite unsigned_lit by lia; lia].
          * assert (Ej : j = 0%nat) by lia. subst j.
            eapply FINAL. rewrite unsigned_lit by lia. rewrite HE, <- Hte, TS, te_0. lia. }
    zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - assert (N0 : length (s1_of s) = 0%nat) by lia.
      eapply FINAL. rewrite ?unsigned_lit by lia. rewrite HE, N0, te_0. lia.
    - zstep. zstep. zstep. zstep.
      eapply (LOOP2 (length (s1_of s))); [lia | reflexivity | rewrite ?unsigned_lit by lia; lia]. }
  (* LOOP 0x15680: s0 = s + i, the bytes before i blank. *)
  assert (LOOP1 : forall (k i : nat) (x8 x12 : word), (trim_lead s - i = k)%nat -> (i <= trim_lead s)%nat ->
    bv_unsigned x8 = bv_unsigned a0 + Z.of_nat i ->
    evt rsegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 x8 s1 (Z_to_bv 64 32) (Z_to_bv 64 4294976000)
               x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15680) fc None M1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i x8 x12 Hk Hi H8.
    - assert (Ei : i = trim_lead s) by lia. subst i.
      pose proof (HR (trim_lead s)) as Rc. pose proof (lead_stop s NZ) as Bc.
      assert (RD : ov_read_bytes rsegs M1 x8 1 = Some [Z_to_bv 8 (nth (trim_lead s) s 0)]).
      { apply (u8ro_read rsegs M1 (bv_unsigned a0) (bs ++ ZERO :: sl) (Z.of_nat (trim_lead s)) _ x8 BY);
          [rewrite Nat2Z.id; apply HB; lia | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
      zstep. zstep. if_cases K; zify_cond K; rewrite ?u8 in K by exact Rc.
      + apply AFTER. exact H8.
      + zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?u8 in K2 by exact Rc.
        * apply AFTER. exact H8.
        * exfalso. apply blank_mask1 in K2; [|pose proof (HR (trim_lead s)); lia]. congruence.
    - assert (Il : (i < trim_lead s)%nat) by lia.
      pose proof (HR i) as Rc. pose proof (lead_blank s i NZ Il) as Bc. pose proof (blank_le32 _ Bc) as Lc.
      assert (RD : ov_read_bytes rsegs M1 x8 1 = Some [Z_to_bv 8 (nth i s 0)]).
      { apply (u8ro_read rsegs M1 (bv_unsigned a0) (bs ++ ZERO :: sl) (Z.of_nat i) _ x8 BY);
          [rewrite Nat2Z.id; apply HB; lia | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
      zstep. zstep. if_cases K; zify_cond K; rewrite ?u8 in K by exact Rc.
      + exfalso. lia.
      + zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?u8 in K2 by exact Rc.
        * exfalso. apply blank_mask0 in K2; [|lia]. congruence.
        * zstep. zstep.
          eapply (IH (S i)); [lia | lia | rewrite unsigned_lit by lia; lia]. }
  eapply (LOOP1 (trim_lead s - 0)%nat 0%nat); [reflexivity | lia | lia].
Qed.
