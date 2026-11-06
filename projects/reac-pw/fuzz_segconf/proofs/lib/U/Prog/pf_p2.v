(** reac_segconf_parse_file, UBSan build (image 1696d6c34ffd): piece P2, the line driver (family F3,
    lib/U/Prog/reac_segconf_parse_file_pieces_c.v, S_P2). Written new.

    Code (UBSan binary):
      HEAD 0x153a8  s7 = p; s4 = lineno; 0x153b8 strchr(p, '\n'); nl = NULL -> 0x153d4 strlen(p), len, s2 = p + len
                    (trap 0x153dc: ~p < len); else (trap 0x153c0: nl == -1) len = nl - p, s2 = nl + 1;
                    0x153e8 s3 = lineno + 1 (trap 0x153ec); 0x153f4 len >= 512 -> LONG 0x153f8
      0x15448       memcpy(buf = sp + 0x1a8, p, len); trap 0x1545c (~buf < len, ~buf from the slot sp + 0x80);
                    buf[len] = 0; the strip_comment loop 0x15474 (a0 = buf + k, a1 = -k; traps 0x1548c a0 == 1,
                    0x1549c a0 == -1); 0x154b4 s4 = 9; 0x154bc trim(buf); empty -> TAIL, '[' -> HDR, else KEY
      TAIL 0x156a4  lbu *s2; bnez -> HEAD; j DONE 0x15c30
    The exits are instantiated at the line's start o, lineno ln and the lines read d ++ [pf_line s o]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env refuse_c reac_segconf_parse_file_c
  reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strchr_c strlen_c memcpy_c trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require SegBridge.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(** ** Memory facts over any segment list *)
Section Gen.
Variable segs : list Segment.

Lemma p2_dj_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma p2_rconf_munch : forall W m m' c rc,
  rconf_at segs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at segs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

(** A write apart from [a, a + length s + 8) keeps the C string at a: cstr_at needs at most 7 bytes of slack. *)
Lemma p2_cstr_trim : forall m a s, cstr_at segs m a s ->
  exists bs sl, bytes_at segs m a (bs ++ ZERO :: sl) /\ zs bs = s /\ ~ In 0 s /\
    Z.of_nat (length sl) = (- (a + Z.of_nat (length s) + 1)) mod 8.
Proof.
  intros m a s (bs & sl & B & Ez & N & S).
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  pose (k := Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8)).
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length s) + 1)) mod 8) by (unfold k; lia).
  clearbody k.
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  exists bs, (firstn k sl). split; [|split; [exact Ez|split; [exact N|rewrite Lk; exact Hk]]].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma p2_cstr_munch : forall W m m' a s,
  cstr_at segs m a s -> munch W m m' -> disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at segs m' a s.
Proof.
  intros W m m' a s C MU D.
  destruct (p2_cstr_trim m a s C) as (bs & sl & B & Ez & N & S).
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  assert (Lbs : length bs = length s) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  exists bs, sl. split; [|split; [exact Ez|split; [exact N|lia]]].
  eapply bytes_at_transport; [exact B | exact MU |].
  eapply p2_dj_sub; [exact D | lia |].
  rewrite length_app; cbn [length]. rewrite Lbs. lia.
Qed.

(** Every byte of a present stack region is a task byte (MemNorm.task_mem's condition). *)
Lemma p2_stk_task : forall m lo hi, MemNorm.task_mem segs m -> stk segs m lo hi ->
  forall x : word, lo <= bv_unsigned x < hi ->
  find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi T (_ & _ & S) x Hx. destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  unfold mrd in Hb. destruct (m x) as [b'|] eqn:E.
  - exact (T x b' E).
  - left. intros Nf. rewrite (MemNorm.seg_rom_unmapped segs x Nf) in Hb. discriminate.
Qed.

Lemma p2_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [O|O].
  - destruct (Z_lt_le_dec x l) as [A|A]; [left; split; [lia|exact O]|].
    destruct (Z_lt_le_dec x h) as [B|B]; [right; intros [C _]; lia | left; split; [lia|exact O]].
  - right. intros [_ C]. exact (O C).
Qed.

Lemma p2_task_munch : forall W m m', MemNorm.task_mem segs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) ->
     find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE) ->
  MemNorm.task_mem segs m'.
Proof.
  intros W m m' T MU H a b E. destruct (p2_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (T a b E).
  - exact (H a O).
Qed.

Lemma p2_saved_len : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; cbn [map concat length]; [reflexivity|].
  rewrite length_app, length_le8, IH. lia.
Qed.

Lemma p2_saved_nth : forall ws m a i w, saved_at segs m a ws -> nth_error ws i = Some w ->
  bytes_at segs m (a + 8 * Z.of_nat i) (le8 w).
Proof.
  induction ws as [|w0 ws IH]; intros m a i w H E; [destruct i; discriminate|].
  unfold saved_at in H. cbn [map concat] in H. apply bytes_at_app in H as [H0 H1].
  destruct i as [|i]; cbn [nth_error] in E.
  - injection E as <-. replace (a + 8 * Z.of_nat 0) with a by lia. exact H0.
  - rewrite length_le8 in H1. specialize (IH m (a + Z.of_nat 8) i w H1 E).
    replace (a + 8 * Z.of_nat (S i)) with (a + Z.of_nat 8 + 8 * Z.of_nat i) by lia. exact IH.
Qed.

Lemma p2_saved_munch : forall W m m' a ws, saved_at segs m a ws -> munch W m m' ->
  disjoint_from W a (8 * Z.of_nat (length ws)) -> saved_at segs m' a ws.
Proof.
  intros W m m' a ws H MU D. unfold saved_at in *. eapply bytes_at_transport; [exact H | exact MU |].
  rewrite p2_saved_len. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact D.
Qed.

(** One byte of a byte list in memory, as the load reads it. *)
Lemma p2_rd1 : forall m a B k b, bytes_at segs m a B -> nth_error B k = Some b ->
  ov_read_bytes segs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [b].
Proof.
  intros m a B k b H E. pose proof (nth_error_Some B k) as NS.
  assert (Hk : (k < length B)%nat) by (apply NS; rewrite E; discriminate).
  change (Z_to_bv 64 (a + Z.of_nat k)) with (wa (a + Z.of_nat k)).
  rewrite (bytes_at_ov_read segs m a B k 1 H) by lia.
  rewrite <- (firstn_skipn k B) in E. rewrite nth_error_app2 in E by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l, Nat.sub_diag in E by lia.
  destruct (skipn k B) as [|x r]; [discriminate|]. cbn in E. injection E as ->. reflexivity.
Qed.

Lemma p2_rd8 : forall m a w, bytes_at segs m a (le8 w) -> ov_read_bytes segs m (Z_to_bv 64 a) 8 = Some (le8 w).
Proof.
  intros m a w H. change (Z_to_bv 64 a) with (wa a). replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a (le8 w) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma p2_bytes_sub : forall m a B k j, bytes_at segs m a B -> (k + j <= length B)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn j (skipn k B)).
Proof.
  intros m a B k j H Hk. rewrite <- (firstn_skipn k B) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn j (skipn k B)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(** A present stack region is writable. *)
Lemma p2_stk_wr : forall m lo hi a k, stk segs m lo hi -> lo <= a -> 0 <= k -> a + k <= hi -> wr_at segs m a k.
Proof.
  intros m lo hi a k (H1 & H2 & H) Ha Hk Hh. split; [lia|]. split; [lia|].
  intros i Hi. apply H. lia.
Qed.

(** A region present before the writes, whose bytes are known after them, is still present. *)
Lemma p2_stk_bytes : forall m0 m a hi B, stk segs m0 a hi -> wmono segs m0 m -> bytes_at segs m a B ->
  hi - a <= Z.of_nat (length B) -> stk segs m a hi.
Proof.
  intros m0 m a hi B (H1 & H2 & H) WM (B1 & B2 & B3) Hl. split; [lia|]. split; [lia|].
  intros x Hx. split; [apply WM; apply H; exact Hx|].
  replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite B3 by lia.
  destruct (nth_error B (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma p2_wr_shrink : forall m a k k', wr_at segs m a k -> 0 <= k' <= k -> wr_at segs m a k'.
Proof. intros m a k k' (H1 & H2 & H) Hk. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

End Gen.

(** ** This build's image *)
Ltac sa_num := cbn [SA SEG_PLAIN SEG_UBSAN sa_img_end sa_img_top sa_guard sa_got_guard sa_catalogue] in *.

Lemma p2_ssp_munch : forall W m m', ssp_ok m -> munch W m m' -> disjoint_from W 0 (sa_img_end SA) -> ssp_ok m'.
Proof.
  intros W m m' (G1 & g & G2) MU D. split; [|exists g].
  - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8.
    eapply p2_dj_sub; [exact D | sa_num; lia | sa_num; lia].
  - eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8.
    eapply p2_dj_sub; [exact D | sa_num; lia | sa_num; lia].
Qed.

Lemma p2_cat_munch : forall W m m', cat_img rsegs m (sa_catalogue SA) -> munch W m m' ->
  disjoint_from W 0 (sa_img_end SA) -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros W m m' CAT MU D a Ha. rewrite <- (CAT a Ha). unfold mrd.
  sa_num. unfold CAT_BYTES in Ha.
  assert (Q : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  rewrite Q. reflexivity.
Qed.

(** The function's post from a cut, back across writes inside the function's own write list. *)
Lemma p2_ret_back : forall v Sp gp tp F m0 m lo c rcf W0 ms,
  0 <= Sp < 2 ^ 64 -> munch W0 m0 m -> wmono rsegs m0 m ->
  sub_fp W0 ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c) ->
  pf_ret v (Z_to_bv 64 Sp) gp tp F m lo c rcf ms -> pf_ret v (Z_to_bv 64 Sp) gp tp F m0 lo c rcf ms.
Proof.
  intros v Sp gp tp F m0 m lo c rcf W0 ms HS MU WM SUB
    (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & m' &
     E & FR & FK & MU' & WM' & MI' & TM' & STK' & Q).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m'.
  split; [exact E|]. split; [exact FR|]. split; [exact FK|]. split.
  - eapply munch_trans; [|exact MU']. eapply munch_weaken; [|exact MU]. rewrite unsigned_lit by lia. exact SUB.
  - split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact TM'|]. split; [exact STK'|exact Q].
Qed.

(** ** The tail: TAIL -> HEAD (pred n) or DONE *)
Lemma p2_zxb_eqb : forall (b : byte) z, 0 <= z < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 z) = (bv_unsigned b =? z).
Proof.
  intros b z Hz. pose proof (SegBridge.byte_range b) as R.
  unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma p2_tail : forall n, H_HEAD (pred n) -> H_DONE -> H_TAIL n.
Proof.
  intros n HH HD. unfold H_TAIL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d HCTX HST Hlt HREG HCUR.
  pose proof HREG as (E2 & _).
  pose proof HCTX as (ENV & TXT & SPILL & LCTX & CSR).
  destruct CSR as (bs & sl & BY & ZB & NZ & SL).
  subst s2. unfold PF_PC_TAIL.
  destruct bs as [|b bs'].
  - (* the text's NUL: DONE *)
    assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (t + Z.of_nat o)) 1 = Some [ZERO]).
    { replace (t + Z.of_nat o) with (t + Z.of_nat o + Z.of_nat 0) by lia.
      apply (p2_rd1 rsegs m _ ([] ++ ZERO :: sl) 0 ZERO BY). reflexivity. }
    step. step.
    replace (negb (bv_eqb (zxb ZERO) (Z_to_bv 64 0))) with false by (vm_compute; reflexivity). cbv iota.
    step.
    assert (E : skipn o s = []) by (rewrite <- ZB; reflexivity).
    rewrite E. cbn [lines lines_go length r_lines]. unfold pf_fin. cbn [fst].
    destruct SPILL as (SP1 & _ & _).
    pose proof (p2_saved_nth rsegs _ m (bv_unsigned sp + 0x10) 9 _ SP1 eq_refl) as SN.
    eapply HD; [exact ENV | exact (proj1 HST) |].
    replace (bv_unsigned sp + PF_NSLOT) with (bv_unsigned sp + 0x10 + 8 * Z.of_nat 9) by (unfold PF_NSLOT; lia).
    exact SN.
  - (* a byte of the next line: HEAD *)
    assert (Hb : bv_unsigned b <> 0).
    { intros E. apply NZ. rewrite <- ZB. cbn [zs map]. left. exact E. }
    assert (Ho : (o < length s)%nat).
    { pose proof (pfa_len_skipn o s) as LS. rewrite <- ZB in LS. cbn [zs map length] in LS. lia. }
    assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (t + Z.of_nat o)) 1 = Some [b]).
    { replace (t + Z.of_nat o) with (t + Z.of_nat o + Z.of_nat 0) by lia.
      apply (p2_rd1 rsegs m _ ((b :: bs') ++ ZERO :: sl) 0 b BY). reflexivity. }
    step. step.
    rewrite p2_zxb_eqb by lia. rewrite (proj2 (Z.eqb_neq _ _) Hb). cbn [negb]. cbv iota.
    eapply HH; [exact HCTX | exact HST | exact Ho | lia | exact HREG | exact HCUR].
Qed.

Lemma p2_in_wp : forall Sp x, ~ outside [(Sp - 32, Sp); (Sp + 424, Sp + 936)] x -> Sp - 32 <= x < Sp + 936.
Proof.
  intros Sp x H. cbn [outside] in H.
  destruct (Z_lt_le_dec x (Sp - 32)); [exfalso; apply H; repeat split; lia|].
  destruct (Z_lt_le_dec x (Sp + 936)); [lia|]. exfalso; apply H; repeat split; lia.
Qed.

Ltac dj := cbn [disjoint_from]; repeat split; lia.

(** ** The head: HEAD -> LONG, HDR, KEY or TAIL *)
Section Head.
Variable n : nat.
Hypotheses (HSC : strchr_contract) (HSL : strlen_contract) (HMC : memcpy_contract) (HTR : trim_contract).
Hypotheses (HLONG : H_LONG n) (HHDR : H_HDR n) (HKEY : H_KEY n) (HTAIL : H_TAIL n).
Variables (Sp : Z) (gp tp s6 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z)
  (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z)
  (d : list (list Z)).
Hypothesis HCTX : pf_hctx m0 fc Sp lo v c t s o ln d.
Hypothesis HST : pf_state m0 Sp c rc cur nm (length (skipn o s)).
Hypothesis Ho : (o < length s)%nat.
Hypothesis Hn : (length (skipn o s) <= n)%nat.
Hypothesis HCUR : pf_curslot m0 Sp c cur.

Local Notation L := (pf_line s o).
Local Notation o' := (pf_next s o).
Local Notation TL := (pf_tline s o).
Local Notation Wp := [(Sp - 32, Sp); (Sp + 424, Sp + 936)].
Local Notation POST := (pf_fin v (Z_to_bv 64 Sp) gp tp F m0 lo c
  (r_lines (r_line rc cur nm (ln + 1) L) (ln + 1) (lines (skipn o' s)))).
Local Notation MST pc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s8 t3 t4 t5 t6 m :=
  (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 59) (Z_to_bv 64 32) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
           (Z_to_bv 64 (-1)) s6 s7 s8 s9 (Z_to_bv 64 35) (Z_to_bv 64 1) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Local Notation INV m B := (munch Wp m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m lo Sp /\
  bytes_at rsegs m (Sp + 424) B /\ length B = 520%nat).

Lemma nums : 0 <= lo /\ lo + 6032 <= Sp /\ Sp + 1056 < 2 ^ 63 /\ 344200 <= lo /\ Sp mod 16 = 0 /\
  0 < t /\ t + Z.of_nat (length s) + 1 <= 2 ^ 64 /\ (t + Z.of_nat (length s) + 8 <= lo \/ Sp + 1056 <= t) /\
  ~ In 0 s /\ Z.of_nat (length s) <= 65535 /\ 0 <= ln <= Z.of_nat o.
Proof.
  pose proof HCTX as ((C0 & C16 & APc & BN & (FRM & TM & SSP & IL & SPH) & CAT & (ST0 & DEP & SP16 & NR) & MI0 & SV) &
                      (T0 & CS & LS & APt & APtc) & _ & LCTX & _).
  pose proof (pf_lctx_ln s o ln d LCTX) as (LN & _).
  destruct CS as (bs & sl & BY & ZB & NZ & _). pose proof (bytes_at_bound _ _ _ _ BY) as BB.
  assert (Lbs : length bs = length s) by (rewrite <- ZB; unfold zs; symmetry; apply length_map).
  rewrite length_app in BB. cbn [length] in BB.
  unfold apart, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *. sa_num.
  destruct ST0 as (LO0 & _).
  pose proof (proj1 (Nat2Z.inj_le _ _) LS) as LSZ.
  replace (Z.of_nat 65535) with 65535 in LSZ by (vm_compute; reflexivity).
  assert (M16 : Sp mod 16 = 0).
  { rewrite <- (Z_mod_plus_full Sp 66 16). replace (Sp + 66 * 16) with (Sp + 1056) by lia. exact SP16. }
  repeat split; try lia; try exact NZ; try exact M16.
Qed.

Lemma wp_sub : sub_fp Wp ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c).
Proof.
  unfold sub_fp. intros x Hx. cbn [outside] in *.
  unfold PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in Hx. destruct Hx as (H1 & _).
  repeat split; intros [A B]; apply H1; split; lia.
Qed.

(** What every exit needs of the memory at the exit, from the memory at the head. *)
Lemma tr : forall m B k, INV m B -> (k <= length (skipn o s))%nat ->
  pf_env m fc Sp lo c v /\ pf_text m Sp lo c t s /\ pf_spill m Sp c /\ pf_state m Sp c rc cur nm k /\
  pf_curslot m Sp c cur.
Proof.
  intros m B k (MU & WM & MI & STK & BB & LB) Hk.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof HCTX as ((C0 & C16 & APc & BN & (FRM & TM & SSP & IL & SPH) & CAT & (ST0 & DEP & SP16 & NR) & MI0 & SV) &
                      (T0 & CS & LS & APt & APtc) & (SP1 & SP2 & SP3) & LCTX & CSR).
  pose proof HST as (RC & CO & (f & BF & ENC) & CNT).
  pose proof APc as APc'. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in APc'.
  assert (D0 : disjoint_from Wp 0 (sa_img_end SA)) by (sa_num; dj).
  destruct (stk_split rsegs m0 lo Sp (Sp + PARSE_FILE_FRAME) ST0 ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ S1].
  destruct (stk_split rsegs m0 Sp (Sp + 424) (Sp + PARSE_FILE_FRAME) S1 ltac:(unfold PARSE_FILE_FRAME; lia))
    as [S2 S3].
  destruct (stk_split rsegs m0 (Sp + 424) (Sp + 936) (Sp + PARSE_FILE_FRAME) S3 ltac:(unfold PARSE_FILE_FRAME; lia))
    as [S4 S5].
  split; [|split; [|split; [|split]]].
  - split; [exact C0|]. split; [exact C16|]. split; [exact APc|]. split; [exact BN|].
    split.
    { split; [exact FRM|]. split.
      - eapply p2_task_munch; [exact TM | exact MU |]. intros x Hx.
        apply (p2_stk_task rsegs m0 lo (Sp + PARSE_FILE_FRAME) TM ST0).
        pose proof (p2_in_wp Sp _ Hx). unfold PARSE_FILE_FRAME. lia.
      - split; [eapply p2_ssp_munch; [exact SSP | exact MU | exact D0]|]. split; [exact IL | exact SPH]. }
    split; [eapply p2_cat_munch; [exact CAT | exact MU | exact D0]|].
    split.
    { split; [|split; [exact DEP | split; [exact SP16 | exact NR]]].
      apply (stk_merge rsegs m lo Sp (Sp + PARSE_FILE_FRAME)); [exact STK | | unfold PARSE_FILE_FRAME; lia].
      apply (stk_merge rsegs m Sp (Sp + 424) (Sp + PARSE_FILE_FRAME)); [| | unfold PARSE_FILE_FRAME; lia].
      - eapply stk_transport_disjoint; [exact S2 | exact MU | exact WM | dj].
      - apply (stk_merge rsegs m (Sp + 424) (Sp + 936) (Sp + PARSE_FILE_FRAME)); [| | unfold PARSE_FILE_FRAME; lia].
        + eapply p2_stk_bytes; [exact S4 | exact WM | exact BB | rewrite LB; lia].
        + eapply stk_transport_disjoint; [exact S5 | exact MU | exact WM | unfold PARSE_FILE_FRAME; dj]. }
    split; [exact MI|].
    eapply p2_saved_munch; [exact SV | exact MU | cbn [sv_list length]; unfold PF_SAVE; dj].
  - split; [exact T0|]. split; [eapply p2_cstr_munch; [exact CS | exact MU | dj]|].
    split; [exact LS|]. split; [exact APt | exact APtc].
  - split; [eapply p2_saved_munch; [exact SP1 | exact MU | cbn [length]; dj]|].
    split; [eapply p2_saved_munch; [exact SP2 | exact MU | cbn [length]; dj]|].
    eapply bytes_at_transport; [exact SP3 | exact MU | rewrite length_le8; unfold PF_CSLOT; dj].
  - split; [eapply p2_rconf_munch; [exact RC | exact MU | unfold SEG_C_SIZE; dj]|].
    split; [exact CO|]. split; [|eapply pf_cnt_mono; [exact Hk | exact CNT]].
    exists f. split; [|exact ENC]. destruct ENC as (Lf & _).
    eapply bytes_at_transport; [exact BF | exact MU | rewrite Lf; unfold PF_NAMEBUF; dj].
  - eapply bytes_at_transport; [exact HCUR | exact MU | rewrite length_le8; unfold PF_CURSLOT; dj].
Qed.

Lemma lines_step : r_lines (rc, cur, nm) ln (lines (skipn o s)) =
  r_lines (r_line rc cur nm (ln + 1) L) (ln + 1) (lines (skipn o' s)).
Proof. rewrite (r_lines_skipn_step s o (rc, cur, nm) ln Ho). reflexivity. Qed.

(** ** The exits *)
Lemma exit_tail : forall m B (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 t3 t4 t5 t6 : word),
  INV m B -> (length L < 512)%nat -> hd0 TL = 0 ->
  evt rsegs POST (MST 0x156a4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) s4 s7 s8 t3 t4 t5 t6 m).
Proof.
  intros m B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 t3 t4 t5 t6 IV HL HE.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof (pf_next_le s o Ho) as NL. pose proof (pf_next_skipn_lt s o Ho) as NLT.
  pose proof HCTX as (_ & _ & _ & LCTX & _).
  destruct (tr m B (length (skipn o' s)) IV ltac:(lia)) as (ENV & TXT & SPILL & STATE & CUR).
  pose proof IV as (MU & WM & _).
  rewrite (r_line_short rc cur nm (ln + 1) s o HL), HE, Z.eqb_refl. cbv iota.
  eapply evt_mono.
  - apply (HTAIL ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 59) (Z_to_bv 64 32) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6 s7 s8 s9
             (Z_to_bv 64 35) (Z_to_bv 64 1) t3 t4 t5 t6 F fc m lo v c t s rc cur nm o' (ln + 1) (d ++ [L]));
      rewrite ?unsigned_lit by lia.
    + split; [exact ENV|]. split; [exact TXT|]. split; [exact SPILL|]. split.
      * apply pf_lctx_next; [exact NZs | exact LCTX | exact Ho].
      * apply L_cstr_skipn_holds; [exact (proj1 (proj2 TXT)) | exact NL].
    + exact STATE.
    + lia.
    + unfold pf_regs. repeat split.
    + exact CUR.
  - intros ms H. eapply p2_ret_back; [lia | exact MU | exact WM | exact wp_sub | exact H].
Qed.

Lemma exit_long : forall m B (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  INV m B -> (512 <= length L)%nat ->
  evt rsegs POST (MST 0x153f8 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (t + Z.of_nat o)) (Z_to_bv 64 (Z.of_nat (length L)))
                      t3 t4 t5 t6 m).
Proof.
  intros m B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 IV HL.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof HCTX as (_ & _ & _ & LCTX & _).
  destruct (tr m B (length (skipn o s)) IV ltac:(lia)) as (ENV & TXT & SPILL & STATE & CUR).
  pose proof IV as (MU & WM & _).
  eapply evt_mono.
  - apply (HLONG ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 59) (Z_to_bv 64 32) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 (t + Z.of_nat o)) (Z_to_bv 64 (Z.of_nat (length L))) s9
             (Z_to_bv 64 35) (Z_to_bv 64 1) t3 t4 t5 t6 F fc m lo v c t s rc cur nm o ln (d ++ [L]));
      rewrite ?unsigned_lit by lia.
    + split; [exact ENV|]. split; [exact TXT|]. split; [exact SPILL|]. split; [exact Ho|]. split; [exact Hn|].
      apply pf_lctx_next; [exact NZs | exact LCTX | exact Ho].
    + exact STATE.
    + unfold pf_regs. repeat split.
    + exact CUR.
    + reflexivity.
    + reflexivity.
    + exact HL.
  - intros ms H. eapply p2_ret_back; [lia | exact MU | exact WM | exact wp_sub | exact H].
Qed.

Lemma exit_hdr : forall m B lp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
  INV m B -> (length L < 512)%nat -> cstr_at rsegs m lp TL -> pf_inb (Sp + PF_BUF) lp TL -> hd0 TL = LBR ->
  evt rsegs POST (MST 0x154d4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 9) (Z_to_bv 64 lp) s8 t3 t4 t5 t6 m).
Proof.
  intros m B lp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 IV HL CL IB HE.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof HCTX as (_ & _ & _ & LCTX & _).
  destruct (tr m B (length (skipn o s)) IV ltac:(lia)) as (ENV & TXT & SPILL & STATE & CUR).
  pose proof IV as (MU & WM & _).
  rewrite (r_line_short rc cur nm (ln + 1) s o HL), HE. change (91 =? 0) with false. change (91 =? 91) with true.
  cbv iota.
  eapply evt_mono.
  - apply (HHDR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 59) (Z_to_bv 64 32) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 lp) s8 s9 (Z_to_bv 64 35) (Z_to_bv 64 1) t3 t4 t5 t6 F fc m lo v c t s rc cur nm o ln
             (d ++ [L]) lp);
      rewrite ?unsigned_lit by lia.
    + split; [exact ENV|]. split; [exact TXT|]. split; [exact SPILL|]. split; [exact Ho|]. split; [exact Hn|].
      apply pf_lctx_next; [exact NZs | exact LCTX | exact Ho].
    + exact STATE.
    + unfold pf_regs. repeat split.
    + exact CUR.
    + reflexivity.
    + exact HL.
    + reflexivity.
    + exact CL.
    + exact IB.
    + exact HE.
  - intros ms H. eapply p2_ret_back; [lia | exact MU | exact WM | exact wp_sub | exact H].
Qed.

Lemma exit_key : forall m B lp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 : word),
  INV m B -> (length L < 512)%nat -> cstr_at rsegs m lp TL -> pf_inb (Sp + PF_BUF) lp TL ->
  hd0 TL <> 0 -> hd0 TL <> LBR ->
  evt rsegs POST (MST 0x154fc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 lp) s8 t3 t4 t5 t6 m).
Proof.
  intros m B lp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 IV HL CL IB H0 H1.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof HCTX as (_ & _ & _ & LCTX & _).
  destruct (tr m B (length (skipn o s)) IV ltac:(lia)) as (ENV & TXT & SPILL & STATE & CUR).
  pose proof IV as (MU & WM & _).
  rewrite (r_line_short rc cur nm (ln + 1) s o HL), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1).
  cbv iota.
  eapply evt_mono.
  - apply (HKEY ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 59) (Z_to_bv 64 32) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 lp) s8 s9 (Z_to_bv 64 35) (Z_to_bv 64 1) t3 t4 t5 t6 F fc m lo v c t s rc cur nm o ln
             (d ++ [L]) lp);
      rewrite ?unsigned_lit by lia.
    + split; [exact ENV|]. split; [exact TXT|]. split; [exact SPILL|]. split; [exact Ho|]. split; [exact Hn|].
      apply pf_lctx_next; [exact NZs | exact LCTX | exact Ho].
    + exact STATE.
    + unfold pf_regs. repeat split.
    + exact CUR.
    + exact HL.
    + reflexivity.
    + exact CL.
    + exact IB.
    + exact H0.
    + exact H1.
  - intros ms H. eapply p2_ret_back; [lia | exact MU | exact WM | exact wp_sub | exact H].
Qed.

Lemma p2_eqb_false : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy H. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact H. Qed.
Lemma p2_eqb_true : forall x y, 0 <= x < 2 ^ 64 -> x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y Hx H. subst y. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma p2_eqb_m1_false : forall x, 0 <= x < 2 ^ 64 - 1 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite unsigned_lit by lia. rewrite unsigned_lit_wrap.
  apply Z.eqb_neq. change ((-1) mod 2 ^ 64) with 18446744073709551615. lia.
Qed.
Lemma p2_ltu_true : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x < y ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y Hx Hy H. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. exact H. Qed.
Lemma p2_ltu_false : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y <= x ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy H. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. exact H. Qed.

Lemma p2_not_ltu_false : forall p l, 0 <= p < 2 ^ 64 -> 0 <= l -> p + l <= 2 ^ 64 - 1 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 p)) 18446744073709551615)) (Z_to_bv 64 l) = false.
Proof.
  intros p l Hp Hl H. rewrite (unsigned_lit p) by lia. rewrite zb_lxor_ones by lia.
  apply p2_ltu_false; lia.
Qed.

Lemma p2_zb_zs : forall bs : list byte, zb (zs bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [zs zb map] in *. f_equal; [|exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(** ** The invariant along the walk *)
Lemma inv0 : exists B0, INV m0 B0.
Proof.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & _).
  pose proof HCTX as ((_ & _ & _ & _ & _ & _ & (ST0 & _ & _ & _) & MI0 & _) & _).
  destruct (stk_split rsegs m0 lo Sp (Sp + PARSE_FILE_FRAME) ST0 ltac:(unfold PARSE_FILE_FRAME; lia)) as [STL S1].
  destruct (stk_split rsegs m0 Sp (Sp + 424) (Sp + PARSE_FILE_FRAME) S1 ltac:(unfold PARSE_FILE_FRAME; lia))
    as [_ S3].
  destruct (stk_split rsegs m0 (Sp + 424) (Sp + 944) (Sp + PARSE_FILE_FRAME) S3 ltac:(unfold PARSE_FILE_FRAME; lia))
    as [S4 _].
  destruct (stk_bytes rsegs m0 (Sp + 424) (Sp + 944) S4 ltac:(lia)) as (B0 & LB0 & BB0).
  exists B0. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI0|].
  split; [exact STL|]. split; [exact BB0|]. rewrite LB0. replace (Sp + 944 - (Sp + 424)) with 520 by lia.
  reflexivity.
Qed.

Lemma inv_step : forall m m' B B' W, INV m B -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  sub_fp W Wp -> stk rsegs m' lo Sp -> bytes_at rsegs m' (Sp + 424) B' -> length B' = 520%nat -> INV m' B'.
Proof.
  intros m m' B B' W (MU & WM & _) MU' WM' MI' SUB ST BB LB.
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [exact SUB | exact MU']]|].
  split; [eapply wmono_trans; eassumption|]. tauto.
Qed.

Lemma inv_keep : forall m m' B W, INV m B -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  sub_fp W Wp -> stk rsegs m' lo Sp -> disjoint_from W (Sp + 424) 520 -> INV m' B.
Proof.
  intros m m' B W IV MU' WM' MI' SUB ST D. pose proof IV as (_ & _ & _ & _ & BB & LB).
  eapply inv_step; try eassumption. eapply bytes_at_transport; [exact BB | exact MU' | rewrite LB; exact D].
Qed.

Lemma sub_stk : sub_fp [(Sp - 32, Sp)] Wp.
Proof. intros x (H & _). cbn [outside]. split; [exact H | exact I]. Qed.
Lemma sub_nil : sub_fp [] Wp.
Proof. intros x _. exact I. Qed.

Lemma p2_zb_firstn : forall k l, zb (firstn k l) = firstn k (zb l).
Proof. intros k l. unfold zb. symmetry. apply firstn_map. Qed.

Lemma line_bytes : forall bs, zs bs = skipn o s -> zb L = firstn (length L) bs.
Proof.
  intros bs ZB. pose proof nums as (_ & _ & _ & _ & _ & _ & _ & _ & NZs & _).
  pose proof (L_line_bytes_holds s o NZs) as (E & _).
  rewrite E at 1. rewrite <- ZB, p2_zb_firstn, p2_zb_zs. reflexivity.
Qed.

Lemma p2_swrap32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma p2_lts_false : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> y <= x ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy H. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  apply Z.ltb_ge. exact H.
Qed.

Lemma wr_buf : forall m B, INV m B -> wr_at rsegs m (Sp + 424) 520.
Proof.
  intros m B (_ & WM & _).
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & _).
  pose proof HCTX as ((_ & _ & _ & _ & _ & _ & (ST0 & _ & _ & _) & _ & _) & _).
  eapply wr_at_transport; [|exact WM].
  eapply p2_stk_wr; [exact ST0 | lia | lia | unfold PARSE_FILE_FRAME; lia].
Qed.

Lemma p2_pfnot_ltu : forall x l, 0 <= x < 2 ^ 64 -> 0 <= l < 2 ^ 64 -> x + l <= 2 ^ 64 - 1 ->
  bv_ltu (pf_not x) (Z_to_bv 64 l) = false.
Proof.
  intros x l Hx Hl H. unfold pf_not. rewrite bv_ltu_Z, unsigned_lit_wrap, (unsigned_lit l) by lia.
  replace (- x - 1) with ((2 ^ 64 - x - 1) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia.
  apply Z.ltb_ge. lia.
Qed.

Lemma p2_firstn_add : forall {A} (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a. induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. f_equal. apply IH.
Qed.
Lemma p2_le1_0 : le1 (Z_to_bv 64 0) = [ZERO].
Proof. reflexivity. Qed.
Lemma p2_zs_firstn : forall k (l : list byte), zs (firstn k l) = firstn k (zs l).
Proof. intros k l. unfold zs. symmetry. apply firstn_map. Qed.
Lemma p2_zs_skipn : forall k (l : list byte), zs (skipn k l) = skipn k (zs l).
Proof. intros k l. unfold zs. symmetry. apply pfa_skipn_map. Qed.
Lemma p2_zs_len : forall l : list byte, length (zs l) = length l.
Proof. intros l. unfold zs. apply length_map. Qed.
Lemma p2_nth_zs : forall k (l : list byte), bv_unsigned (nth k l ZERO) = nth k (zs l) 0.
Proof. intros k l. unfold zs. rewrite <- (map_nth bv_unsigned l ZERO k). reflexivity. Qed.

(** ** After the strip loop, 0x154b4: s4 = '\t', trim(buf), the dispatch on its first byte *)
Lemma after_strip : forall SB R4 m4 (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 : word),
  (length L < 512)%nat -> zs SB = r_strip_comment L -> ~ In ZERO SB ->
  INV m4 (SB ++ ZERO :: R4) -> (length SB + 1 + length R4 = 520)%nat ->
  evt rsegs POST (MST 0x154b4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m4).
Proof.
  intros SB R4 m4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 HL ESB NSB IV LSB.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof IV as (MU & WM & MI & STK & BB & LB4).
  pose proof (r_strip_comment_len_le L) as SLe.
  assert (LSBL : (length SB <= length L)%nat) by (rewrite <- (p2_zs_len SB), ESB; exact SLe).
  pose proof HCTX as ((_ & _ & _ & _ & _ & _ & (ST0 & _ & _ & NR) & _ & _) & _).
  pose proof (wr_buf m4 _ IV) as WB.
  pose proof (Z.mod_pos_bound (- (Sp + 424 + Z.of_nat (length (zs SB)) + 1)) 8 ltac:(lia)) as MB.
  rewrite p2_zs_len in MB.
  step. step. step.
  eapply evt_cut.
  { eapply HTR with (s := zs SB) (lo := lo); rewrite ?unsigned_lit by lia.
    unfold trim_pre. split; [lia|]. split.
    - exists SB, R4. split; [exact BB|]. split; [reflexivity|]. split; [apply SegBridge.zs_nulfree; exact NSB|].
      rewrite p2_zs_len. lia.
    - split; [eapply p2_wr_shrink; [exact WB | rewrite p2_zs_len; lia]|].
      split; [unfold apart; right; lia|].
      split; [|exact MI].
      split; [exact STK|]. split; [unfold TRIM_STACK; lia|]. split; [exact M16|].
      intros a Ha. apply NR. unfold PARSE_FILE_FRAME. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 &
              -> & MU5 & WM5 & MI5 & STK5 & Q5).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit Sp) in MU5, STK5 by lia. rewrite (unsigned_lit (Sp + 424)) in MU5, Q5 by lia.
  rewrite (unsigned_lit (Sp + 424)) by lia.
  unfold trim_end_addr, TRIM_STACK in MU5.
  destruct (L_trim_holds (zs SB) (SegBridge.zs_nulfree SB NSB)) as (LT1 & LT2 & LT3).
  rewrite p2_zs_len in LT1.
  set (lead := trim_lead (zs SB)) in *. set (rtl := length (r_trim (zs SB))) in *.
  set (RB := firstn rtl (skipn lead SB)).
  assert (ERB : zs RB = r_trim (zs SB)) by (unfold RB; rewrite p2_zs_firstn, p2_zs_skipn; symmetry; exact LT2).
  assert (LRB : length RB = rtl) by (unfold RB; rewrite length_firstn, length_skipn; lia).
  assert (ETL : TL = zs RB) by (unfold pf_tline; rewrite <- ESB, ERB; reflexivity).
  assert (NRB : ~ In ZERO RB).
  { intros H. apply NSB. unfold RB in H.
    rewrite <- (firstn_skipn lead SB). apply in_or_app. right.
    rewrite <- (firstn_skipn rtl (skipn lead SB)). apply in_or_app. left. exact H. }
  set (R5 := skipn (lead + rtl + 1) (SB ++ ZERO :: R4)).
  assert (LR5 : length R5 = (520 - (lead + rtl + 1))%nat) by (unfold R5; rewrite length_skipn, length_app; cbn [length]; lia).
  assert (EF : firstn (lead + rtl) SB = firstn lead SB ++ RB) by (unfold RB; apply p2_firstn_add).
  assert (Q5' : bytes_at rsegs m5 (Sp + 424) (firstn lead SB ++ RB ++ [ZERO])).
  { rewrite app_assoc, <- EF. rewrite <- (p2_zb_zs (firstn (lead + rtl) SB)), p2_zs_firstn. exact Q5. }
  assert (T5 : bytes_at rsegs m5 (Sp + 424 + Z.of_nat (lead + rtl + 1)) R5).
  { assert (BB4 : bytes_at rsegs m4 (Sp + 424 + Z.of_nat (lead + rtl + 1)) R5).
    { pose proof (p2_bytes_sub rsegs m4 _ _ (lead + rtl + 1) (length R5) BB) as BS.
      change (skipn (lead + rtl + 1) (SB ++ ZERO :: R4)) with R5 in BS.
      rewrite firstn_all2 in BS by lia. apply BS. rewrite LR5, length_app. cbn [length]. lia. }
    eapply bytes_at_transport; [exact BB4 | exact MU5 |]. dj. }
  assert (LFL : length (firstn lead SB) = lead) by (rewrite length_firstn; lia).
  assert (BL5 : bytes_at rsegs m5 (Sp + 424 + Z.of_nat lead) (RB ++ ZERO :: R5)).
  { apply bytes_at_app in Q5' as [_ Q5']. rewrite LFL in Q5'.
    replace (RB ++ ZERO :: R5) with ((RB ++ [ZERO]) ++ R5) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact Q5'|]. rewrite length_app, LRB. cbn [length].
    replace (Sp + 424 + Z.of_nat lead + Z.of_nat (rtl + 1)) with (Sp + 424 + Z.of_nat (lead + rtl + 1)) by lia.
    exact T5. }
  assert (BB5 : bytes_at rsegs m5 (Sp + 424) (firstn lead SB ++ RB ++ ZERO :: R5)).
  { apply bytes_at_app. split; [apply bytes_at_app in Q5' as [Q5' _]; exact Q5'|]. rewrite LFL. exact BL5. }
  assert (IV5 : INV m5 (firstn lead SB ++ RB ++ ZERO :: R5)).
  { eapply inv_step; [exact IV | exact MU5 | exact WM5 | exact MI5 | | exact STK5 | exact BB5 |].
    - intros x (H1 & H2 & _). cbn [outside]. split; [exact H1|]. split; [|exact I].
      intros [A1 A2]. apply H2. split; lia.
    - rewrite length_app, length_app, LFL, LRB. cbn [length]. lia. }
  assert (CT : cstr_at rsegs m5 (Sp + 424 + Z.of_nat lead) TL).
  { rewrite ETL. exists RB, R5. split; [exact BL5|]. split; [reflexivity|].
    split; [apply SegBridge.zs_nulfree; exact NRB|].
    pose proof (Z.mod_pos_bound (- (Sp + 424 + Z.of_nat lead + Z.of_nat (length (zs RB)) + 1)) 8 ltac:(lia)).
    lia. }
  assert (IBT : pf_inb (Sp + PF_BUF) (Sp + 424 + Z.of_nat lead) TL).
  { unfold pf_inb, PF_BUF. rewrite ETL, p2_zs_len, LRB. lia. }
  step.
  destruct RB as [|b RB'] eqn:ERBc.
  - (* the trimmed line is empty: TAIL *)
    assert (RD : ov_read_bytes rsegs m5 (Z_to_bv 64 (Sp + 424 + Z.of_nat lead)) 1 = Some [ZERO]).
    { replace (Sp + 424 + Z.of_nat lead) with (Sp + 424 + Z.of_nat lead + Z.of_nat 0) by lia.
      apply (p2_rd1 rsegs m5 _ _ 0 ZERO BL5). reflexivity. }
    step. step.
    replace (bv_eqb (zxb ZERO) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity). cbv iota.
    eapply exit_tail; [exact IV5 | exact HL |]. rewrite ETL. reflexivity.
  - assert (RD : ov_read_bytes rsegs m5 (Z_to_bv 64 (Sp + 424 + Z.of_nat lead)) 1 = Some [b]).
    { replace (Sp + 424 + Z.of_nat lead) with (Sp + 424 + Z.of_nat lead + Z.of_nat 0) by lia.
      apply (p2_rd1 rsegs m5 _ _ 0 b BL5). reflexivity. }
    assert (Hb : bv_unsigned b <> 0).
    { intros E. apply NRB. left. apply bv_eq. rewrite E. reflexivity. }
    assert (HD : hd0 TL = bv_unsigned b) by (rewrite ETL; reflexivity).
    step. step. rewrite p2_zxb_eqb by lia. rewrite (proj2 (Z.eqb_neq _ _) Hb). cbv iota.
    step. step. rewrite p2_zxb_eqb by lia.
    destruct (Z.eqb_spec (bv_unsigned b) 91) as [E91|N91]; cbn [negb]; cbv iota.
    + eapply exit_hdr; [exact IV5 | exact HL | exact CT | exact IBT | rewrite HD; exact E91].
    + eapply exit_key; [exact IV5 | exact HL | exact CT | exact IBT | rewrite HD; exact Hb | rewrite HD; exact N91].
Qed.

(** ** The strip_comment loop 0x15474 (a0 = buf + k, a1 = -k) *)
Lemma p2_if_eqb_false : forall (b : byte) z (X Y : word), 0 <= z < 2 ^ 64 -> bv_unsigned b <> z ->
  (if bv_eqb (zxb b) (Z_to_bv 64 z) then X else Y) = Y.
Proof. intros b z X Y Hz H. rewrite p2_zxb_eqb by lia. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma p2_if_eqb_true : forall (b : byte) z (X Y : word), 0 <= z < 2 ^ 64 -> bv_unsigned b = z ->
  (if bv_eqb (zxb b) (Z_to_bv 64 z) then X else Y) = X.
Proof. intros b z X Y Hz H. rewrite p2_zxb_eqb by lia. rewrite H, Z.eqb_refl. reflexivity. Qed.
Lemma p2_eqb_neg_false : forall k, 0 < k < 2 ^ 64 -> bv_eqb (Z_to_bv 64 (- k)) (Z_to_bv 64 0) = false.
Proof.
  intros k Hk. unfold bv_eqb. rewrite unsigned_lit_wrap, (unsigned_lit 0) by lia. apply Z.eqb_neq.
  replace (- k) with ((2 ^ 64 - k) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.
Ltac bz := try change (bv_unsigned ZERO) with 0 in *; lia.
Ltac alia := rewrite ?unsigned_lit by lia; lia.

Lemma L_bytes : exists LB, zs LB = L /\ ~ In ZERO LB.
Proof.
  pose proof nums as (_ & _ & _ & _ & _ & _ & _ & _ & NZs & _).
  pose proof HCTX as (_ & _ & _ & _ & CSR). destruct CSR as (bs & sl & _ & ZB & _ & _).
  pose proof (L_line_bytes_holds s o NZs) as (E & NL0 & _).
  exists (firstn (length L) bs). split.
  - rewrite p2_zs_firstn, ZB. symmetry. exact E.
  - apply SegBridge.nul_free_bytes. rewrite p2_zs_firstn, ZB, <- E. exact NL0.
Qed.

Lemma inv_store0 : forall m B k, INV m B -> (k < 512)%nat ->
  INV (write_to_mem m (Z_to_bv 64 (Sp + 424 + Z.of_nat k)) [ZERO]) (upd_bytes B k [ZERO]).
Proof.
  intros m B k IV Hk. pose proof nums as (LO0 & LOS & SPH' & _).
  pose proof IV as (MU & WM & MI & STK & BB & LBl).
  pose proof (wr_buf m _ IV) as WB.
  pose proof (wr_at_store_ok rsegs m (Sp + 424) 520 (Z.of_nat k) 1 WB ltac:(lia) ltac:(lia)) as HS.
  fold (wa (Sp + 424 + Z.of_nat k)).
  split; [eapply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact STK | lia | cbn [length]; lia]|].
  split.
  - pose proof (bytes_at_write_inside rsegs m (Sp + 424) B (Z.of_nat k) [ZERO] BB ltac:(lia)
                  ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as W.
    rewrite Nat2Z.id in W. exact W.
  - rewrite upd_bytes_length by (cbn [length]; lia). exact LBl.
Qed.

Lemma upd_line : forall LB R k, (k <= length LB)%nat ->
  upd_bytes (LB ++ ZERO :: R) k [ZERO] = firstn k LB ++ ZERO :: skipn (S k) (LB ++ ZERO :: R).
Proof.
  intros LB R k Hk. unfold upd_bytes. rewrite firstn_app. replace (k - length LB)%nat with 0%nat by lia.
  rewrite app_nil_r. cbn [length app]. replace (k + 1)%nat with (S k) by lia. reflexivity.
Qed.

Lemma cut_store : forall LB R3 m3 k a (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 : word),
  zs LB = L -> ~ In ZERO LB -> (length L < 512)%nat -> INV m3 (LB ++ ZERO :: R3) ->
  (length LB + 1 + length R3 = 520)%nat -> (k <= length L)%nat -> r_strip_comment L = firstn k L ->
  a = Sp + 424 + Z.of_nat k ->
  evt rsegs POST (MST 0x154b4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6
                      (write_to_mem m3 (Z_to_bv 64 a) (le1 (Z_to_bv 64 0)))).
Proof.
  intros LB R3 m3 k a ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 ELB NLB HL IV LB3 Hk ES Ea.
  subst a. rewrite p2_le1_0.
  assert (LLB : length LB = length L) by (rewrite <- ELB, p2_zs_len; reflexivity).
  pose proof (inv_store0 m3 _ k IV ltac:(lia)) as IV4. rewrite upd_line in IV4 by lia.
  eapply after_strip with (SB := firstn k LB) (R4 := skipn (S k) (LB ++ ZERO :: R3)).
  - exact HL.
  - rewrite p2_zs_firstn, ELB. symmetry. exact ES.
  - intros H. apply NLB. rewrite <- (firstn_skipn k LB). apply in_or_app. left. exact H.
  - exact IV4.
  - rewrite length_firstn, length_skipn, length_app. cbn [length]. lia.
Qed.

Lemma cont : forall k m3 (ra t0 t1 t2 a2 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
  (k < 512)%nat ->
  (forall a0 a1 a2' : word, a0 = Z_to_bv 64 (Sp + 424 + Z.of_nat (S k)) -> a1 = Z_to_bv 64 (- Z.of_nat (S k)) ->
     evt rsegs POST (MST 0x15474 ra t0 t1 t2 a0 a1 a2' (Z_to_bv 64 9) a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                         (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 ln) (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m3)) ->
  evt rsegs POST (MST 0x1549c ra t0 t1 t2 (Z_to_bv 64 (Sp + 424 + Z.of_nat k)) (Z_to_bv 64 (- Z.of_nat k)) a2
                      (Z_to_bv 64 9) a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1))
                      (Z_to_bv 64 ln) (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m3).
Proof.
  intros k m3 ra t0 t1 t2 a2 a4 a5 a6 a7 s8 t3 t4 t5 t6 Hk K.
  pose proof nums as (LO0 & LOS & SPH' & _).
  step. rewrite p2_eqb_m1_false by lia. cbv iota.
  step. step. step.
  eapply K; rewrite ?unsigned_Z_to_bv_add; f_equal; lia.
Qed.

Lemma mark_case : forall LB R3 m3 k (ra t0 t1 t2 a2 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
  zs LB = L -> ~ In ZERO LB -> (length L < 512)%nat -> INV m3 (LB ++ ZERO :: R3) ->
  (length LB + 1 + length R3 = 520)%nat ->
  (k < length L)%nat -> is_mark (nth k L 0) = true ->
  (r_comment_at L k = false ->
   forall a0 a1 a2' : word, a0 = Z_to_bv 64 (Sp + 424 + Z.of_nat (S k)) -> a1 = Z_to_bv 64 (- Z.of_nat (S k)) ->
     evt rsegs POST (MST 0x15474 ra t0 t1 t2 a0 a1 a2' (Z_to_bv 64 9) a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                         (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 ln) (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m3)) ->
  (forall i, (i < k)%nat -> r_comment_at L i = false) ->
  evt rsegs POST (MST 0x15488 ra t0 t1 t2 (Z_to_bv 64 (Sp + 424 + Z.of_nat k)) (Z_to_bv 64 (- Z.of_nat k)) a2
                      (Z_to_bv 64 9) a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1))
                      (Z_to_bv 64 ln) (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m3).
Proof.
  intros LB R3 m3 k ra t0 t1 t2 a2 a4 a5 a6 a7 s8 t3 t4 t5 t6 ELB NLB HL IV LB3 Hk HM K HC.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof IV as (_ & _ & _ & _ & BB & _).
  assert (LLB : length LB = length L) by (rewrite <- ELB, p2_zs_len; reflexivity).
  pose proof (L_line_bytes_holds s o NZs) as (_ & NZL & _).
  pose proof (wr_buf m3 _ IV) as WB.
  destruct k as [|k'].
  - step. rewrite p2_eqb_true by lia. cbv iota.
    step.
    pose proof (wr_at_store_ok rsegs m3 (Sp + 424) 520 0 1 WB ltac:(lia) ltac:(lia)) as HS.
    step.
    eapply (cut_store LB R3 m3 0); [exact ELB | exact NLB | exact HL | exact IV | exact LB3 | lia | | alia].
    apply r_strip_comment_at; [exact NZL | lia | intros j Hj; lia |].
    intros _. unfold r_comment_at. rewrite HM. reflexivity.
  - step. rewrite p2_eqb_neg_false by lia. cbv iota.
    step. rewrite p2_eqb_false by lia. cbv iota.
    set (b := nth k' LB ZERO).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (Sp + 424 + Z.of_nat k')) 1 = Some [b]).
    { apply (p2_rd1 rsegs m3 _ _ k' b BB). rewrite nth_error_app1 by lia. apply nth_error_nth'. lia. }
    assert (Hy : bv_unsigned b = nth k' L 0) by (unfold b; rewrite p2_nth_zs, ELB; reflexivity).
    assert (EC : r_comment_at L (S k') = sp_tab (nth k' L 0)).
    { unfold r_comment_at. rewrite HM. cbn [Nat.eqb orb andb]. replace (S k' - 1)%nat with k' by lia. reflexivity. }
    pose proof (wr_at_store_ok rsegs m3 (Sp + 424) 520 (Z.of_nat (S k')) 1 WB ltac:(lia) ltac:(lia)) as HS.
    assert (CUT : sp_tab (nth k' L 0) = true -> r_strip_comment L = firstn (S k') L).
    { intros ST. apply r_strip_comment_at; [exact NZL | lia | exact HC | intros _; rewrite EC; exact ST]. }
    step.
    destruct (sp_tab (nth k' L 0)) eqn:STY.
    + unfold sp_tab in STY. apply orb_true_iff in STY.
      destruct (Z.eqb_spec (nth k' L 0) 32) as [E32|N32].
      * step. rewrite p2_if_eqb_true by bz.
        step.
        eapply (cut_store LB R3 m3 (S k')); [exact ELB | exact NLB | exact HL | exact IV | exact LB3 | lia | | alia].
        apply CUT. reflexivity.
      * destruct STY as [STY|STY]; [discriminate STY|]. apply Z.eqb_eq in STY.
        step. rewrite p2_if_eqb_false by bz. step. rewrite p2_if_eqb_true by bz.
        step.
        eapply (cut_store LB R3 m3 (S k')); [exact ELB | exact NLB | exact HL | exact IV | exact LB3 | lia | | alia].
        apply CUT. reflexivity.
    + unfold sp_tab in STY. apply orb_false_iff in STY as [N32 N9]. apply Z.eqb_neq in N32, N9.
      step. rewrite p2_if_eqb_false by bz. step. rewrite p2_if_eqb_false by bz.
      apply cont; [lia|]. intros a0' a1' a2' E0 E1. exact (K EC a0' a1' a2' E0 E1).
Qed.

Lemma strip_loop : forall LB R3 m3, zs LB = L -> ~ In ZERO LB -> (length L < 512)%nat ->
  INV m3 (LB ++ ZERO :: R3) -> (length LB + 1 + length R3 = 520)%nat ->
  forall j k (ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
  (length L - k = j)%nat -> (k <= length L)%nat -> (forall i, (i < k)%nat -> r_comment_at L i = false) ->
  a0 = Z_to_bv 64 (Sp + 424 + Z.of_nat k) -> a1 = Z_to_bv 64 (- Z.of_nat k) ->
  evt rsegs POST (MST 0x15474 ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 9) a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 ln) (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m3).
Proof.
  intros LB R3 m3 ELB NLB HL IV LB3 j.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof IV as (_ & _ & _ & _ & BB & _).
  assert (LLB : length LB = length L) by (rewrite <- ELB, p2_zs_len; reflexivity).
  pose proof (L_line_bytes_holds s o NZs) as (_ & NZL & _).
  induction j as [|j IH]; intros k ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s8 t3 t4 t5 t6 Hj Hk HC E0 E1; subst a0 a1.
  - (* the line's NUL: no comment *)
    assert (Ek : k = length L) by lia. subst k.
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (Sp + 424 + Z.of_nat (length L))) 1 = Some [ZERO]).
    { apply (p2_rd1 rsegs m3 _ _ (length L) ZERO BB). rewrite nth_error_app2 by lia. rewrite LLB, Nat.sub_diag.
      reflexivity. }
    step. step. rewrite p2_if_eqb_false by bz. step. rewrite p2_if_eqb_false by bz.
    step. rewrite p2_if_eqb_true by bz.
    eapply after_strip with (SB := LB) (R4 := R3); [exact HL | | exact NLB | exact IV | exact LB3].
    rewrite ELB, (r_strip_comment_at L (length L) NZL ltac:(lia) HC ltac:(lia)), firstn_all. reflexivity.
  - assert (Hk' : (k < length L)%nat) by lia.
    set (b := nth k LB ZERO).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (Sp + 424 + Z.of_nat k)) 1 = Some [b]).
    { apply (p2_rd1 rsegs m3 _ _ k b BB). rewrite nth_error_app1 by lia. apply nth_error_nth'. lia. }
    assert (Hx : bv_unsigned b = nth k L 0) by (unfold b; rewrite p2_nth_zs, ELB; reflexivity).
    assert (Hb0 : bv_unsigned b <> 0).
    { intros E. apply NLB. replace ZERO with b; [apply nth_In; lia|]. apply bv_eq. rewrite E. reflexivity. }
    assert (K : r_comment_at L k = false ->
                forall a0 a1 a2' : word, a0 = Z_to_bv 64 (Sp + 424 + Z.of_nat (S k)) ->
                  a1 = Z_to_bv 64 (- Z.of_nat (S k)) ->
                  evt rsegs POST (MST 0x15474 ra t0 t1 t2 a0 a1 a2' (Z_to_bv 64 9) a4 a5 a6 a7
                                      (Z_to_bv 64 (t + Z.of_nat o')) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 ln)
                                      (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m3)).
    { intros Hc a0' a1' a2' E0' E1'. eapply (IH (S k)); [lia | lia | | exact E0' | exact E1'].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|Ne]; [exact Hc | apply HC; lia]. }
    step.
    destruct (is_mark (nth k L 0)) eqn:IM.
    + pose proof IM as IM'. unfold is_mark in IM'. apply orb_true_iff in IM'.
      destruct (Z.eqb_spec (nth k L 0) 35) as [E35|N35].
      * step. rewrite p2_if_eqb_true by bz.
        eapply mark_case; [exact ELB | exact NLB | exact HL | exact IV | exact LB3 | exact Hk' | exact IM | exact K |
                           exact HC].
      * destruct IM' as [IM'|IM']; [discriminate IM'|]. apply Z.eqb_eq in IM'.
        step. rewrite p2_if_eqb_false by bz. step. rewrite p2_if_eqb_true by bz.
        eapply mark_case; [exact ELB | exact NLB | exact HL | exact IV | exact LB3 | exact Hk' | exact IM | exact K |
                           exact HC].
    + pose proof IM as IM'. unfold is_mark in IM'. apply orb_false_iff in IM' as [N35 N59].
      apply Z.eqb_neq in N35, N59.
      step. rewrite p2_if_eqb_false by bz. step. rewrite p2_if_eqb_false by bz.
      step. rewrite p2_if_eqb_false by bz. step.
      apply cont; [lia|]. intros a0' a1' a2' E0' E1'.
      apply (K ltac:(unfold r_comment_at; rewrite IM; reflexivity) a0' a1' a2' E0' E1').
Qed.

(** ** The short line 0x15448: memcpy, buf[len] = 0, the strip loop, trim, the dispatch *)
Lemma short : forall m B (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  INV m B -> bytes_at rsegs m (t + Z.of_nat o) (zb L) -> (length L < 512)%nat ->
  evt rsegs POST (MST 0x15448 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o'))
                      (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 ln) (Z_to_bv 64 (t + Z.of_nat o))
                      (Z_to_bv 64 (Z.of_nat (length L))) t3 t4 t5 t6 m).
Proof.
  intros m B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 IV BL HL.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof (pf_line_len_le s o) as LLe. pose proof (pfa_len_skipn o s) as LR.
  pose proof IV as (MU & WM & MI & STK & BB & LB).
  pose proof (wr_buf m B IV) as WB.
  assert (LZB : length (zb L) = length L) by (unfold zb; apply length_map).
  step. step. step. step.
  eapply evt_cut.
  { eapply HMC with (src := zb L) (junk := firstn (length L) B); rewrite ?unsigned_lit by lia.
    - exact BL.
    - rewrite LZB. lia.
    - rewrite Nat2Z.id. split; [split|].
      + cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r.
        pose proof (p2_bytes_sub rsegs m _ _ 0 (length L) BB) as BS. cbn [skipn] in BS.
        replace (Sp + 424 + Z.of_nat 0) with (Sp + 424) in BS by lia. apply BS. lia.
      + cbn [cells_size csize]. eapply p2_wr_shrink; [exact WB | lia].
    - lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              -> & MU2 & WM2 & MI2 & RW2 & BY2).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ?(unsigned_lit (Sp + 424)), ?(unsigned_lit (Z.of_nat (length L))) in MU2 by lia.
  rewrite ?(unsigned_lit (Sp + 424)), ?(unsigned_lit (Z.of_nat (length L))) in RW2 by lia.
  rewrite ?(unsigned_lit (t + Z.of_nat o)) in BY2 by lia.
  rewrite ?Nat2Z.id in RW2.
  set (B2 := zb L ++ skipn (length L) B).
  assert (BB2 : bytes_at rsegs m2 (Sp + 424) B2).
  { unfold B2. apply bytes_at_app. split.
    - destruct RW2 as ((_ & BR) & _). cbn [cells_bytes cbytes] in BR. rewrite app_nil_r in BR. exact BR.
    - rewrite LZB. pose proof BB as BB'. rewrite <- (firstn_skipn (length L) B) in BB'.
      apply bytes_at_app in BB' as [_ BB']. rewrite length_firstn, Nat.min_l in BB' by lia.
      eapply bytes_at_transport; [exact BB' | exact MU2 | rewrite length_skipn; dj]. }
  assert (LB2 : length B2 = 520%nat) by (unfold B2; rewrite length_app, length_skipn; lia).
  assert (IV2 : INV m2 B2).
  { eapply inv_step; [exact IV | exact MU2 | exact WM2 | exact MI2 | | | exact BB2 | exact LB2].
    - intros x (_ & H2 & _). cbn [outside]. split; [|exact I].
      intros [A1 A2]. apply H2. split; lia.
    - eapply stk_transport_disjoint; [exact STK | exact MU2 | exact WM2 | dj]. }
  destruct (tr m2 B2 (length (skipn o s)) IV2 ltac:(lia)) as (_ & _ & (_ & SP2 & _) & _ & _).
  pose proof (p2_saved_nth rsegs _ m2 (Sp + 0x70) 2 _ SP2 eq_refl) as SN.
  pose proof (p2_rd8 rsegs m2 _ _ SN) as RD.
  step. step. rewrite p2_pfnot_ltu by (unfold PF_BUF; lia). cbv iota.
  step. step. step.
  rewrite ?(unsigned_lit (Sp + 424)), ?(unsigned_lit (Z.of_nat (length L))) by lia.
  pose proof (wr_buf m2 B2 IV2) as WB2.
  pose proof (wr_at_store_ok rsegs m2 (Sp + 424) 520 (Z.of_nat (length L)) 1 WB2 ltac:(lia) ltac:(lia)) as HS.
  step. rewrite p2_le1_0.
  step.
  destruct L_bytes as (LBy & ELB & NLB).
  assert (ZL : zb L = LBy) by (rewrite <- ELB; apply p2_zb_zs).
  assert (LLB : length LBy = length L) by (rewrite <- ELB, p2_zs_len; reflexivity).
  pose proof (inv_store0 m2 B2 (length L) IV2 HL) as IV3.
  assert (EU : upd_bytes B2 (length L) [ZERO] = LBy ++ ZERO :: skipn (S (length L)) B2).
  { unfold upd_bytes. cbn [length app]. replace (length L + 1)%nat with (S (length L)) by lia. f_equal.
    unfold B2. rewrite firstn_app, LZB, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r, firstn_all2 by lia.
    exact ZL. }
  rewrite EU in IV3.
  assert (LB3 : (length LBy + 1 + length (skipn (S (length L)) B2) = 520)%nat) by (rewrite length_skipn; lia).
  eapply (strip_loop LBy (skipn (S (length L)) B2) _ ELB NLB HL IV3 LB3 (length L - 0) 0);
    [lia | lia | intros i Hi; lia | rewrite ?unsigned_lit by lia; f_equal; lia | f_equal; lia].
Qed.

(** ** The join 0x153e8: lineno++, then the length test *)
Lemma join : forall m B (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 t3 t4 t5 t6 : word),
  INV m B -> bytes_at rsegs m (t + Z.of_nat o) (zb L) ->
  s2 = Z_to_bv 64 (t + Z.of_nat o') -> s8 = Z_to_bv 64 (Z.of_nat (length L)) ->
  evt rsegs POST (MST 0x153e8 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ln) (Z_to_bv 64 ln)
                      (Z_to_bv 64 (t + Z.of_nat o)) s8 t3 t4 t5 t6 m).
Proof.
  intros m B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 t3 t4 t5 t6 IV BL E2 E8. subst s2 s8.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof (pf_line_len_le s o) as LLe. pose proof (pfa_len_skipn o s) as LR.
  assert (LNB : 0 <= ln < 65536) by (pose proof Ho; lia).
  step. rewrite (unsigned_lit ln) by lia. rewrite p2_swrap32 by lia.
  step. rewrite p2_lts_false by lia. cbv iota.
  step. step.
  destruct (Nat.lt_ge_cases (length L) 512) as [HS|HG].
  - rewrite p2_ltu_true by lia. cbv iota.
    eapply short; [exact IV | exact BL | exact HS].
  - rewrite p2_ltu_false by lia. cbv iota.
    eapply exit_long; [exact IV | exact HG].
Qed.

(** ** The head 0x153a8: strchr, and strlen when no '\n' is left *)
Lemma head_walk : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 t3 t4 t5 t6 : word),
  evt rsegs (pf_fin v (Z_to_bv 64 Sp) gp tp F m0 lo c (r_lines (rc, cur, nm) ln (lines (skipn o s))))
    (MST 0x153a8 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat o)) (Z_to_bv 64 ln) s4 s7 s8
         t3 t4 t5 t6 m0).
Proof.
  intros. rewrite lines_step.
  pose proof nums as (LO0 & LOS & SPH' & IL' & M16 & T0' & TB & APt' & NZs & LS' & LN).
  pose proof HCTX as ((_ & _ & _ & _ & (_ & _ & _ & _ & _) & _ & (ST0 & _ & _ & _) & MI0 & _) & _ & _ & _ & CSR).
  destruct (p2_cstr_trim rsegs m0 _ _ CSR) as (bs & sl & BY & ZB & NZR & SL).
  pose proof (pfa_len_skipn o s) as LR.
  assert (Lbs : length bs = (length s - o)%nat) by (rewrite <- LR, <- ZB; unfold zs; symmetry; apply length_map).
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat o + Z.of_nat (length (skipn o s)) + 1)) 8 ltac:(lia)) as MB.
  assert (NZB : ~ In ZERO bs) by (apply SegBridge.nul_free_bytes; rewrite ZB; exact NZR).
  destruct (stk_split rsegs m0 lo Sp (Sp + PARSE_FILE_FRAME) ST0 ltac:(unfold PARSE_FILE_FRAME; lia)) as [STL _].
  destruct inv0 as (B0 & IV0).
  pose proof (L_next_holds s o Ho) as (_ & _ & _ & EN). unfold pf_line in EN.
  pose proof (pf_line_len_le s o) as LLe. unfold pf_line in LLe.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HSC with (str := bs) (slack := sl) (lo := lo); rewrite ?unsigned_lit by lia.
    - exact STL.
    - exact BY.
    - exact NZB.
    - rewrite Lbs, SL, LR. lia.
    - exact MI0.
    - lia.
    - rewrite Lbs, SL, LR. unfold apart in *. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              -> & MU1 & WM1 & MI1 & STK1 & BY1).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite unsigned_lit in MU1, STK1, BY1 by lia.
  assert (IV1 : INV m1 B0) by (eapply inv_keep; [exact IV0 | exact MU1 | exact WM1 | exact MI1 | exact sub_stk |
                                                  exact STK1 | dj]).
  rewrite (unsigned_lit (t + Z.of_nat o)) by lia.
  replace (bv_unsigned (Z_to_bv 64 10) mod 256) with 10 by reflexivity.
  rewrite (SegBridge.bridge_strchr (t + Z.of_nat o) 10 bs NZB ltac:(lia)), ZB.
  destruct (L_break_nl_holds (skipn o s) NZR) as [(SC & SPL) | (SC & E1 & E2)]; rewrite SC.
  - (* a '\n' ends the line *)
    assert (LL : (length (fst (break_nl (skipn o s))) + 1 <= length (skipn o s))%nat).
    { rewrite SPL at 2. rewrite length_app. cbn [length]. lia. }
    assert (BL1 : bytes_at rsegs m1 (t + Z.of_nat o) (zb L)).
    { rewrite (line_bytes bs ZB). pose proof BY1 as BB. apply bytes_at_app in BB as [BB _].
      pose proof (p2_bytes_sub rsegs m1 _ _ 0 (length L) BB) as BS. cbn [skipn] in BS.
      replace (t + Z.of_nat o + Z.of_nat 0) with (t + Z.of_nat o) in BS by lia.
      apply BS. rewrite Lbs. unfold pf_line. lia. }
    step. rewrite p2_eqb_false by lia. cbv iota.
    step. rewrite p2_eqb_m1_false by lia. cbv iota.
    step. step. step.
    eapply (join m1 B0); [exact IV1 | exact BL1 | |].
    + f_equal. rewrite EN. destruct (Nat.ltb_spec (o + length (fst (break_nl (skipn o s)))) (length s)); lia.
    + rewrite !unsigned_lit by lia. f_equal. unfold pf_line. lia.
  - (* the line is the rest of the text: strlen *)
    step. rewrite p2_eqb_true by lia. cbv iota.
    step. step.
    eapply evt_cut.
    { eapply HSL with (str := bs) (slack := sl); rewrite ?unsigned_lit by lia.
      - exact BY1.
      - exact NZB.
      - rewrite Lbs, SL, LR. lia.
      - exact MI1. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                -> & MU2 & WM2 & MI2 & BY2).
    rewrite ret_pc_even by (try lia; reflexivity).
    rewrite unsigned_lit in BY2 by lia.
    assert (STK2 : stk rsegs m2 lo Sp) by (eapply stk_transport_disjoint; [exact STK1 | exact MU2 | exact WM2 | exact I]).
    assert (IV2 : INV m2 B0) by (eapply inv_keep; [exact IV1 | exact MU2 | exact WM2 | exact MI2 | exact sub_nil |
                                                    exact STK2 | exact I]).
    assert (LE : length (fst (break_nl (skipn o s))) = length bs) by (rewrite E1, LR, Lbs; reflexivity).
    assert (BL2 : bytes_at rsegs m2 (t + Z.of_nat o) (zb L)).
    { rewrite (line_bytes bs ZB). pose proof BY2 as BB. apply bytes_at_app in BB as [BB _].
      pose proof (p2_bytes_sub rsegs m2 _ _ 0 (length L) BB) as BS. cbn [skipn] in BS.
      replace (t + Z.of_nat o + Z.of_nat 0) with (t + Z.of_nat o) in BS by lia.
      apply BS. rewrite Lbs. unfold pf_line. lia. }
    step. step. rewrite p2_not_ltu_false by lia. cbv iota.
    step. step.
    eapply (join m2 B0); [exact IV2 | exact BL2 | |].
    + rewrite ?unsigned_lit by lia. f_equal. rewrite EN.
      destruct (Nat.ltb_spec (o + length (fst (break_nl (skipn o s)))) (length s)); lia.
    + f_equal. unfold pf_line. lia.
Qed.

End Head.

(** ** S_P2 *)
Theorem pf_p2_holds : strchr_contract -> strlen_contract -> memcpy_contract -> trim_contract -> S_P2.
Proof.
  intros HSC HSL HMC HTR n. split.
  - intros HLONG HHDR HKEY HTAIL. unfold H_HEAD.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m lo v c t s rc cur nm o ln d HCTX HST Ho Hn HREG HCUR.
    destruct HREG as (E2 & E3 & E0 & E1 & E5 & E10 & E11). subst s2 s3 s0 s1 s5 s10 s11.
    pose proof (Z_to_bv_bv_unsigned sp) as Esp.
    set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
    unfold PF_PC_HEAD.
    eapply head_walk; eassumption.
  - intros HH HD. exact (p2_tail n HH HD).
Qed.
