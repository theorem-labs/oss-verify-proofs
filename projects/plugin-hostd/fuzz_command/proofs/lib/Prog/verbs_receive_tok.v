From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem verbs_receive_words verbs_receive_disp strtok_r_c strlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strspn_c strcspn_c.
Import ListNotations.
Open Scope Z_scope.

Definition TOKENIZE : Z := 0x174b4.
Definition VR_EMPTY : Z := 0x176bc.

Definition tok_post (sp gp tp s0 s9 s10 s11 msg cb : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
    (m : word -> option byte) (T : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word)
                    (m' : word -> option byte) (ps : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 cb a0' a1' a2' a3' a4' a5' a6' a7' msg s3' s4' s5' s6' s7' s8'
                  s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 (match firstn 64 (words T) with [] => VR_EMPTY | _ => DISPATCH end)) fc None m'
             (seg_rom rsegs) /\
    (firstn 64 (words T) <> [] -> s3' = ntokw (firstn 64 (words T)) /\ s5' = ntokw (firstn 64 (words T))) /\
    Forall2 (fun p w => cstr0_at m' (bv_unsigned p) w /\ bv_unsigned cb <= bv_unsigned p /\
                        bv_unsigned p + Z.of_nat (length w) + 1 <= bv_unsigned cb + Z.of_nat (length T) + 1)
            ps (firstn 64 (words T)) /\
    (exists junk, rw_cells rsegs m' (bv_unsigned sp) [CB 520 junk]) /\
    bytes_at rsegs m' (bv_unsigned sp + 8) (concat (map le8 ps)) /\
    munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp, bv_unsigned sp + 520);
           (bv_unsigned cb, bv_unsigned cb + Z.of_nat (length T) + 1)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Lemma firstn_split : forall {A} (l : list A) i j, (i <= j)%nat ->
  firstn j l = firstn i l ++ firstn (j - i) (skipn i l).
Proof.
  intros A l. induction l as [|x l IH]; intros i j H.
  - rewrite skipn_nil, !firstn_nil. reflexivity.
  - destruct i as [|i]; [cbn [firstn skipn app]; rewrite Nat.sub_0_r; reflexivity|].
    destruct j as [|j]; [lia|]. cbn [firstn skipn app Nat.sub]. f_equal. apply IH. lia.
Qed.

Lemma nth_skipn_cons : forall {A} (l : list A) n x y, skipn n l = x :: y -> nth_error l n = Some x /\ skipn (S n) l = y.
Proof.
  intros A l n x y H. split.
  - rewrite <- (Nat.add_0_r n), <- nth_error_skipn, H. reflexivity.
  - replace (S n) with (1 + n)%nat by lia. rewrite <- skipn_skipn, H. reflexivity.
Qed.

Lemma firstn_S_nth : forall {A} (l : list A) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
  intros A l. induction l as [|y l IH]; intros n x H; [destruct n; discriminate|].
  destruct n as [|n]; cbn in H |- *; [inversion H; reflexivity|]. rewrite (IH n x H). reflexivity.
Qed.

Lemma match_ne : forall {A} (l : list A) (a b : Z), l <> [] -> match l with [] => a | _ => b end = b.
Proof. intros A [|x l] a b H; [congruence | reflexivity]. Qed.

Lemma len_cle8 : forall ws : list word, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia. Qed.

Lemma tok_cut_len : forall r, length (tok_cut sepl r) = length r.
Proof.
  intros r. pose proof (tok_j_le r). unfold tok_cut.
  destruct (Nat.ltb_spec (tok_j sepl r) (length r)) as [L|L]; [|reflexivity].
  rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia.
Qed.

Lemma tok_j_sep : forall r, (tok_j sepl r < length r)%nat ->
  exists y, nth_error r (tok_j sepl r) = Some y /\ is_sep y = true.
Proof.
  intros r H. pose proof (cspn_stop (skipn (tok_i sepl r) r)) as CS.
  rewrite length_skipn in CS. unfold tok_j in *.
  destruct (CS ltac:(lia)) as (y & rr & Ey & Hy). exists y. split; [|exact Hy].
  rewrite skipn_skipn in Ey. apply nth_skipn_cons in Ey. destruct Ey as [Ey _].
  replace (tok_i sepl r + cspn_len sepl (skipn (tok_i sepl r) r))%nat
    with (cspn_len sepl (skipn (tok_i sepl r) r) + tok_i sepl r)%nat by lia.
  exact Ey.
Qed.

Lemma cut_byte : forall r b, nth_error (r ++ [Z_to_bv 8 0]) (tok_j sepl r) = Some b -> is_sep b = false ->
  nth_error (tok_cut sepl r ++ [Z_to_bv 8 0]) (tok_j sepl r) = Some b.
Proof.
  intros r b H S. unfold tok_cut. destruct (Nat.ltb_spec (tok_j sepl r) (length r)) as [L|L]; [|exact H].
  destruct (tok_j_sep r L) as (y & Hy & Sy).
  rewrite nth_error_app1 in H by lia. rewrite Hy in H. inversion H; subst. congruence.
Qed.

Lemma tok_word_len : forall r, length (tok_word r) = (tok_j sepl r - tok_i sepl r)%nat.
Proof. intros r. pose proof (tok_j_le r). unfold tok_word. rewrite length_firstn, length_skipn. lia. Qed.

Lemma cut_split : forall r, (tok_i sepl r < length r)%nat ->
  tok_cut sepl r ++ [Z_to_bv 8 0] =
  firstn (tok_i sepl r) r ++ (tok_word r ++ [Z_to_bv 8 0]) ++
  (if Nat.ltb (tok_j sepl r) (length r) then tok_rest r ++ [Z_to_bv 8 0] else []).
Proof.
  intros r H. pose proof (tok_i_le_j r) as IJ. pose proof (tok_j_le r) as JL.
  unfold tok_cut, tok_word, tok_rest.
  destruct (Nat.ltb_spec (tok_j sepl r) (length r)) as [L|L].
  - rewrite (firstn_split r (tok_i sepl r) (tok_j sepl r)) by lia. rewrite <- !app_assoc. reflexivity.
  - assert (Ej : tok_j sepl r = length r) by lia. rewrite Ej.
    rewrite (firstn_all2 (n := (length r - tok_i sepl r)%nat)) by (rewrite length_skipn; lia).
    rewrite app_nil_r, app_assoc, firstn_skipn. reflexivity.
Qed.

Lemma tok_j_rep : forall n, tok_j sepl (repeat (Z_to_bv 8 65) n) = n.
Proof.
  intros n. unfold tok_j, tok_i.
  assert (S0 : spn_len sepl (repeat (Z_to_bv 8 65) n) = 0%nat) by (destruct n; reflexivity).
  rewrite S0.
  assert (G : forall k, cspn_len sepl (repeat (Z_to_bv 8 65) k) = k).
  { induction k as [|k IH]; [reflexivity|]. cbn [repeat cspn_len].
    change (existsb (fun c : byte => bv_unsigned c =? bv_unsigned (Z_to_bv 8 65)) sepl) with false.
    rewrite IH. reflexivity. }
  exact (G n).
Qed.

Lemma rep_notin : forall n, ~ In (Z_to_bv 8 0) (repeat (Z_to_bv 8 65) n).
Proof. intros n H. apply repeat_spec in H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.

Lemma sepl_notin : ~ In (Z_to_bv 8 0) sepl.
Proof.
  unfold sepl. cbn [map]. intros [H|[H|H]]; [| |exact H]; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

Lemma notin_nz : forall l, ~ In (Z_to_bv 8 0) l -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
  intros l H. apply Forall_forall. intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|].
  apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma nosep_b : forall l, forallb (fun b => negb (is_sep b)) l = true -> Forall (fun b => is_sep b = false) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros b Hb. specialize (H b Hb).
  destruct (is_sep b); [discriminate | reflexivity].
Qed.

Lemma ba_eq : forall mk a a' bs, bytes_at rsegs mk a bs -> a = a' -> bytes_at rsegs mk a' bs.
Proof. intros; subst; assumption. Qed.

Lemma wr_at_sub : forall mk A n A' n', wr_at rsegs mk A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  wr_at rsegs mk A' n'.
Proof.
  intros mk A n A' n' (H1 & H2 & H3) Ha Hn Hn'. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A' + i) with (A + (A' - A + i)) by lia. apply H3. lia.
Qed.

Lemma bytes_of_rd : forall mk A n, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs mk (wa (A + Z.of_nat i)) = Some b) ->
  exists bs, length bs = n /\ bytes_at rsegs mk A bs.
Proof.
  intros mk A n HA HN H.
  assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\
                forall i, (i < k)%nat -> mrd rsegs mk (wa (A + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H k ltac:(lia)) as (b & Hb).
      exists (bs ++ [b]). split; [rewrite length_app; cbn [length]; lia|].
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

Lemma le8_of : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs H. rewrite <- store_bytes_8'. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2^64).
  rewrite Z_to_le_bytes_mod by lia. rewrite <- H. apply Z_to_le_bytes_to_Z.
Qed.

Lemma keep_nosep : forall mk mk' (S0 C : Z) r A bs,
  munch [(S0 - 128, S0); (S0, S0 + 8); (C + Z.of_nat (tok_j sepl r), C + Z.of_nat (tok_j sepl r) + 1)] mk mk' ->
  u8arr rsegs mk C (r ++ [Z_to_bv 8 0]) -> u8arr rsegs mk' C (tok_cut sepl r ++ [Z_to_bv 8 0]) ->
  bytes_at rsegs mk A bs -> Forall (fun b => is_sep b = false) bs ->
  A + Z.of_nat (length bs) <= S0 - 128 \/ S0 + 8 <= A ->
  bytes_at rsegs mk' A bs.
Proof.
  intros mk mk' S0 C r A bs MU [B1 _] [B2 _] HB NS D.
  pose proof HB as (HA & HL & HI). pose proof (tok_j_le r) as JL. pose proof (tok_cut_len r) as CL.
  pose proof B1 as (_ & _ & H1). pose proof B2 as (_ & _ & H2).
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  rewrite <- Eb, <- (HI i Hi).
  destruct (Z.eq_dec (A + Z.of_nat i) (C + Z.of_nat (tok_j sepl r))) as [Eq|Ne].
  - assert (HJ : nth_error (r ++ [Z_to_bv 8 0]) (tok_j sepl r) = Some b).
    { rewrite <- (H1 (tok_j sepl r)) by (rewrite length_app; cbn [length]; lia). rewrite <- Eq, (HI i Hi). exact Eb. }
    rewrite Eq.
    rewrite (H1 (tok_j sepl r)) by (rewrite length_app; cbn [length]; lia).
    rewrite (H2 (tok_j sepl r)) by (rewrite length_app, CL; cbn [length]; lia).
    rewrite HJ. apply cut_byte; [exact HJ|]. rewrite Forall_forall in NS. apply NS. eapply nth_error_In. exact Eb.
  - unfold mrd. rewrite MU; [reflexivity|]. cbn [outside]. rewrite wa_unsigned by lia. repeat split; lia.
Qed.

Lemma keep_any : forall mk mk' (S0 C : Z) r A bs,
  munch [(S0 - 128, S0); (S0, S0 + 8); (C + Z.of_nat (tok_j sepl r), C + Z.of_nat (tok_j sepl r) + 1)] mk mk' ->
  u8arr rsegs mk' C (tok_cut sepl r ++ [Z_to_bv 8 0]) ->
  bytes_at rsegs mk A bs -> A + Z.of_nat (length bs) <= S0 - 128 \/ S0 + 8 <= A ->
  exists bs', length bs' = length bs /\ bytes_at rsegs mk' A bs'.
Proof.
  intros mk mk' S0 C r A bs MU [B2 _] HB D.
  pose proof HB as (HA & HL & HI). pose proof (tok_j_le r) as JL. pose proof (tok_cut_len r) as CL.
  pose proof B2 as (_ & _ & H2).
  apply bytes_of_rd; [lia | lia |]. intros i Hi.
  destruct (Z.eq_dec (A + Z.of_nat i) (C + Z.of_nat (tok_j sepl r))) as [Eq|Ne].
  - rewrite Eq. rewrite (H2 (tok_j sepl r)) by (rewrite length_app, CL; cbn [length]; lia).
    destruct (nth_error (tok_cut sepl r ++ [Z_to_bv 8 0]) (tok_j sepl r)) as [b|] eqn:E.
    + exists b. reflexivity.
    + apply nth_error_None in E. rewrite length_app, CL in E. cbn [length] in E. lia.
  - assert (MX : mrd rsegs mk' (wa (A + Z.of_nat i)) = mrd rsegs mk (wa (A + Z.of_nat i))).
    { unfold mrd. rewrite MU; [reflexivity|]. cbn [outside]. rewrite wa_unsigned by lia. repeat split; lia. }
    rewrite MX, (HI i Hi). destruct (nth_error bs i) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. lia.
Qed.

Lemma slot_split : forall mk A (pv : word) junk, rw_cells rsegs mk A [C8 pv; CB 512 junk] ->
  rw_cells rsegs mk A [C8 pv] /\ u8arr rsegs mk (A + 8) junk /\ length junk = 512%nat.
Proof.
  intros mk A pv junk [[Hwf HB] HW]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (_ & HL & _).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite length_le8 in B2. cbn [cells_size csize] in HW.
  split; [|split; [split|exact HL]].
  - split; [split|].
    + cbn. tauto.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
    + cbn [cells_size csize]. apply (wr_at_sub _ _ _ _ _ HW); lia.
  - eapply ba_eq; [exact B2 | lia].
  - rewrite HL. apply (wr_at_sub _ _ _ _ _ HW); lia.
Qed.

Lemma slot_merge : forall mk A (sv : word) arr, rw_cells rsegs mk A [C8 sv] -> u8arr rsegs mk (A + 8) arr ->
  length arr = 512%nat -> exists junk, rw_cells rsegs mk A [CB 520 junk].
Proof.
  intros mk A sv arr [[_ HB] HW] [HB2 HW2] HL. exists (le8 sv ++ arr).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. cbn [cells_size csize] in HW.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_app, length_le8, HL; reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB|]. rewrite length_le8.
    eapply ba_eq; [exact HB2 | lia].
  - cbn [cells_size csize]. destruct HW as (W1 & W2 & W3). destruct HW2 as (V1 & V2 & V3). rewrite HL in V2, V3.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i 8).
    + apply W3. lia.
    + replace (A + i) with (A + 8 + (i - 8)) by lia. apply V3. lia.
Qed.

Lemma addiw_k : forall k : nat, (k < 64)%nat ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.of_nat k)) + 1)) = Z_to_bv 64 (Z.of_nat (S k)).
Proof.
  intros k Hk. assert (HM : bv_half_modulus 32 = 2^31) by reflexivity.
  rewrite unsigned_lit by lia. rewrite bv_swrap_small by (rewrite HM; lia).
  f_equal. lia.
Qed.

Lemma ltu_k : forall k : nat, (k < 64)%nat -> bv_ltu (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 63) = Nat.ltb k 63.
Proof.
  intros k Hk. unfold bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Nat.ltb_spec k 63); [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Section Tok.
Hypothesis SR : strtok_r_contract.
Variables (m : word -> option byte) (sp cb gp tp s0 s9 s10 s11 msg : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (T : list byte).
Local Notation SP := (bv_unsigned sp).
Local Notation EN := (bv_unsigned cb + Z.of_nat (length T) + 1).
Local Notation QQ := (tok_post sp gp tp s0 s9 s10 s11 msg cb F fc lo m T).
Hypothesis HCB : 0 < bv_unsigned cb.
Hypothesis HEN : EN <= 2^64.
Hypothesis HDJ : EN <= lo \/ SP + 520 <= bv_unsigned cb.
Hypothesis HLO : lo + 128 <= SP.
Hypothesis HIT : IMG_TOP <= lo.
Hypothesis HSP : SP + 520 <= 2^64.

Definition tokq (mk : word -> option byte) (p : word) (w : list byte) : Prop :=
  cstr0_at mk (bv_unsigned p) w /\ bv_unsigned cb <= bv_unsigned p /\ bv_unsigned p + Z.of_nat (length w) + 1 <= EN /\
  Forall (fun b => is_sep b = false) w.

Definition remp (mk : word -> option byte) (C : Z) (ws : list (list byte)) : Prop :=
  (C = 0 /\ ws = []) \/
  (exists r, C <> 0 /\ u8arr rsegs mk C (r ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) r /\
             bv_unsigned cb <= C /\ C + Z.of_nat (length r) + 1 = EN /\ words r = ws).

Definition basem (mk : word -> option byte) : Prop :=
  munch [(SP - 128, SP); (SP, SP + 520); (bv_unsigned cb, EN)] m mk /\ wmono rsegs m mk /\ mem_inv rsegs mk /\
  stk rsegs mk lo SP /\ bytes_at rsegs mk SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD)) /\
  exists g, bytes_at rsegs mk SSP_GUARD (le8 g).

Definition cpost (ra s1 s2 s3 s4 s5 s6 s7 s8 : word) (mk : word -> option byte) (ws : list (list byte))
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mk' : word -> option byte)
                    (sv' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None mk' (seg_rom rsegs) /\
    basem mk' /\ rw_cells rsegs mk' SP [C8 sv'] /\
    (forall p w, tokq mk p w -> tokq mk' p w) /\
    (forall X, length X = 512%nat -> u8arr rsegs mk (SP + 8) X -> u8arr rsegs mk' (SP + 8) X) /\
    match ws with
    | [] => a0' = Z_to_bv 64 0
    | w :: ws' => bv_unsigned a0' <> 0 /\ tokq mk' a0' w /\ remp mk' (bv_unsigned sv') ws'
    end.

Lemma tok_call : forall (ra t0 t1 t2 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 pv : word) mk ws,
  basem mk -> rw_cells rsegs mk SP [C8 pv] ->
  remp mk (if bv_unsigned a0 =? 0 then bv_unsigned pv else bv_unsigned a0) ws ->
  evt rsegs (cpost ra s1 s2 s3 s4 s5 s6 s7 s8 mk ws)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x1064c) sp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x21048) fc None mk (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 pv mk ws HB SL HR.
  pose proof HB as (MU & WM & MI & ST & GOT & g & GU).
  pose proof HIT as HIT'. unfold IMG_TOP in HIT'.
  assert (SEPB : bytes_at rsegs mk (bv_unsigned (Z_to_bv 64 0x1064c)) (sepl ++ [Z_to_bv 8 0])).
  { rewrite unsigned_lit by lia. apply img_bytes; [exact MI | vm_compute; reflexivity]. }
  assert (SEPL : length sepl = 2%nat) by reflexivity.
  remember (if bv_unsigned a0 =? 0 then bv_unsigned pv else bv_unsigned a0) as C eqn:EC.
  destruct HR as [(C0 & ->) | (r & CNZ & U & NZ & LC & LE & WR)].
  - set (n := Z.to_nat (SP - 1)).
    assert (TJ : Z.of_nat (tok_j sepl (repeat (Z_to_bv 8 65) n)) = SP - 1) by (rewrite tok_j_rep; unfold n; lia).
    eapply evt_cut.
    { eapply (SR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x1064c) sp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3 t4 t5 t6 F fc mk C pv (repeat (Z_to_bv 8 65) n) [] sepl lo g);
        [ exact SL | exact EC | intros H; exfalso; exact (H C0) | apply rep_notin | exact SEPB | exact sepl_notin
        | exact GOT | exact GU | exact ST | lia | left; rewrite unsigned_lit by lia; rewrite SEPL; lia
        | right; lia | left; unfold SSP_GOT; lia | left; unfold SSP_GUARD; lia | exact MI ]. }
    intros ms' PO. unfold strtok_r_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk' &
                    E & MU' & WM' & MI' & ST' & SL' & _).
    subst ms'. rewrite C0, TJ in MU'. rewrite C0 in SL'.
    apply evt_done. unfold cpost.
    exists t0', t1', t2', (Z_to_bv 64 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mk', (Z_to_bv 64 0).
    split; [rewrite C0; reflexivity|].
    split; [|split; [exact SL'|split; [|split]]].
    + split; [|split; [|split; [|split; [|split]]]].
      * eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *.
        repeat split; lia.
      * eapply wmono_trans; eassumption.
      * exact MI'.
      * exact ST'.
      * eapply bytes_at_transport; [exact GOT | exact MU' |]. cbn [disjoint_from]. rewrite length_le8.
        unfold SSP_GOT. repeat split; lia.
      * exists g. eapply bytes_at_transport; [exact GU | exact MU' |]. cbn [disjoint_from]. rewrite length_le8.
        unfold SSP_GUARD. repeat split; lia.
    + intros p w (HC & L1 & L2 & NS). split; [|split; [exact L1|split; [exact L2|exact NS]]].
      destruct HC as [HB0 HZ]. split; [|exact HZ].
      eapply bytes_at_transport; [exact HB0 | exact MU' |]. cbn [disjoint_from]. rewrite length_app. cbn [length].
      repeat split; lia.
    + intros X HX U0. eapply u8arr_transport; [exact U0 | exact MU' | exact WM' |]. cbn [disjoint_from]. rewrite HX.
      repeat split; lia.
    + reflexivity.
  - assert (CP : 0 < C) by lia.
    pose proof (u8arr_bound _ _ _ _ U) as UB. rewrite length_app in UB. cbn [length] in UB.
    pose proof (tok_j_le r) as JL. pose proof (tok_i_le_j r) as IJ. pose proof (tok_cut_len r) as CL.
    eapply evt_cut.
    { eapply (SR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x1064c) sp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3 t4 t5 t6 F fc mk C pv r [] sepl lo g);
        [ exact SL | exact EC
        | intros _; split; [exact U|]; split; [apply bytes_at_nil; lia|]; split; [rewrite SEPL; intros H; exfalso; lia|];
          cbn [length]; split; lia
        | exact NZ | exact SEPB | exact sepl_notin
        | exact GOT | exact GU | exact ST | lia | left; rewrite unsigned_lit by lia; rewrite SEPL; lia
        | right; lia | left; unfold SSP_GOT; lia | left; unfold SSP_GUARD; lia | exact MI ]. }
    intros ms' PO. unfold strtok_r_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk' &
                    E & MU' & WM' & MI' & ST' & SL' & UP).
    subst ms'. destruct (UP CNZ) as [U' _]. clear UP.
    assert (KEEP : forall A bs, bytes_at rsegs mk A bs -> Forall (fun b => is_sep b = false) bs ->
                   A + Z.of_nat (length bs) <= SP - 128 \/ SP + 8 <= A -> bytes_at rsegs mk' A bs).
    { intros A bs HB0 NS D. exact (keep_nosep mk mk' SP C r A bs MU' U U' HB0 NS D). }
    apply evt_done. unfold cpost.
    exists t0', t1', t2', (Z_to_bv 64 (tok_ret C sepl r)), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mk',
      (Z_to_bv 64 (tok_save C sepl r)).
    split; [reflexivity|].
    split; [|split; [exact SL'|split; [|split]]].
    + split; [|split; [|split; [|split; [|split]]]].
      * eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *.
        repeat split; lia.
      * eapply wmono_trans; eassumption.
      * exact MI'.
      * exact ST'.
      * apply KEEP; [exact GOT | apply nosep_b; vm_compute; reflexivity | left; rewrite length_le8; unfold SSP_GOT; lia].
      * destruct (keep_any mk mk' SP C r SSP_GUARD (le8 g) MU' U' GU) as (bs' & BL & BB).
        { left. rewrite length_le8. unfold SSP_GUARD. lia. }
        exists (Z_to_bv 64 (bytes_le_to_Z bs')). rewrite le8_of by (rewrite BL; apply length_le8). exact BB.
    + intros p w (HC & L1 & L2 & NS). split; [|split; [exact L1|split; [exact L2|exact NS]]].
      destruct HC as [HB0 HZ]. split; [|exact HZ].
      apply KEEP; [exact HB0 | apply Forall_app; split; [exact NS | constructor; [reflexivity | constructor]] |].
      rewrite length_app. cbn [length]. lia.
    + intros X HX U0. eapply u8arr_transport; [exact U0 | exact MU' | exact WM' |]. cbn [disjoint_from]. rewrite HX.
      repeat split; lia.
    + rewrite <- WR.
      destruct (Nat.lt_ge_cases (tok_i sepl r) (length r)) as [IL|IG].
      * destruct (words_step r IL) as (WS & _ & IJ'). rewrite WS.
        assert (TR : tok_ret C sepl r = C + Z.of_nat (tok_i sepl r)).
        { unfold tok_ret. rewrite (proj2 (Z.eqb_neq C 0) CNZ).
          destruct (Nat.eqb_spec (tok_i sepl r) (length r)); [lia|]. reflexivity. }
        rewrite TR. rewrite unsigned_lit by lia.
        pose proof U' as [UB' UW']. rewrite (cut_split r IL) in UB'.
        apply bytes_at_app in UB'. destruct UB' as [_ UB']. apply bytes_at_app in UB'. destruct UB' as [UB1 UB2].
        rewrite length_firstn, Nat.min_l in UB1, UB2 by lia. rewrite length_app, tok_word_len in UB2.
        cbn [length] in UB2.
        rewrite length_app, CL in UW'. cbn [length] in UW'.
        split; [lia|]. split.
        -- unfold tokq, cstr0_at. rewrite unsigned_lit by lia. rewrite tok_word_len.
           split; [split; [exact UB1 | apply notin_nz; intros H; exact (NZ (in_tok_word r _ H))]|].
           split; [lia|]. split; [lia|]. apply tok_word_nosep.
        -- destruct (Nat.lt_ge_cases (tok_j sepl r) (length r)) as [JL'|JG].
           ++ rewrite (proj2 (Nat.ltb_lt _ _) JL') in UB2.
              assert (TS : tok_save C sepl r = C + Z.of_nat (tok_j sepl r) + 1).
              { unfold tok_save. rewrite (proj2 (Z.eqb_neq C 0) CNZ).
                destruct (Nat.leb_spec (length r) (tok_j sepl r)); [lia|]. reflexivity. }
              rewrite TS, unsigned_lit by lia. right. exists (tok_rest r).
              assert (RL : length (tok_rest r) = (length r - S (tok_j sepl r))%nat)
                by (unfold tok_rest; apply length_skipn).
              split; [lia|]. split; [split|].
              ** eapply ba_eq; [exact UB2 | lia].
              ** rewrite length_app. cbn [length]. apply (wr_at_sub _ _ _ _ _ UW'); lia.
              ** split; [intros H; exact (NZ (in_tok_rest r _ H))|]. split; [lia|]. split; [lia|reflexivity].
           ++ assert (TS : tok_save C sepl r = 0).
              { unfold tok_save. rewrite (proj2 (Nat.leb_le _ _) JG). rewrite orb_true_r. reflexivity. }
              rewrite TS. left. split; [reflexivity|]. unfold tok_rest. rewrite skipn_all2 by lia. reflexivity.
      * assert (EI : tok_i sepl r = length r) by lia. rewrite (words_none r EI).
        f_equal. unfold tok_ret. rewrite EI, Nat.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma tok_fin : forall ps mk (sv pc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' t3' t4' t5'
                               t6' : word),
  pc = Z_to_bv 64 (match firstn 64 (words T) with [] => VR_EMPTY | _ => DISPATCH end) ->
  basem mk -> rw_cells rsegs mk SP [C8 sv] ->
  (exists rest, u8arr rsegs mk (SP + 8) (concat (map le8 ps) ++ rest) /\
                length (concat (map le8 ps) ++ rest) = 512%nat) ->
  Forall2 (tokq mk) ps (firstn 64 (words T)) ->
  (firstn 64 (words T) <> [] -> s3' = ntokw (firstn 64 (words T)) /\ s5' = ntokw (firstn 64 (words T))) ->
  evt rsegs QQ (MS (mkR ra' sp gp tp t0' t1' t2' s0 cb a0' a1' a2' a3' a4' a5' a6' a7' msg s3' s4' s5' s6' s7' s8'
                        s9 s10 s11 t3' t4' t5' t6') F pc fc None mk (seg_rom rsegs)).
Proof.
  intros ps mk sv pc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6'
    HPC HB SL (rest & UA & UL) HF HS.
  pose proof HB as (MU & WM & MI & ST & _).
  apply evt_done. unfold tok_post.
  exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s3', s4', s5', s6', s7', s8', t3', t4', t5', t6', mk, ps.
  split; [rewrite HPC; reflexivity|].
  split; [exact HS|].
  split.
  { eapply Forall2_impl; [|exact HF]. intros p w (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact H3]]. }
  split; [eapply slot_merge; [exact SL | exact UA | exact UL]|].
  split; [destruct UA as [UB _]; apply bytes_at_app in UB; exact (proj1 UB)|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|exact ST].
Qed.

Definition linv (k : nat) (qs : list word) (p sv : word) (mk : word -> option byte) : Prop :=
  length qs = k /\ (k < 64)%nat /\
  Forall2 (tokq mk) qs (firstn k (words T)) /\
  (exists w, nth_error (words T) k = Some w /\ tokq mk p w) /\
  (exists rest, length rest = (512 - 8 * k)%nat /\ u8arr rsegs mk (SP + 8) (concat (map le8 qs) ++ rest)) /\
  rw_cells rsegs mk SP [C8 sv] /\
  remp mk (bv_unsigned sv) (skipn (S k) (words T)) /\
  basem mk.

Lemma tok_store : forall k qs p sv mk, linv k qs p sv mk ->
  store_ok rsegs mk (wa (SP + 8 + 8 * Z.of_nat k)) 8 = true /\
  basem (write_to_mem mk (wa (SP + 8 + 8 * Z.of_nat k)) (le8 p)) /\
  rw_cells rsegs (write_to_mem mk (wa (SP + 8 + 8 * Z.of_nat k)) (le8 p)) SP [C8 sv] /\
  remp (write_to_mem mk (wa (SP + 8 + 8 * Z.of_nat k)) (le8 p)) (bv_unsigned sv) (skipn (S k) (words T)) /\
  Forall2 (tokq (write_to_mem mk (wa (SP + 8 + 8 * Z.of_nat k)) (le8 p))) (qs ++ [p]) (firstn (S k) (words T)) /\
  exists rest, length rest = (512 - 8 * S k)%nat /\
    u8arr rsegs (write_to_mem mk (wa (SP + 8 + 8 * Z.of_nat k)) (le8 p)) (SP + 8) (concat (map le8 (qs ++ [p])) ++ rest).
Proof.
  intros k qs p sv mk (QL & KL & HF & (w & NW & TW) & (rest & RL & UA) & SL & HR & HB).
  pose proof HB as (MU & WM & MI & ST & GOT & g & GU).
  pose proof HIT as HIT'. unfold IMG_TOP in HIT'.
  assert (L8 : Z.of_nat (length (le8 p)) = 8) by (rewrite length_le8; reflexivity).
  assert (LA : length (concat (map le8 qs) ++ rest) = 512%nat) by (rewrite length_app, len_cle8, RL; lia).
  assert (SOK : store_ok rsegs mk (wa (SP + 8 + 8 * Z.of_nat k)) 8 = true).
  { destruct UA as [_ UW]. apply (wr_at_store_ok rsegs mk (SP + 8) _ (8 * Z.of_nat k) 8 UW); [lia | rewrite LA; lia]. }
  assert (TF : forall q v, tokq mk q v -> tokq (write_to_mem mk (wa (SP + 8 + 8 * Z.of_nat k)) (le8 p)) q v).
  { intros q v (HC & L1 & L2 & NS). split; [|split; [exact L1|split; [exact L2|exact NS]]].
    destruct HC as [HB0 HZ]. split; [|exact HZ]. apply bytes_at_write_other; [exact HB0 | lia | lia |].
    rewrite length_app. cbn [length]. lia. }
  split; [exact SOK|]. split; [|split; [|split; [|split]]].
  - split; [|split; [|split; [|split; [|split]]]].
    + apply munch_write; [exact MU | lia | lia |]. cbn [inside]. lia.
    + apply wmono_write. exact WM.
    + apply mem_inv_store; [exact MI|]. rewrite length_le8. exact SOK.
    + apply stk_write; [exact ST | lia | lia].
    + apply bytes_at_write_other; [exact GOT | lia | lia |]. rewrite length_le8. unfold SSP_GOT. lia.
    + exists g. apply bytes_at_write_other; [exact GU | lia | lia |]. rewrite length_le8. unfold SSP_GUARD. lia.
  - apply rw_cells_frame; [exact SL | lia | lia |]. cbn [cells_size csize]. lia.
  - destruct HR as [HR|(r & CNZ & U & NZ & LC & LE & WR)]; [left; exact HR|].
    right. exists r. split; [exact CNZ|]. split; [|split; [exact NZ|split; [exact LC|split; [exact LE|exact WR]]]].
    apply u8arr_frame; [exact U | lia | lia |]. rewrite length_app. cbn [length]. lia.
  - rewrite (firstn_S_nth _ _ _ NW). apply Forall2_app.
    + eapply Forall2_impl; [exact TF | exact HF].
    + constructor; [apply TF; exact TW | constructor].
  - exists (skipn 8 rest). split; [rewrite length_skipn, RL; lia|].
    rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
    destruct UA as [UB UW]. split.
    + eapply bytes_at_ext.
      { apply (bytes_at_write_inside rsegs mk (SP + 8) _ (8 * Z.of_nat k) (le8 p) UB); [lia|].
        rewrite length_le8, LA. lia. }
      rewrite <- (firstn_skipn 8 rest) at 1.
      replace (Z.to_nat (8 * Z.of_nat k)) with (length (concat (map le8 qs))) by (rewrite len_cle8; lia).
      rewrite upd_bytes_mid by (rewrite length_le8, length_firstn; lia). rewrite app_assoc. reflexivity.
    + apply wr_at_write. rewrite LA in UW.
      replace (Z.of_nat (length ((concat (map le8 qs) ++ le8 p) ++ skipn 8 rest))) with (Z.of_nat 512); [exact UW|].
      rewrite !length_app, length_le8, length_skipn, len_cle8. lia.
Qed.

Lemma tok_body : forall k qs p sv mk (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
  linv k qs p sv mk ->
  (forall p' sv' mk' (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' : word),
     (k < 63)%nat -> linv (S k) (qs ++ [p]) p' sv' mk' ->
     evt rsegs QQ (MS (mkR ra' sp gp tp t0' t1' t2' s0 cb p' a1' a2' a3' a4' a5' a6' a7' msg
                     (Z_to_bv 64 (Z.of_nat (S k))) (Z_to_bv 64 0x1064c) (Z_to_bv 64 (Z.of_nat (S k)))
                     (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat (S k))) (Z_to_bv 64 63) s8' s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x174e8) fc None mk' (seg_rom rsegs))) ->
  evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 cb p a1 a2 a3 a4 a5 a6 a7 msg
                  (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 0x1064c) (Z_to_bv 64 (Z.of_nat k))
                  (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat k)) (Z_to_bv 64 63) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x174e8) fc None mk (seg_rom rsegs)).
Proof.
  intros k qs p sv mk ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 HI K.
  destruct (tok_store k qs p sv mk HI) as (SOK & B1 & SL1 & HR1 & HF1 & (rest1 & RL1 & UA1)).
  pose proof HI as (QL & KL & _ & (w & NW & _) & _).
  change (wa (SP + 8 + 8 * Z.of_nat k)) with (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat k)) in SOK.
  do 7 step.
  eapply evt_cut.
  { eapply tok_call; [exact B1 | exact SL1 | exact HR1]. }
  destruct (skipn (S k) (words T)) as [|w' ws'] eqn:SK.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk' & sv' &
                E & B2 & SL2 & TK2 & AR2 & A0).
    subst ms'. subst a0'. fix_ret.
    step. step. if_true.
    assert (LW : length (words T) = S k).
    { pose proof (nth_error_lt _ _ _ NW). apply (f_equal (@length _)) in SK. rewrite length_skipn in SK.
      cbn [length] in SK. lia. }
    assert (FE : firstn 64 (words T) = firstn (S k) (words T)) by (rewrite !firstn_all2 by lia; reflexivity).
    assert (NE : firstn 64 (words T) <> []).
    { rewrite FE, (firstn_S_nth _ _ _ NW). intros H. destruct (firstn k (words T)); discriminate. }
    eapply tok_fin with (ps := qs ++ [p]) (sv := sv').
    + rewrite (match_ne _ _ _ NE). reflexivity.
    + exact B2.
    + exact SL2.
    + exists rest1. split; [apply AR2; [|exact UA1]|]; rewrite length_app, len_cle8, length_app, RL1, QL; cbn [length];
        lia.
    + rewrite FE. eapply Forall2_impl; [exact TK2 | exact HF1].
    + intros _. unfold ntokw. rewrite FE, firstn_all2 by lia. rewrite LW. split; [apply addiw_k; lia | f_equal; lia].
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk' & sv' &
                E & B2 & SL2 & TK2 & AR2 & NZ2 & TW2 & HR2).
    subst ms'. fix_ret.
    destruct (nth_skipn_cons _ _ _ _ SK) as [NW' SK'].
    pose proof (nth_error_lt _ _ _ NW') as LW.
    step. step. if_false. step. step.
    rewrite ltu_k by lia.
    destruct (Nat.lt_ge_cases k 63) as [K63|K63].
    + rewrite (proj2 (Nat.ltb_lt k 63) K63). cbv iota.
      replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.of_nat k)) + 1)))
        with (Z_to_bv 64 (Z.of_nat (S k))) by (symmetry; apply addiw_k; lia).
      replace (Z_to_bv 64 (Z.of_nat k + 1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
      replace (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat k + 8)) with (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat (S k)))
        by (f_equal; lia).
      eapply K; [exact K63|].
      split; [rewrite length_app, QL; cbn [length]; lia|].
      split; [lia|].
      split; [eapply Forall2_impl; [exact TK2 | exact HF1]|].
      split; [exists w'; split; [exact NW' | exact TW2]|].
      split.
      { exists rest1. split; [exact RL1|]. apply AR2; [|exact UA1].
        rewrite length_app, len_cle8, length_app, RL1, QL; cbn [length]; lia. }
      split; [exact SL2|].
      split; [rewrite SK'; exact HR2 | exact B2].
    + rewrite (proj2 (Nat.ltb_ge k 63) K63). cbv iota.
      assert (FE : firstn 64 (words T) = firstn (S k) (words T)) by (f_equal; lia).
      assert (NE : firstn 64 (words T) <> []).
      { rewrite FE, (firstn_S_nth _ _ _ NW). intros H. destruct (firstn k (words T)); discriminate. }
      eapply tok_fin with (ps := qs ++ [p]) (sv := sv').
      * rewrite (match_ne _ _ _ NE). reflexivity.
      * exact B2.
      * exact SL2.
      * exists rest1. split; [apply AR2; [|exact UA1]|]; rewrite length_app, len_cle8, length_app, RL1, QL;
          cbn [length]; lia.
      * rewrite FE. eapply Forall2_impl; [exact TK2 | exact HF1].
      * intros _. unfold ntokw. rewrite length_firstn, Nat.min_l by lia.
        split; [rewrite addiw_k by lia; f_equal; lia | f_equal; lia].
Qed.

Lemma tok_loop : forall d k qs p sv mk (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
  (k + d = 63)%nat -> linv k qs p sv mk ->
  evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 cb p a1 a2 a3 a4 a5 a6 a7 msg
                  (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 0x1064c) (Z_to_bv 64 (Z.of_nat k))
                  (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat k)) (Z_to_bv 64 63) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x174e8) fc None mk (seg_rom rsegs)).
Proof.
  induction d as [|d IH]; intros k qs p sv mk ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 HK HI;
    apply (tok_body k qs p sv mk ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 HI);
    intros p' sv' mk' ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' KL HI'.
  - lia.
  - apply (IH (S k) (qs ++ [p]) p' sv' mk'); [lia | exact HI'].
Qed.

Lemma tok_main : forall (ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 pv : word) junk can,
  u8arr rsegs m (bv_unsigned cb) (T ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) T ->
  rw_cells rsegs m SP [C8 pv; CB 512 junk] -> ssp_at m can -> stk rsegs m lo SP -> mem_inv rsegs m ->
  evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 cb a1 a2 a3 a4 a5 a6 a7 msg s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6) F (Z_to_bv 64 TOKENIZE) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 pv junk can HU HNZ HSL HSSP ST HMI.
  destruct (slot_split _ _ _ _ HSL) as (SL & AR & JL).
  assert (HB : basem m).
  { destruct HSSP as [G1 G2]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI|].
    split; [exact ST|]. split; [exact G1|exists can; exact G2]. }
  assert (HR : remp m (bv_unsigned cb) (words T)).
  { right. exists T. split; [lia|]. split; [exact HU|]. split; [exact HNZ|]. split; [lia|]. split; [lia|reflexivity]. }
  unfold TOKENIZE. do 6 step.
  eapply evt_cut.
  { eapply tok_call; [exact HB | exact SL |].
    replace (bv_unsigned cb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact HR. }
  destruct (words T) as [|w ws] eqn:WT.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk' & sv' &
                E & B2 & SL2 & TK2 & AR2 & A0).
    subst ms'. subst a0'. fix_ret.
    step. if_true.
    eapply tok_fin with (ps := []) (sv := sv').
    + rewrite WT. reflexivity.
    + exact B2.
    + exact SL2.
    + exists junk. split; [apply AR2; [exact JL | exact AR] | exact JL].
    + rewrite WT. constructor.
    + rewrite WT. intros H. exfalso. apply H. reflexivity.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk' & sv' &
                E & B2 & SL2 & TK2 & AR2 & NZ2 & TW2 & HR2).
    subst ms'. fix_ret.
    step. if_false. do 6 step.
    replace (Z_to_bv 64 (bv_unsigned sp + 8)) with (Z_to_bv 64 (SP + 8 + 8 * Z.of_nat 0)) by (f_equal; lia).
    eapply (tok_loop 63 0 [] a0' sv' mk'); [reflexivity|].
    split; [reflexivity|]. split; [lia|]. split; [constructor|].
    split; [exists w; split; [rewrite WT; reflexivity | exact TW2]|].
    split; [exists junk; split; [rewrite JL; reflexivity | apply AR2; [exact JL | exact AR]]|].
    split; [exact SL2|]. split; [rewrite WT; exact HR2 | exact B2].
Qed.

End Tok.

Theorem vr_tokenize : strtok_r_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (T junk : list byte) (pv can : word),
    u8arr rsegs m (bv_unsigned a0) (T ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) T -> 0 < bv_unsigned a0 ->
    bv_unsigned a0 + Z.of_nat (length T) + 1 <= lo \/ bv_unsigned sp + 520 <= bv_unsigned a0 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 pv; CB 512 junk] ->
    ssp_at m can -> stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> IMG_TOP <= lo ->
    mem_inv rsegs m ->
    evt rsegs (tok_post sp gp tp s0 s9 s10 s11 s2 a0 F fc lo m T)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOKENIZE) fc None m (seg_rom rsegs)).
Proof.
  intros SR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo T
    junk pv can HU HNZ HC HD HSL HSSP ST HLO HIT HMI.
  pose proof (u8arr_bound _ _ _ _ HU) as UB. rewrite length_app in UB. cbn [length] in UB.
  pose proof (rw_cells_bound _ _ _ _ HSL) as SB. cbn [cells_size csize] in SB.
  eapply tok_main; try eassumption; lia.
Qed.
