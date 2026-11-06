(* model_write (fuzz_link.c:403-421), PLAIN build: the walk of its contract (lib/Prog/model_write_c.v)
   on the plain image, 0x15c50, 264 bytes (link/ct/dis/plain/model_write.s).

   Shape: a 560-byte frame (ra, s0..s4 saved at sp'+0x228..0x200); -EINVAL for a NULL name (0x15c74),
   a NULL alias (0x15c7c) or an empty name (0x15c88); strlen of the alias (0x15c90), -ENAMETOOLONG
   above 255 (0x15c98); index_of (0x15cac), -ENODEV for 0 (0x15cb0); then the RTM_NEWLINK of
   link_spec`s `req_write` in the frame at sp': memset of its `len` bytes (0x15cd0), six stores
   (0x15ce0-0x15cfc), memcpy of the alias to sp'+36 (0x15d0c); talk (0x15d2c) answers.
   index_of and talk are `leaf` contracts, called through lib/Prog/mk_call.v `leaf_call`; strlen,
   memset and memcpy are the libc contracts, instantiated closed at the end. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf mk_call hp_md_kit model_write_c index_of_c talk_c memset_c memset memcpy_c memcpy
  strlen_c strlen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* ---- pure facts and view uniqueness (as in the model_read walk) ---- *)

(* the strlen slack, cut to what strlen reads: the bytes up to the next multiple of 8 *)
Lemma mw_slack_trim : forall m A s slack,
  bytes_at rsegs m A (s ++ [zb 0]) -> bytes_at rsegs m (A + Z.of_nat (length s) + 1) slack ->
  (- (A + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
  exists slk, bytes_at rsegs m A (s ++ zb 0 :: slk)
    /\ Z.of_nat (length slk) = (- (A + Z.of_nat (length s) + 1)) mod 8.
Proof.
  intros m A s slack B1 B2 Hl.
  pose proof (Z.mod_pos_bound (- (A + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hk.
  remember ((- (A + Z.of_nat (length s) + 1)) mod 8) as k eqn:Ek. clear Ek.
  exists (firstn (Z.to_nat k) slack). split.
  - replace (s ++ zb 0 :: firstn (Z.to_nat k) slack) with ((s ++ [zb 0]) ++ firstn (Z.to_nat k) slack)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact B1|].
    rewrite length_app. cbn [length].
    replace (A + Z.of_nat (length s + 1)) with (A + Z.of_nat (length s) + 1) by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) slack) in B2. apply bytes_at_app in B2. exact (proj1 B2).
  - rewrite length_firstn. lia.
Qed.

(* what a refused write leaves: the model block as it was *)
Lemma mw_refused_tail : forall m1 mF sp0 pm mbs kbs,
  munch [(sp0 - 704, sp0)] m1 mF -> wmono rsegs m1 mF ->
  model_at m1 pm mbs -> model_wf mbs -> (pm + MD_SIZE <= sp0 - 704 \/ sp0 <= pm) ->
  exists mbs', model_at mF pm mbs' /\ model_wf mbs'
      /\ md_next mbs' = Z.of_nat (k_next (md_kstate mbs kbs))
      /\ md_socket_errno mbs' = k_sock (md_kstate mbs kbs)
      /\ md_send_errno mbs' = k_send (md_kstate mbs kbs)
      /\ md_reqs mbs' = md_reqs mbs /\ md_n_req mbs' = Z.of_nat (length (md_reqs mbs))
      /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs.
Proof.
  intros m1 mF sp0 pm mbs kbs MUf WMf MA1 MWF AFM.
  pose proof MWF as (Hr & Hn & _).
  exists mbs. split; [apply (model_at_munch _ m1 mF _ mbs MA1 MUf WMf); apply clear1; lia|].
  split; [exact MWF|]. cbn [md_kstate k_next k_sock k_send].
  split; [rewrite Z2Nat.id by lia; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [unfold md_reqs; rewrite length_map, length_seq, Z2Nat.id by lia; reflexivity|].
  split; reflexivity.
Qed.

(* ---- the request the main path builds ---- *)

(* 32 + ((alen + 7) & 0x1fc) is link_spec`s 32 + NL_ALIGN(4 + alen) for every alias of at most 255 bytes *)
Lemma mw_len_eq : forall n, 0 <= n <= 255 -> Z.land (n + 7) 508 = nl_align (4 + n).
Proof.
  intros n Hn.
  assert (B : forallb (fun k => Z.eqb (Z.land (Z.of_nat k + 7) 508) (nl_align (4 + Z.of_nat k))) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B (Z.to_nat n)). rewrite Z2Nat.id in B by lia.
  apply Z.eqb_eq, B. apply in_seq. lia.
Qed.

Lemma mw_cut2 : forall m A n j k, rw_cells rsegs m A [CB n j] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k j)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k j)].
Proof.
  intros m A n j k H Hk. apply (rw_cells_cb_cut _ _ _ _ k) in H; [|exact Hk].
  change [CB k (firstn k j); CB (n - k) (skipn k j)] with ([CB k (firstn k j)] ++ [CB (n - k) (skipn k j)]) in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. split; [exact H1|].
  cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma mw_cb_bytes : forall m A n j, rw_cells rsegs m A [CB n j] -> bytes_at rsegs m A j.
Proof. intros m A n j [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma mw_firstn_repeat : forall {T : Type} (x : T) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof.
  intros T x n. induction n as [|n IH]; intros [|k] Hk; cbn; try reflexivity; [lia|].
  f_equal. apply IH. lia.
Qed.

Lemma mw_skipn_repeat : forall {T : Type} (x : T) n k, skipn k (repeat x n) = repeat x (n - k).
Proof. intros T x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

(* the 36 zero bytes of the header, cut at the fields the six stores write *)
Lemma mw_split36 : forall m A, rw_cells rsegs m A [CB 36 (repeat (zb 0) 36)] ->
  rw_cells rsegs m A [CB 4 (repeat (zb 0) 4); CB 4 (repeat (zb 0) 4); CB 4 (repeat (zb 0) 4);
                      CB 8 (repeat (zb 0) 8); CB 4 (repeat (zb 0) 4); CB 8 (repeat (zb 0) 8);
                      CB 2 (repeat (zb 0) 2); CB 2 (repeat (zb 0) 2)].
Proof.
  intros m A [[_ B] W]. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split.
  - cbn [cells_bytes cbytes] in *. exact B.
  - exact W.
Qed.

(* the bytes at sp' after the stores and the memcpy are link_spec`s `req_write` *)
Lemma mw_req_write_at : forall m A w0 w1 w2 w3 w4 w5 al idx len tl,
  bv_unsigned w0 = len -> len = nl_align (4 + Z.of_nat (length al)) + 32 ->
  bv_unsigned w1 = 327696 -> bv_unsigned w2 = 1 -> bv_unsigned w3 = idx ->
  bv_unsigned w4 = 4 + Z.of_nat (length al) -> bv_unsigned w5 = 20 ->
  tl = zeros (nl_align (RTA_HDR + Z.of_nat (length al)) - RTA_HDR - Z.of_nat (length al)) ->
  rw_cells rsegs m A [C4 w0; C4 w1; C4 w2; CB 8 (repeat (zb 0) 8); C4 w3; CB 8 (repeat (zb 0) 8);
                      C2 w4; C2 w5] ->
  bytes_at rsegs m (A + 36) al ->
  bytes_at rsegs m (A + 36 + Z.of_nat (length al)) tl ->
  bytes_at rsegs m A (req_write idx al).
Proof.
  intros m A w0 w1 w2 w3 w4 w5 al idx len tl E0 EL E1 E2 E3 E4 E5 -> [[_ B1] _] B2 B3.
  cbn [cells_bytes cbytes] in B1. unfold le4, le2 in B1. rewrite E0, E1, E2, E3, E4, E5, app_nil_r in B1.
  assert (EP : forall t, Z_to_le_bytes 2 RTM_NEWLINK ++ Z_to_le_bytes 2 (F_REQUEST + F_ACK)
                           ++ Z_to_le_bytes 4 1 ++ zeros 4 ++ zeros 4 ++ t
                         = Z_to_le_bytes 4 327696 ++ Z_to_le_bytes 4 1 ++ repeat (zb 0) 8 ++ t).
  { intros t. rewrite !app_assoc. f_equal. apply bytes_eq_bz. vm_compute. reflexivity. }
  assert (ER : req_write idx al =
    (Z_to_le_bytes 4 len ++ Z_to_le_bytes 4 327696 ++ Z_to_le_bytes 4 1 ++ repeat (zb 0) 8
     ++ Z_to_le_bytes 4 idx ++ repeat (zb 0) 8 ++ Z_to_le_bytes 2 (4 + Z.of_nat (length al))
     ++ Z_to_le_bytes 2 20)
    ++ al ++ zeros (nl_align (RTA_HDR + Z.of_nat (length al)) - RTA_HDR - Z.of_nat (length al))).
  { unfold req_write. cbv zeta. rewrite EP. rewrite <- !app_assoc.
    replace (32 + nl_align (RTA_HDR + Z.of_nat (length al))) with len by (unfold RTA_HDR; lia).
    reflexivity. }
  rewrite ER. apply bytes_at_app. split; [exact B1|]. apply bytes_at_app. split.
  - replace (A + Z.of_nat (length (Z_to_le_bytes 4 len ++ Z_to_le_bytes 4 327696 ++ Z_to_le_bytes 4 1
        ++ repeat (zb 0) 8 ++ Z_to_le_bytes 4 idx ++ repeat (zb 0) 8
        ++ Z_to_le_bytes 2 (4 + Z.of_nat (length al)) ++ Z_to_le_bytes 2 20)))
      with (A + 36) by (cbn; lia).
    exact B2.
  - replace (A + Z.of_nat (length (Z_to_le_bytes 4 len ++ Z_to_le_bytes 4 327696 ++ Z_to_le_bytes 4 1
        ++ repeat (zb 0) 8 ++ Z_to_le_bytes 4 idx ++ repeat (zb 0) 8
        ++ Z_to_le_bytes 2 (4 + Z.of_nat (length al)) ++ Z_to_le_bytes 2 20)) + Z.of_nat (length al))
      with (A + 36 + Z.of_nat (length al)) by (cbn; lia).
    exact B3.
Qed.

Ltac mw_prologue ST := carve_frame 560%nat ST; do 9 zstep.

Ltac mw_curm := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Ltac mw_top S v := lazymatch type of S with stk _ _ _ ?h => replace h with v in S by lia end.

(* the refused paths: the frame is still one piece FR *)
Ltac mw_refused_head sp MU WM MI ST FR MA NK IT SN' SL' :=
  apply evt_done; eexists; eexists; split; [reflexivity|];
  split; [apply regs_preserved_mkR|];
  split; [exact MU|]; split; [exact WM|]; split; [exact MI|];
  split;
  [ let S1 := fresh "S1" in
    pose proof (stk_release rsegs _ _ _ _ ST FR ltac:(lia)) as S1; cbn [cells_size csize Nat.add] in S1;
    replace (bv_unsigned sp + -560 + Z.of_nat 560) with (bv_unsigned sp) in S1 by lia; exact S1
  | ];
  let MA0 := fresh "MA0" in let NK0 := fresh "NK0" in let IT0 := fresh "IT0" in
  let SN0 := fresh "SN0" in let SL0 := fresh "SL0" in
  intros ? ? ? ? ? MA0 NK0 IT0 SN0 SL0;
  pose proof (model_at_uniq _ _ _ _ MA0 MA) as ->; pose proof (nlk_at_uniq _ _ _ NK0 NK) as ->;
  pose proof (iftab_uniq _ _ _ _ IT0 IT) as ->; pose proof (str_arg_uniq _ _ _ _ SN0 SN') as ->;
  pose proof (str_arg_uniq _ _ _ _ SL0 SL') as ->;
  unfold write_model, write_core; cbv zeta; cbn [length Nat.eqb].

Ltac mw_refused_tail_tac MUw WM MA MWF AFM :=
  cbn [w_rc w_reqs w_state]; split; [reflexivity|];
  exact (mw_refused_tail _ _ _ _ _ _ MUw WM MA MWF AFM).

Section Walk.
Hypothesis HIDX : index_of_contract_P.
Hypothesis HTALK : talk_contract.
Hypothesis HMS : memset_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HSL : strlen_contract.

Theorem model_write_holds : model_write_contract.
Proof.
  unfold model_write_contract. apply leaf_intro.
  - intros r1 r2 m E H. unfold arg, apart_frame, frame_apart_gnl, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. unfold arg. rewrite !E. reflexivity.
  - intros r1 r2 m q1 q2 m' E1 E2 H. unfold arg in *. rewrite <- !E1, <- !E2. exact H.
  - unfold leaf_walk, MODEL_WRITE.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HPRE MI ST LO SP.
    destruct HPRE as (mbs & kbs & tab & nm & al & MA & MWF & NK & FAG & NWF & IT & SN & SL & AGM & AFM
                      & AFN & AFL & SLK & AFT).
    unfold frame_apart_gnl, apart_frame in *.
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_sp in *.
    lazymatch goal with |- evt _ ?Q _ => assert (HQ : q_ext Q) end.
    { apply leaf_q_ext. intros q1 q2 m' E H. cbv beta in *. rewrite <- !E. exact H. }
    pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1.
    pose proof (zr_word a2) as Ra2. unfold inr64 in *.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 704, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + MD_SIZE)] m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 704, bv_unsigned sp)] m) as MUw.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    assert (U560 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -560)) = bv_unsigned sp + -560)
      by (apply unsigned_lit; lia).
    pose proof SN as SN'. pose proof SL as SL'.
    destruct nm as [s|].
    2: { cbn [str_arg] in SN. mw_prologue ST. zstep. if_true. do 8 zstep.
         mw_refused_head sp MU WM MI ST FR MA NK IT SN' SL'. mw_refused_tail_tac MUw WM MA MWF AFM. }
    destruct al as [a|].
    2: { cbn [str_arg] in SL. destruct SN as [Hn0 _]. mw_prologue ST. zstep. if_false. zstep. zstep. if_true.
         do 8 zstep. mw_refused_head sp MU WM MI ST FR MA NK IT SN' SL'. mw_refused_tail_tac MUw WM MA MWF AFM. }
    destruct SN as [Hn0 [BN NN]]. destruct SL as [Ha0 CA].
    specialize (AFN s eq_refl). specialize (AFL a eq_refl).
    destruct (SLK a eq_refl) as (slack & BSl & Hsl). clear SLK.
    destruct (mw_slack_trim m (bv_unsigned a2) a slack (proj1 CA) BSl Hsl) as (slk & BA & Hslk).
    clear BSl Hsl slack.
    assert (LS : Z.of_nat (length slk) <= 7)
      by (rewrite Hslk; pose proof (Z.mod_pos_bound (- (bv_unsigned a2 + Z.of_nat (length a) + 1)) 8 ltac:(lia)); lia).
    assert (SLKP : forall X, X = bv_unsigned a2 ->
              (- (X + Z.of_nat (length a) + 1)) mod 8 <= Z.of_nat (length slk)) by (intros X ->; lia).
    clear Hslk. pose proof (proj2 CA) as NA.
    mw_prologue ST.
    zstep. if_false. zstep. zstep. if_false. zstep.
    let mm := mw_curm in rename mm into m1.
    destruct s as [|c s'].
    { (* the empty name *)
      assert (HR : ov_read_bytes rsegs m1 a1 1 = Some [zb 0]).
      { pose proof (bytes_at_ov_read rsegs m1 (bv_unsigned a1) ([] ++ [zb 0]) 0 1 BN ltac:(cbn; lia)) as E.
        rewrite (wa_of_var a1 (bv_unsigned a1 + Z.of_nat 0)) in E by lia. exact E. }
      zstep. zstep. if_true. do 8 zstep.
      mw_refused_head sp MU WM MI ST FR MA NK IT SN' SL'. mw_refused_tail_tac MUw WM MA MWF AFM. }
    assert (HR : ov_read_bytes rsegs m1 a1 1 = Some [c]).
    { pose proof (bytes_at_ov_read rsegs m1 (bv_unsigned a1) ((c :: s') ++ [zb 0]) 0 1 BN
                    ltac:(cbn; lia)) as E.
      rewrite (wa_of_var a1 (bv_unsigned a1 + Z.of_nat 0)) in E by lia. exact E. }
    assert (Hc0 : c <> zb 0) by (intros ->; apply NN; left; reflexivity).
    assert (HC : bv_unsigned (Z_to_bv 64 (bv_unsigned c)) <> 0).
    { rewrite unsigned_lit; [exact (byte_ne0 c Hc0)|]. pose proof (bv_unsigned_in_range 8 c) as Hb.
      unfold bv_modulus in Hb. cbn in Hb. lia. }
    zstep. zstep. if_false. clear HR. zstep. zstep.
    (* strlen of the alias *)
    eapply evt_cut.
    { eapply HSL with (str := a) (slack := slk); [exact BA | exact NA | exact (SLKP _ eq_refl) | exact MI]. }
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
               & -> & MUs & WMs & MIs & BAs).
    clear BA. transport_after_call rsegs m1 m2 MUs WMs.
    clear MUs WMs MI. rename MIs into MI. rename BAs into BA.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length a))) = Z.of_nat (length a)).
    { apply unsigned_lit. pose proof (bytes_at_bound _ _ _ _ BA) as B. rewrite length_app in B.
      cbn [length] in B. lia. }
    destruct (Z_le_gt_dec (Z.of_nat (length a)) 255) as [AL|AL].
    2: { zstep. zstep. if_false. zstep. zstep. do 8 zstep.
         mw_refused_head sp MU WM MI ST FR MA NK IT SN' SL'.
         assert (HAL : (ALIAS_MAX <=? Z.of_nat (length a)) = true) by (apply Z.leb_le; unfold ALIAS_MAX; lia).
         rewrite HAL. mw_refused_tail_tac MUw WM MA MWF AFM. }
    assert (HAL : (ALIAS_MAX <=? Z.of_nat (length a)) = false) by (apply Z.leb_gt; unfold ALIAS_MAX; lia).
    zstep. zstep. if_true. zstep. zstep. zstep.
    (* index_of of the name *)
    assert (CG : clear_of [(bv_unsigned sp - 704, bv_unsigned sp)] A_G_NL NK_SIZE)
      by (apply clear1; clear - FAG; unfold apart_gnl in *; lia).
    assert (NK2 : nlk_at m2 kbs) by exact (nlk_at_munch _ m m2 kbs NK MUw WM CG).
    assert (IT2 : iftab_at m2 kbs tab).
    { apply (iftab_at_munch _ m m2 kbs tab IT MUw CG). intros i n2 ix p Hi Hp. apply clear1.
      pose proof (AFT i n2 ix p Hi Hp) as X. clear - X. lia. }
    assert (CS2 : cstr_at m2 (bv_unsigned a1) (c :: s')) by (split; [exact BN | exact NN]).
    assert (SLOT : forall i p, 0 <= i < 80 -> u64_at m2 (A_G_NL + NK_IF_NAME + 8 * i) p ->
                     u64_at m (A_G_NL + NK_IF_NAME + 8 * i) p)
      by (intros i p Hi Hp; exact (u64_slot_back _ m m2 i p MUw CG Hi Hp)).
    eapply (leaf_call _ _ _ _ _ HIDX).
    { exact index_of_post_ext. }
    { exact HQ. }
    { exists kbs, tab, (c :: s'). unfold apart_frame, frame_apart_gnl. rewrite ?mkR_a0, ?mkR_sp, U560.
      refine (conj NK2 (conj _ (conj IT2 (conj Hn0 (conj CS2 (conj _ _)))))).
      - clear - FAG. unfold apart_gnl in *. lia.
      - clear - AFN. lia.
      - intros i n2 ix p Hi Hp.
        assert (Li : 0 <= Z.of_nat i < 80).
        { assert (L : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
          destruct IT2 as (_ & HL & _). lia. }
        pose proof (AFT i n2 ix p Hi (SLOT (Z.of_nat i) p Li Hp)) as X. clear - X. lia. }
    { exact MI. }
    { rewrite U560. exact ST. }
    { rewrite U560. lia. }
    { rewrite U560. lia. }
    intros ra' t0'' t1'' t2'' a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 MUi WMi MIi STi POi.
    cbv beta in POi. unfold writes_nothing in MUi. rewrite U560 in MUi, STi.
    assert (IDX : a0' = wz (index_of tab (c :: s'))) by exact (POi kbs tab (c :: s') NK2 IT2 CS2).
    clear POi NK2 IT2 CS2 SLOT.
    transport_after_call rsegs m2 m3 MUi WMi.
    clear MUi WMi MI. rename MIi into MI. try clear ST. rename STi into ST.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (Ridx : 0 <= index_of tab (c :: s') < 2 ^ 31)
      by exact (index_of_range tab _ (iftab_range m kbs tab IT)).
    assert (UA : bv_unsigned a0' = index_of tab (c :: s')) by (rewrite IDX; unfold wz; apply unsigned_lit; lia).
    destruct (Z.eq_dec (index_of tab (c :: s')) 0) as [I0|I0].
    { zstep. if_true. zstep. do 8 zstep.
      mw_refused_head sp MU WM MI ST FR MA NK IT SN' SL'.
      assert (HI0 : (index_of tab (c :: s') =? 0) = true) by (apply Z.eqb_eq; exact I0).
      rewrite HAL, HI0. mw_refused_tail_tac MUw WM MA MWF AFM. }
    zstep. if_false.
    do 8 zstep.
    (* the request length: s4 = 32 + ((alen + 7) & 0x1fc) *)
    pose proof (nl_align_le (4 + Z.of_nat (length a)) ltac:(lia)) as NLA.
    rewrite (mw_len_eq (Z.of_nat (length a))) by lia.
    remember (nl_align (4 + Z.of_nat (length a)) + 32) as len eqn:Elen.
    assert (LENr : 36 + Z.of_nat (length a) <= len <= 294) by lia.
    assert (Us4 : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    (* the frame: [sp-560, sp-560+len) for the request, the rest of the 512 bytes, the saves *)
    lazymatch type of FR with rw_cells _ _ _ (CB 512 ?j :: ?rest) =>
      change (CB 512 j :: rest) with ([CB 512 j] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FR512 FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    replace (bv_unsigned sp + -560 + Z.of_nat 512) with (bv_unsigned sp + -48) in FRhi by lia.
    destruct (mw_cut2 _ _ _ _ (Z.to_nat len) FR512 ltac:(lia)) as [FRm FRrest]. clear FR512.
    replace (bv_unsigned sp + -560 + Z.of_nat (Z.to_nat len)) with (bv_unsigned sp + -560 + len) in FRrest by lia.
    (* memset(sp', 0, len) *)
    eapply evt_cut.
    { rewrite <- U560, <- Us4 in FRm. eapply HMS; [exact FRm | exact MI]. }
    intros ms (t0m & t1m & t2m & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3m & t4m & t5m & t6m & m4
               & -> & MUm & WMm & MIm & FRz).
    rewrite U560, Us4 in MUm, FRz.
    change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in FRz.
    clear FRm. transport_after_call rsegs m3 m4 MUm WMm.
    clear MUm WMm MI. rename MIm into MI.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    (* the 36 header bytes the six stores fill, and the rest of the request *)
    destruct (mw_cut2 _ _ _ _ 36 FRz ltac:(lia)) as [FR36 FRt]. clear FRz.
    rewrite mw_firstn_repeat in FR36 by lia. rewrite mw_skipn_repeat in FRt.
    apply mw_split36 in FR36.
    replace (bv_unsigned sp + -560 + Z.of_nat 36) with (bv_unsigned sp + -524) in FRt by lia.
    do 11 zstep.
    let mm := mw_curm in rename mm into m5.
    do 4 zstep.
    (* memcpy(sp'+36, alias, alen) *)
    destruct (mw_cut2 _ _ _ _ (length a) FRt ltac:(lia)) as [FRa FRz2]. clear FRt.
    rewrite mw_firstn_repeat in FRa by lia. rewrite mw_skipn_repeat in FRz2.
    assert (U524 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -524)) = bv_unsigned sp + -524)
      by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply HMC with (src := a) (junk := repeat (Z_to_bv 8 0) (length a)).
      - exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BA)).
      - rewrite UL, Nat2Z.id. reflexivity.
      - rewrite U524, UL, Nat2Z.id. exact FRa.
      - rewrite U524, UL. lia.
      - exact MI. }
    intros ms (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m6
               & -> & MUc & WMc & MIc & FRac & BSc).
    rewrite U524, UL in MUc. rewrite U524, UL, Nat2Z.id in FRac.
    clear BSc FRa. transport_after_call rsegs m5 m6 MUc WMc.
    clear MUc WMc MI. rename MIc into MI.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    (* the request at sp' *)
    assert (REQ : bytes_at rsegs m6 (bv_unsigned sp + -560) (req_write (index_of tab (c :: s')) a)).
    { pose proof (mw_cb_bytes _ _ _ _ FRac) as B2. pose proof (mw_cb_bytes _ _ _ _ FRz2) as B3.
      refine (mw_req_write_at m6 (bv_unsigned sp + -560) _ _ _ _ _ _ a (index_of tab (c :: s')) len
                (repeat (Z_to_bv 8 0) (Z.to_nat len - 36 - length a)) _ Elen _ _ UA _ _ _ FR36 _ _).
      - exact Us4.
      - reflexivity.
      - reflexivity.
      - rewrite unsigned_lit by lia. lia.
      - reflexivity.
      - unfold zeros, RTA_HDR. f_equal; try reflexivity; lia.
      - replace (bv_unsigned sp + -560 + 36) with (bv_unsigned sp + -524) by lia. exact B2.
      - replace (bv_unsigned sp + -560 + 36 + Z.of_nat (length a)) with (bv_unsigned sp + -524 + Z.of_nat (length a))
          by lia.
        exact B3. }
    assert (MA6 : model_at m6 (bv_unsigned a0) mbs).
    { apply (model_at_munch _ m m6 _ mbs MA MUw WM). apply clear1. clear - AFM. lia. }
    assert (NK6 : nlk_at m6 kbs) by exact (nlk_at_munch _ m m6 kbs NK MUw WM CG).
    pose proof (req_write_len (index_of tab (c :: s')) a ltac:(unfold ALIAS_MAX; lia)) as RL.
    unfold RTA_HDR in RL.
    assert (RL' : Z.of_nat (length (req_write (index_of tab (c :: s')) a)) = len) by lia.
    clear MUw RL.
    do 8 zstep.
    (* talk(m, sp', len, 0, 0, 0, 0) *)
    eapply (leaf_call _ _ _ _ _ HTALK).
    { intros r1 r2 mm q1 q2 mm' E1 E2 H. unfold arg, spZ in *. rewrite <- !E1, <- !E2. exact H. }
    { exact HQ. }
    { exists mbs, kbs, (req_write (index_of tab (c :: s')) a).
      unfold apart_frame, frame_apart_gnl, apart, buf_arg, NL_SENT_LEN.
      rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_a6, ?mkR_sp, ?U560, ?Us4.
      change (bv_unsigned (Z_to_bv 64 0)) with 0.
      refine (conj MA6 (conj MWF (conj NK6 (conj _ (conj NWF (conj REQ (conj RL' (conj _ (conj _ (conj _
               (conj _ (conj _ (conj _ (conj _ (conj AGM (conj _ (conj _ (conj _ _))))))))))))))))));
        first [ intros ?; exfalso; lia | clear - FAG; unfold apart_gnl in *; lia | lia ]. }
    { exact MI. }
    { rewrite U560. exact ST. }
    { rewrite U560. lia. }
    { rewrite U560. lia. }
    intros ra2 t0t t1t t2t a0t a1t a2t a3t a4t a5t a6t a7t t3t t4t t5t t6t m7 MUt WMt MIt STt POt.
    cbv beta in POt, MUt.
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_a6, ?mkR_sp in POt.
    rewrite ?U560, ?Us4 in POt.
    rewrite ?mkR_a0, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_a6 in MUt. rewrite ?U560 in MUt, STt.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in MUt. cbn [Z.eqb] in MUt.
    pose proof (POt mbs kbs (req_write (index_of tab (c :: s')) a) MA6 NK6 REQ RL') as PT.
    cbv zeta in PT. destruct PT as (RC & (mbs' & MA' & MWF' & NX & SE & SD & NM & MK & RQ & NR) & _).
    clear POt REQ.
    transport_after_call rsegs m6 m7 MUt WMt.
    clear MUt WMt MI. rename MIt into MI. try clear ST. rename STt into ST.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    zstep. do 8 zstep.
    apply evt_done. eexists. eexists. split; [reflexivity|].
    split; [apply regs_preserved_mkR|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split.
    { pose proof (stk_release rsegs _ _ _ _ ST FR36 ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1.
      mw_top S1 (bv_unsigned sp + -524).
      pose proof (stk_release rsegs _ _ _ _ S1 FRac ltac:(lia)) as S2. cbn [cells_size csize] in S2.
      mw_top S2 (bv_unsigned sp + -524 + Z.of_nat (length a)).
      pose proof (stk_release rsegs _ _ _ _ S2 FRz2 ltac:(lia)) as S3. cbn [cells_size csize] in S3.
      mw_top S3 (bv_unsigned sp + -560 + len).
      pose proof (stk_release rsegs _ _ _ _ S3 FRrest ltac:(lia)) as S4. cbn [cells_size csize] in S4.
      mw_top S4 (bv_unsigned sp + -48).
      pose proof (stk_release rsegs _ _ _ _ S4 FRhi ltac:(lia)) as S5. cbn [cells_size csize Nat.add] in S5.
      mw_top S5 (bv_unsigned sp). exact S5. }
    intros ? ? ? ? ? MA0 NK0 IT0 SN0 SL0.
    pose proof (model_at_uniq _ _ _ _ MA0 MA) as ->. pose proof (nlk_at_uniq _ _ _ NK0 NK) as ->.
    pose proof (iftab_uniq _ _ _ _ IT0 IT) as ->. pose proof (str_arg_uniq _ _ _ _ SN0 SN') as ->.
    pose proof (str_arg_uniq _ _ _ _ SL0 SL') as ->.
    unfold write_model, write_core. cbv zeta. cbn [length Nat.eqb].
    assert (HI0 : (index_of tab (c :: s') =? 0) = false) by (apply Z.eqb_neq; exact I0).
    rewrite HAL, HI0. cbn [w_rc w_reqs w_state].
    split; [exact RC|].
    exists mbs'. refine (conj MA' (conj MWF' (conj NX (conj _ (conj SD (conj RQ (conj _ (conj NM MK)))))))).
    + rewrite SE, talk_after_sock. reflexivity.
    + rewrite NR, RQ. reflexivity.
Qed.
End Walk.

Theorem model_write_holds_closed : index_of_contract_P -> talk_contract -> model_write_contract.
Proof.
  intros HIDX HTALK. exact (model_write_holds HIDX HTALK memset_holds memcpy_holds strlen_holds).
Qed.

Print Assumptions model_write_holds_closed.
Print Assumptions model_write_holds.
About model_write_holds.
About model_write_holds_closed.
