From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP Image ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import snprintf_c CommandModel CommandFP CommandTac
  printf_facts_c memchr_c strlen_c strcmp_c sup_reply_code_c rec_code_declared_c rec_shape_of_c syntax_reply_matches_c
  check_reply_answer_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Lemma rw_cells_app_split : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  destruct Hw as (Ha & Hn & Hw). rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma stk_after_write : forall W m m' A k bs, stk rsegs m A (A + k) -> wmono rsegs m m' -> munch W m m' ->
  bytes_at rsegs m' A bs -> (forall x, A + Z.of_nat (length bs) <= x < A + k -> outside W x) -> stk rsegs m' A (A + k).
Proof.
  intros W m m' A k bs (H1 & H2 & H) Hw Hm (Ba & Bl & Bb) Ho.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Z_lt_le_dec a (A + Z.of_nat (length bs))) as [Hin|Hout].
  - replace a with (A + Z.of_nat (Z.to_nat (a - A))) by lia. rewrite Bb by lia.
    destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply Ho. lia.
Qed.

Lemma task_mem_munch : forall m m' lo hi, MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  munch [(lo, hi)] m m' -> MemNorm.task_mem rsegs m'.
Proof.
  intros m m' lo hi TM (_ & _ & HS) MU a b E.
  destruct (Z_lt_le_dec (bv_unsigned a) lo) as [L|L]; [|destruct (Z_lt_le_dec (bv_unsigned a) hi) as [H|H]].
  2: { destruct (HS (bv_unsigned a) (conj L H)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
       destruct (m a) as [b'|] eqn:Ea; [exact (TM a b' Ea)|].
       unfold wview in W. rewrite Ea in W.
       destruct (find_segment rsegs (bv_unsigned a) 1) as [s|]; [left; discriminate | contradiction]. }
  all: rewrite (MU a) in E; [exact (TM a b E) | cbn [outside]; split; [lia | exact I]].
Qed.

Lemma mod64_32 : forall c, (c mod 2^64) mod 2^32 = c mod 2^32.
Proof. intros c. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.

Lemma sx32_small : forall n, 0 <= n < 2^31 -> sx32 (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof.
  intros n Hn. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma pf_digits_len : forall f x acc, (length (pf_digits f x acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc; cbn [pf_digits]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|].
  specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma pf_dec_len : forall c, (length (pf_dec c) <= 12)%nat.
Proof.
  intros c. unfold pf_dec. destruct (c <? 0); cbn [length].
  - pose proof (pf_digits_len 11 (- c) []) as H. cbn [length] in H. lia.
  - pose proof (pf_digits_len 11 c []) as H. cbn [length] in H. lia.
Qed.

Lemma shape_find_in : forall rows v, In (shape_find rows v) (SHAPE_LIT :: map snd rows).
Proof.
  induction rows as [|[[na nm] rp] rows IH]; intros v; cbn [shape_find map snd].
  - left. reflexivity.
  - destruct (rec_shape_of_c.bytes_eqb _ _).
    + right. left. reflexivity.
    + destruct (IH v) as [H|H]; [left; exact H | right; right; exact H].
Qed.

Definition shape_ok (A : Z) : bool :=
  ro_bytes_b rsegs A (img_str A ++ [NUL]) && (Z.of_nat (length (img_str A)) <? 128) &&
  forallb (fun z => negb (z =? 0)) (map bv_unsigned (img_str A)) && (0 <? A) && (A + 129 <=? 76404).

Lemma shape_all_ok : forallb shape_ok (SHAPE_LIT :: map snd shape_rows) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma shape_cstr : forall m A, mem_inv rsegs m -> In A (SHAPE_LIT :: map snd shape_rows) ->
  cstr_at m A (img_str A) /\ Z.of_nat (length (img_str A)) < 128 /\ 0 < A /\ A + 129 <= 76404.
Proof.
  intros m A HI Hin. pose proof shape_all_ok as H. rewrite forallb_forall in H. specialize (H A Hin).
  unfold shape_ok in H. repeat rewrite andb_true_iff in H. destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.ltb_lt in H2. apply Z.ltb_lt in H4. apply Z.leb_le in H5.
  split; [split|].
  - apply lit_at; [exact HI | exact H1 | lia | rewrite length_app; cbn [length]; lia].
  - apply notin_nul_lit. exact H3.
  - lia.
Qed.

Lemma nz_of_notin : forall (l : list byte) b, ~ In NUL l -> In b l -> bv_unsigned b <> 0.
Proof. intros l b H Hb E. apply H. replace NUL with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. Qed.

Lemma cstr_tr : forall lo S m m' a s, cstr_at m a s -> disjoint_from [(lo, S)] a (Z.of_nat (length s) + 1) ->
  munch [(lo, S)] m m' -> cstr_at m' a s.
Proof.
  intros lo S m m' a s [Hb Hn] Hd Hm. split; [|exact Hn].
  eapply bytes_at_transport; [exact Hb|exact Hm|]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact Hd.
Qed.

Lemma cstr_prefix : forall m a s slack, bytes_at rsegs m a (s ++ NUL :: slack) -> bytes_at rsegs m a (s ++ [NUL]).
Proof.
  intros m a s slack H. replace (s ++ NUL :: slack) with ((s ++ [NUL]) ++ slack) in H by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma str_prefix : forall m a s slack, bytes_at rsegs m a (s ++ slack) -> bytes_at rsegs m a s.
Proof. intros m a s slack H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma nul_read : forall m a s slack, bytes_at rsegs m a (s ++ NUL :: slack) ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat (length s))) 1 = Some [NUL].
Proof.
  intros m a s slack H. rewrite (bytes_at_ov_read _ _ _ _ (length s) 1 H) by (rewrite length_app; cbn; lia).
  rewrite skipn_app_exact. reflexivity.
Qed.

Lemma memchr_none : forall c (xr : list byte), c = 0 -> ~ In NUL xr ->
  find_byte c (firstn (Z.to_nat (Z.of_nat (length xr))) xr) = None.
Proof.
  intros c xr -> H. rewrite Nat2Z.id, firstn_all. apply find_byte_notin. intros b Hb. exact (nz_of_notin _ _ H Hb).
Qed.

Lemma memchr_res_none : forall A c n (xr : list byte), find_byte c (firstn (Z.to_nat n) xr) = None -> memchr_res A c n xr = 0.
Proof. intros A c n xr H. unfold memchr_res. rewrite H. reflexivity. Qed.

Lemma rw8_bytes : forall m A v, rw_cells rsegs m A [C8 v] -> bytes_at rsegs m A (le8 v).
Proof. intros m A v [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma res_below_img : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? CommandModel.IMG_END + 4096)
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_free_hi : forall D n, CommandModel.IMG_END + 4096 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs [_ H2].
  pose proof (proj1 (forallb_forall _ _) res_below_img s Hs) as E. apply Z.leb_le in E. lia.
Qed.

Lemma bytes_tr8 : forall lo hi m m' a v, bytes_at rsegs m a (le8 v) -> disjoint_from [(lo, hi)] a 8 ->
  munch [(lo, hi)] m m' -> bytes_at rsegs m' a (le8 v).
Proof. intros lo hi m m' a v Hb Hd Hm. eapply bytes_at_transport; [exact Hb | exact Hm |]. rewrite length_le8. exact Hd. Qed.

Lemma bytes_tr_str : forall lo hi m m' a s sl, bytes_at rsegs m a (s ++ NUL :: sl) ->
  disjoint_from [(lo, hi)] a (Z.of_nat (length s) + 1 + Z.of_nat (length sl)) ->
  munch [(lo, hi)] m m' -> bytes_at rsegs m' a (s ++ NUL :: sl).
Proof.
  intros lo hi m m' a s sl Hb Hd Hm. eapply bytes_at_transport; [exact Hb | exact Hm |].
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ. cbn [disjoint_from] in *. lia.
Qed.

Theorem check_reply_holds : memchr_contract -> check_reply_answer_contract -> sup_reply_code_contract -> strlen_contract ->
  rec_shape_of_contract -> snprintf_contract -> rec_code_declared_contract -> strcmp_contract ->
  syntax_reply_matches_contract -> check_reply_contract.
Proof.
  intros MC CRA SRC SLC RSO SNP RCD SC SRM.
  unfold memchr_contract in MC. unfold check_reply_answer_contract in CRA. unfold sup_reply_code_contract in SRC.
  unfold strlen_contract in SLC. unfold rec_shape_of_contract in RSO. unfold snprintf_contract in SNP.
  unfold rec_code_declared_contract in RCD. unfold strcmp_contract in SC. unfold syntax_reply_matches_contract in SRM.
  unfold check_reply_contract, CHECK_REPLY, CHECK_REPLY_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros ans rep ww p0 xr slack xa w0 sl0 n can.
  intros MI TM FRM ST LO IE SPH GG GU HG HA HN1 HR HRS HSH RNZ HXR HXN HXP HXD HXA HN HWN HWND HWW HWWD A0AL HW0 HWNZ AOK ROK.
  pose proof (bytes_ro8 _ _ _ HG) as RG. pose proof (bytes_ro4 _ _ _ HN1) as RN1.
  pose proof (bytes_ro8 _ _ _ HR) as RR. pose proof (bytes_ro8 _ _ _ HRS) as RRS.
  pose proof (bytes_ro4 _ _ _ HWN) as RWN. pose proof (bytes_ro8 _ _ _ HWW) as RWW.
  unfold GOT_GREC, G_REC, REC_ANSWER, REC_NREPLIES, REC_REPLY, REC_REPLY_SIZE, CommandModel.IMG_END, WORDS_N, WORDS_W,
    CommandModel.GOT_GUARD, CommandModel.GUARD, G_SHAPES in *.
  assert (LSH : Z.of_nat (length g_shapes_bytes) = 448) by (vm_compute; reflexivity).
  unfold outside_stack, disjoint_from in HXD, HWND, HWWD.
  change (213032 + 920) with 213952 in RN1, HN1. change (213032 + 928) with 213960 in RR, HR.
  change (213032 + 936) with 213968 in RRS, HRS. change (213032 + 912) with 213944 in HA.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 rep) as Rrep.
  assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  pose proof (bytes_at_bound _ _ _ _ HXR) as BXR. rewrite length_app in BXR. cbn [length] in BXR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (fun m' => task_mem_munch m m' lo (bv_unsigned sp) TM ST) as TMW.
  carve_frame 64%nat ST.
  assert (SPv : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (apply unsigned_lit; split; [Lia.lia | Lia.lia]).
  do 9 zstep.
  zstep. if_cases HB1; [exfalso; vm_compute in HB1; discriminate HB1|].
  zstep. zstep. if_cases HB2; [exfalso; zify_cond HB2; lia|].
  do 4 zstep.
  zstep. if_cases HOV; [exfalso; zify_cond HOV; lia|].
  do 4 zstep. if_cases HXZ.
  { exfalso. zify_cond HXZ.
    destruct (Z.ltb_spec 0 (bv_unsigned rep)) as [L1|L1]; destruct (Z.ltb_spec (bv_unsigned rep + Z.of_nat (length xr)) 1) as [L2|L2];
      try (vm_compute in HXZ; discriminate HXZ); lia. }
  zstep. if_cases HRZ; [exfalso; zify_cond HRZ; lia|].
  clear HOV HXZ HRZ.
  pose proof (nul_read _ _ _ _ HXR) as HRB.
  zstep. zstep. if_cases HB3; [exfalso; vm_compute in HB3; discriminate HB3|].
  clear HRB HB1 HB2 HB3.
  zstep.
  eapply evt_cut.
  { eapply MC with (buf := xr).
    - exact (str_prefix _ _ _ _ HXR).
    - unfold memchr_ok. rewrite (unsigned_lit (Z.of_nat (length xr))) by lia.
      rewrite memchr_none; [cbv beta iota; lia | vm_compute; reflexivity | exact HXN].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & HB2').
  subst ms'. clear HB2'.
  transport_after_call rsegs m1 m2 MU2 WM2.
  clear MU2 WM2 MI.
  rewrite memchr_res_none
    by (rewrite (unsigned_lit (Z.of_nat (length xr))) by lia; apply memchr_none; [vm_compute; reflexivity | exact HXN]).
  fix_ret.
  zstep. if_cases HB4; [exfalso; vm_compute in HB4; discriminate HB4|].
  clear HB4.
  zstep. zstep.
  eapply evt_cut.
  { eapply CRA with (lo := lo) (ans := ans) (rep := rep) (ww := ww) (p0 := p0) (xr := xr) (xa := xa) (w0 := w0) (n := n) (can := can).
    - exact MI2.
    - rewrite SPv. exact ST.
    - rewrite SPv. unfold CHECK_REPLY_ANSWER_K. lia.
    - unfold CommandModel.IMG_END. lia.
    - exact HG.
    - exact HA.
    - exact HR.
    - exact (rw8_bytes _ _ _ GG).
    - exact (rw8_bytes _ _ _ GU).
    - exact RNZ.
    - split; [exact (cstr_prefix _ _ _ _ HXR) | exact HXN].
    - unfold outside_stack, disjoint_from. rewrite SPv. lia.
    - intros NZ. destruct (HXA NZ) as [HC HD]. split.
      + eapply cstr_tr; [exact HC | exact HD | exact MU].
      + unfold outside_stack, disjoint_from in *. rewrite SPv. lia.
    - exact HN.
    - exact HWN.
    - unfold outside_stack, disjoint_from. rewrite SPv. lia.
    - exact HWW.
    - unfold outside_stack, disjoint_from. rewrite SPv. lia.
    - exact A0AL.
    - intros N1. destruct (HW0 ltac:(lia)) as (H1 & H2 & H3 & H4 & H5 & H6). unfold word_slot.
      unfold outside_stack, disjoint_from in H2, H6.
      split; [exact (bytes_tr8 _ _ _ _ _ _ H1 H2 MU)|].
      split; [unfold outside_stack, disjoint_from; rewrite SPv; lia|].
      split; [split; [exact (cstr_prefix _ _ _ _ (bytes_tr_str _ _ _ _ _ _ _ H3 H6 MU)) | exact H4]|].
      unfold outside_stack, disjoint_from. rewrite SPv. lia.
    - intros N1. apply HWNZ. lia.
    - exact AOK. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & E & MU3 & WM3 & MI3 & ST3).
  subst ms'. rewrite SPv in MU3, ST3.
  transport_after_call rsegs m2 m3 MU3 WM3.
  clear MU3 WM3 MI2.
  fix_ret.
  zstep. zstep.
  pose proof (lit_at _ RESP_LIT resp_lit_bytes MI3 ltac:(vm_compute; reflexivity) ltac:(unfold RESP_LIT; lia)
                ltac:(unfold RESP_LIT; cbn; lia)) as HL.
  eapply evt_cut.
  { eapply SRC with (lo := lo) (x := xr).
    - exact MI3.
    - rewrite SPv. exact ST3.
    - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
    - exact RNZ.
    - exact (cstr_prefix _ _ _ _ HXR).
    - exact HXN.
    - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
    - exact HL.
    - rewrite SPv. unfold SUP_REPLY_CODE_FRAME, RESP_LIT. lia. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & E & MU4 & WM4 & MI4 & ST4).
  subst ms'. rewrite SPv in MU4, ST4. unfold SUP_REPLY_CODE_FRAME in MU4. clear HL.
  transport_after_call rsegs m3 m4 MU4 WM4.
  clear MU4 WM4 MI3.
  fix_ret.
  pose proof (reply_code_range xr) as RC.
  zstep. if_cases HB5.
  - zify_cond HB5.
    assert (RCn : reply_code xr < 0).
    { destruct (Z_lt_le_dec (reply_code xr) 0) as [Hn|Hge]; [exact Hn|]. rewrite Z.mod_small in HB5 by lia. lia. }
    destruct ROK as [ROKn _]. destruct (ROKn RCn) as [DC XE]. clear ROKn.
    set (T := [114; 101; 115; 112; 32] ++ pf_dec (reply_code xr)).
    assert (XT : pf_bytes T = xr) by (symmetry; exact XE).
    pose proof (pf_dec_len (reply_code xr)) as LD.
    assert (LT : (length T <= 17)%nat) by (unfold T; rewrite length_app; cbn [length]; lia).
    do 6 zstep.
    destruct (rw_cells_app_split _ _ [CB 32 _] [C8 s2; C8 s1; C8 s0; C8 ra] FR) as [FB FR2]. clear FR.
    cbn [cells_size csize Nat.add] in FR2.
    replace (bv_unsigned sp + -64 + Z.of_nat 32) with (bv_unsigned sp + -32) in FR2 by lia.
    pose proof (stk_of_rw_cells rsegs _ _ _ FB) as SB. cbn [cells_size csize Nat.add] in SB.
    change (Z.of_nat 32) with 32 in SB.
    zstep.
    pose proof (lit_at _ 0x10982 (pf_bytes ([114; 101; 115; 112; 32; 37; 100] ++ [0])) MI4 ltac:(vm_compute; reflexivity)
                  ltac:(lia) ltac:(cbn; lia)) as HF.
    eapply evt_cut.
    { eapply SNP with (lo := lo) (canary := can) (fmt := [114; 101; 115; 112; 32; 37; 100])
        (ps := [PLit 114; PLit 101; PLit 115; PLit 112; PLit 32; Pd]) (args := [AInt (reply_code xr)]) (T := T).
      - exact HF.
      - rewrite unsigned_lit by lia. unfold RO_LO. lia.
      - rewrite unsigned_lit by lia. unfold RO_END. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      - reflexivity.
      - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact RC|]. rewrite unsigned_lit_wrap. apply mod64_32.
      - unfold T. cbn [pf_text option_map app]. rewrite app_nil_r. reflexivity.
      - rewrite SPv. exact FB.
      - rewrite unsigned_lit by lia. lia.
      - lia.
      - rewrite SPv. lia.
      - rewrite SPv. right. lia.
      - rewrite SPv. apply img_free_hi. unfold CommandModel.IMG_END. lia.
      - rewrite SPv. exact ST4.
      - rewrite SPv. unfold SNPRINTF_K. lia.
      - unfold snprintf_c.IMG_END. lia.
      - rewrite SPv. lia.
      - exact FRM.
      - exact MI4.
      - exact (TMW m4 MU).
      - exact (rw8_bytes _ _ _ GG).
      - exact (rw8_bytes _ _ _ GU). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Ft & fc' & m5 &
                E & MU5 & WM5 & MI5 & _ & FRM5 & FEQ & ST5 & HT).
    subst ms'. rewrite SPv in MU5, ST5, HT. clear HF.
    replace (Z.to_nat (bv_unsigned (Z_to_bv 64 32) - 1)) with 31%nat in MU5, HT by reflexivity.
    rewrite firstn_all2 in MU5, HT by lia.
    pose proof (stk_after_write _ _ _ _ 32 _ SB WM5 MU5 HT) as SB1.
    assert (SB2 : stk rsegs m5 (bv_unsigned sp + -64) (bv_unsigned sp + -64 + 32)).
    { apply SB1. intros y Hy. unfold pf_bytes in Hy. rewrite length_map, length_app in Hy. cbn [length] in Hy.
      cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    clear SB1.
    transport_after_call rsegs m4 m5 MU5 WM5.
    clear MU5 WM5 MI4.
    pose proof (stk_merge rsegs _ _ _ _ ST5 SB2 ltac:(lia)) as ST6. clear ST5 SB2. rename ST6 into ST5.
    replace (bv_unsigned sp + -64 + 32) with (bv_unsigned sp + -32) in ST5 by lia.
    unfold pf_bytes in HT. rewrite map_app in HT. fold (pf_bytes T) in HT. rewrite XT in HT.
    fix_ret.
    zstep. zstep.
    pose proof (lit_at _ REC_CODES rec_codes_bytes MI5 ltac:(vm_compute; reflexivity) ltac:(unfold REC_CODES; lia)
                  ltac:(unfold REC_CODES; vm_compute; discriminate)) as HRC.
    eapply evt_cut.
    { eapply RCD with (c := reply_code xr).
      - exact RC.
      - reflexivity.
      - exact HRC. }
    intros ms' (? & ? & ? & E). subst ms'. rewrite DC. clear HRC.
    fix_ret.
    zstep. if_cases HB7; [exfalso; vm_compute in HB7; discriminate HB7|].
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SC with (sx := xr) (sy := xr).
      - exact (cstr_prefix _ _ _ _ HXR).
      - exact HXN.
      - rewrite SPv. exact HT.
      - exact HXN. }
    intros ms' (r & ? & ? & ? & E & Hr). subst ms'.
    assert (R0 : r = Z_to_bv 64 0) by (apply Hr; reflexivity). subst r.
    fix_ret.
    zstep. if_cases HB8; [|exfalso; vm_compute in HB8; discriminate HB8].
    do 5 zstep. release_frame FR2 ST5 (bv_unsigned sp). zstep. finish.
  - zify_cond HB5.
    assert (RCp : 0 <= reply_code xr).
    { destruct (Z_lt_le_dec (reply_code xr) 0) as [Hn|Hge]; [|exact Hge]. exfalso.
      assert (M : reply_code xr mod 18446744073709551616 = reply_code xr + 18446744073709551616)
        by (symmetry; apply Z.mod_unique with (-1); lia).
      lia. }
    destruct ROK as [_ ROKp]. specialize (ROKp RCp).
    zstep. zb_masks. rewrite A0AL.
    zstep. if_cases HAL; [exfalso; zify_cond HAL; lia|].
    zstep. rewrite sx32_small by lia.
    zstep. if_cases HB6.
    + assert (N0 : n = 0) by (zify_cond HB6; try rewrite Z.mod_small in HB6 by lia; lia).
      unfold shape_addr in ROKp. rewrite (proj2 (Z.eqb_eq n 0) N0) in ROKp. cbv beta iota in ROKp.
      do 4 zstep.
      destruct (shape_cstr m4 SHAPE_LIT MI4 (or_introl eq_refl)) as (HSA & LSA & A0 & AE).
      eapply evt_cut.
      { eapply SRM with (lo := lo) (shape := img_str SHAPE_LIT) (reply := xr) (slack := slack) (can := can).
        - exact MI4.
        - rewrite SPv. exact ST4.
        - rewrite SPv. unfold SYNTAX_REPLY_MATCHES_K. lia.
        - unfold CommandModel.IMG_END. lia.
        - rewrite unsigned_lit by (unfold SHAPE_LIT; lia). unfold SHAPE_LIT. lia.
        - rewrite unsigned_lit by (unfold SHAPE_LIT; lia). exact HSA.
        - unfold outside_stack, disjoint_from. rewrite SPv. rewrite unsigned_lit by (unfold SHAPE_LIT; lia).
          unfold SHAPE_LIT in *. lia.
        - exact RNZ.
        - exact HXR.
        - exact HXN.
        - exact HXP.
        - unfold outside_stack, disjoint_from. rewrite SPv. lia.
        - exact (rw8_bytes _ _ _ GG).
        - exact (rw8_bytes _ _ _ GU).
        - lia. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & E & MU5 & WM5 & MI5 & ST5).
      subst ms'. rewrite SPv in MU5, ST5.
      transport_after_call rsegs m4 m5 MU5 WM5.
      clear MU5 WM5 MI4.
      fix_ret.
      destruct (reply_matches (img_str SHAPE_LIT) xr) eqn:RM1.
      * zstep. if_cases HB7; [|exfalso; vm_compute in HB7; discriminate HB7].
        do 5 zstep. release_frame FR ST5 (bv_unsigned sp). zstep. finish; intros; reflexivity.
      * exfalso. destruct ROKp as [E1|E1]; congruence.
    + assert (NN : n <> 0) by (zify_cond HB6; try rewrite Z.mod_small in HB6 by lia; lia).
      unfold shape_addr in ROKp. rewrite (proj2 (Z.eqb_neq n 0) NN) in ROKp. cbv beta iota in ROKp.
      destruct (HW0 NN) as (H1 & H2 & H3 & H4 & H5 & H6). clear HW0.
      unfold outside_stack, disjoint_from in H2, H6.
      pose proof (bytes_tr8 _ _ _ _ _ _ H1 H2 MU) as HWP.
      pose proof (bytes_tr_str _ _ _ _ _ _ _ H3 H6 MU) as HP0. clear H1 H3.
      pose proof (bytes_ro8 _ _ _ HWP) as RWP.
      pose proof (bytes_at_bound _ _ _ _ HP0) as BP0. rewrite length_app in BP0. cbn [length] in BP0.
      destruct (HWNZ NN) as [WWNZ WWAL]. clear HWNZ.
      zstep. zstep. if_cases HWZ; [exfalso; zify_cond HWZ; lia|].
      zstep. zb_masks. rewrite WWAL.
      zstep. if_cases HWA; [exfalso; zify_cond HWA; lia|].
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply SLC with (str := w0) (slack := sl0).
        - exact HP0.
        - exact H4.
        - exact H5.
        - exact MI4. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & E & MU5 & WM5 & MI5 & HP0').
      subst ms'. clear HP0'.
      transport_after_call rsegs m4 m5 MU5 WM5.
      clear MU5 WM5 MI4.
      fix_ret.
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply RSO with (lo := lo) (v := w0).
        - exact MI5.
        - rewrite SPv. exact ST4.
        - rewrite SPv. unfold REC_SHAPE_OF_FRAME. lia.
        - exact HSH.
        - rewrite SPv. unfold REC_SHAPE_OF_FRAME, G_SHAPES. left. lia.
        - rewrite (unsigned_lit (Z.of_nat (length w0))) by lia. reflexivity.
        - intros _. split; [exact (str_prefix _ _ _ _ HP0)|].
          rewrite SPv. rewrite (unsigned_lit (Z.of_nat (length w0))) by lia. unfold REC_SHAPE_OF_FRAME. lia. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & E & MU6 & WM6 & MI6 & ST6).
      subst ms'. rewrite SPv in MU6, ST6. unfold REC_SHAPE_OF_FRAME in MU6.
      transport_after_call rsegs m5 m6 MU6 WM6.
      clear MU6 WM6 MI5.
      fix_ret.
      zstep.
      zstep. zstep.
      destruct (shape_cstr m6 (shape_find shape_rows w0) MI6 (shape_find_in shape_rows w0)) as (HSA & LSA & A0 & AE).
      eapply evt_cut.
      { eapply SRM with (lo := lo) (shape := img_str (shape_find shape_rows w0)) (reply := xr) (slack := slack) (can := can).
        - exact MI6.
        - rewrite SPv. exact ST6.
        - rewrite SPv. unfold SYNTAX_REPLY_MATCHES_K. lia.
        - unfold CommandModel.IMG_END. lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. exact HSA.
        - unfold outside_stack, disjoint_from. rewrite SPv. rewrite unsigned_lit by lia. lia.
        - exact RNZ.
        - exact HXR.
        - exact HXN.
        - exact HXP.
        - unfold outside_stack, disjoint_from. rewrite SPv. lia.
        - exact (rw8_bytes _ _ _ GG).
        - exact (rw8_bytes _ _ _ GU).
        - lia. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & E & MU7 & WM7 & MI7 & ST7).
      subst ms'. rewrite SPv in MU7, ST7.
      transport_after_call rsegs m6 m7 MU7 WM7.
      clear MU7 WM7 MI6 HSA.
      fix_ret.
      destruct (reply_matches (img_str (shape_find shape_rows w0)) xr) eqn:RM1.
      * zstep. if_cases HB7; [|exfalso; vm_compute in HB7; discriminate HB7].
        do 5 zstep. release_frame FR ST7 (bv_unsigned sp). zstep. finish; intros; reflexivity.
      * zstep. if_cases HB7; [exfalso; vm_compute in HB7; discriminate HB7|].
        zstep. zstep. zstep. zstep.
        destruct (shape_cstr m7 SHAPE_LIT MI7 (or_introl eq_refl)) as (HSB & LSB & B0 & BE).
        eapply evt_cut.
        { eapply SRM with (lo := lo) (shape := img_str SHAPE_LIT) (reply := xr) (slack := slack) (can := can).
          - exact MI7.
          - rewrite SPv. exact ST7.
          - rewrite SPv. unfold SYNTAX_REPLY_MATCHES_K. lia.
          - unfold CommandModel.IMG_END. lia.
          - rewrite unsigned_lit by (unfold SHAPE_LIT; lia). unfold SHAPE_LIT. lia.
          - rewrite unsigned_lit by (unfold SHAPE_LIT; lia). exact HSB.
          - unfold outside_stack, disjoint_from. rewrite SPv. rewrite unsigned_lit by (unfold SHAPE_LIT; lia).
            unfold SHAPE_LIT in *. lia.
          - exact RNZ.
          - exact HXR.
          - exact HXN.
          - exact HXP.
          - unfold outside_stack, disjoint_from. rewrite SPv. lia.
          - exact (rw8_bytes _ _ _ GG).
          - exact (rw8_bytes _ _ _ GU).
          - lia. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & E & MU8 & WM8 & MI8 & ST8).
        subst ms'. rewrite SPv in MU8, ST8.
        transport_after_call rsegs m7 m8 MU8 WM8.
        clear MU8 WM8 MI7.
        fix_ret.
        destruct (reply_matches (img_str SHAPE_LIT) xr) eqn:RM2.
        -- zstep. if_cases HB8; [exfalso; vm_compute in HB8; discriminate HB8|].
           do 5 zstep. release_frame FR ST8 (bv_unsigned sp). zstep. finish; intros; reflexivity.
        -- exfalso. destruct ROKp as [E1|E1]; congruence.
Qed.
