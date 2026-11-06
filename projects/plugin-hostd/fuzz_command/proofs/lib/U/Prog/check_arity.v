From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandTac check_reply_c strcmp_c strcspn_c strncmp_c bcmp_c check_arity_c check_arity_lib
  check_arity_syn check_arity_fmt.
Import ListNotations.
Open Scope Z_scope.

Definition row_bytes (r : Z * Z * Z) : list byte :=
  match r with (na, sy, fm) => le8 (Z_to_bv 64 na) ++ le8 (Z_to_bv 64 sy) ++ le4 (Z_to_bv 64 fm) ++ [NUL; NUL; NUL; NUL] end.

Definition lit_ok (A : Z) : bool :=
  ro_bytes_b rsegs A (img_str A ++ [NUL]) && (Z.of_nat (length (img_str A)) <? 128) &&
  forallb (fun z => negb (z =? 0)) (map bv_unsigned (img_str A)) && (0 <? A) && (A + 129 <=? 348056).

Definition rowchk (r : Z * Z * Z) : bool :=
  match r with (na, sy, fm) =>
    lit_ok na && lit_ok sy && ((fm =? 0) || (fm =? 1)) &&
    (0 <=? fst (row_arity (img_str sy) fm)) && (snd (row_arity (img_str sy) fm) <=? UNB)
  end.

Lemma rows_ok : forallb rowchk parsed_rows = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lit_facts : forall m A, mem_inv rsegs m -> lit_ok A = true ->
  cstr_at m A (img_str A) /\ Z.of_nat (length (img_str A)) < 128 /\ 0 < A /\ A + 129 <= 348056.
Proof.
  intros m A HI H. unfold lit_ok in H. repeat rewrite andb_true_iff in H. destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.ltb_lt in H2. apply Z.ltb_lt in H4. apply Z.leb_le in H5.
  split; [split|].
  - apply lit_at; [exact HI | exact H1 | lia | rewrite length_app; cbn [length]; lia].
  - apply notin_nul_lit. exact H3.
  - lia.
Qed.

Lemma read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_read rsegs m a bs 0 (length bs) H ltac:(lia) ltac:(cbn [Z.to_nat]; lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma row_reads : forall m B na sy fm, bytes_at rsegs m B (row_bytes (na, sy, fm)) ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (Z_to_bv 64 na)) /\
  ov_read_bytes rsegs m (wa (B + 8)) 8 = Some (le8 (Z_to_bv 64 sy)) /\
  ov_read_bytes rsegs m (wa (B + 16)) 4 = Some (le4 (Z_to_bv 64 fm)).
Proof.
  intros m B na sy fm H. unfold row_bytes in H.
  apply bytes_at_app in H as [H1 H]. apply bytes_at_app in H as [H2 H]. apply bytes_at_app in H as [H3 _].
  pose proof (read_all _ _ _ H1) as R1. pose proof (read_all _ _ _ H2) as R2. pose proof (read_all _ _ _ H3) as R3.
  rewrite length_le8 in R1. rewrite !length_le8 in R2. rewrite !length_le8, length_le4 in R3.
  change (Z.of_nat 8) with 8 in R2, R3. replace (B + 8 + 8) with (B + 16) in R3 by lia.
  split; [exact R1 | split; [exact R2 | exact R3]].
Qed.

Definition acond (t : Z) (o : option (Z * Z)) : Prop :=
  match o with None => True | Some (mn, mx) => mn <= Z.min t 64 - 1 <= mx end.

Lemma arity_cont : forall t v q nc fn0, arity_ok t v q nc fn0 -> t <> 0 -> ~ (q = 0 /\ nc = 0) ->
  ~ (0 < nc /\ fn0 = REC_BROADCAST /\ passed_on_m v = true) -> acond t (row_find v parsed_rows).
Proof. intros t v q nc fn0 [H|[H|[H|H]]] H1 H2 H3; [contradiction | contradiction | contradiction | exact H]. Qed.

Lemma cspn_len_le : forall set s, (cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn [cspn_len length]; [lia|]. destruct (existsb _ _); lia. Qed.

Lemma vp_len : forall v f, cspn_len (str [32; 9]) v <> length f -> verb_prefix v f = false.
Proof. intros v f H. unfold verb_prefix. rewrite (proj2 (Nat.eqb_neq _ _) H). reflexivity. Qed.

Lemma vp_pre : forall v f, prefixb v f = false -> verb_prefix v f = false.
Proof. intros v f H. unfold verb_prefix. rewrite H, andb_false_r. reflexivity. Qed.

Lemma passed_on_false : forall v, bytes_eqb v (img_str 0x1067c) = false -> bytes_eqb v (img_str 0x104e2) = false ->
  verb_prefix v (str [99; 111; 110; 110; 101; 99; 116]) = false ->
  verb_prefix v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) = false -> passed_on_m v = false.
Proof. intros v H1 H2 H3 H4. unfold passed_on_m. rewrite H1, H2, H3, H4. reflexivity. Qed.

Lemma ca_sx32_zero : forall q, 0 <= q < 2^32 -> (bv_unsigned (sx32 (Z_to_bv 64 q)) = 0 <-> q = 0).
Proof.
  intros q Hq. unfold sx32. rewrite (unsigned_lit q) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  split; intros H.
  - Z.div_mod_to_equations. lia.
  - subst q. reflexivity.
Qed.

Lemma ca_walk_prefix : forall k s rest, ~ In NUL s -> ~ In NUL k -> k <> [] ->
  exists v, strncmp_walk (s ++ [NUL]) (k ++ rest) (length k - 1) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
  induction k as [|c k IH]; intros s rest Hs Hk Hne; [congruence|].
  destruct (notin_nul_cons c k Hk) as [Hc Hk'].
  destruct s as [|a s'].
  - cbn [app strncmp_walk]. unfold NUL. rewrite Z_to_bv_unsigned. cbn [bv_wrap].
    eexists. split; [reflexivity|]. split; [intros E; exfalso; change (bv_wrap 8 0) with 0 in E; lia | intros E; discriminate].
  - destruct (notin_nul_cons a s' Hs) as [Ha Hs'].
    cbn [app length].
    destruct k as [|c2 k2].
    + cbn [app strncmp_walk Nat.sub Nat.eqb]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
      cbn [orb]. replace (0 - 0)%nat with 0%nat by reflexivity.
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
      * eexists. split; [reflexivity|]. split; [intros _; cbn; f_equal; apply bv_eq; exact E | intros _; lia].
      * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E; subst; lia].
    + replace (S (length (c2 :: k2)) - 1)%nat with (S (length (c2 :: k2) - 1)) by (cbn; lia).
      cbn [strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
      cbn [orb Nat.eqb].
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
      * destruct (IH s' rest Hs' Hk' ltac:(discriminate)) as (v & Hw & Hv).
        exists v. split; [exact Hw|]. rewrite Hv. cbn [firstn length].
        replace a with c by (apply bv_eq; symmetry; exact E).
        split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
      * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E1 _; subst; lia].
Qed.

Lemma ca_strncmp_prefix : forall s k rest, ~ In NUL s -> ~ In NUL k -> k <> [] ->
  exists v, strncmp_model (s ++ [NUL]) (k ++ rest) (Z.of_nat (length k)) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
  intros s k rest Hs Hk Hne. unfold strncmp_model.
  destruct k as [|c k']; [congruence|].
  replace (Z.of_nat (length (c :: k')) =? 0) with false by (cbn [length]; symmetry; apply Z.eqb_neq; lia).
  replace (Z.to_nat (Z.of_nat (length (c :: k')) - 1)) with (length (c :: k') - 1)%nat by lia.
  apply ca_walk_prefix; assumption.
Qed.

Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z).
  Hypothesis LO : lo + 240 <= bv_unsigned sp.
  Hypothesis IE : 348056 <= lo.

  Definition fsaved : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation POST := (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Lemma ret_ok : forall j m' xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        xt3 xt4 xt5 xt6,
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -144) (CB 40 j :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -144) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    evt rsegs POST (SGU sp gp tp F fc 0x14b64 xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
                      xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m').
  Proof.
    intros j m' xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 MI FR ST MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
    unfold fsaved in FR.
    do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
  Qed.

  Variables (t : Z) (p0 : word) (v : list byte) (j0 : list byte).
  Hypothesis HT : 1 <= t <= 4096.
  Hypothesis SC : strcmp_contract.
  Hypothesis SYN : syn_path_spec.
  Hypothesis FMT : fmt_path_spec.

  Lemma tail_ok : forall j m' rmn rmx xra xs0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7
                         xt3 xt4 xt5 xt6,
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -144) (CB 40 j :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -144) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    0 <= rmn <= Z.min t 64 - 1 -> Z.min t 64 - 1 <= rmx <= UNB ->
    evt rsegs POST (SGU sp gp tp F fc 0x14b54 xra xs0 (Z_to_bv 64 rmx) (Z_to_bv 64 (Z.min t 64)) xs3 xs4 xs5 xs6 xs7 xs8
                      xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 rmn) xa7 xt3 xt4 xt5 xt6 m').
  Proof.
    intros j m' rmn rmx xra xs0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7
      xt3 xt4 xt5 xt6 MI FR ST MU WM R1 R2.
    unfold UNB in R2.
    zstep. try rewrite (unsigned_lit (Z.min t 64)) by lia. rewrite ?ca_swrap32_id by lia.
    zstep. if_cases B0; [exfalso; zify_cond B0; rewrite ?ca_signed_small in B0 by lia; lia|].
    zstep. if_cases B1; [exfalso; zify_cond B1; rewrite ?ca_signed_small in B1 by lia; lia|].
    zstep. if_cases B2; [exfalso; zify_cond B2; rewrite ?ca_signed_small in B2 by lia; lia|].
    eapply ret_ok; eassumption.
  Qed.

  Lemma rows_loop : forall rows i m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (i + length rows = 22)%nat -> rows <> [] -> forallb rowchk rows = true ->
    bytes_at rsegs m' (140992 + 24 * Z.of_nat i) (concat (map row_bytes rows)) ->
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -144) (CB 40 j0 :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -144) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    bytes_at rsegs m' (bv_unsigned p0) (v ++ [NUL]) -> ~ In NUL v ->
    acond t (row_find v rows) ->
    evt rsegs POST (SGU sp gp tp F fc 0x14744 xra p0 (Z_to_bv 64 (141000 + 24 * Z.of_nat i)) (Z_to_bv 64 (Z.min t 64))
                      (Z_to_bv 64 (Z.of_nat (length rows))) s4 s5 s6 s7 s8 s9 s10 s11 xt0 xt1 xt2
                      xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m').
  Proof.
    pose proof SC as SC'. unfold strcmp_contract in SC'.
    pose proof SYN as SYN'. unfold syn_path_spec, path_spec in SYN'.
    pose proof FMT as FMT'. unfold fmt_path_spec, path_spec in FMT'.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    induction rows as [|[[na sy] fm] rows IH];
      intros i m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hi Hne Hok HG MI FR ST MU WM HV HVn AC;
      [congruence|].
    cbn [forallb] in Hok. apply andb_prop in Hok as [Hrow Hok].
    unfold rowchk in Hrow. repeat rewrite andb_true_iff in Hrow.
    destruct Hrow as [[[[Hna Hsy] Hfm] Hmn] Hmx].
    apply Z.leb_le in Hmn. apply Z.leb_le in Hmx.
    cbn [map concat] in HG. apply bytes_at_app in HG as [HR0 HG'].
    replace (Z.of_nat (length (row_bytes (na, sy, fm)))) with 24 in HG'
      by (unfold row_bytes; rewrite !length_app, !length_le8, length_le4; reflexivity).
    destruct (row_reads m' _ na sy fm HR0) as (RNA & RSY & RFM). clear HR0.
    destruct (lit_facts m' na MI Hna) as ([HNA HNAn] & LNA & NA0 & NAE).
    destruct (lit_facts m' sy MI Hsy) as ([HSY HSYn] & LSY & SY0 & SYE).
    assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
    change (length ((na, sy, fm) :: rows)) with (S (length rows)) in *.
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SC' with (sx := v) (sy := img_str na).
      - exact HV.
      - exact HVn.
      - rewrite unsigned_lit by lia. exact HNA.
      - exact HNAn. }
    intros ms' (r0 & x11 & x12 & x13 & E & Hr). subst ms'.
    fix_ret.
    revert AC. cbn [row_find]. destruct (bytes_eqb (img_str na) v) eqn:EQ; intros AC.
    - apply bytes_eqb_iff in EQ.
      assert (R0 : r0 = Z_to_bv 64 0) by (apply Hr; symmetry; exact EQ). subst r0.
      zstep. if_cases B1; [|exfalso; vm_compute in B1; discriminate B1].
      apply orb_true_iff in Hfm as [Hfm|Hfm]; apply Z.eqb_eq in Hfm; subst fm;
        destruct (row_arity (img_str sy) _) as [rmn rmx] eqn:RA; cbn [fst snd] in Hmn, Hmx; cbn [acond] in AC.
      + zstep. zstep. zstep. if_cases B2; [|exfalso; vm_compute in B2; discriminate B2].
        eapply evt_cut.
        { eapply SYN' with (A := sy) (SS := img_str sy) (m0 := m) (lo := lo) (saved := fsaved) (rmn := rmn) (rmx := rmx);
            [exact HSYn | lia | lia | lia | lia | lia | | exact RA].
          unfold uinv. exact (conj MI (conj (ex_intro _ j0 FR) (conj ST (conj MU (conj WM HSY))))). }
        intros ms' (m2 & xra' & xs0' & xs3' & xs4' & xs5' & xs6' & xs7' & xs8' & xs9' & xs10' & xs11' & xt0' & xt1' & xt2' &
                    xa0' & xa1' & xa2' & xa3' & xa4' & xa5' & xa7' & xt3' & xt4' & xt5' & xt6' & INV2 & ->).
        destruct INV2 as (MI2 & [j2 FR2] & ST2 & MU2 & WM2 & _).
        eapply tail_ok; [exact MI2 | exact FR2 | exact ST2 | exact MU2 | exact WM2 | lia | lia].
      + zstep. zstep. zstep. if_cases B2; [exfalso; vm_compute in B2; discriminate B2|].
        eapply evt_cut.
        { eapply FMT' with (A := sy) (SS := img_str sy) (m0 := m) (lo := lo) (saved := fsaved) (rmn := rmn) (rmx := rmx);
            [exact HSYn | lia | lia | lia | lia | lia | | exact RA].
          unfold uinv. exact (conj MI (conj (ex_intro _ j0 FR) (conj ST (conj MU (conj WM HSY))))). }
        intros ms' (m2 & xra' & xs0' & xs3' & xs4' & xs5' & xs6' & xs7' & xs8' & xs9' & xs10' & xs11' & xt0' & xt1' & xt2' &
                    xa0' & xa1' & xa2' & xa3' & xa4' & xa5' & xa7' & xt3' & xt4' & xt5' & xt6' & INV2 & ->).
        destruct INV2 as (MI2 & [j2 FR2] & ST2 & MU2 & WM2 & _).
        eapply tail_ok; [exact MI2 | exact FR2 | exact ST2 | exact MU2 | exact WM2 | lia | lia].
    - assert (RN : bv_unsigned r0 <> 0).
      { intros H. apply bv0_iff, Hr in H. rewrite H in EQ.
        rewrite (proj2 (bytes_eqb_iff _ _) eq_refl) in EQ. discriminate EQ. }
      zstep. if_cases B1; [exfalso; zify_cond B1; lia|].
      zstep. zstep. zstep. if_cases B3.
      + eapply ret_ok; eassumption.
      + zify_cond B3. zstep.
        destruct rows as [|r' rows']; [exfalso; cbn [length] in B3; Z.div_mod_to_equations; lia|].
        match goal with |- context [Z_to_bv 64 (141000 + 24 * Z.of_nat i + ?c)] =>
          replace (141000 + 24 * Z.of_nat i + c) with (141000 + 24 * Z.of_nat (S i)) by lia end.
        match goal with |- context [Z_to_bv 64 (Z.of_nat (S (length (r' :: rows'))) + ?c)] =>
          replace (Z.of_nat (S (length (r' :: rows'))) + c) with (Z.of_nat (length (r' :: rows'))) by lia end.
        replace (140992 + 24 * Z.of_nat i + 24) with (140992 + 24 * Z.of_nat (S i)) in HG' by lia.
        eapply (IH (S i)); [lia | discriminate | exact Hok | exact HG' | exact MI | exact FR | exact ST | exact MU |
                            exact WM | exact HV | exact HVn | exact AC].
  Qed.

  Variables (W ww : word).

  Lemma cont_ok : forall m' xra xs1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -144) (CB 40 j0 :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -144) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    bytes_at rsegs m' 140992 g_parsed_bytes ->
    ro_cells rsegs m' (bv_unsigned W + 16) [C8 ww] -> bv_unsigned ww <> 0 -> bv_unsigned ww mod 8 = 0 ->
    ro_cells rsegs m' (bv_unsigned ww) [C8 p0] ->
    bytes_at rsegs m' (bv_unsigned p0) (v ++ [NUL]) -> ~ In NUL v ->
    acond t (row_find v parsed_rows) ->
    evt rsegs POST (SGU sp gp tp F fc 0x14718 xra W xs1 (Z_to_bv 64 t) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt0 xt1 xt2
                      xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m').
  Proof.
    intros m' xra xs1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 MI FR ST MU WM GP HWW WN WA HW1 HV HVn AC.
    assert (TL : forall xa0', evt rsegs POST
      (SGU sp gp tp F fc 0x14724 xra W xs1 (Z_to_bv 64 (Z.min t 64)) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt0 xt1 xt2
           xa0' xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m')).
    { intros xa0'.
      zstep. zstep. if_cases B2; [exfalso; zify_cond B2; lia|].
      zstep. zb_masks. rewrite WA.
      zstep. if_cases B3; [exfalso; zify_cond B3; lia|].
      zstep. zstep. zstep. zstep.
      change (Z_to_bv 64 141000) with (Z_to_bv 64 (141000 + 24 * Z.of_nat 0)).
      change (Z_to_bv 64 22) with (Z_to_bv 64 (Z.of_nat (length parsed_rows))).
      eapply (rows_loop parsed_rows 0); [reflexivity | discriminate | exact rows_ok | exact GP | exact MI | exact FR |
                                         exact ST | exact MU | exact WM | exact HV | exact HVn | exact AC]. }
    zstep. zstep. if_cases B1.
    - zify_cond B1. rewrite ?ca_signed_small in B1 by lia.
      replace (Z_to_bv 64 t) with (Z_to_bv 64 (Z.min t 64)) by (f_equal; lia).
      apply TL.
    - zify_cond B1. rewrite ?ca_signed_small in B1 by lia.
      zstep.
      replace (Z_to_bv 64 64) with (Z_to_bv 64 (Z.min t 64)) by (f_equal; lia).
      apply TL.
  Qed.
End Main.

Theorem check_arity_main : syn_path_spec -> fmt_path_spec -> strcmp_contract -> strcspn_contract -> strncmp_contract ->
  check_arity_contract.
Proof.
  intros SYN FMT SC SCS SNC.
  pose proof SC as SC'. unfold strcmp_contract in SC'. unfold strcspn_contract in SCS. unfold strncmp_contract in SNC.
  unfold check_arity_contract, CHECK_ARITY, CHECK_ARITY_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros t q nc fn0 ww p0 v can MI ST LO IE GG GU GPB GGR HNC HNCB HFN GGQ HQ HQB HT HA0 HTB HTD HWW HWWD HWS HWN AOK.
  unfold outside_stack, disjoint_from, WORDS_N, WORDS_W, GOT_GREC, G_REC, GOT_GQUIT, G_QUIT, REC_NCALLS,
    REC_CALLS, CALL_FN, IMG_END, G_PARSED, GOT_GUARD, GUARD in *.
  change (213032 + 8) with 213040 in HNCB. change (213032 + 16 + 0) with 213048 in HFN.
  apply bytes_ro4 in HTB. apply bytes_ro8 in HWW. apply bytes_ro8 in GGR. apply bytes_ro8 in GGQ.
  apply bytes_ro4 in HNCB. apply bytes_ro4 in HQB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. change (bv_modulus 64) with (2^64) in Ra0.
  assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  assert (LGP : Z.of_nat (length g_parsed_bytes) = 528) by (vm_compute; reflexivity).
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 144%nat ST.
  do 14 zstep.
  match type of FR with rw_cells _ _ _ (CB 40 ?j :: _) => set (j0 := j) in FR; clearbody j0 end.
  match type of MI with mem_inv _ ?mm => rename mm into m0 end.
  assert (HFN' : 0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m0 213048 (le4 (Z_to_bv 64 fn0))).
  { intros N. destruct (HFN N) as [F1 F2]. split; [exact F1|].
    eapply bytes_at_transport; [exact F2 | exact MU | cbn [disjoint_from]; simpl_sizes; slia]. }
  clear HFN.
  zstep. zstep. zb_masks. rewrite HA0.
  zstep. if_cases HAL; [exfalso; zify_cond HAL; lia|].
  zstep. rewrite ca_sx32_small by lia.
  zstep. if_cases B0.
  { zify_cond B0. eapply ret_ok; eassumption. }
  zify_cond B0. assert (HT1 : 1 <= t <= 4096) by lia.
  destruct (HWS ltac:(lia)) as (HW1 & HW2 & [HW3 HW4] & HW5). clear HWS.
  destruct (HWN ltac:(lia)) as [WN WA]. clear HWN.
  unfold outside_stack, disjoint_from in HW2, HW5.
  apply (bytes_at_transport rsegs [(lo, bv_unsigned sp)] m m0) in HW1; [| exact MU | cbn [disjoint_from]; simpl_sizes; slia].
  apply (bytes_at_transport rsegs [(lo, bv_unsigned sp)] m m0) in HW3; [| exact MU | cbn [disjoint_from]; simpl_sizes; slia].
  apply bytes_ro8 in HW1.
  pose proof (bytes_at_bound _ _ _ _ HW3) as BV. rewrite length_app in BV. cbn [length] in BV.
  do 6 zstep.
  rewrite (ca_sx32_small nc) by lia.
  match goal with |- evt ?segs ?Q (MS ?R ?F0 _ ?fc0 ?rv ?mm ?ro) =>
    assert (K : 0 < nc -> evt segs Q (MS R F0 (Z_to_bv 64 0x14688) fc0 rv mm ro)) end.
  { intros NC.
    destruct (HFN' NC) as [HFR HFB]. apply bytes_ro4 in HFB.
    zstep. rewrite (ca_sx32_small fn0) by lia.
    zstep. zstep. if_cases B3.
    - zify_cond B3.
      assert (AC : acond t (row_find v parsed_rows)).
      { apply (arity_cont t v q nc fn0 AOK); [lia | lia | unfold REC_BROADCAST; intros (_ & N & _); lia]. }
      eapply cont_ok; eassumption.
    - zify_cond B3.
      zstep. zstep. if_cases B4; [exfalso; zify_cond B4; lia|].
      zstep. zb_masks. rewrite WA.
      zstep. if_cases B5; [exfalso; zify_cond B5; lia|].
      zstep.
      pose proof (lit_facts m0 0x1067c MI ltac:(vm_compute; reflexivity)) as ([HL1 HL1n] & _ & _ & _).
      pose proof (lit_facts m0 0x104e2 MI ltac:(vm_compute; reflexivity)) as ([HL2 HL2n] & _ & _ & _).
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply SC' with (sx := v) (sy := img_str 0x1067c).
        - exact HW3.
        - exact HW4.
        - rewrite unsigned_lit by lia. exact HL1.
        - exact HL1n. }
      intros ms' (r1 & x11 & x12 & x13 & E & Hr1). subst ms'. fix_ret.
      zstep. if_cases Br4.
      { eapply ret_ok; eassumption. }
      zify_cond Br4.
      assert (EQ1 : bytes_eqb v (img_str 0x1067c) = false).
      { destruct (bytes_eqb v (img_str 0x1067c)) eqn:E1; [|reflexivity].
        exfalso. apply Br4, bv0_iff, Hr1, bytes_eqb_iff, E1. }
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply SC' with (sx := v) (sy := img_str 0x104e2).
        - exact HW3.
        - exact HW4.
        - rewrite unsigned_lit by lia. exact HL2.
        - exact HL2n. }
      intros ms' (r2 & y11 & y12 & y13 & E & Hr2). subst ms'. fix_ret.
      zstep. if_cases Br5.
      { eapply ret_ok; eassumption. }
      zify_cond Br5.
      assert (EQ2 : bytes_eqb v (img_str 0x104e2) = false).
      { destruct (bytes_eqb v (img_str 0x104e2)) eqn:E2; [|reflexivity].
        exfalso. apply Br5, bv0_iff, Hr2, bytes_eqb_iff, E2. }
      pose proof (lit_at m0 67148 (str [32; 9] ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HSP.
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply SCS with (str := v) (slack := []) (set := str [32; 9]) (lo := lo) (can := can).
        - exact HW3.
        - exact HW4.
        - intros Hl. cbn in Hl. lia.
        - rewrite unsigned_lit by lia. exact HSP.
        - apply notin_nul_lit. vm_compute. reflexivity.
        - exact GG.
        - exact GU.
        - rewrite unsigned_lit by lia. exact ST.
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
        - rewrite unsigned_lit by lia. left. cbn. lia.
        - unfold CSPN_SSP_GOT. left. lia.
        - unfold CSPN_SSP_GUARD. left. lia.
        - exact MI. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & E & MU2 & WM2 & MI2 & ST2).
      subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. clear HSP.
      transport_after_call rsegs m0 m2 MU2 WM2.
      clear MU2 WM2 MI.
      fix_ret.
      pose proof (cspn_len_le (str [32; 9]) v) as CL.
      assert (AC2 : prefixb v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) = false \/
                    cspn_len (str [32; 9]) v <> 10%nat -> prefixb v (str [99; 111; 110; 110; 101; 99; 116]) = false \/
                    cspn_len (str [32; 9]) v <> 7%nat -> acond t (row_find v parsed_rows)).
      { intros P10 P7. apply (arity_cont t v q nc fn0 AOK); [lia | lia |].
        intros (_ & _ & PO). rewrite passed_on_false in PO; [discriminate PO | exact EQ1 | exact EQ2 | |].
        - destruct P7 as [P7|P7]; [apply vp_pre; exact P7 | apply vp_len; unfold str; cbn [map length]; exact P7].
        - destruct P10 as [P10|P10]; [apply vp_pre; exact P10 | apply vp_len; unfold str; cbn [map length]; exact P10]. }
      zstep. zstep. if_cases Br6.
      + zify_cond Br6. try rewrite Z.mod_small in Br6 by lia.
        zstep. zstep. zstep. zstep. zstep.
        pose proof (lit_at m2 66953 (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL])
                      MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HK.
        destruct (ca_strncmp_prefix v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) (str [32; 37; 115; 32; 37; 115] ++ [NUL])
                    HW4 ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(discriminate)) as (vv & Hv & Hv0).
        eapply evt_cut.
        { eapply SNC with (ls := v ++ [NUL])
            (rs := str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL]) (v := vv).
          - exact HW3.
          - rewrite unsigned_lit by lia. exact HK.
          - replace (bv_unsigned (Z_to_bv 64 10)) with (Z.of_nat (length (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116])))
              by reflexivity. exact Hv.
          - exact MI2. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & E & MU3 & WM3 & MI3 & HB1 & HB2).
        subst ms'. clear HB1 HB2 HK.
        transport_after_call rsegs m2 m3 MU3 WM3.
        clear MU3 WM3 MI2.
        fix_ret.
        pose proof (strncmp_model_range _ _ _ _ Hv) as VR.
        zstep. if_cases Br7.
        { eapply ret_ok; eassumption. }
        zify_cond Br7.
        assert (VN : vv <> 0) by (intros ->; apply Br7; reflexivity).
        assert (PF : prefixb v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) = false).
        { destruct (prefixb v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116])) eqn:P; [|reflexivity].
          exfalso. apply VN, Hv0, prefixb_iff, P. }
        assert (AC : acond t (row_find v parsed_rows)) by (apply AC2; [left; exact PF | right; lia]).
        eapply cont_ok; eassumption.
      + zify_cond Br6. try rewrite Z.mod_small in Br6 by lia.
        zstep. zstep. if_cases Br8.
        * zify_cond Br8. try rewrite Z.mod_small in Br8 by lia.
          assert (AC : acond t (row_find v parsed_rows)) by (apply AC2; [right; lia | right; lia]).
          eapply cont_ok; eassumption.
        * zify_cond Br8. try rewrite Z.mod_small in Br8 by lia.
          zstep. zstep. zstep. zstep. zstep. zstep.
          pose proof (lit_at m2 67069 (str [99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL])
                        MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HK.
          destruct (ca_strncmp_prefix v (str [99; 111; 110; 110; 101; 99; 116]) (str [32; 37; 115; 32; 37; 115] ++ [NUL])
                      HW4 ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(discriminate)) as (vv & Hv & Hv0).
          eapply evt_cut.
          { eapply SNC with (ls := v ++ [NUL])
              (rs := str [99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL]) (v := vv).
            - exact HW3.
            - rewrite unsigned_lit by lia. exact HK.
            - replace (bv_unsigned (Z_to_bv 64 7)) with (Z.of_nat (length (str [99; 111; 110; 110; 101; 99; 116])))
                by reflexivity. exact Hv.
            - exact MI2. }
          intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & E & MU3 & WM3 & MI3 & HB1 & HB2).
          subst ms'. clear HB1 HB2 HK.
          transport_after_call rsegs m2 m3 MU3 WM3.
          clear MU3 WM3 MI2.
          fix_ret.
          pose proof (strncmp_model_range _ _ _ _ Hv) as VR.
          zstep. if_cases Br7.
          { eapply ret_ok; eassumption. }
          zify_cond Br7.
          assert (VN : vv <> 0) by (intros ->; apply Br7; reflexivity).
          assert (PF : prefixb v (str [99; 111; 110; 110; 101; 99; 116]) = false).
          { destruct (prefixb v (str [99; 111; 110; 110; 101; 99; 116])) eqn:P; [|reflexivity].
            exfalso. apply VN, Hv0, prefixb_iff, P. }
          assert (AC : acond t (row_find v parsed_rows)) by (apply AC2; [right; lia | left; exact PF]).
          eapply cont_ok; eassumption. }
  zstep. if_cases B1.
  - zify_cond B1. apply ca_sx32_zero in B1; [|lia].
    zstep. if_cases B2.
    + eapply ret_ok; eassumption.
    + zify_cond B2. apply K. lia.
  - zify_cond B1. assert (Q0 : q <> 0) by (intros Q0; apply B1, ca_sx32_zero; [lia | exact Q0]).
    zstep. if_cases B2.
    + zify_cond B2. apply K. lia.
    + zify_cond B2. pos_false_tac. zstep.
      assert (AC : acond t (row_find v parsed_rows)) by (apply (arity_cont t v q nc fn0 AOK); [lia | lia | intros (N & _); lia]).
      eapply cont_ok; eassumption.
Qed.

Theorem check_arity_holds : strcmp_contract -> strcspn_contract -> strncmp_contract -> bcmp_contract -> check_arity_contract.
Proof.
  intros SC SCS SNC BC. exact (check_arity_main (syn_path_holds BC) (fmt_path_holds BC) SC SCS SNC).
Qed.
