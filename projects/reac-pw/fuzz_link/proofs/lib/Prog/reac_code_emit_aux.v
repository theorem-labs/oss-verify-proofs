(* reac-pw/fuzz_link, PLAIN build: the memory and printf facts the walk of reac_code_emit
   (lib/Prog/reac_code_emit.v) uses.
   - link's memory FILE (lib/Prog/memfile_c.v `memfile_k`, `mf_dyn`, `mf_pend_bytes`) and the stack
     protector's words kept across a write set (lib/Lib/Frame.v `munch`) that misses them; the seven
     words `mf_dyn` names and the k pending bytes read out of `memfile_k`; k is one number;
   - `task_mem` kept across stores into writable bytes;
   - the caller's format and its arguments (reac_code_emit_c.v `emit_fmt`) kept across a write set
     that misses them, and one text for one format: a format `pf_parse` reads is one byte list, and the
     arguments `pf_args_ok` names are one list (the contract's Post quantifies over them);
   - a constant string of the image as a `%s` argument (lib/Prog/link_msgs_fit.v `str_ok`);
   - the four va_list slots out of reac_code_emit's frame cells. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf mk_str mk_marks memfile_c printf_facts_c vfprintf_c link_msgs_fit reac_code_emit_c mf_walk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YI14 YK1j YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Bytes and fields kept across a write set that misses them
   ========================================================================== *)

(* a field of the FILE block, kept *)
Lemma fld_munch : forall W m m' f, munch W m m' -> 0 <= f -> f + MemFile.MF_BLOCK <= 2 ^ 64 ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) ->
  forall o n v, 0 <= o -> o + Z.of_nat n <= MemFile.MF_BLOCK -> mf_fld m f o n v -> mf_fld m' f o n v.
Proof.
  intros W m m' f MU F0 F1 HO o n v Ho Hn H. unfold mf_fld in *.
  apply (val_munch W m m' (f + o) n v H MU); [lia | lia |]. intros z Hz. apply HO. lia.
Qed.

Lemma memfile_k_munch : forall W m m' f k, memfile_k m f k -> munch W m m' -> wmono rsegs m m' ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) -> memfile_k m' f k.
Proof.
  intros W m m' f k (MA & WIN & WB & WS & PL) MU WM HO.
  pose proof MA as (F0 & F1 & _).
  pose proof (fld_munch W m m' f MU ltac:(lia) F1 HO) as HF.
  split; [apply (memfile_at_munch W m m' f MA MU); intros z Hz; apply HO;
          unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *; lia|].
  split; [|split; [exact (wr_at_transport rsegs m m' _ _ WB WM)
               |split; [exact (wr_at_transport rsegs m m' _ _ WS WM) | exact PL]]].
  unfold mf_win in *.
  destruct WIN as [(Hk & A & B & C) | (Hk & A & B & C)]; [left | right];
    (split; [exact Hk|]); (split; [|split]); apply HF; try assumption;
    unfold MemFile.MF_BLOCK; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma mf_dyn_munch : forall W m m' f fl om wend wpos wbase pos len,
  mf_dyn m f fl om wend wpos wbase pos len -> munch W m m' -> 0 <= f -> f + MemFile.MF_BLOCK <= 2 ^ 64 ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) -> mf_dyn m' f fl om wend wpos wbase pos len.
Proof.
  intros W m m' f fl om wend wpos wbase pos len D MU F0 F1 HO.
  pose proof (fld_munch W m m' f MU F0 F1 HO) as HF.
  unfold mf_dyn in *.
  destruct D as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & A1 & A2 & A3 & A4 & A5 & A6 & A7).
  do 7 (split; [assumption|]).
  repeat (split; [apply HF; [unfold MemFile.MF_COOKIE; lia
                            | unfold MemFile.MF_COOKIE, MemFile.MF_BLOCK; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                            | assumption]|]).
  apply HF; [unfold MemFile.MF_COOKIE; lia
            | unfold MemFile.MF_COOKIE, MemFile.MF_BLOCK; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
            | assumption].
Qed.

Lemma mf_pend_munch : forall W m m' f pb, mf_pend_bytes m f pb -> munch W m m' ->
  Z.of_nat (length pb) <= MemFile.MF_BUFSIZ ->
  (forall z, f <= z < f + MemFile.MF_BLOCK -> outside W z) -> mf_pend_bytes m' f pb.
Proof.
  intros W m m' f pb H MU L HO. unfold mf_pend_bytes in *. apply (bytes_munch W m m' _ pb H MU).
  intros z Hz. apply HO. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *. lia.
Qed.

Lemma guard_munch : forall W m m', guard_words m -> munch W m m' ->
  (forall z, GOT_GUARD <= z < GOT_GUARD + 8 -> outside W z) ->
  (forall z, GUARD <= z < GUARD + 8 -> outside W z) -> guard_words m'.
Proof.
  intros W m m' (HG & g & HQ) MU H1 H2. split.
  - apply (bytes_munch W m m' _ _ HG MU). rewrite length_le8. exact H1.
  - exists g. apply (bytes_munch W m m' _ _ HQ MU). rewrite length_le8. exact H2.
Qed.

(* ==========================================================================
   2. task_mem kept across stores into writable bytes
   ========================================================================== *)

Lemma task_mem_munch : forall W m m', task_mem rsegs m -> munch W m m' ->
  (forall x : word, outside W (bv_unsigned x) \/ wview rsegs m x <> None) -> task_mem rsegs m'.
Proof.
  intros W m m' TM MU H x b E. destruct (H x) as [O|V].
  - rewrite (MU x O) in E. exact (TM x b E).
  - unfold wview in V. destruct (m x) as [b'|] eqn:Em; [exact (TM x b' Em)|].
    left. destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:Ef; [congruence|].
    exfalso. apply V. reflexivity.
Qed.

Lemma task_mem_frame : forall m m' l h, task_mem rsegs m -> munch [(l, h)] m m' ->
  (forall a, l <= a < h -> wview rsegs m (wa a) <> None) -> task_mem rsegs m'.
Proof.
  intros m m' l h TM MU H. apply (task_mem_munch [(l, h)] m m' TM MU). intros x.
  destruct (Z.lt_ge_cases (bv_unsigned x) l) as [L|L]; [left; cbn [outside]; split; [lia | exact I]|].
  destruct (Z.lt_ge_cases (bv_unsigned x) h) as [U|U]; [|left; cbn [outside]; split; [lia | exact I]].
  right. pose proof (H (bv_unsigned x) ltac:(lia)) as V. unfold wa in V. rewrite Z_to_bv_bv_unsigned in V.
  exact V.
Qed.

(* ==========================================================================
   3. What `memfile_k` gives: the seven words, the pending bytes, one k
   ========================================================================== *)

Lemma mf_dyn_of_k : forall m f k, memfile_k m f k -> f + MemFile.MF_BLOCK < 2 ^ 64 ->
  exists fl om wend wpos wbase pos len, mf_dyn m f fl om wend wpos wbase pos len.
Proof.
  intros m f k (MA & WIN & _) Hf.
  destruct MA as (F0 & F1 & F2 & _ & FL & OM & _ & (pos & len & PL & LS & CP & CL)).
  change (MemFile.mf_size MemFile.link_mf) with 4096 in LS.
  destruct FL as [FL|FL]; [exists MemFile.F_NORD | exists (MemFile.F_NORD + MemFile.F_ERR)];
  (destruct OM as [OM|OM]; [exists 0 | exists YI14.U32M1]);
  (destruct WIN as [(Hk & A & B & C) | (Hk & A & B & C)];
   [exists 0, 0, 0 | exists (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ), (f + MemFile.MF_BUF + k), (f + MemFile.MF_BUF)]);
  exists pos, len; unfold mf_dyn;
  (split; [unfold MemFile.F_NORD, MemFile.F_ERR; lia|]);
  (split; [unfold YI14.U32M1; lia|]);
  (split; [unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia|]);
  (split; [unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia|]);
  (split; [unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia|]);
  (split; [lia|]); (split; [unfold SAID_SIZE; lia|]);
  repeat (split; [assumption|]); assumption.
Qed.

Lemma find_seg_out : forall x, x < 0x10000 \/ 0x97000 <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity]. exfalso.
  pose proof (YK1j.find_segment_range _ _ _ _ E) as R. pose proof (YK1j.find_segment_in _ _ _ _ E) as I.
  assert (B : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) &&
                                (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x97000)) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B s I). apply andb_prop in B as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Lemma mrd_of_wview_out : forall m x, wview rsegs m x <> None ->
  bv_unsigned x < 0x10000 \/ 0x97000 <= bv_unsigned x -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x V Hx. unfold wview in V. unfold mrd. destruct (m x) as [b|]; [exists b; reflexivity|].
  rewrite (find_seg_out _ Hx) in V. exfalso. apply V. reflexivity.
Qed.

Lemma mf_pend_of_k : forall m f k, memfile_k m f k ->
  exists pb, mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k.
Proof.
  intros m f k MK. pose proof (memfile_k_range m f k MK) as Rk.
  destruct MK as (MA & _ & WB & _ & PL). destruct MA as (F0 & F1 & _).
  assert (Hb : forall i, 0 <= i < k -> exists b, mrd rsegs m (wa (f + MemFile.MF_BUF + i)) = Some b).
  { intros i Hi. destruct WB as (_ & _ & W).
    specialize (W (MemFile.MF_BUF + i) ltac:(unfold MemFile.MF_BUF, MemFile.MF_BLOCK, MemFile.MF_BUFSIZ in *; lia)).
    rewrite Z.add_assoc in W. apply (mrd_of_wview_out m _ W).
    rewrite wa_unsigned by (unfold MemFile.MF_BUF, MemFile.MF_BLOCK, MemFile.MF_BUFSIZ in *; lia).
    unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BUF, MemFile.MF_BLOCK, MemFile.MF_BUFSIZ in *; lia. }
  exists (map (fun i => match mrd rsegs m (wa (f + MemFile.MF_BUF + Z.of_nat i)) with Some b => b | None => zb 0 end)
              (seq 0 (Z.to_nat k))).
  split.
  - unfold mf_pend_bytes. split; [unfold MemFile.MF_BUF; lia|].
    split; [rewrite length_map, length_seq; unfold MemFile.MF_BUF, MemFile.MF_BLOCK, MemFile.MF_BUFSIZ in *; lia|].
    intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map.
    replace (nth_error (seq 0 (Z.to_nat k)) i) with (Some i)
      by (symmetry; rewrite nth_error_seq; destruct (Nat.ltb_spec i (Z.to_nat k)); [reflexivity | lia]).
    cbn [option_map]. destruct (Hb (Z.of_nat i) ltac:(lia)) as [b Eb]. rewrite Eb. reflexivity.
  - rewrite length_map, length_seq. lia.
Qed.

Lemma memfile_k_unique : forall m f k1 k2, memfile_k m f k1 -> memfile_k m f k2 ->
  f + MemFile.MF_BLOCK < 2 ^ 64 -> k1 = k2.
Proof.
  intros m f k1 k2 (MA & W1 & _) (_ & W2 & _) Hf. destruct MA as (F0 & _).
  unfold mf_win, mf_fld in *. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *.
  destruct W1 as [(E1 & A1 & B1 & C1) | (K1 & A1 & B1 & C1)],
           W2 as [(E2 & A2 & B2 & C2) | (K2 & A2 & B2 & C2)].
  - lia.
  - pose proof (val8_inj m _ _ _ A1 A2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (val8_inj m _ _ _ A1 A2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (val8_inj m _ _ _ B1 B2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* ==========================================================================
   4. The caller's format and arguments: kept, and one text
   ========================================================================== *)

Lemma pf_args_ok_munch : forall m m' S lo D n S' lo' rs args, pf_args_ok m S lo D n rs args ->
  munch [(lo, S); (D, D + n)] m m' -> lo <= lo' -> S' <= S -> pf_args_ok m' S' lo' D n rs args.
Proof.
  intros m m' S lo D n S' lo' rs args. revert rs.
  induction args as [|a args IH]; intros rs H MU L1 L2; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2]. split; [|exact (IH rs H2 MU L1 L2)].
  destruct a as [v|u|s]; cbn [pf_arg_ok] in *; [exact H1 | exact H1|].
  destruct H1 as (HF & slack & B & PAD & POS & A1 & A2). split; [exact HF|]. exists slack.
  split; [|split; [exact PAD|split; [exact POS|split; lia]]].
  apply (bytes_munch _ m m' _ _ B MU). intros z Hz. rewrite length_app in Hz. unfold pf_bytes in Hz.
  rewrite length_map, length_app in Hz. cbn [length] in Hz.
  cbn [outside]. split; [lia | split; [lia | exact I]].
Qed.

(* the format and the arguments of `emit_fmt` after a write set inside the callee windows and the FILE block *)
Lemma emit_fmt_munch : forall m m' regs fp fmt ps args T f S' lo',
  emit_fmt m regs fp fmt ps args T -> arg regs 0 = f -> mf_place_ok f ->
  munch [(spZ regs - 6112, spZ regs); (f, f + MemFile.MF_BLOCK)] m m' ->
  IMG_TOP <= spZ regs - 6112 -> spZ regs - 6112 <= lo' -> S' <= spZ regs ->
  bytes_at rsegs m' fp (pf_bytes (fmt ++ [0])) /\
  pf_args_ok m' S' lo' f MemFile.MF_BLOCK [getr regs 14; getr regs 15; getr regs 16; getr regs 17] args.
Proof.
  intros m m' regs fp fmt ps args T f S' lo' (EB & R1 & R2 & EP & ET & EA) Ef PL MU IT L1 L2.
  rewrite Ef in EA. split.
  - apply (bytes_munch _ m m' _ _ EB MU). intros z Hz. unfold pf_bytes in Hz.
    rewrite length_map, length_app in Hz. cbn [length] in Hz. cbn [outside].
    unfold mf_place_ok, RO_LO, RO_END, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in *.
    split; [lia | split; [lia | exact I]].
  - exact (pf_args_ok_munch m m' _ _ _ _ S' lo' _ args EA MU L1 L2).
Qed.

Lemma byte8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hz.
Qed.

(* two byte strings (no NUL, each byte below 256) whose NUL-terminated images start at one address are one *)
Lemma zstr_unique : forall s1 s2 m a x1 x2,
  Forall (fun c => 0 < c < 256) s1 -> Forall (fun c => 0 < c < 256) s2 ->
  bytes_at rsegs m a (map (Z_to_bv 8) (s1 ++ [0]) ++ x1) ->
  bytes_at rsegs m a (map (Z_to_bv 8) (s2 ++ [0]) ++ x2) -> s1 = s2.
Proof.
  induction s1 as [|c1 s1 IH]; intros [|c2 s2] m a x1 x2 F1 F2 B1 B2; cbn [app map] in B1, B2.
  - reflexivity.
  - exfalso. pose proof (Forall_inv F2) as Hc. cbv beta in Hc.
    apply bytes_at_hd in B1, B2. rewrite B1 in B2. assert (E : Z_to_bv 8 0 = Z_to_bv 8 c2) by congruence.
    apply (f_equal bv_unsigned) in E. rewrite !byte8_lit in E by lia. lia.
  - exfalso. pose proof (Forall_inv F1) as Hc. cbv beta in Hc.
    apply bytes_at_hd in B1, B2. rewrite B1 in B2. assert (E : Z_to_bv 8 c1 = Z_to_bv 8 0) by congruence.
    apply (f_equal bv_unsigned) in E. rewrite !byte8_lit in E by lia. lia.
  - pose proof (Forall_inv F1) as Hc1. pose proof (Forall_inv F2) as Hc2. cbv beta in Hc1, Hc2.
    pose proof (bytes_at_hd _ _ _ _ B1) as H1. pose proof (bytes_at_hd _ _ _ _ B2) as H2.
    rewrite H1 in H2. assert (E : Z_to_bv 8 c1 = Z_to_bv 8 c2) by congruence.
    apply (f_equal bv_unsigned) in E. rewrite !byte8_lit in E by lia.
    subst c2. f_equal.
    exact (IH s2 m (a + 1) x1 x2 (Forall_inv_tail F1) (Forall_inv_tail F2)
              (bytes_at_tl _ _ _ _ B1) (bytes_at_tl _ _ _ _ B2)).
Qed.

(* every byte of a format `pf_parse` reads is in 1..255 *)
Lemma parse_range_n : forall n f ps, (length f <= n)%nat -> pf_parse f = Some ps ->
  Forall (fun c => 0 < c < 256) f.
Proof.
  induction n as [|n IH]; intros f ps Hl H.
  - destruct f; [constructor | cbn in Hl; lia].
  - destruct f as [|b r]; [constructor|]. cbn [length] in Hl. cbn [pf_parse] in H.
    destruct (Z.eqb_spec b 37) as [Eb|Eb]; cbv beta iota in H.
    + subst b. destruct r as [|c r1]; cbv beta iota in H; [discriminate H|]. cbn [length] in Hl.
      apply Forall_cons; [lia|].
      assert (One : forall c' (q : list pf_piece -> list pf_piece), 0 < c' < 256 ->
                    option_map q (pf_parse r1) = Some ps -> Forall (fun c => 0 < c < 256) (c' :: r1)).
      { intros c' q Hc' Hq. apply Forall_cons; [exact Hc'|].
        destruct (pf_parse r1) as [p1|] eqn:P; cbn [option_map] in Hq; [|discriminate Hq].
        exact (IH r1 p1 ltac:(lia) P). }
      assert (Two : forall c' c2 c3 r3 (q : list pf_piece -> list pf_piece),
                    0 < c' < 256 -> 0 < c2 < 256 -> 0 < c3 < 256 -> r1 = c2 :: c3 :: r3 ->
                    option_map q (pf_parse r3) = Some ps -> Forall (fun c => 0 < c < 256) (c' :: r1)).
      { intros c' c2 c3 r3 q H1 H2 H3 -> Hq. cbn [length] in Hl.
        apply Forall_cons; [exact H1|]. apply Forall_cons; [exact H2|]. apply Forall_cons; [exact H3|].
        destruct (pf_parse r3) as [p3|] eqn:P; cbn [option_map] in Hq; [|discriminate Hq].
        exact (IH r3 p3 ltac:(lia) P). }
      destruct (Z.eqb_spec c 100) as [Ec|Ec]; cbv beta iota in H; [subst c; exact (One 100 _ ltac:(lia) H)|].
      destruct (Z.eqb_spec c 99) as [Ec2|Ec2]; cbv beta iota in H; [subst c; exact (One 99 _ ltac:(lia) H)|].
      destruct (Z.eqb_spec c 115) as [Ec3|Ec3]; cbv beta iota in H; [subst c; exact (One 115 _ ltac:(lia) H)|].
      destruct (Z.eqb_spec c 48) as [Ec4|Ec4]; cbv beta iota in H.
      { subst c. destruct r1 as [|c2 [|c3 r3]]; cbv beta iota in H; try discriminate H.
        destruct (Z.eqb_spec c2 52) as [E2|E2], (Z.eqb_spec c3 120) as [E3|E3]; cbn [andb] in H;
          [subst; exact (Two 48 52 120 r3 _ ltac:(lia) ltac:(lia) ltac:(lia) eq_refl H) | | |];
          destruct (Z.eqb_spec c2 50) as [E4|E4]; cbn [andb] in H; try discriminate H;
          subst; exact (Two 48 50 120 r3 _ ltac:(lia) ltac:(lia) ltac:(lia) eq_refl H). }
      destruct (Z.eqb_spec c 108) as [Ec5|Ec5]; cbv beta iota in H.
      { subst c. destruct r1 as [|c2 [|c3 r3]]; cbv beta iota in H; try discriminate H.
        destruct (Z.eqb_spec c2 108) as [E2|E2], (Z.eqb_spec c3 117) as [E3|E3]; cbn [andb] in H;
          try discriminate H.
        subst; exact (Two 108 108 117 r3 _ ltac:(lia) ltac:(lia) ltac:(lia) eq_refl H). }
      destruct (Z.eqb_spec c 46) as [Ec6|Ec6]; cbv beta iota in H; [|discriminate H].
      { subst c. destruct r1 as [|c2 [|c3 r3]]; cbv beta iota in H; try discriminate H.
        destruct (Z.eqb_spec c2 42) as [E2|E2], (Z.eqb_spec c3 115) as [E3|E3]; cbn [andb] in H;
          try discriminate H.
        subst; exact (Two 46 42 115 r3 _ ltac:(lia) ltac:(lia) ltac:(lia) eq_refl H). }
    + destruct ((0 <? b) && (b <? 256)) eqn:F; cbv beta iota in H; [|discriminate H].
      apply andb_prop in F as [F1 F2]. apply Z.ltb_lt in F1. apply Z.ltb_lt in F2.
      apply Forall_cons; [lia|].
      destruct (pf_parse r) as [p1|] eqn:P; cbn [option_map] in H; [exact (IH r p1 ltac:(lia) P) | discriminate H].
Qed.

Lemma int_eq : forall (r : word) v1 v2,
  (-2^31 <= v1 < 2^31 /\ bv_unsigned r mod 2^32 = v1 mod 2^32) ->
  (-2^31 <= v2 < 2^31 /\ bv_unsigned r mod 2^32 = v2 mod 2^32) -> v1 = v2.
Proof.
  intros r v1 v2 [R1 E1] [R2 E2]. rewrite E1 in E2.
  assert (P : 2 ^ 32 = 4294967296) by reflexivity. assert (P' : 2 ^ 31 = 2147483648) by reflexivity.
  rewrite P in *. rewrite P' in *.
  pose proof (Z.div_mod v1 4294967296 ltac:(lia)) as D1. pose proof (Z.div_mod v2 4294967296 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound v1 4294967296 ltac:(lia)). pose proof (Z.mod_pos_bound v2 4294967296 ltac:(lia)).
  lia.
Qed.

Lemma str_eq : forall m S lo D n (r : word) s1 s2,
  pf_arg_ok m S lo D n r (APtr s1) -> pf_arg_ok m S lo D n r (APtr s2) -> s1 = s2.
Proof.
  intros m S lo D n r s1 s2 (F1 & x1 & B1 & _) (F2 & x2 & B2 & _).
  exact (zstr_unique s1 s2 m (bv_unsigned r) x1 x2 F1 F2 B1 B2).
Qed.

Ltac one_arg IH ps :=
  lazymatch goal with
  | H1 : pf_text _ ?a1 = Some _, H2 : pf_text _ ?a2 = Some _,
    P1 : pf_args_ok _ _ _ _ _ ?rs ?a1, P2 : pf_args_ok _ _ _ _ _ ?rs ?a2 |- ?a1 = ?a2 =>
      let v1 := fresh "v" in let u1 := fresh "u" in let s1 := fresh "s" in let a1' := fresh "a" in
      let v2 := fresh "v" in let u2 := fresh "u" in let s2 := fresh "s" in let a2' := fresh "a" in
      destruct a1 as [|[v1|u1|s1] a1']; cbn [pf_text] in H1; try discriminate H1;
      destruct a2 as [|[v2|u2|s2] a2']; cbn [pf_text] in H2; try discriminate H2;
      let r := fresh "r" in let rs' := fresh "rs" in
      destruct rs as [|r rs']; [destruct P1|];
      let Q1 := fresh "Q" in let Q2 := fresh "Q" in
      destruct P1 as [Q1 P1], P2 as [Q2 P2];
      let E1 := fresh "E" in let E2 := fresh "E" in
      destruct (pf_text ps a1') eqn:E1; cbn [option_map] in H1; try discriminate H1;
      destruct (pf_text ps a2') eqn:E2; cbn [option_map] in H2; try discriminate H2;
      rewrite (IH _ _ _ _ _ _ _ _ _ _ E1 E2 P1 P2);
      first [ cbn [pf_arg_ok] in Q1, Q2; rewrite (int_eq _ _ _ Q1 Q2); reflexivity
            | cbn [pf_arg_ok] in Q1, Q2; rewrite <- Q1, <- Q2; reflexivity
            | rewrite (str_eq _ _ _ _ _ _ _ _ Q1 Q2); reflexivity ]
  end.

(* the arguments `pf_args_ok` names for one format and one register list are one list *)
Lemma args_unique : forall ps m S lo D n rs a1 a2 T1 T2,
  pf_text ps a1 = Some T1 -> pf_text ps a2 = Some T2 ->
  pf_args_ok m S lo D n rs a1 -> pf_args_ok m S lo D n rs a2 -> a1 = a2.
Proof.
  induction ps as [|p ps IH]; intros m S lo D n rs a1 a2 T1 T2 H1 H2 P1 P2.
  - destruct a1, a2; cbn [pf_text] in H1, H2; congruence.
  - destruct p.
    + cbn [pf_text] in H1, H2.
      destruct (pf_text ps a1) eqn:E1; cbn [option_map] in H1; [|discriminate H1].
      destruct (pf_text ps a2) eqn:E2; cbn [option_map] in H2; [|discriminate H2].
      exact (IH _ _ _ _ _ _ _ _ _ _ E1 E2 P1 P2).
    + one_arg IH ps.
    + one_arg IH ps.
    + one_arg IH ps.
    + one_arg IH ps.
    + one_arg IH ps.
    + one_arg IH ps.
    + destruct a1 as [|[k1|u1|s1] [|[w1|v1|t1] a1]]; cbn [pf_text] in H1; try discriminate H1;
      destruct a2 as [|[k2|u2|s2] [|[w2|v2|t2] a2]]; cbn [pf_text] in H2; try discriminate H2.
      destruct rs as [|r1 [|r2 rs]]; [destruct P1 | destruct P1 as [_ []] |].
      destruct P1 as [Q1 [R1 P1]], P2 as [Q2 [R2 P2]].
      destruct ((0 <=? k1) && (k1 <=? Z.of_nat (length t1))); cbv beta iota in H1; [|discriminate H1].
      destruct ((0 <=? k2) && (k2 <=? Z.of_nat (length t2))); cbv beta iota in H2; [|discriminate H2].
      destruct (pf_text ps a1) eqn:E1; cbn [option_map] in H1; [|discriminate H1].
      destruct (pf_text ps a2) eqn:E2; cbn [option_map] in H2; [|discriminate H2].
      rewrite (IH _ _ _ _ _ _ _ _ _ _ E1 E2 P1 P2).
      cbn [pf_arg_ok] in Q1, Q2. rewrite (int_eq _ _ _ Q1 Q2), (str_eq _ _ _ _ _ _ _ _ R1 R2). reflexivity.
Qed.

(* one text: two readings of `emit_fmt` at one address, memory and register map give one T *)
Lemma emit_fmt_unique : forall m regs fp fmt1 ps1 args1 T1 fmt2 ps2 args2 T2,
  emit_fmt m regs fp fmt1 ps1 args1 T1 -> emit_fmt m regs fp fmt2 ps2 args2 T2 -> T1 = T2.
Proof.
  intros m regs fp fmt1 ps1 args1 T1 fmt2 ps2 args2 T2 (B1 & _ & _ & P1 & X1 & A1) (B2 & _ & _ & P2 & X2 & A2).
  assert (Ef : fmt1 = fmt2).
  { apply (zstr_unique fmt1 fmt2 m fp [] []).
    - exact (parse_range_n _ fmt1 ps1 (le_n _) P1).
    - exact (parse_range_n _ fmt2 ps2 (le_n _) P2).
    - rewrite app_nil_r. exact B1.
    - rewrite app_nil_r. exact B2. }
  subst fmt2. rewrite P1 in P2. injection P2 as <-.
  rewrite (args_unique ps1 m _ _ _ _ _ args1 args2 T1 T2 X1 X2 A1 A2) in X1. rewrite X1 in X2.
  injection X2 as ->. reflexivity.
Qed.

(* ==========================================================================
   5. The two calls' arguments
   ========================================================================== *)

(* a constant string of the image as a `%s` argument below the callee's window *)
Lemma str_arg_ok : forall m S lo D n (r : word) A s slack, str_ok A s slack -> mem_inv rsegs m ->
  bv_unsigned r = A -> RO_END <= lo -> mf_place_ok D -> n = MemFile.MF_BLOCK ->
  pf_arg_ok m S lo D n r (APtr s).
Proof.
  intros m S lo D n r A s slack (SB & SPAD & SR1 & SR2 & SF) MI Er Hlo PL En. cbn [pf_arg_ok]. rewrite Er.
  subst n. split; [exact SF|]. exists (pf_bytes slack).
  assert (Ls : length (pf_bytes slack) = length slack) by (unfold pf_bytes; apply length_map). rewrite Ls.
  split; [exact (SB m MI)|]. split; [exact SPAD|]. split; [unfold RO_LO in SR1; lia|].
  unfold mf_place_ok, IMG_LO, IMG_TOP, RO_LO, RO_END, MemFile.MF_BLOCK in *. split; lia.
Qed.

(* fprintf's Post, read through `getr` only *)
Lemma pf_post_ext : forall f k pb T fl om wend pos len,
  post_ext (fun regs m regs' m' => res regs' = Z.of_nat (length T) /\ pf_file_post m' f k pb T fl om wend pos len).
Proof.
  intros f k pb T fl om wend pos len r1 r2 m q1 q2 m' E1 E2 [H1 H2].
  split; [unfold res in *; rewrite <- E2; exact H1 | exact H2].
Qed.

(* the four va_list slots of reac_code_emit's frame: the 8-byte cells at sp+0x20..+0x38 *)
Lemma va_of_frame : forall m A v0 v1 v2 v3 w4 w5 w6 w7,
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C8 v3; C8 w4; C8 w5; C8 w6; C8 w7] ->
  va_slots m (A + 32) [w4; w5; w6; w7].
Proof.
  intros m A v0 v1 v2 v3 w4 w5 w6 w7 [[_ B] _]. unfold va_slots.
  assert (E : cells_bytes [C8 v0; C8 v1; C8 v2; C8 v3; C8 w4; C8 w5; C8 w6; C8 w7] =
              (le8 v0 ++ le8 v1 ++ le8 v2 ++ le8 v3) ++ flat_map le8 [w4; w5; w6; w7])
    by (cbn [cells_bytes cbytes flat_map]; rewrite <- !app_assoc; reflexivity).
  rewrite E in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite !length_app, !length_le8 in B. exact B.
Qed.

(* fprintf's Pre at reac_code_emit's call (+0x44): "%s: %s " with "reac-pw" and "E_NOT_MARKED" *)
Lemma emit_head_pre : forall regs m f k fl om wend wpos wbase pos len pb,
  arg regs 0 = f -> arg regs 1 = FMT_EMIT_A ->
  bv_unsigned (getr regs 12) = S_REACPW_A -> bv_unsigned (getr regs 13) = S_ENM_A ->
  mem_inv rsegs m -> memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len ->
  mf_pend_bytes m f pb -> Z.of_nat (length pb) = k -> k + 22 <= MemFile.MF_BUFSIZ ->
  f + MemFile.MF_BLOCK <= spZ regs - FPRINTF_K -> IMG_TOP <= spZ regs - FPRINTF_K -> guard_words m ->
  arg regs 0 = f /\
  memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
  mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
  bytes_at rsegs m (arg regs 1) (pf_bytes (FMT_EMIT ++ [0])) /\
  RO_LO <= arg regs 1 /\ arg regs 1 + Z.of_nat (length FMT_EMIT) + 1 <= RO_END /\
  pf_parse FMT_EMIT = Some PS_EMIT /\ pf_text PS_EMIT [APtr S_REACPW; APtr S_ENM] = Some T_EMIT /\
  pf_args_ok m (spZ regs) (spZ regs - FPRINTF_K) f MemFile.MF_BLOCK
    [getr regs 12; getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17]
    [APtr S_REACPW; APtr S_ENM] /\
  k + Z.of_nat (length T_EMIT) <= MemFile.MF_BUFSIZ /\
  f + MemFile.MF_BLOCK <= spZ regs - FPRINTF_K /\ IMG_TOP <= spZ regs - FPRINTF_K /\
  guard_words m.
Proof.
  intros regs m f k fl om wend wpos wbase pos len pb E0 E1 E2 E3 MI MK MD MP LP FIT FB IT GW.
  destruct fmt_emit_ok as (FBy & FR1 & FR2 & FP & _ & _).
  pose proof (memfile_k_place m f k MK) as PL.
  split; [exact E0|]. split; [exact MK|]. split; [exact MD|]. split; [exact MP|]. split; [exact LP|].
  rewrite E1. split; [exact (FBy m MI)|]. split; [exact FR1|]. split; [exact FR2|]. split; [exact FP|].
  split; [exact text_emit|].
  split; [|split; [rewrite (emit_code_len T_EMIT text_emit); lia | split; [exact FB | split; [exact IT | exact GW]]]].
  cbn [pf_args_ok]. split; [|split; [|exact I]].
  - apply (str_arg_ok _ _ _ _ _ _ _ _ _ s_reacpw_ok MI E2); [unfold IMG_TOP, RO_END in *; lia | exact PL | reflexivity].
  - apply (str_arg_ok _ _ _ _ _ _ _ _ _ s_enm_ok MI E3); [unfold IMG_TOP, RO_END in *; lia | exact PL | reflexivity].
Qed.
