(* attr_text (fuzz_link.c:168-172), PLAIN build: the walk of lib/Prog/attr_text_c.v on the plain
   image. 91 instructions at 0x1534c: strlen(s), then nl_attr_put(w, type, s, strlen(s) + !bare),
   which is nl_put16 of the length, nl_put16 of the type, nl_put of the text and nl_pad.

   The walk carries the reply writer as lib/Prog/hp_wr_kit.v does: `stk` over the 4112 bytes of
   the structure, and the two cells of w->n and w->full. The code meets three merge points
   (0x15404 after the header, 0x15444 after the text, 0x1548c the epilogue), so the walk is a
   chain of lemmas, last block first: `at_m3`, `at_m2`, `at_m1`, then the entry block. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf hp_wr_kit attr_text_c strlen_c memcpy_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* what `leaf` asks at the `ret`, with the callee-saved registers named *)
Definition at_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (w lo : Z)
    (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -64, bv_unsigned sp); (w, w + 4112)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (forall bs, nlw_at m0 w bs -> exists bs', nlw_at m' w bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs').

(* the memory at a merge point: the writer (w->n = n, w->full = f), the footprint so far, and the
   frame with the eight saved registers *)
Definition atst (m0 m : word -> option byte) (w lo sp0 n f : Z) (fr : list cell) : Prop :=
  stk rsegs m w (w + 4112) /\
  (exists tn tf pad, rw_cells rsegs m (w + 4096) [CB 8 tn; CB 4 tf; CB 4 pad] /\
     bytes_le_to_Z tn = n /\ bytes_le_to_Z tf = f) /\
  munch [(sp0 + -64, sp0); (w, w + 4112)] m0 m /\ wmono rsegs m0 m /\
  mem_inv rsegs m /\ stk rsegs m lo (sp0 + -64) /\ rw_cells rsegs m (sp0 + -64) fr.

Lemma bytes_present : forall m a (k : nat),
  0 <= a -> a + Z.of_nat k <= 2^64 ->
  (forall i, (i < k)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, length bs = k /\ bytes_at rsegs m a bs.
Proof.
  intros m a k Ha Hk H.
  assert (G : forall j, (j <= k)%nat -> exists bs, length bs = j /\
                forall i, (i < j)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i).
  { induction j as [|j IH]; intros Hj.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H j ltac:(lia)) as (b & Hb).
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eqb_spec i j) as [->|Hne].
      + rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G k ltac:(lia)) as (bs & Hlen & Hbs).
  exists bs. split; [exact Hlen|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

(* the two field cells after the walk stored into them, back in the shape `atst` keeps *)
Lemma fields_ok : forall m A c1 c2 c3 n f,
  rw_cells rsegs m A [c1; c2; c3] -> csize c1 = 8%nat -> csize c2 = 4%nat -> csize c3 = 4%nat ->
  bytes_le_to_Z (cbytes c1) = n -> bytes_le_to_Z (cbytes c2) = f ->
  exists tn tf pad, rw_cells rsegs m A [CB 8 tn; CB 4 tf; CB 4 pad] /\
    bytes_le_to_Z tn = n /\ bytes_le_to_Z tf = f.
Proof.
  intros m A c1 c2 c3 n f [[Hwf Hb] Hw] E1 E2 E3 Hn Hf.
  cbn [cells_wf] in Hwf. destruct Hwf as (W1 & W2 & W3 & _).
  exists (cbytes c1), (cbytes c2), (cbytes c3). split; [|split; assumption].
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite !cbytes_length by assumption. rewrite E1, E2, E3. tauto.
  - cbn [cells_bytes cbytes]. cbn [cells_bytes] in Hb. exact Hb.
  - cbn [cells_size csize]. cbn [cells_size] in Hw. rewrite E1, E2, E3 in Hw. exact Hw.
Qed.

Lemma bytes_at_firstn : forall m A bs (k : nat), bytes_at rsegs m A bs -> bytes_at rsegs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H.
  apply (proj1 (bytes_at_app rsegs m A _ _)) in H. exact (proj1 H).
Qed.

(* the writer's state across a callee that wrote only [a, a + k), inside w->b *)
Lemma st_call : forall m0 m m' w lo sp0 n f fr a k,
  atst m0 m w lo sp0 n f fr -> cells_size fr = 64%nat ->
  (w + 4112 <= sp0 + -64 \/ sp0 <= w) ->
  w <= a -> 0 <= k -> a + k <= w + 4096 ->
  munch [(a, a + k)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  (forall x, a <= x < a + k -> exists b, mrd rsegs m' (wa x) = Some b) ->
  atst m0 m' w lo sp0 n f fr.
Proof.
  intros m0 m m' w lo sp0 n f fr a k (SW & (tn & tf & pad & HC & Hn & Hf) & MU & WM & MI & ST & FR)
    Hfr APF Ha Hk Hak MUc WMc MIc Hcov.
  assert (Hcase : forall x, outside [(a, a + k)] x \/ (exists b, mrd rsegs m' (wa x) = Some b)).
  { intros x. destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + k)).
    - right. apply Hcov. lia.
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
  pose proof (rw_cells_bound rsegs m _ _ HC) as HB1. cbn [cells_size csize] in HB1.
  pose proof (rw_cells_bound rsegs m _ _ FR) as HB2. rewrite Hfr in HB2.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply stk_transport_mrd; [exact SW | exact MUc | exact WMc | intros x _; apply Hcase].
  - exists tn, tf, pad. split; [|split; assumption].
    eapply rw_cells_transport; [exact HC | exact MUc | exact WMc |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [lia | exact I].
  - eapply wmono_trans; eassumption.
  - exact MIc.
  - eapply stk_transport_mrd; [exact ST | exact MUc | exact WMc | intros x _; apply Hcase].
  - eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |].
    rewrite Hfr. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* nl_pad's `srliw s1, a0, 2; slli s1, s1, 2` of a0 = n + 3, as the step leaves it *)
Lemma pad_val : forall n, 0 <= n <= 4096 ->
  Z.shiftl (bv_swrap 32 (Z.shiftr (bv_wrap 32 (n + 3)) 2) mod 18446744073709551616) 2 = 4 * ((n + 3) / 4).
Proof.
  intros n Hn.
  rewrite (bv_wrap_small 32 (n + 3)) by (change (bv_modulus 32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. apply Z.mul_comm.
Qed.

Ltac eqw := first [ reflexivity | word_eq_tac ].

(* `atst` at a merge point, out of the hypotheses the walk tactics keep up to date; the two
   field values are left to `fval` *)
Ltac pack_atst :=
  unfold atst;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
  [ eassumption
  | eapply fields_ok; [ eassumption | reflexivity | reflexivity | reflexivity | | ]
  | eassumption | eassumption | eassumption | eassumption | eassumption ].

Ltac fval :=
  cbn [cbytes];
  first [ eassumption
        | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; lia
        | rewrite bytes_le_to_Z_le4; reflexivity ].

Ltac fix_ret :=
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* 0x1548c, the epilogue *)
Lemma at_m3 : forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra a0 : word) (lo : Z)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (n f : Z)
    (rav spv t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v t3 t4 t5 t6 : word),
  spv = Z_to_bv 64 (bv_unsigned sp + -64) ->
  lo + 64 <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
  atst m0 m (bv_unsigned a0) lo (bv_unsigned sp) n f [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  0 <= n <= 4096 -> 0 <= f <= 1 -> (forall bs, nlw_at m0 (bv_unsigned a0) bs -> nw_n bs <= n) ->
  evt rsegs (at_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra (bv_unsigned a0) lo F fc m0)
    (MS (mkR rav spv gp tp t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1548c) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra a0 lo F fc m0 m n f
         rav spv t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v t3 t4 t5 t6
         Esp LO SP (SW & (tn & tf & pad & HC & Hn & Hf) & MU & WM & MI & ST & FR) Hnr Hfr HB.
  subst spv.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  destruct (nlw_from m (bv_unsigned a0) n f tn tf pad SW HC Hn Hf) as (bs' & HW' & En & Ef).
  apply evt_done. unfold at_post.
  do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  intros bs HB0. exists bs'. split; [exact HW'|].
  split; [unfold nlw_wf, NL_CHUNK_MAX; rewrite En, Ef; lia|].
  rewrite En. apply HB. exact HB0.
Qed.

(* 0x15444, nl_pad with a1 = w->n = n: P = NL_ALIGN(n) <= 4096 always, so the full exit at 0x15454
   is unreachable; memset(w->b + n, 0, P - n) when P <> n, then w->n = P *)
Lemma at_m2 : memset_contract ->
  forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra a0 : word) (lo : Z)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (n f : Z)
    (rav spv t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v t3 t4 t5 t6 : word),
  spv = Z_to_bv 64 (bv_unsigned sp + -64) -> s0v = a0 -> s4v = Z_to_bv 64 (bv_unsigned a0 + 4096) ->
  a1v = Z_to_bv 64 n ->
  lo + 64 <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
  0 <= bv_unsigned a0 -> bv_unsigned a0 + 4112 <= 2^64 ->
  (bv_unsigned a0 + 4112 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= bv_unsigned a0) ->
  atst m0 m (bv_unsigned a0) lo (bv_unsigned sp) n f [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  0 <= n <= 4096 -> 0 <= f <= 1 -> (forall bs, nlw_at m0 (bv_unsigned a0) bs -> nw_n bs <= n) ->
  evt rsegs (at_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra (bv_unsigned a0) lo F fc m0)
    (MS (mkR rav spv gp tp t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15444) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra a0 lo F fc m0 m n f
         rav spv t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v t3 t4 t5 t6
         Esp Es0 Es4 Ea1 LO SP HwA HwB APF ATST Hnr Hfr HB.
  subst spv s0v s4v a1v.
  pose proof ATST as (SW & (tn & tf & pad & HC & Hn & Hf) & MU & WM & MI & ST & FR).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  zstep. zstep. zstep. zstep. zstep.
  rewrite (pad_val n Hnr).
  remember (4 * ((n + 3) / 4)) as P eqn:EP.
  assert (HP : n <= P <= 4096) by (subst P; Z.div_mod_to_equations; lia). clear EP.
  zstep. if_cases Hg.
  2: { cbv iota. zify_cond Hg. exfalso. Z.div_mod_to_equations. lia. }
  cbv iota. clear Hg.
  zstep. if_cases Hg2.
  - (* nothing to pad: w->n = n *)
    cbv iota. zify_cond Hg2. rewrite ?Z.mod_small in Hg2 by lia. subst P.
    zstep.
    eapply at_m3 with (n := n) (f := f);
      [ eqw | exact LO | exact SP | pack_atst; fval | lia | lia | exact HB ].
  - cbv iota. zify_cond Hg2. rewrite ?Z.mod_small in Hg2 by lia.
    zstep. zstep. zstep. zstep. zstep.
    destruct (cells_of_stk m (bv_unsigned a0) (bv_unsigned a0 + 4112) (bv_unsigned a0 + n) (Z.to_nat (P - n))
                SW ltac:(lia) ltac:(lia)) as (junk & Hjl & HJ).
    eapply evt_cut.
    { eapply MEMSET with (junk := junk); [ | exact MI ].
      rewrite !unsigned_lit by lia. exact HJ. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                & E & MUc & WMc & MIc & CC).
    subst ms'. rewrite !unsigned_lit in MUc, CC by lia.
    assert (COV : forall x, bv_unsigned a0 + n <= x < bv_unsigned a0 + n + (P - n) ->
                    exists b, mrd rsegs m' (wa x) = Some b).
    { intros x Hx. eapply stk_cover_cells; [exact CC | cbn [cells_size csize]; lia]. }
    pose proof (st_call m0 m m' (bv_unsigned a0) lo (bv_unsigned sp) n f _ (bv_unsigned a0 + n) (P - n)
                  ATST ltac:(reflexivity) APF ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc COV) as ATST'.
    clear SW HC MU WM MI ST FR Hn Hf ATST CC COV MUc WMc HJ.
    destruct ATST' as (SW & (tn' & tf' & pad' & HC & Hn & Hf) & MU & WM & MI & ST & FR).
    assert (Ltn : length tn' = 8%nat) by (destruct HC as [[Hwf _] _]; cbn in Hwf; tauto).
    fix_ret.
    zstep. rewrite (ld_cb tn' Ltn), Hn. zstep. zstep.
    eapply at_m3 with (n := P) (f := f);
      [ eqw | exact LO | exact SP | pack_atst; fval | lia | lia | intros bs H; specialize (HB bs H); lia ].
Qed.

(* 0x15404, nl_put(w, s, D) with a1 = w->n = n and s2 = D: full when n + D > 4096; nothing to copy
   when D = 0; else memcpy(w->b + n, s, D) and w->n = n + D *)
Lemma at_m1 : memcpy_contract -> memset_contract ->
  forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra a0 a2 : word) (lo : Z)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (n f D : Z) (sbs : list byte)
    (rav spv t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v t3 t4 t5 t6 : word),
  spv = Z_to_bv 64 (bv_unsigned sp + -64) -> s0v = a0 -> s1v = a2 -> s2v = Z_to_bv 64 D ->
  s4v = Z_to_bv 64 (bv_unsigned a0 + 4096) -> a1v = Z_to_bv 64 n ->
  lo + 64 <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
  0 <= bv_unsigned a0 -> bv_unsigned a0 + 4112 <= 2^64 ->
  (bv_unsigned a0 + 4112 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= bv_unsigned a0) ->
  atst m0 m (bv_unsigned a0) lo (bv_unsigned sp) n f [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  0 <= n <= 4096 -> 0 <= f <= 1 -> (forall bs, nlw_at m0 (bv_unsigned a0) bs -> nw_n bs <= n) ->
  bytes_at rsegs m (bv_unsigned a2) sbs -> 0 <= D <= Z.of_nat (length sbs) ->
  (bv_unsigned a0 + 4112 <= bv_unsigned a2 \/ bv_unsigned a2 + Z.of_nat (length sbs) <= bv_unsigned a0) ->
  evt rsegs (at_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra (bv_unsigned a0) lo F fc m0)
    (MS (mkR rav spv gp tp t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15404) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY MEMSET sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra a0 a2 lo F fc m0 m n f D sbs
         rav spv t0 t1 t2 s0v s1v a0v a1v a2v a3v a4v a5v a6v a7v s2v s3v s4v s5v s6v t3 t4 t5 t6
         Esp Es0 Es1 Es2 Es4 Ea1 LO SP HwA HwB APF ATST Hnr Hfr HB BS HD HDJ.
  subst spv s0v s1v s2v s4v a1v.
  pose proof ATST as (SW & (tn & tf & pad & HC & Hn & Hf) & MU & WM & MI & ST & FR).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
  pose proof (bytes_at_bound _ _ _ _ BS) as [BSa BSb].
  zstep. zstep. zstep.
  zstep. if_cases Hg.
  - cbv iota. zify_cond Hg.
    zstep. if_cases Hg2.
    + (* D = 0: w->n = n + D *)
      cbv iota. zify_cond Hg2.
      zstep. zstep.
      eapply (at_m2 MEMSET) with (n := n + D) (f := f);
        [ eqw | eqw | eqw | eqw | exact LO | exact SP | exact HwA | exact HwB | exact APF
        | pack_atst; fval | lia | lia | intros bs H; specialize (HB bs H); lia ].
    + cbv iota. zify_cond Hg2.
      zstep. zstep. zstep. zstep.
      destruct (cells_of_stk m (bv_unsigned a0) (bv_unsigned a0 + 4112) (bv_unsigned a0 + n) (Z.to_nat D)
                  SW ltac:(lia) ltac:(lia)) as (junk & Hjl & HJ).
      eapply evt_cut.
      { eapply MEMCPY with (src := firstn (Z.to_nat D) sbs) (junk := junk).
        - apply bytes_at_firstn. exact BS.
        - rewrite unsigned_lit by lia. apply firstn_length_le. lia.
        - rewrite !unsigned_lit by lia. exact HJ.
        - rewrite !unsigned_lit by lia. lia.
        - exact MI. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                  & E & MUc & WMc & MIc & CC & BSc).
      subst ms'. rewrite !unsigned_lit in MUc, CC by lia.
      assert (COV : forall x, bv_unsigned a0 + n <= x < bv_unsigned a0 + n + D ->
                      exists b, mrd rsegs m' (wa x) = Some b).
      { intros x Hx. eapply stk_cover_cells; [exact CC | cbn [cells_size csize]; lia]. }
      pose proof (st_call m0 m m' (bv_unsigned a0) lo (bv_unsigned sp) n f _ (bv_unsigned a0 + n) D
                    ATST ltac:(reflexivity) APF ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc COV) as ATST'.
      clear SW HC MU WM MI ST FR Hn Hf ATST CC COV MUc WMc HJ BSc BS.
      destruct ATST' as (SW & (tn' & tf' & pad' & HC & Hn & Hf) & MU & WM & MI & ST & FR).
      assert (Ltn : length tn' = 8%nat) by (destruct HC as [[Hwf _] _]; cbn in Hwf; tauto).
      fix_ret.
      zstep. rewrite (ld_cb tn' Ltn), Hn. zstep. zstep. zstep.
      eapply (at_m2 MEMSET) with (n := n + D) (f := f);
        [ eqw | eqw | eqw | eqw | exact LO | exact SP | exact HwA | exact HwB | exact APF
        | pack_atst; fval | lia | lia | intros bs H; specialize (HB bs H); lia ].
  - (* full: w->full = 1 *)
    cbv iota. zify_cond Hg.
    zstep. zstep. zstep.
    eapply (at_m2 MEMSET) with (n := n) (f := 1);
      [ eqw | eqw | eqw | eqw | exact LO | exact SP | exact HwA | exact HwB | exact APF
      | pack_atst; fval | lia | lia | exact HB ].
Qed.

Theorem attr_text_holds_h : strlen_contract -> memcpy_contract -> memset_contract -> attr_text_contract.
Proof.
  intros STRLEN MEMCPY MEMSET.
  unfold attr_text_contract. apply leaf_intro.
  - intros r1 r2 m E H.
    assert (SPG : forall R : bvmap 5 word, spZ R = bv_unsigned (getr R 2)) by reflexivity.
    unfold arg, apart_frame in *. rewrite !SPG in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. unfold arg. rewrite <- !E. reflexivity.
  - intros r1 r2 m q1 q2 m' E _ H. unfold arg in *. rewrite <- E. exact H.
  - unfold leaf_walk, ATTR_TEXT.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros PRE MI ST LO SP.
    destruct PRE as (bs0 & s & HW0 & HWF0 & HS0 & HCS & (slack & HSL & HSLn) & HDJ & APF & APS).
    rewrite !mkR_a0.
    rewrite mkR_a0 in HW0, HDJ, APF. rewrite mkR_a2 in HS0, HCS, HSL, HSLn, HDJ, APS.
    unfold apart_frame, NW_SIZE in APF, APS. unfold NW_SIZE in HDJ. rewrite mkR_sp in APF, APS.
    eapply evt_mono with
      (P := at_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra (bv_unsigned a0) lo F fc m).
    2: { intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                     & m' & E & MU & WM & MI' & ST' & PO).
         exists (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     t3' t4' t5' t6'), m'.
         split; [exact E|]. split; [apply regs_preserved_mkR|].
         split; [replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; unfold NW_SIZE; exact MU|].
         split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. exact PO. }
    pose proof (nlw_bound m (bv_unsigned a0) bs0 HW0) as [HwA HwB]. unfold NW_SIZE in HwB.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
    pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
    destruct HWF0 as [HN0 HF0]. unfold NL_CHUNK_MAX in HN0.
    pose proof (stk_of_nlw m (bv_unsigned a0) bs0 HW0) as SW. unfold NW_SIZE in SW.
    destruct (nlw_cells m (bv_unsigned a0) bs0 HW0) as (tn0 & tf0 & pad0 & HC & Htn & Htf).
    assert (Ltn0 : length tn0 = 8%nat) by (destruct HC as [[Hwf _] _]; cbn in Hwf; tauto).
    (* the strlen slack of the Pre, as "a byte is there", before the prologue overwrites the frame *)
    pose proof (bytes_at_bound _ _ _ _ HSL) as [HSLa HSLb].
    assert (SLK : forall i, (i < length slack)%nat ->
              exists b, mrd rsegs m (wa (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct HSL as (_ & _ & HN). rewrite (HN i Hi).
      destruct (nth_error slack i) as [b|] eqn:E; [exists b; reflexivity|].
      apply nth_error_None in E. lia. }
    clear HSL.
    destruct HCS as [HCSb HCSn].
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp);
                            (bv_unsigned a0, bv_unsigned a0 + 4112)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 64%nat ST.
    (* prologue: frame, eight `sd`, s2 = bare, s1 = s, s3 = type, s0 = w, s4 = w + 4096, a0 = s *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* the slack strlen reads, rebuilt at the memory after the prologue: each of its r <= 7 bytes is
       in the frame, in the structure, or outside both and so still the Pre's *)
    set (r := (- (bv_unsigned a2 + Z.of_nat (length s) + 1)) mod 8) in *.
    assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (bytes_present mm (bv_unsigned a2 + Z.of_nat (length s) + 1) (Z.to_nat r))
        as (sl & Hsl & BSL);
      [ lia | rewrite Z2Nat.id by lia; lia | | ]
    end.
    { intros i Hi.
      assert (Hix : (i < length slack)%nat) by lia.
      destruct (Z.leb_spec (bv_unsigned sp + -64) (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i)) as [F1|F1];
      destruct (Z.ltb_spec (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i) (bv_unsigned sp)) as [F2|F2];
      destruct (Z.leb_spec (bv_unsigned a0) (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i)) as [G1|G1];
      destruct (Z.ltb_spec (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i) (bv_unsigned a0 + 4112)) as [G2|G2];
      first
        [ replace (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i)
            with (bv_unsigned sp + -64 + Z.of_nat (Z.to_nat (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i
                                                             - (bv_unsigned sp + -64)))) by lia;
          eapply cells_mrd; [exact FR | cbn [cells_size csize Nat.add]; lia]
        | pose proof SW as (_ & _ & HSW);
          exact (proj2 (HSW (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i) ltac:(lia)))
        | destruct (SLK i Hix) as (b & Hb); exists b; unfold mrd in *;
          rewrite (MU (wa (bv_unsigned a2 + Z.of_nat (length s) + 1 + Z.of_nat i)));
          [ exact Hb | rewrite wa_unsigned by lia; cbn [outside]; refine (conj _ (conj _ I)); lia ] ]. }
    assert (BST : forall mm, bytes_at rsegs mm (bv_unsigned a2) (s ++ [zb 0]) ->
                    bytes_at rsegs mm (bv_unsigned a2 + Z.of_nat (length s) + 1) sl ->
                    bytes_at rsegs mm (bv_unsigned a2) (s ++ Z_to_bv 8 0 :: sl)).
    { intros mm B1 B2. replace (s ++ Z_to_bv 8 0 :: sl) with ((s ++ [zb 0]) ++ sl)
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact B1|]. rewrite length_app. cbn [length].
      replace (bv_unsigned a2 + Z.of_nat (length s + 1)) with (bv_unsigned a2 + Z.of_nat (length s) + 1) by lia.
      exact B2. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply STRLEN with (str := s) (slack := sl);
                        [ apply BST; eassumption | exact HCSn
                        | rewrite Hsl, Z2Nat.id by lia; apply Z.le_refl | eassumption ]
                     | unfold strlen_post; post_call rsegs mm ] end.
    clear BSL POST BST.
    (* a1 = w->n, s2 = D = |s| + !bare, then the guard of nl_put16(w, RTA_HDR + D) *)
    zstep. rewrite (ld_cb tn0 Ltn0), Htn.
    zstep. zstep. zstep. zstep.
    assert (HDs : 0 <= Z.b2z (bv_unsigned a3 <? 1) <= 1) by (destruct (bv_unsigned a3 <? 1); cbn; lia).
    assert (HBm : forall bs, nlw_at m (bv_unsigned a0) bs -> nw_n bs <= nw_n bs0)
      by (intros bs H; rewrite (nlw_at_unique m (bv_unsigned a0) bs bs0 H HW0); lia).
    assert (HDJs : bv_unsigned a0 + 4112 <= bv_unsigned a2 \/
                   bv_unsigned a2 + Z.of_nat (length (s ++ [zb 0])) <= bv_unsigned a0)
      by (rewrite length_app; cbn [length]; lia).
    assert (HDl : 0 <= Z.of_nat (length s) + Z.b2z (bv_unsigned a3 <? 1) <= Z.of_nat (length (s ++ [zb 0])))
      by (rewrite length_app; cbn [length]; lia).
    zstep. if_cases Hg.
    + (* full at the first nl_put16: w->full = 1, w->n stays *)
      cbv iota. zify_cond Hg.
      assert (Hfull : 4095 <= nw_n bs0) by (Z.div_mod_to_equations; lia). clear Hg.
      zstep. zstep. zstep.
      eapply (at_m1 MEMCPY MEMSET) with (n := nw_n bs0) (f := 1)
        (D := Z.of_nat (length s) + Z.b2z (bv_unsigned a3 <? 1)) (sbs := s ++ [zb 0]);
        [ eqw | eqw | eqw | eqw | eqw | eqw | exact LO | exact SP | exact HwA | exact HwB | exact APF
        | pack_atst; fval | lia | lia | exact HBm | exact HCSb | exact HDl | exact HDJs ].
    + cbv iota. zify_cond Hg.
      assert (Hput : nw_n bs0 <= 4094) by (Z.div_mod_to_equations; lia). clear Hg.
      (* the two length bytes at w->b + n, then w->n = n + 2 *)
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (nw_store_ok mm (bv_unsigned a0) (nw_n bs0) 1 SW ltac:(lia) ltac:(unfold NW_SIZE; lia)) as HS end.
      zstep. store_done.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (nw_store_ok mm (bv_unsigned a0) (nw_n bs0 + 1) 1 SW ltac:(lia) ltac:(unfold NW_SIZE; lia)) as HS end.
      zstep. store_done.
      zstep. rewrite (ld_cb tn0 Ltn0), Htn.
      zstep. zstep. zstep. zstep.
      zstep. if_cases Hg2.
      * (* the two type bytes at w->b + n + 2, then w->n = n + 4 *)
        cbv iota. zify_cond Hg2.
        assert (Hput2 : nw_n bs0 <= 4092) by (Z.div_mod_to_equations; lia). clear Hg2.
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (nw_store_ok mm (bv_unsigned a0) (nw_n bs0 + 2) 1 SW ltac:(lia) ltac:(unfold NW_SIZE; lia)) as HS end.
        zstep. store_done.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (nw_store_ok mm (bv_unsigned a0) (nw_n bs0 + 2 + 1) 1 SW ltac:(lia) ltac:(unfold NW_SIZE; lia)) as HS end.
        zstep. store_done.
        zstep. zstep. zstep.
        eapply (at_m1 MEMCPY MEMSET) with (n := nw_n bs0 + 4) (f := nw_full bs0)
          (D := Z.of_nat (length s) + Z.b2z (bv_unsigned a3 <? 1)) (sbs := s ++ [zb 0]);
          [ eqw | eqw | eqw | eqw | eqw | eqw | exact LO | exact SP | exact HwA | exact HwB | exact APF
          | pack_atst; fval | lia | lia | intros bs H; specialize (HBm bs H); lia
          | exact HCSb | exact HDl | exact HDJs ].
      * (* full at the second nl_put16: w->full = 1, w->n = n + 2 *)
        cbv iota. zify_cond Hg2. clear Hg2.
        zstep. zstep. zstep.
        eapply (at_m1 MEMCPY MEMSET) with (n := nw_n bs0 + 2) (f := 1)
          (D := Z.of_nat (length s) + Z.b2z (bv_unsigned a3 <? 1)) (sbs := s ++ [zb 0]);
          [ eqw | eqw | eqw | eqw | eqw | eqw | exact LO | exact SP | exact HwA | exact HwB | exact APF
          | pack_atst; fval | lia | lia | intros bs H; specialize (HBm bs H); lia
          | exact HCSb | exact HDl | exact HDJs ].
Qed.

From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require strlen memcpy memset.

Theorem attr_text_holds : attr_text_contract.
Proof.
  apply attr_text_holds_h; [exact strlen.strlen_holds | exact memcpy.memcpy_holds | exact memset.memset_holds].
Qed.

Print Assumptions attr_text_holds.
