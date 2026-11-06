(* The op_unmark arm (c3) of LLVMFuzzerTestOneInput, plain image: the facts the walk of the inlined
   model_unmark loop (0x13b4c-0x13bb4, LC3Loop.v) uses.
   - pure facts: bcmp against "reac-pw:served", the reader's answer is small, the walk of `unmark`
     takes one name per round, the model's chunk state after a read or a write;
   - the mark slot j of the model block is a C string in memory;
   - the three write sets (model_read, bcmp, model_write) stay inside c3l_Wz, and c3_mem survives a
     write set inside c3l_Wz (LC3Keep's transports);
   - model_read's and model_write's Pre at the call sites, and their Posts read back. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import model_read_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Defs LC3Keep.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Words
   ========================================================================== *)

Lemma c3l_signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia.
  apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

Lemma c3l_lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !c3l_signed_small by lia. reflexivity. Qed.

Lemma c3l_sx32 : forall n, 0 <= n < 2 ^ 31 -> sx32 (wz n) = wz n.
Proof.
  intros n Hn. unfold sx32, wz. f_equal. rewrite unsigned_lit by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma c3l_eqb0 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec x 0) as [->|Hn]; [reflexivity|].
  apply Z.eqb_neq. intros E. pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

Lemma c3l_getr10 : forall r : bvmap 5 word, getr r 10 = reg_get r 10.
Proof. intros. reflexivity. Qed.

Section Args.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Lemma c3l_arg0 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 0 = bv_unsigned a0.
Proof. reflexivity. Qed.
Lemma c3l_arg1 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1 = bv_unsigned a1.
Proof. reflexivity. Qed.
Lemma c3l_arg2 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 2 = bv_unsigned a2.
Proof. reflexivity. Qed.
Lemma c3l_arg3 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 3 = bv_unsigned a3.
Proof. reflexivity. Qed.
Lemma c3l_arg4 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 4 = bv_unsigned a4.
Proof. reflexivity. Qed.
Lemma c3l_arg5 : arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 5 = bv_unsigned a5.
Proof. reflexivity. Qed.
Lemma c3l_spZ : spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) = bv_unsigned sp.
Proof. reflexivity. Qed.
End Args.

(* ==========================================================================
   2. Lists and bytes
   ========================================================================== *)

Lemma c3l_byte_zero : forall b : byte, bv_unsigned b = 0 -> b = zb 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma c3l_byte_eq : forall a b : byte, bv_unsigned a = bv_unsigned b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Lemma c3l_nth_firstn : forall {A} (l : list A) n i,
  nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i]; cbn; try reflexivity;
    try (rewrite IH; reflexivity);
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma c3l_nth_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l. induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma c3l_slice_nth : forall (c : list byte) off len i, 0 <= off -> 0 <= len ->
  nth_error (slice c off len) i =
    if (i <? Z.to_nat len)%nat then nth_error c (Z.to_nat off + i) else None.
Proof. intros c off len i H0 H1. unfold slice. rewrite c3l_nth_firstn, c3l_nth_skipn. reflexivity. Qed.

Lemma c3l_slice_length : forall (c : list byte) off len, 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> length (slice c off len) = Z.to_nat len.
Proof. intros c off len H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma c3l_bytes_at_slice : forall m a (c : list byte) off len, bytes_at rsegs m a c -> 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> bytes_at rsegs m (a + off) (slice c off len).
Proof.
  intros m a c off len (Ha & Hl & H) H0 H1 H2. pose proof (c3l_slice_length c off len H0 H1 H2) as LS.
  split; [lia|]. split; [rewrite LS; lia|]. intros i Hi. rewrite LS in Hi. rewrite c3l_slice_nth by lia.
  replace (i <? Z.to_nat len)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite <- H by lia. f_equal. f_equal. lia.
Qed.

(* a byte list with a NUL holds its C string, then the NUL *)
Lemma c3l_cstr_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ [zb 0] ++ rest /\ ~ In (zb 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr in *. cbn [nul_at firstn] in *. unfold bz in *.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  - exists l. cbn [firstn app]. rewrite (c3l_byte_zero b E). split; [reflexivity | intros []].
  - cbn [length] in H. destruct (IH ltac:(lia)) as (rest & Hl & Hn). exists rest.
    cbn [firstn app]. split; [f_equal; exact Hl|].
    intros [Hb|Hin]; [apply E; rewrite Hb; reflexivity | exact (Hn Hin)].
Qed.

Lemma c3l_skipn_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn. apply IH. exact H.
Qed.

Lemma c3l_mk_names_length : forall gbs, length (mk_names gbs) = Z.to_nat (mk_n gbs).
Proof. intros gbs. unfold mk_names. rewrite length_map, length_seq. reflexivity. Qed.

Lemma c3l_nmark_le : forall mbs, model_wf mbs -> 0 <= md_n_mark mbs <= 32.
Proof. intros mbs (_ & _ & _ & _ & _ & R & _). unfold MARKS_MAX in R. exact R. Qed.

(* mark slot j of the model block: the name md_marks gives, as a C string in memory *)
Lemma c3l_slot : forall m md mbs j, model_at m md mbs -> model_wf mbs -> 0 <= j < md_n_mark mbs ->
  nth_error (md_marks mbs) (Z.to_nat j) = Some (cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) /\
  cstr_at m (md + MD_MARK + MARK_LEN * j) (cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) /\
  (length (cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) < 16)%nat.
Proof.
  intros m md mbs j [[B _] L] MW Hj.
  destruct MW as (_ & _ & _ & _ & _ & R & T). unfold MARKS_MAX in R.
  specialize (T j Hj). unfold MARK_LEN in T. change (Z.to_nat 16) with 16%nat in T.
  unfold MD_SIZE in L.
  assert (LS : length (slice mbs (MD_MARK + 16 * j) 16) = 16%nat)
    by (rewrite c3l_slice_length; unfold MD_MARK; lia).
  split; [|split].
  - unfold md_marks. rewrite nth_error_map, nth_error_seq.
    replace (Z.to_nat j <? Z.to_nat (md_n_mark mbs))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [option_map Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
  - unfold MARK_LEN.
    pose proof (c3l_bytes_at_slice m md mbs (MD_MARK + 16 * j) 16 B ltac:(unfold MD_MARK; lia) ltac:(lia)
                  ltac:(unfold MD_MARK; lia)) as BS.
    destruct (c3l_cstr_split (slice mbs (MD_MARK + 16 * j) 16) ltac:(rewrite LS; lia)) as (rest & E & Nn).
    replace (md + MD_MARK + 16 * j) with (md + (MD_MARK + 16 * j)) by lia.
    split; [|exact Nn]. rewrite E in BS. rewrite app_assoc in BS.
    exact (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) BS)).
  - unfold MARK_LEN, cstr. rewrite length_firstn. lia.
Qed.

(* ==========================================================================
   3. bcmp(buf, "reac-pw:served", 15) over a C string in buf
   ========================================================================== *)

Lemma c3l_no_nul_check : forall l, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (zb 0) l.
Proof.
  intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). discriminate H.
Qed.

Lemma c3l_served_nonul : ~ In (zb 0) S_SERVED.
Proof. apply c3l_no_nul_check. vm_compute. reflexivity. Qed.

(* it stops at the first difference, at the latest at the string's NUL *)
Lemma c3l_memcmp_walk : forall p s, ~ In (zb 0) s -> ~ In (zb 0) p ->
  exists v, StrFun.memcmp_model (s ++ [zb 0]) (p ++ [zb 0]) (S (length p)) = Some v /\ -256 < v < 256 /\
            (v = 0 <-> s = p).
Proof.
  induction p as [|b p IH]; intros s Ns Np.
  - destruct s as [|a s].
    + exists 0. split; [reflexivity|]. split; [lia|]. tauto.
    + assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply c3l_byte_zero; exact E).
      pose proof (StrFun.byte_range a) as Ra.
      exists (bv_unsigned a - bv_unsigned (zb 0)). split.
      * cbn [app StrFun.memcmp_model length].
        replace (bv_unsigned a =? bv_unsigned (zb 0)) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. change (bv_unsigned (zb 0)) with 0. exact Ha.
      * change (bv_unsigned (zb 0)) with 0. split; [lia|]. split; [lia | discriminate].
  - assert (Hb : bv_unsigned b <> 0) by (intros E; apply Np; left; apply c3l_byte_zero; exact E).
    pose proof (StrFun.byte_range b) as Rb.
    destruct s as [|a s].
    + exists (bv_unsigned (zb 0) - bv_unsigned b). split.
      * cbn [app StrFun.memcmp_model length].
        replace (bv_unsigned (zb 0) =? bv_unsigned b) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. change (bv_unsigned (zb 0)) with 0. lia.
      * change (bv_unsigned (zb 0)) with 0. split; [lia|]. split; [lia | discriminate].
    + assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply c3l_byte_zero; exact E).
      pose proof (StrFun.byte_range a) as Ra.
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
      * apply c3l_byte_eq in Eab. subst b.
        destruct (IH s (fun H => Ns (or_intror H)) (fun H => Np (or_intror H))) as (v & Hv & Rv & Iv).
        exists v. split.
        -- cbn [app StrFun.memcmp_model length]. rewrite Z.eqb_refl. exact Hv.
        -- split; [exact Rv|]. rewrite Iv.
           split; [intros ->; reflexivity | intros H; injection H as H; exact H].
      * exists (bv_unsigned a - bv_unsigned b). split.
        -- cbn [app StrFun.memcmp_model length].
           replace (bv_unsigned a =? bv_unsigned b) with false by (symmetry; apply Z.eqb_neq; exact Nab).
           reflexivity.
        -- split; [lia|]. split; [lia | intros H; injection H as H _; subst b; contradiction].
Qed.

Lemma c3l_bcmp_served : forall s, ~ In (zb 0) s ->
  exists v, StrFun.memcmp_model (s ++ [zb 0]) (S_SERVED ++ [zb 0]) 15 = Some v /\ -256 < v < 256 /\
            (v = 0 <-> bl_eqb s S_SERVED = true).
Proof.
  intros s Ns. destruct (c3l_memcmp_walk S_SERVED s Ns c3l_served_nonul) as (v & Hv & Rv & Iv).
  exists v. split; [exact Hv|]. split; [exact Rv|]. rewrite bl_eqb_iff. exact Iv.
Qed.

(* ==========================================================================
   4. The model: the reader's answer, the chunk state, one round of `unmark`
   ========================================================================== *)

Lemma c3l_rd32_range : forall c off, 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off. unfold rd32, link_spec.rdn. pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as H1.
  assert (L : (length (slice c off 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (slice c off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  set (q := 2 ^ (8 * Z.of_nat (length (slice c off 4)))) in *. lia.
Qed.

Lemma c3l_rd32s_range : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s. cbv zeta. pose proof (c3l_rd32_range c off) as R.
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)); lia.
Qed.

Lemma c3l_msg_scan_err : forall fuel c off left code, msg_scan fuel c off left = NlErr code ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros c off left code H; cbn [msg_scan] in H; [discriminate|].
  destruct (left <? NL_HDR); [discriminate|].
  destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off)); [discriminate|].
  destruct (rd16 c (off + 4) =? NL_ERROR).
  - destruct (rd32 c off <? NL_HDR + NL_ERR_BODY); [discriminate|]. injection H as <-. apply c3l_rd32s_range.
  - destruct (rd16 c (off + 4) =? RTM_NEWLINK); [discriminate|]. exact (IH _ _ _ _ H).
Qed.

Lemma c3l_chunk_loop_err : forall fuel cs i code j, chunk_loop fuel cs i = (NlErr code, j) ->
  - 2 ^ 31 <= code < 2 ^ 31.
Proof.
  induction fuel as [|f IH]; intros cs i code j H; cbn [chunk_loop] in H; [discriminate|].
  destruct (nth_error cs i) as [c|]; [|discriminate].
  destruct (chunk_walk c) as [| |code'|a] eqn:E.
  - exact (IH _ _ _ _ H).
  - discriminate.
  - injection H as <- _. exact (c3l_msg_scan_err _ _ _ _ _ E).
  - discriminate.
Qed.

Lemma c3l_talk_rc_range : forall K, 0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < talk_rc_lib K < 2 ^ 32.
Proof.
  intros K Hs Hd He. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j] eqn:E.
  destruct v as [| |code|a]; simpl.
  - lia.
  - unfold E_IO. lia.
  - pose proof (c3l_chunk_loop_err _ _ _ _ _ E). lia.
  - lia.
Qed.

Lemma c3l_read_rc_range : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < r_rc (read_core tab nm kc ac reqs K) < 2 ^ 32.
Proof.
  intros tab nm kc ac reqs K Hs Hd He. unfold read_core.
  destruct nm as [s|]; [|cbn [r_rc]; unfold E_INVAL; lia]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [cbn [r_rc]; unfold E_INVAL; lia|].
  destruct (index_of tab s =? 0); [cbn [r_rc]; unfold E_NODEV; lia|].
  cbn [r_rc]. apply c3l_talk_rc_range; assumption.
Qed.

(* the model's answer to a read: a small number, 0 exactly when the reader's is *)
Lemma c3l_read_rc : forall nm mbs kbs, model_wf mbs -> nlk_wf kbs ->
  - 2 ^ 32 < norm_rc (r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))) < 2 ^ 32 /\
  (norm_rc (r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))) = 0 <->
   r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)) = 0).
Proof.
  intros nm mbs kbs (_ & _ & Hs & Hd & _) (_ & _ & _ & _ & _ & _ & _ & _ & He & _).
  pose proof (c3l_read_rc_range link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs) Hs Hd He) as R.
  set (x := r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))) in *.
  unfold norm_rc, RC_FAILS. destruct (Z.ltb_spec 0 x); (split; [lia | split; intros; lia]).
Qed.

Lemma c3l_talk_after_ce : forall K, k_chunks (talk_after K) = k_chunks K /\ k_end (talk_after K) = k_end K.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

Lemma c3l_read_ce : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K /\
  k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros. unfold read_core. destruct nm as [s|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply c3l_talk_after_ce.
Qed.

Lemma c3l_write_ce : forall tab nm al reqs K,
  k_chunks (w_state (write_core tab nm al reqs K)) = k_chunks K /\
  k_end (w_state (write_core tab nm al reqs K)) = k_end K.
Proof.
  intros. unfold write_core. destruct nm as [s|]; [|split; reflexivity].
  destruct al as [a|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply c3l_talk_after_ce.
Qed.

(* the model's view of the exchange, from its three cells and the fake kernel's chunks *)
Lemma c3l_md_kstate : forall mbs kbs K, k_chunks K = nk_chunks kbs -> k_end K = nk_end_errno kbs ->
  md_next mbs = Z.of_nat (k_next K) -> md_socket_errno mbs = k_sock K -> md_send_errno mbs = k_send K ->
  md_kstate mbs kbs = K.
Proof.
  intros mbs kbs [c n e s d] H1 H2 H3 H4 H5. cbn [k_chunks k_next k_end k_sock k_send] in *.
  unfold md_kstate. rewrite <- H1, <- H2, H3, H4, H5, Nat2Z.id. reflexivity.
Qed.

Lemma c3l_uw_cons : forall tab nm rest reqs K, unmark_walk tab (nm :: rest) reqs K =
  if negb (r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) =? 0)
  then unmark_walk tab rest (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                   (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
  else if negb (bl_eqb (r_alias (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) S_SERVED)
  then unmark_walk tab rest (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                   (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
  else unmark_walk tab rest
         (w_reqs (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                    (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))))
         (w_state (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
                    (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K)))).
Proof. reflexivity. Qed.

(* one round of the walk that skips the write: the read failed, or the alias is not ours *)
Lemma c3l_step_skip : forall tab names j nm reqs K U, 0 <= j -> nth_error names (Z.to_nat j) = Some nm ->
  unmark_walk tab (skipn (Z.to_nat j) names) reqs K = U ->
  (r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) <> 0 \/
   bl_eqb (r_alias (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) S_SERVED = false) ->
  unmark_walk tab (skipn (Z.to_nat (j + 1)) names) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
    (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) = U.
Proof.
  intros tab names j nm reqs K U Hj Hn UW Hc.
  rewrite (c3l_skipn_nth _ _ _ Hn), c3l_uw_cons in UW.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  destruct (r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) =? 0) eqn:E.
  - destruct Hc as [Hc|Hc]; [apply Z.eqb_eq in E; contradiction|].
    rewrite Hc in UW. cbn [negb] in UW. exact UW.
  - cbn [negb] in UW. exact UW.
Qed.

(* one round of the walk that writes the empty alias *)
Lemma c3l_step_write : forall tab names j nm reqs K U, 0 <= j -> nth_error names (Z.to_nat j) = Some nm ->
  unmark_walk tab (skipn (Z.to_nat j) names) reqs K = U ->
  r_rc (read_core tab (Some nm) 0 ALIAS_MAX reqs K) = 0 ->
  bl_eqb (r_alias (read_core tab (Some nm) 0 ALIAS_MAX reqs K)) S_SERVED = true ->
  unmark_walk tab (skipn (Z.to_nat (j + 1)) names)
    (w_reqs (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
               (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K))))
    (w_state (write_core tab (Some nm) (Some []) (r_reqs (read_core tab (Some nm) 0 ALIAS_MAX reqs K))
               (r_state (read_core tab (Some nm) 0 ALIAS_MAX reqs K)))) = U.
Proof.
  intros tab names j nm reqs K U Hj Hn UW H0 Hs.
  rewrite (c3l_skipn_nth _ _ _ Hn), c3l_uw_cons in UW.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  rewrite H0, Hs in UW. cbn [negb Z.eqb] in UW. exact UW.
Qed.

(* ==========================================================================
   5. Where the slot's pieces lie, and what a call may write
   ========================================================================== *)

Lemma c3l_lenv_nums : forall E, lenv_ok E ->
  0x960e0 + SLOT_STACK_Z <= e_S E /\ e_S E <= 2 ^ 47 /\ 4096 <= e_md E /\
  e_md E + MD_SIZE <= e_S E - SLOT_STACK_Z /\ (e_md E + MD_SIZE <= 0x10000 \/ 0x97000 <= e_md E).
Proof.
  intros E (H1 & H2 & _ & Bmd & _).
  pose proof (c3_blk_img _ _ _ Bmd ltac:(unfold MD_SIZE; lia)) as I.
  destruct Bmd as (B1 & B2 & _). repeat split; assumption.
Qed.

(* the write set of a call in the loop: the stack below the frame, the model block, the 256-byte buffer *)
Definition c3l_Wz (E : lenv) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE);
   (e_S E - SLOT_FRAME + FO_B256, e_S E - SLOT_FRAME + FO_B256 + 256)].

Lemma c3l_Wz_sub : forall E, lenv_ok E -> sub_fp (c3l_Wz E) (c3_W E).
Proof.
  intros E HE. pose proof (c3l_lenv_nums E HE) as (H1 & H2 & H3 & H4 & _).
  unfold sub_fp, c3l_Wz, c3_W. cbn [outside]. intros x (X1 & X2 & X3 & X4 & X5 & X6 & _).
  unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256 in *. repeat split; try exact I; lia.
Qed.

Lemma c3l_Wz_task : forall E x, lenv_ok E -> 0 <= x < 2 ^ 64 -> ~ outside (c3l_Wz E) x -> x < TASK_SIZE.
Proof.
  intros E x HE _ HO. pose proof (c3l_lenv_nums E HE) as (H1 & H2 & H3 & H4 & _).
  assert (TS : TASK_SIZE = 2 ^ 47) by (vm_compute; reflexivity). rewrite TS.
  unfold c3l_Wz in HO. cbn [outside] in HO. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *.
  destruct (Z_lt_dec x (e_S E)) as [L|L]; [lia|].
  exfalso. apply HO. repeat split; try exact I; lia.
Qed.

Lemma c3l_dj_static : forall E a n, lenv_ok E -> 0x10000 <= a -> a + n <= 0x960e0 ->
  disjoint_from (c3l_Wz E) a n.
Proof.
  intros E a n HE Ha Hn. pose proof (c3l_lenv_nums E HE) as (H1 & H2 & H3 & H4 & H5).
  unfold c3l_Wz. cbn [disjoint_from]. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *.
  repeat split; try exact I; lia.
Qed.

(* the frame's cells: the first 120 bytes, then the 256-byte buffer at sp + 0x78 *)
Definition c3l_lh11 (md mk P N : Z) (j0 j1 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N); CB 40 j1].

Lemma c3l_frame_split : forall m A md mk P N j0 j1 j2,
  rw_cells rsegs m A (lh_cells md mk P N j0 j1 j2) <->
  rw_cells rsegs m A (c3l_lh11 md mk P N j0 j1) /\ rw_cells rsegs m (A + FO_B256) [CB 256 j2].
Proof.
  intros m A md mk P N j0 j1 j2.
  change (lh_cells md mk P N j0 j1 j2) with (c3l_lh11 md mk P N j0 j1 ++ [CB 256 j2]).
  rewrite c3_rw_cells_app. reflexivity.
Qed.

(* c3_mem survives a write set inside c3l_Wz that gives back the model block and the buffer *)
Lemma c3l_keep : forall E P N kbs mbs mbs' gbs m m',
  lenv_ok E -> c3_mem E P N kbs mbs gbs m ->
  munch (c3l_Wz E) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  model_at m' (e_md E) mbs' -> model_wf mbs' ->
  (exists j2, rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_B256) [CB 256 j2]) ->
  c3_mem E P N kbs mbs' gbs m'.
Proof.
  intros E P N kbs mbs mbs' gbs m m' HE CM MU WM MI' ST' MA' MW' (j2' & B').
  destruct CM as ((j0 & j1 & j2 & FR) & SAV & NL & NW & IT & GN & OD & PR & LA & TX & IP & _ & _ & MK & MKW &
                  CU & ER & GU & _ & TM & _).
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof HE as (_ & _ & _ & _ & (Bk1 & Bk2 & _) & _ & _ & Amk & _ & (Bp1 & Bp2 & _) & Apm & _ & Hsv).
  assert (DS : forall a n, 0x10000 <= a -> a + n <= 0x960e0 -> disjoint_from (c3l_Wz E) a n)
    by (intros a n Ha Hn; exact (c3l_dj_static E a n HE Ha Hn)).
  apply c3l_frame_split in FR. destruct FR as [F1 _].
  unfold c3_mem.
  split.
  { exists j0, j1, j2'. apply c3l_frame_split. split; [|exact B'].
    eapply (rw_cells_transport rsegs); [exact F1 | exact MU | exact WM |].
    change (cells_size (c3l_lh11 (e_md E) (e_mk E) P N j0 j1)) with 120%nat.
    unfold c3l_Wz. cbn [disjoint_from]. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *.
    repeat split; try exact I; lia. }
  split.
  { eapply (bytes_at_transport rsegs); [exact SAV | exact MU |]. rewrite Hsv.
    unfold c3l_Wz. cbn [disjoint_from]. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *.
    repeat split; try exact I; lia. }
  split.
  { destruct NL as [U L]. split; [|exact L]. eapply (u8arr_transport rsegs); [exact U | exact MU | exact WM |].
    apply DS; rewrite ?L; unfold A_G_NL, NK_SIZE; lia. }
  split; [exact NW|].
  split.
  { eapply c3_iftab_tr; [exact IT | exact IP | exact MU | reflexivity | apply DS | apply DS | apply DS | apply DS];
      unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX, A_G_NAMES, G_NAMES_SIZE; lia. }
  split; [eapply c3_gnames_tr; [exact GN | exact MU | apply DS]; unfold A_G_NAMES, G_NAMES_SIZE; lia|].
  split; [eapply c3_odd_tr; [exact OD | exact MU | apply DS | apply DS]; unfold A_ODD; lia|].
  split; [eapply c3_policy_tr; [exact PR | exact MU | apply DS]; lia|].
  split; [eapply c3_la_tr; [exact LA | exact MU | exact WM | apply DS]; unfold A_LONG_ALIAS, LONG_ALIAS_SIZE; lia|].
  split; [eapply c3_texts_tr; [exact TX | exact MU | apply DS]; unfold A_TEXTS; lia|].
  split; [eapply c3_ifptrs_tr; [exact IP | exact MU | apply DS]; unfold A_G_NL, NK_IF_NAME; lia|].
  split; [exact MA'|].
  split; [exact MW'|].
  split.
  { destruct MK as [U L]. split; [|exact L]. eapply (u8arr_transport rsegs); [exact U | exact MU | exact WM |].
    rewrite L. unfold c3l_Wz. cbn [disjoint_from]. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE, MK_SIZE in *.
    repeat split; try exact I; lia. }
  split; [exact MKW|].
  split.
  { eapply c3_cursor_tr; [exact CU | exact MU |].
    unfold c3l_Wz. cbn [disjoint_from]. unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *.
    repeat split; try exact I; lia. }
  split; [exact (wr_at_transport rsegs m m' _ _ ER WM)|].
  split; [eapply c3_guard_tr; [exact GU | exact MU | apply DS | apply DS]; unfold A_GOT_GUARD_S, A_GUARD_S; lia|].
  split; [exact MI'|].
  split.
  { eapply (c3_task_mem_munch (c3l_Wz E)); [exact TM | exact MU |]. intros x Hx HO.
    exact (c3l_Wz_task E x HE Hx HO). }
  exact ST'.
Qed.

(* the pointer a reader finds in if_name[i]: interfaces()'s pointer, up to the word's wrap *)
Lemma c3l_ptr_mod : forall m i n2 ix p, ifptrs_at m -> nth_error link_tab i = Some (n2, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  exists q k, p = q + 18446744073709551616 * k /\ 0x10000 <= q /\ q + Z.of_nat (length n2) + 1 <= 0x743f8.
Proof.
  intros m i n2 ix p HP Hn Hu.
  destruct (c3_link_tab_home i n2 ix Hn) as (Hi & Hh).
  pose proof (HP i Hi) as Hq. unfold u64_at in Hu, Hq.
  pose proof (c3_bytes_at_same _ _ _ _ Hu Hq ltac:(rewrite !length_le8; reflexivity)) as E.
  apply c3_le8_inj in E. unfold wz in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E.
  pose proof (c3_link_ptr_range i Hi) as R. unfold A_G_NAMES, G_NAMES_SIZE in R, Hh.
  rewrite (Z.mod_small (nth i link_ptrs 0)) in E by lia.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as D.
  exists (nth i link_ptrs 0), (p / 2 ^ 64). split; [|split]; [rewrite E in D; lia | lia | lia].
Qed.

(* ==========================================================================
   6. model_read and model_write at the loop's call sites
   ========================================================================== *)

Definition c3l_rd_pre : bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [model_read_contract] in model_read_contract with
        | leaf _ _ ?P _ _ => exact P end).
Definition c3l_rd_wr : bvmap 5 word -> (word -> option byte) -> list ivl :=
  ltac:(lazymatch eval cbv delta [model_read_contract] in model_read_contract with
        | leaf _ _ _ ?W _ => exact W end).
Definition c3l_rd_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [model_read_contract] in model_read_contract with
        | leaf _ _ _ _ ?Q => exact Q end).
Definition c3l_wr_pre : bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [model_write_contract] in model_write_contract with
        | leaf _ _ ?P _ _ => exact P end).
Definition c3l_wr_wr : bvmap 5 word -> (word -> option byte) -> list ivl :=
  ltac:(lazymatch eval cbv delta [model_write_contract] in model_write_contract with
        | leaf _ _ _ ?W _ => exact W end).
Definition c3l_wr_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [model_write_contract] in model_write_contract with
        | leaf _ _ _ _ ?Q => exact Q end).

(* model_read (m, &m->mark[j], NULL, 0, sp + 0x78, 256) at 0x13b74 *)
Lemma c3l_read_pre : forall E P N kbs mbs gbs m j regs,
  lenv_ok E -> c3_mem E P N kbs mbs gbs m -> 0 <= j < md_n_mark mbs ->
  spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_md E -> arg regs 1 = e_md E + MD_MARK + MARK_LEN * j ->
  arg regs 2 = 0 -> arg regs 3 = 0 -> arg regs 4 = e_S E - SLOT_FRAME + FO_B256 -> arg regs 5 = 256 ->
  c3l_rd_pre regs m.
Proof.
  intros E P N kbs mbs gbs m j regs HE CM Hj SP A0 A1 A2 A3 A4 A5.
  destruct CM as ((j0 & j1 & j2 & FR) & _ & NL & NW & IT & _ & _ & _ & _ & _ & IP & MDA & MDW & _).
  apply c3l_frame_split in FR. destruct FR as [_ B256].
  destruct (c3l_slot m (e_md E) mbs j MDA MDW Hj) as (_ & Cn & Ln).
  set (nm := cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) in *.
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof (c3l_nmark_le mbs MDW) as Hn32.
  unfold c3l_rd_pre, frame_apart_gnl, apart_frame. cbv beta.
  rewrite SP, A0, A1, A2, A3, A4, A5.
  exists mbs, kbs, link_tab, (Some nm).
  unfold SLOT_FRAME, SLOT_STACK_Z, FO_B256, MD_SIZE, MD_MARK, MARK_LEN, apart_gnl, apart, A_G_NL, NK_SIZE in *.
  split; [exact MDA|]. split; [exact MDW|]. split; [exact NL|]. split; [lia|].
  split; [exact NW|]. split; [exact IT|]. split; [split; [lia | exact Cn]|].
  split; [intros H; exfalso; apply H; reflexivity|].
  split; [intros _ _; exists j2; exact B256|].
  split; [lia|]. split; [lia|].
  split; [intros _ s Hs; injection Hs as <-; lia|].
  split; [intros H; lia|]. split; [intros _; lia|].
  split.
  { intros i n2 ix p Hn Hu. destruct (c3l_ptr_mod m i n2 ix p IP Hn Hu) as (q & k & -> & Q1 & Q2).
    destruct (Z.lt_trichotomy k 0) as [K|[K|K]]; [left | left | right]; lia. }
  split; [intros s Hs; injection Hs as <-; split; intros; lia|].
  split; [intros H; exfalso; lia|].
  split.
  { intros _ _. split; [lia|]. split; [lia|].
    intros i n2 ix p Hn Hu. destruct (c3l_ptr_mod m i n2 ix p IP Hn Hu) as (q & k & -> & Q1 & Q2).
    destruct (Z.lt_trichotomy k 0) as [K|[K|K]]; [right | right | left]; lia. }
  intros H; exfalso; lia.
Qed.

Lemma c3l_read_post : forall regs m regs' m', c3l_rd_post regs m regs' m' ->
  forall mbs kbs nm md a b,
  arg regs 0 = md -> arg regs 1 = a -> arg regs 2 = 0 -> arg regs 3 = 0 -> arg regs 4 = b -> arg regs 5 = 256 ->
  b <> 0 -> model_at m md mbs -> nlk_at m kbs -> iftab_at m kbs link_tab -> a <> 0 -> cstr_at m a nm ->
  reg_get regs' 10 = wz (norm_rc (r_rc (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))) /\
  (exists mbs', model_at m' md mbs' /\ model_wf mbs' /\
     md_next mbs' = Z.of_nat (k_next (r_state (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))) /\
     md_socket_errno mbs' = k_sock (r_state (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))) /\
     md_send_errno mbs' = k_send (r_state (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))) /\
     md_reqs mbs' = r_reqs (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)) /\
     md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs) /\
  cstr_at m' b (r_alias (read_core link_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))) /\
  (exists junk, rw_cells rsegs m' b [CB 256 junk]).
Proof.
  intros regs m regs' m' PO mbs kbs nm md a b A0 A1 A2 A3 A4 A5 Hb MA NL IT Ha Cn.
  unfold c3l_rd_post in PO. cbv beta in PO. rewrite A0, A1, A2, A3, A4, A5 in PO.
  specialize (PO mbs kbs link_tab (Some nm) MA NL IT (conj Ha Cn)). cbv zeta in PO.
  destruct PO as (R10 & (mbs' & X1 & X2 & X3 & X4 & X5 & X6 & _ & X7 & X8) & _ & Cal & _ & Bj).
  split; [rewrite <- c3l_getr10; exact R10|].
  split; [exists mbs'; exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 X8)))))))|].
  split; [exact (Cal Hb ltac:(lia))|].
  exact (Bj Hb ltac:(lia)).
Qed.

Lemma c3l_empty_slack : forall m, mem_inv rsegs m ->
  bytes_at rsegs m (A_EMPTY + Z.of_nat (length (@nil byte)) + 1) (map (Z_to_bv 8) [46; 0; 117; 115; 97; 103; 101]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_EMPTY; cbn; lia | cbn; unfold A_EMPTY; lia |].
  unfold A_EMPTY. vm_compute. repeat split; reflexivity.
Qed.

(* model_write (m, &m->mark[j], "") at 0x13ba4 *)
Lemma c3l_write_pre : forall E P N kbs mbs gbs m j regs,
  lenv_ok E -> c3_mem E P N kbs mbs gbs m -> 0 <= j < md_n_mark mbs ->
  spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_md E -> arg regs 1 = e_md E + MD_MARK + MARK_LEN * j ->
  arg regs 2 = A_EMPTY -> c3l_wr_pre regs m.
Proof.
  intros E P N kbs mbs gbs m j regs HE CM Hj SP A0 A1 A2.
  destruct CM as (_ & _ & NL & NW & IT & _ & _ & (_ & _ & _ & Cemp) & _ & _ & IP & MDA & MDW & _ & _ & _ & _ & _ &
                  MI & _).
  destruct (c3l_slot m (e_md E) mbs j MDA MDW Hj) as (_ & Cn & Ln).
  set (nm := cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) in *.
  pose proof (c3l_lenv_nums E HE) as (HS1 & HS2 & Hm1 & Hm2 & Imd).
  pose proof (c3l_nmark_le mbs MDW) as Hn32.
  pose proof (c3l_empty_slack m MI) as SL.
  unfold c3l_wr_pre, frame_apart_gnl, apart_frame. cbv beta.
  rewrite SP, A0, A1, A2.
  exists mbs, kbs, link_tab, (Some nm), (Some []).
  unfold SLOT_FRAME, SLOT_STACK_Z, MD_SIZE, MD_MARK, MARK_LEN, apart_gnl, A_G_NL, NK_SIZE in *.
  split; [exact MDA|]. split; [exact MDW|]. split; [exact NL|]. split; [lia|].
  split; [exact NW|]. split; [exact IT|]. split; [split; [lia | exact Cn]|].
  split; [split; [unfold A_EMPTY; lia | exact Cemp]|].
  split; [lia|]. split; [lia|].
  split; [intros s Hs; injection Hs as <-; lia|].
  split; [intros s Hs; injection Hs as <-; cbn [length]; unfold A_EMPTY; lia|].
  split.
  { intros s Hs; injection Hs as <-. eexists. split; [exact SL|]. apply Z.leb_le. vm_compute. reflexivity. }
  intros i n2 ix p Hn Hu. destruct (c3l_ptr_mod m i n2 ix p IP Hn Hu) as (q & k & -> & Q1 & Q2).
  destruct (Z.lt_trichotomy k 0) as [K|[K|K]]; [left | left | right]; lia.
Qed.

Lemma c3l_write_post : forall regs m regs' m', c3l_wr_post regs m regs' m' ->
  forall mbs kbs nm md a,
  arg regs 0 = md -> arg regs 1 = a -> arg regs 2 = A_EMPTY ->
  model_at m md mbs -> nlk_at m kbs -> iftab_at m kbs link_tab -> a <> 0 -> cstr_at m a nm -> cstr_at m A_EMPTY [] ->
  exists mbs', model_at m' md mbs' /\ model_wf mbs' /\
     md_next mbs' = Z.of_nat (k_next (w_state (write_core link_tab (Some nm) (Some []) (md_reqs mbs) (md_kstate mbs kbs)))) /\
     md_socket_errno mbs' = k_sock (w_state (write_core link_tab (Some nm) (Some []) (md_reqs mbs) (md_kstate mbs kbs))) /\
     md_send_errno mbs' = k_send (w_state (write_core link_tab (Some nm) (Some []) (md_reqs mbs) (md_kstate mbs kbs))) /\
     md_reqs mbs' = w_reqs (write_core link_tab (Some nm) (Some []) (md_reqs mbs) (md_kstate mbs kbs)) /\
     md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs.
Proof.
  intros regs m regs' m' PO mbs kbs nm md a A0 A1 A2 MA NL IT Ha Cn Ce.
  unfold c3l_wr_post in PO. cbv beta in PO. rewrite A0, A1, A2 in PO.
  assert (Hne : A_EMPTY <> 0) by (unfold A_EMPTY; lia).
  specialize (PO mbs kbs link_tab (Some nm) (Some []) MA NL IT (conj Ha Cn) (conj Hne Ce)).
  cbv zeta in PO.
  destruct PO as (_ & (mbs' & X1 & X2 & X3 & X4 & X5 & X6 & _ & X7 & X8)).
  exists mbs'. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 X8))))))).
Qed.

(* the two calls' write sets, inside c3l_Wz *)
Lemma c3l_rd_fp : forall E regs m (sp : word), lenv_ok E -> bv_unsigned sp = e_S E - SLOT_FRAME ->
  arg regs 0 = e_md E -> arg regs 2 = 0 -> arg regs 4 = e_S E - SLOT_FRAME + FO_B256 -> arg regs 5 = 256 ->
  sub_fp ((bv_unsigned sp - 240, bv_unsigned sp) :: c3l_rd_wr regs m) (c3l_Wz E).
Proof.
  intros E regs m sp HE SP A0 A2 A4 A5. pose proof (c3l_lenv_nums E HE) as (H1 & H2 & H3 & H4 & _).
  unfold c3l_rd_wr. cbv beta. rewrite SP, A0, A2, A4, A5.
  replace (e_S E - SLOT_FRAME + FO_B256 =? 0) with false
    by (symmetry; apply Z.eqb_neq; unfold SLOT_FRAME, SLOT_STACK_Z, FO_B256 in *; lia).
  unfold sub_fp, c3l_Wz. cbn [outside Z.eqb]. intros x (X1 & X2 & X3 & _).
  unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *. repeat split; try exact I; lia.
Qed.

Lemma c3l_wr_fp : forall E regs m (sp : word), lenv_ok E -> bv_unsigned sp = e_S E - SLOT_FRAME ->
  arg regs 0 = e_md E -> sub_fp ((bv_unsigned sp - 704, bv_unsigned sp) :: c3l_wr_wr regs m) (c3l_Wz E).
Proof.
  intros E regs m sp HE SP A0. pose proof (c3l_lenv_nums E HE) as (H1 & H2 & H3 & H4 & _).
  unfold c3l_wr_wr. cbv beta. rewrite SP, A0.
  unfold sub_fp, c3l_Wz. cbn [outside]. intros x (X1 & X2 & X3 & _).
  unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *. repeat split; try exact I; lia.
Qed.

Lemma c3l_wr_buf_dj : forall E regs m (sp : word), lenv_ok E -> bv_unsigned sp = e_S E - SLOT_FRAME ->
  arg regs 0 = e_md E ->
  disjoint_from ((bv_unsigned sp - 704, bv_unsigned sp) :: c3l_wr_wr regs m) (e_S E - SLOT_FRAME + FO_B256) 256.
Proof.
  intros E regs m sp HE SP A0. pose proof (c3l_lenv_nums E HE) as (H1 & H2 & H3 & H4 & _).
  unfold c3l_wr_wr. cbv beta. rewrite SP, A0. cbn [disjoint_from].
  unfold SLOT_STACK_Z, SLOT_FRAME, FO_B256, MD_SIZE in *. repeat split; try exact I; lia.
Qed.

(* the arguments of a register map in mkR form *)
Ltac c3l_arg_solve :=
  first [ rewrite c3l_spZ | rewrite c3l_arg0 | rewrite c3l_arg1 | rewrite c3l_arg2 | rewrite c3l_arg3
        | rewrite c3l_arg4 | rewrite c3l_arg5 ];
  repeat (rewrite unsigned_lit; [|unfold SLOT_FRAME, SLOT_STACK_Z, FO_B256, MD_MARK, MARK_LEN, MD_SIZE, A_EMPTY in *; lia]);
  first [ reflexivity | unfold SLOT_FRAME, SLOT_STACK_Z, FO_B256, MD_MARK, MARK_LEN, MD_SIZE, A_EMPTY in *; lia ].
