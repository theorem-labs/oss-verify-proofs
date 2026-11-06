(* talk (fuzz_link.c:333-384), PLAIN build: the walk of talk_contract (lib/Prog/talk_c.v).

   The code at 0x156e4 (964 bytes, link/ct/dis/plain/talk.s) is walked in pieces stated in
   lib/Prog/talk_defs.v and lib/Prog/talk_pro.v; this file composes them:
     0x156e4 P_pro      the frame and the 13 saved registers
     0x1571c            the socket errno and the send errno of the model block (each used once)
     0x15740            owe: the request into the model's ring (memcpy), its length, the count
     0x1579c            the cursor against g_nl.n_chunks, then F_chunk (the chunk and message
                        loops) or the end errno
     0x158a0 P_spill    the RTM_NEWLINK arm's spills, then F_attr (attributes, kind, take_text)
     0x1584c F_exit     the epilogue
   The specs of the model block are link_spec's talk_core / talk_rc_model / talk_after /
   talk_owes / talk_attrs over md_kstate. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf talk_c talk_defs talk_kit talk_model talk_exit talk_pro memcpy_c memcpy
  talk_msg talk_chunk talk_take talk_kind talk_attr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
Local Open Scope Z_scope.

(* ==========================================================================
   1. pure facts
   ========================================================================== *)

Lemma tw_slice_upd_other : forall (l xs : list byte) (p : nat) (o n : Z),
  0 <= o -> 0 <= n -> (p + length xs <= length l)%nat ->
  (o + n <= Z.of_nat p \/ Z.of_nat p + Z.of_nat (length xs) <= o) ->
  slice (upd_bytes l p xs) o n = slice l o n.
Proof.
  intros l xs p o n Ho Hn Hp D. unfold slice. apply nth_error_ext. intros i.
  rewrite !nth_error_firstn, !nth_error_skipn.
  destruct (Nat.ltb_spec i (Z.to_nat n)); [|reflexivity].
  destruct (Nat.ltb_spec (Z.to_nat o + i) (length l)) as [L|L].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec p (Z.to_nat o + i)); destruct (Nat.ltb_spec (Z.to_nat o + i) (p + length xs));
      cbn [andb]; try reflexivity; lia.
  - rewrite !(proj2 (nth_error_None _ _)); [reflexivity | lia | rewrite upd_bytes_length; lia].
Qed.

Lemma tw_fld_upd_other : forall (l xs : list byte) (p : nat) (o : Z),
  0 <= o -> (p + length xs <= length l)%nat ->
  (o + 4 <= Z.of_nat p \/ Z.of_nat p + Z.of_nat (length xs) <= o) ->
  fld_u32 (upd_bytes l p xs) o = fld_u32 l o.
Proof.
  intros l xs p o Ho Hp D. unfold fld_u32, link_spec.rdn. rewrite tw_slice_upd_other by lia. reflexivity.
Qed.

Lemma tw_core_sock : forall K, k_sock K <> 0 ->
  talk_rc_model K = norm_rc (- k_sock K) /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 (k_send K) /\ talk_owes K = false.
Proof.
  intros K H. unfold talk_rc_model, talk_rc_lib, talk_attrs, talk_after, talk_owes, talk_core.
  destruct (Z.eqb_spec (k_sock K) 0); [contradiction|]. cbn. repeat split.
Qed.

Lemma tw_core_send : forall K, k_sock K = 0 -> k_send K <> 0 ->
  talk_rc_model K = norm_rc (- k_send K) /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 0 /\ talk_owes K = false.
Proof.
  intros K H1 H2. unfold talk_rc_model, talk_rc_lib, talk_attrs, talk_after, talk_owes, talk_core.
  rewrite H1. destruct (Z.eqb_spec (k_send K) 0); [contradiction|]. cbn. repeat split.
Qed.

Definition tw_rc (v : nlv) (e : Z) : Z :=
  match v with NlNone => - e | NlShort => - E_IO | NlErr c => c | NlLink _ => 0 end.
Definition tw_at (v : nlv) : attrs := match v with NlLink a => a | _ => no_attrs end.

Lemma tw_core_main : forall K v j, k_sock K = 0 -> k_send K = 0 ->
  chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K) = (v, j) ->
  talk_after K = Kst (k_chunks K) j (k_end K) 0 0 /\ talk_owes K = true /\
  talk_attrs K = tw_at v /\ talk_rc_model K = norm_rc (tw_rc v (k_end K)).
Proof.
  intros K v j H1 H2 H3. unfold talk_rc_model, talk_rc_lib, talk_attrs, talk_after, talk_owes, talk_core.
  rewrite H1, H2. cbn [negb Z.eqb andb]. rewrite H3. destruct v; cbn; repeat split.
Qed.

Lemma tw_cl_bound : forall f cs i v j, chunk_loop f cs i = (v, j) -> (j <= Nat.max i (length cs))%nat.
Proof.
  induction f as [|f IH]; intros cs i v j H; cbn [chunk_loop] in H.
  - inversion H; subst; lia.
  - destruct (nth_error cs i) as [c|] eqn:E.
    + assert (L : (i < length cs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
      destruct (chunk_walk c); try (inversion H; subst; lia).
      specialize (IH cs (S i) v j H). lia.
    + inversion H; subst; lia.
Qed.

Lemma tw_dj_mono : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[x y] W IH]; intros a n n' H Hn; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eauto].
Qed.

Lemma tw_bufs_munch : forall W m1 m2 acc KD KN AD AN,
  bufs m1 acc KD KN AD AN -> munch W m1 m2 -> wmono rsegs m1 m2 ->
  (KD <> 0 -> 1 <= KN -> disjoint_from W KD KN) -> (AD <> 0 -> 1 <= AN -> disjoint_from W AD AN) ->
  bufs m2 acc KD KN AD AN.
Proof.
  intros W m1 m2 acc KD KN AD AN (B1 & B2 & B3 & B4) MU WM D1 D2. split; [|split; [|split]].
  - intros H1 H2. destruct (B1 H1 H2) as [j Hj]. exists j. eapply rw_cells_transport; [exact Hj | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply D1; assumption.
  - intros H1 H2. destruct (B2 H1 H2) as [j Hj]. exists j. eapply rw_cells_transport; [exact Hj | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply D2; assumption.
  - intros pay E H1 H2. destruct (B3 pay E H1 H2) as [Hb Hn]. split; [|exact Hn].
    eapply bytes_at_transport; [exact Hb | exact MU |].
    apply (tw_dj_mono W KD KN); [apply D1; assumption|].
    rewrite length_app. cbn [length]. pose proof (cut_text_len pay KN H2). lia.
  - intros pay E H1 H2. destruct (B4 pay E H1 H2) as [Hb Hn]. split; [|exact Hn].
    eapply bytes_at_transport; [exact Hb | exact MU |].
    apply (tw_dj_mono W AD AN); [apply D2; assumption|].
    rewrite length_app. cbn [length]. pose proof (cut_text_len pay AN H2). lia.
Qed.

Lemma tw_rng : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.

Lemma tw_u8arr_sub : forall m A bs off len, u8arr rsegs m A bs -> 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length bs) ->
  rw_cells rsegs m (A + off) [CB (Z.to_nat len) (slice bs off len)].
Proof.
  intros m A bs off len [Hb (W1 & W2 & W3)] H1 H2 H3. split; [split|].
  - cbn. split; [rewrite tk_slice_length by lia; reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply tk_bytes_slice; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace (A + off + i) with (A + (off + i)) by lia. apply W3. lia.
Qed.

Lemma tw_stk_fin : forall m lo SP cs1 cs2, stk rsegs m lo (SP + -144) ->
  rw_cells rsegs m (SP + -144) cs1 -> cells_size cs1 = 40%nat ->
  rw_cells rsegs m (SP + -104) cs2 -> cells_size cs2 = 104%nat -> lo <= SP + -144 ->
  stk rsegs m lo SP.
Proof.
  intros m lo SP cs1 cs2 S0 C1 L1 C2 L2 Hlo.
  pose proof (stk_release rsegs m lo (SP + -144) cs1 S0 C1 Hlo) as S1. rewrite L1 in S1.
  replace (SP + -144 + Z.of_nat 40) with (SP + -104) in S1 by lia.
  pose proof (stk_release rsegs m lo (SP + -104) cs2 S1 C2 ltac:(lia)) as S2. rewrite L2 in S2.
  replace (SP + -104 + Z.of_nat 104) with SP in S2 by lia. exact S2.
Qed.

Lemma tw_saved_size : forall RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11,
  cells_size (saved_cells RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11) = 104%nat.
Proof. reflexivity. Qed.

Lemma tw_bytes_out : forall W m m' A (bs : list byte), bytes_at rsegs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (H1 & H2 & H) MU HO. split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite MU; [reflexivity|].
  rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma tw_rw_out : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU WM HO. split; [split; [exact Hwf|]|].
  - eapply tw_bytes_out; [exact Hb | exact MU |]. rewrite cells_bytes_length by exact Hwf. exact HO.
  - eapply wr_at_transport; eauto.
Qed.

Lemma tw_u8arr_out : forall W m m' A bs, u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> u8arr rsegs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU WM HO. split; [eapply tw_bytes_out; eauto | eapply wr_at_transport; eauto].
Qed.

Lemma tw_bufs_out : forall W m1 m2 acc KD KN AD AN,
  bufs m1 acc KD KN AD AN -> munch W m1 m2 -> wmono rsegs m1 m2 ->
  (KD <> 0 -> 1 <= KN -> forall x, KD <= x < KD + KN -> outside W x) ->
  (AD <> 0 -> 1 <= AN -> forall x, AD <= x < AD + AN -> outside W x) ->
  bufs m2 acc KD KN AD AN.
Proof.
  intros W m1 m2 acc KD KN AD AN (B1 & B2 & B3 & B4) MU WM D1 D2. split; [|split; [|split]].
  - intros H1 H2. destruct (B1 H1 H2) as [j Hj]. exists j. eapply tw_rw_out; [exact Hj | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply D1; assumption.
  - intros H1 H2. destruct (B2 H1 H2) as [j Hj]. exists j. eapply tw_rw_out; [exact Hj | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply D2; assumption.
  - intros pay E H1 H2. destruct (B3 pay E H1 H2) as [Hb Hn]. split; [|exact Hn].
    eapply tw_bytes_out; [exact Hb | exact MU |]. intros x Hx. apply (D1 H1 H2).
    rewrite length_app in Hx. cbn [length] in Hx. pose proof (cut_text_len pay KN H2). lia.
  - intros pay E H1 H2. destruct (B4 pay E H1 H2) as [Hb Hn]. split; [|exact Hn].
    eapply tw_bytes_out; [exact Hb | exact MU |]. intros x Hx. apply (D2 H1 H2).
    rewrite length_app in Hx. cbn [length] in Hx. pose proof (cut_text_len pay AN H2). lia.
Qed.

Lemma tw_munch_sub : forall W W' m1 m2 m3, munch W m1 m2 -> munch W' m2 m3 ->
  (forall x, outside W x -> outside W' x) -> munch W m1 m3.
Proof. intros W W' m1 m2 m3 H1 H2 HS x Hx. rewrite (H2 x (HS _ Hx)). apply H1, Hx. Qed.

Lemma tw_nlk_read4 : forall m kbs off, nlk_at m kbs -> 0 <= off -> off + 4 <= NK_SIZE ->
  ov_read_bytes rsegs m (Z_to_bv 64 (tG + off)) 4 = Some (le4 (Z_to_bv 64 (fld_u32 kbs off))).
Proof.
  intros m kbs off [[Hb _] L] H1 H2.
  rewrite (tk_read m tG kbs off 4 Hb H1) by lia. f_equal. unfold fld_u32, link_spec.rdn.
  change (Z.of_nat 4) with 4. apply tk_le4. rewrite tk_slice_length by lia. reflexivity.
Qed.

Ltac outs := intros; cbn [outside] in *; repeat split; try exact I; lia.

(* ==========================================================================
   2. the walk, over one call
   ========================================================================== *)

Section Walk.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (mbs kbs req : list byte)
  (SP M R LEN KD KN AD AN : Z).
Hypotheses (ESP : bv_unsigned sp = SP) (EM : bv_unsigned a0 = M) (ER : bv_unsigned a1 = R)
  (ELEN : bv_unsigned a2 = LEN) (EKD : bv_unsigned a3 = KD) (EKN : bv_unsigned a4 = KN)
  (EAD : bv_unsigned a5 = AD) (EAN : bv_unsigned a6 = AN).
Hypotheses (MD : model_at m M mbs) (MWF : model_wf mbs) (NK : nlk_at m kbs)
  (FAG : apart_gnl (SP - 144) 144) (NWF : nlk_wf kbs)
  (RQ : bytes_at rsegs m R req) (RQL : Z.of_nat (length req) = LEN) (LENB : 0 <= LEN <= NL_SENT_LEN)
  (BK : buf_arg m KD KN) (BA : buf_arg m AD AN) (APR : apart R LEN M MD_SIZE)
  (SK : KD <> 0 -> 1 <= KN -> apart_gnl KD KN /\ apart KD KN M MD_SIZE)
  (SA : AD <> 0 -> 1 <= AN -> apart_gnl AD AN /\ apart AD AN M MD_SIZE)
  (SKA : KD <> 0 -> 1 <= KN -> AD <> 0 -> 1 <= AN -> apart KD KN AD AN)
  (AGM : apart_gnl M MD_SIZE) (AFM : apart M MD_SIZE (SP - 144) 144)
  (AFR : apart R LEN (SP - 144) 144)
  (AFK : KD <> 0 -> apart KD KN (SP - 144) 144)
  (AFA : AD <> 0 -> apart AD AN (SP - 144) 144)
  (MI : mem_inv rsegs m) (ST : stk rsegs m lo SP) (LO : lo + 144 <= SP) (SPB : SP < 2 ^ 63)
  (MEMCPY : memcpy_contract) (FCH : F_chunk_spec) (FAT : F_attr_spec).

Definition K0 : kstate := md_kstate mbs kbs.

(* the goal: the `leaf` Post of talk_contract at this call *)
Definition Qf : machine_state -> Prop := fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
  ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
  regs_preserved (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) regs' /\
  munch ((SP - 144, SP) :: [(M, M + MD_SIZE); (KD, KD + bw KD KN); (AD, AD + bw AD AN)]) m m' /\
  wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP /\
  (forall mbs0 kbs0 req0, model_at m M mbs0 -> nlk_at m kbs0 ->
     bytes_at rsegs m R req0 -> Z.of_nat (length req0) = LEN ->
     let K0 := md_kstate mbs0 kbs0 in
     getr regs' 10 = wz (talk_rc_model K0)
     /\ (exists mbs', model_at m' M mbs' /\ model_wf mbs'
           /\ md_next mbs' = Z.of_nat (k_next (talk_after K0))
           /\ md_socket_errno mbs' = 0
           /\ md_send_errno mbs' = k_send (talk_after K0)
           /\ md_n_mark mbs' = md_n_mark mbs0 /\ md_marks mbs' = md_marks mbs0
           /\ md_reqs mbs' = (if talk_owes K0 then owe (md_reqs mbs0) req0 else md_reqs mbs0)
           /\ md_n_req mbs' = Z.of_nat (length (md_reqs mbs')))
     /\ (forall pay, a_kind (talk_attrs K0) = Some pay -> KD <> 0 -> 1 <= KN ->
           cstr_at m' KD (cut_text pay KN))
     /\ (forall pay, a_alias (talk_attrs K0) = Some pay -> AD <> 0 -> 1 <= AN ->
           cstr_at m' AD (cut_text pay AN))
     /\ (a_kind (talk_attrs K0) = None ->
           munch [(M, M + MD_SIZE); (AD, AD + bw AD AN); (SP - 144, SP)] m m')
     /\ (a_alias (talk_attrs K0) = None ->
           munch [(M, M + MD_SIZE); (KD, KD + bw KD KN); (SP - 144, SP)] m m')
     /\ (KD <> 0 -> 1 <= KN -> exists junk, rw_cells rsegs m' KD [CB (Z.to_nat KN) junk])
     /\ (AD <> 0 -> 1 <= AN -> exists junk, rw_cells rsegs m' AD [CB (Z.to_nat AN) junk])).

(* the state of the memory between the prologue and the epilogue *)
Definition ctx (m' : word -> option byte) (mb : list byte) (cslo : list cell) (acc : attrs) : Prop :=
  model_at m' M mb /\ nlk_at m' kbs /\ bufs m' acc KD KN AD AN /\
  rw_cells rsegs m' (SP + -144) cslo /\ cells_size cslo = 40%nat /\
  rw_cells rsegs m' (SP + -104) (saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  stk rsegs m' lo (SP + -144) /\ mem_inv rsegs m' /\ wmono rsegs m m' /\
  munch ((SP - 144, SP) :: [(M, M + MD_SIZE); (KD, KD + bw KD KN); (AD, AD + bw AD AN)]) m m' /\
  (a_kind acc = None -> munch [(M, M + MD_SIZE); (AD, AD + bw AD AN); (SP - 144, SP)] m m') /\
  (a_alias acc = None -> munch [(M, M + MD_SIZE); (KD, KD + bw KD KN); (SP - 144, SP)] m m').

Lemma RNG : 0 <= SP < 2 ^ 64 /\ 0 <= M < 2 ^ 64 /\ 0 <= R < 2 ^ 64 /\ 0 <= LEN < 2 ^ 64 /\
  0 <= KD < 2 ^ 64 /\ 0 <= KN < 2 ^ 64 /\ 0 <= AD < 2 ^ 64 /\ 0 <= AN < 2 ^ 64.
Proof.
  rewrite <- ESP, <- EM, <- ER, <- ELEN, <- EKD, <- EKN, <- EAD, <- EAN.
  repeat split; apply tw_rng.
Qed.

Lemma MBND : M + MD_SIZE <= 2 ^ 64.
Proof. destruct MD as [[Hb _] L]. pose proof (bytes_at_bound rsegs m M mbs Hb). lia. Qed.

Lemma MWF' : 0 <= md_n_req mbs <= NL_SENT_MAX /\ 0 <= md_next mbs < 2 ^ 31 /\
  0 <= md_socket_errno mbs < 2 ^ 31 /\ 0 <= md_send_errno mbs < 2 ^ 31.
Proof. destruct MWF as (H1 & H2 & H3 & H4 & _). tauto. Qed.

Lemma NWF' : 0 <= nk_n_chunks kbs <= NL_CHUNKS /\ 0 <= nk_end_errno kbs < 2 ^ 31.
Proof. destruct NWF as (H1 & _ & _ & _ & _ & _ & _ & _ & H9 & _). tauto. Qed.

(* the live part of each buffer: empty when the pointer is NULL or the cap is 0 *)
Lemma BUFK : KD <> 0 -> 1 <= KN -> KD + KN <= 2 ^ 64 /\ apart_gnl KD KN /\ apart KD KN M MD_SIZE /\
  apart KD KN (SP - 144) 144.
Proof.
  intros H1 H2. destruct (BK H1 H2) as [j Hj]. pose proof (rw_cells_bound rsegs m KD _ Hj) as B.
  cbn [cells_size csize] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  destruct (SK H1 H2) as [G Mm]. pose proof (AFK H1) as Fr.
  split; [lia|]. split; [exact G|]. split; [exact Mm | exact Fr].
Qed.

Lemma BUFA : AD <> 0 -> 1 <= AN -> AD + AN <= 2 ^ 64 /\ apart_gnl AD AN /\ apart AD AN M MD_SIZE /\
  apart AD AN (SP - 144) 144.
Proof.
  intros H1 H2. destruct (BA H1 H2) as [j Hj]. pose proof (rw_cells_bound rsegs m AD _ Hj) as B.
  cbn [cells_size csize] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  destruct (SA H1 H2) as [G Mm]. pose proof (AFA H1) as Fr.
  split; [lia|]. split; [exact G|]. split; [exact Mm | exact Fr].
Qed.

Lemma bw_cases : forall p n, 0 <= n -> bw p n = 0 \/ (p <> 0 /\ bw p n = n /\ (n = 0 \/ 1 <= n)).
Proof. intros p n Hn. unfold bw. destruct (Z.eqb_spec p 0); [left; reflexivity | right; lia]. Qed.


(* the five regions talk writes or reads are apart: model block, g_nl, frame, live kind buffer,
   live alias buffer *)
Lemma SEP0 : (M + MD_SIZE <= A_G_NL \/ A_G_NL + NK_SIZE <= M) /\
  (M + MD_SIZE <= SP - 144 \/ SP <= M) /\ (SP <= A_G_NL \/ A_G_NL + NK_SIZE <= SP - 144).
Proof.
  pose proof AGM as X1. pose proof AFM as X2. pose proof FAG as X3. unfold apart_gnl, apart in X1, X2, X3.
  split; [exact X1|]. split; lia.
Qed.

Lemma SEPK : forall x, KD <= x < KD + bw KD KN ->
  ~ (M <= x < M + MD_SIZE) /\ ~ (A_G_NL <= x < A_G_NL + NK_SIZE) /\ ~ (SP - 144 <= x < SP) /\
  ~ (AD <= x < AD + bw AD AN) /\ 0 <= x < 2 ^ 64.
Proof.
  intros x Hx. pose proof RNG as Rg.
  assert (H0 : bw KD KN = KN /\ KD <> 0 /\ 1 <= KN).
  { unfold bw in *. destruct (Z.eqb_spec KD 0); [lia|]. split; [reflexivity|]. lia. }
  destruct H0 as (Be & Bz & Bn). rewrite Be in Hx.
  destruct (BUFK Bz Bn) as (Bb & G & Mm & Fr). unfold apart_gnl, apart in G, Mm, Fr.
  split; [clear G Fr; lia|]. split; [clear Mm Fr; lia|]. split; [clear G Mm; lia|]. split; [|clear G Mm Fr; lia].
  clear G Mm Fr. unfold bw. destruct (Z.eqb_spec AD 0); [lia|].
  destruct (Z.lt_ge_cases AN 1); [lia|].
  pose proof (SKA Bz Bn ltac:(assumption) ltac:(assumption)) as X. unfold apart in X. lia.
Qed.

Lemma SEPA : forall x, AD <= x < AD + bw AD AN ->
  ~ (M <= x < M + MD_SIZE) /\ ~ (A_G_NL <= x < A_G_NL + NK_SIZE) /\ ~ (SP - 144 <= x < SP) /\
  ~ (KD <= x < KD + bw KD KN) /\ 0 <= x < 2 ^ 64.
Proof.
  intros x Hx. pose proof RNG as Rg.
  assert (H0 : bw AD AN = AN /\ AD <> 0 /\ 1 <= AN).
  { unfold bw in *. destruct (Z.eqb_spec AD 0); [lia|]. split; [reflexivity|]. lia. }
  destruct H0 as (Be & Bz & Bn). rewrite Be in Hx.
  destruct (BUFA Bz Bn) as (Bb & G & Mm & Fr). unfold apart_gnl, apart in G, Mm, Fr.
  split; [clear G Fr; lia|]. split; [clear Mm Fr; lia|]. split; [clear G Mm; lia|]. split; [|clear G Mm Fr; lia].
  clear G Mm Fr. unfold bw. destruct (Z.eqb_spec KD 0); [lia|].
  destruct (Z.lt_ge_cases KN 1); [lia|].
  pose proof (SKA ltac:(assumption) ltac:(assumption) Bz Bn) as X. unfold apart in X. lia.
Qed.

Lemma bw_live : forall p n, p <> 0 -> 1 <= n -> bw p n = n.
Proof. intros p n H1 H2. unfold bw. destruct (Z.eqb_spec p 0); lia. Qed.

Lemma tw_live_mrd_k : forall m2 x acc, bufs m2 acc KD KN AD AN -> KD <= x < KD + bw KD KN ->
  exists b, mrd rsegs m2 (wa x) = Some b.
Proof.
  intros m2 x acc (BK2 & _) Hx. unfold bw in Hx. destruct (Z.eqb_spec KD 0); [lia|].
  destruct (Z.lt_ge_cases KN 1); [lia|]. destruct (BK2 ltac:(assumption) ltac:(assumption)) as [j Hj].
  apply (tk_bytes_mrd m2 KD j); [exact (tk_rw_bytes _ _ _ _ Hj)|]. rewrite (tk_rw_len _ _ _ _ Hj). lia.
Qed.

Lemma tw_live_mrd_a : forall m2 x acc, bufs m2 acc KD KN AD AN -> AD <= x < AD + bw AD AN ->
  exists b, mrd rsegs m2 (wa x) = Some b.
Proof.
  intros m2 x acc (_ & BA2 & _) Hx. unfold bw in Hx. destruct (Z.eqb_spec AD 0); [lia|].
  destruct (Z.lt_ge_cases AN 1); [lia|]. destruct (BA2 ltac:(assumption) ltac:(assumption)) as [j Hj].
  apply (tk_bytes_mrd m2 AD j); [exact (tk_rw_bytes _ _ _ _ Hj)|]. rewrite (tk_rw_len _ _ _ _ Hj). lia.
Qed.

(* --------------------------------------------------------------------------
   the context lemmas
   -------------------------------------------------------------------------- *)

Lemma ctx_init : forall m1 jl,
  munch [(SP + -144, SP)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 (SP + -144) [CB 40 jl] ->
  rw_cells rsegs m1 (SP + -104) (saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  stk rsegs m lo (SP + -144) ->
  ctx m1 mbs [CB 40 jl] no_attrs /\ bytes_at rsegs m1 R req.
Proof.
  intros m1 jl MU WM MI1 FL FH STK. pose proof RNG as Rg. pose proof SEP0 as (S1 & S2 & S3).
  pose proof AFR as Xr. unfold apart in Xr.
  destruct MD as [MDa MDl]. destruct NK as [NKa NKl].
  split; [|eapply tw_bytes_out; [exact RQ | exact MU |]; rewrite RQL; outs].
  split; [split; [eapply tw_u8arr_out; [exact MDa | exact MU | exact WM |]; rewrite MDl; outs | exact MDl]|].
  split; [split; [eapply tw_u8arr_out; [exact NKa | exact MU | exact WM |]; rewrite NKl; outs | exact NKl]|].
  split.
  { split; [|split; [|split]].
    - intros H1 H2. destruct (BK H1 H2) as [j Hj]. exists j. eapply tw_rw_out; [exact Hj | exact MU | exact WM |].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      destruct (BUFK H1 H2) as (_ & _ & _ & X). unfold apart in X. outs.
    - intros H1 H2. destruct (BA H1 H2) as [j Hj]. exists j. eapply tw_rw_out; [exact Hj | exact MU | exact WM |].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      destruct (BUFA H1 H2) as (_ & _ & _ & X). unfold apart in X. outs.
    - intros pay E. discriminate E.
    - intros pay E. discriminate E. }
  split; [exact FL|]. split; [reflexivity|]. split; [exact FH|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MU | exact WM | cbn; split; [lia | exact I]]|].
  split; [exact MI1|]. split; [exact WM|].
  split; [|split].
  - eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx |- *. split; [lia | exact I].
  - intros _. eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx |- *. split; [lia | exact I].
  - intros _. eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx |- *. split; [lia | exact I].
Qed.

Lemma ctx_bytes : forall m1 mb cs acc, ctx m1 mb cs acc -> u8arr rsegs m1 M mb /\ Z.of_nat (length mb) = MD_SIZE.
Proof. intros m1 mb cs acc (C & _). exact C. Qed.

Lemma ctx_nlk : forall m1 mb cs acc, ctx m1 mb cs acc -> nlk_at m1 kbs.
Proof. intros m1 mb cs acc (_ & C & _). exact C. Qed.

Lemma ctx_read4 : forall m1 mb cs acc off, ctx m1 mb cs acc -> 0 <= off -> off + 4 <= MD_SIZE ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 (M + off)) 4 = Some (le4 (Z_to_bv 64 (fld_u32 mb off))).
Proof.
  intros m1 mb cs acc off C H1 H2. destruct (ctx_bytes m1 mb cs acc C) as [[Hb _] L].
  rewrite (tk_read m1 M mb off 4 Hb H1) by lia. f_equal. unfold fld_u32, link_spec.rdn.
  change (Z.of_nat 4) with 4. apply tk_le4. rewrite tk_slice_length by lia. reflexivity.
Qed.

Lemma ctx_store_ok : forall m1 mb cs acc off (j : nat), ctx m1 mb cs acc -> 0 <= off ->
  off + Z.of_nat j <= MD_SIZE -> store_ok rsegs m1 (Z_to_bv 64 (M + off)) j = true.
Proof.
  intros m1 mb cs acc off j C H1 H2. destruct (ctx_bytes m1 mb cs acc C) as [[_ Hw] L].
  change (Z_to_bv 64 (M + off)) with (wa (M + off)). eapply wr_at_store_ok; [exact Hw | lia | lia].
Qed.

(* a write that stays inside the model block *)
Lemma ctx_model_write : forall m1 m2 mb cs acc (a n : Z) mb2,
  ctx m1 mb cs acc ->
  munch [(a, a + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  model_at m2 M mb2 -> M <= a -> a + n <= M + MD_SIZE ->
  ctx m2 mb2 cs acc.
Proof.
  intros m1 m2 mb cs acc a n mb2 (CM & CN & CB & CL & CLs & CH & CS & CI & CW & CU & CK & CA) MU WM MI2 MD2 Ha Hn.
  pose proof RNG as Rg. pose proof SEP0 as (S1 & S2 & S3). pose proof MBND as Mb.
  destruct CN as [CNa CNl].
  split; [exact MD2|].
  split; [split; [eapply tw_u8arr_out; [exact CNa | exact MU | exact WM |]; rewrite CNl; outs | exact CNl]|].
  split.
  { eapply tw_bufs_out; [exact CB | exact MU | exact WM | |].
    - intros H1 H2 x Hx. rewrite <- (bw_live KD KN H1 H2) in Hx. pose proof (SEPK x Hx). outs.
    - intros H1 H2 x Hx. rewrite <- (bw_live AD AN H1 H2) in Hx. pose proof (SEPA x Hx). outs. }
  split; [eapply tw_rw_out; [exact CL | exact MU | exact WM |]; rewrite CLs; outs|].
  split; [exact CLs|].
  split; [eapply tw_rw_out; [exact CH | exact MU | exact WM |]; rewrite tw_saved_size; outs|].
  split.
  { eapply tk_stk_transport; [exact CS | exact MU | exact WM |]. intros x Hx.
    destruct (Z.ltb_spec x a); destruct (Z.ltb_spec x (a + n)); try (left; outs).
    right. destruct MD2 as [[Hb2 _] L2]. apply (tk_bytes_mrd m2 M mb2 x Hb2). lia. }
  split; [exact MI2|]. split; [eapply wmono_trans; eassumption|].
  split; [|split].
  - eapply tw_munch_sub; [exact CU | exact MU | outs].
  - intros E. eapply tw_munch_sub; [exact (CK E) | exact MU | outs].
  - intros E. eapply tw_munch_sub; [exact (CA E) | exact MU | outs].
Qed.

Lemma ctx_store_model : forall m1 mb cs acc off xs, ctx m1 mb cs acc -> 0 <= off ->
  off + Z.of_nat (length xs) <= MD_SIZE ->
  ctx (write_to_mem m1 (Z_to_bv 64 (M + off)) xs) (upd_bytes mb (Z.to_nat off) xs) cs acc.
Proof.
  intros m1 mb cs acc off xs C H1 H2. pose proof RNG as Rg. pose proof MBND as Mb.
  destruct (ctx_bytes m1 mb cs acc C) as [[Hb Hw] L].
  pose proof (ctx_store_ok m1 mb cs acc off (length xs) C H1 H2) as HS.
  change (Z_to_bv 64 (M + off)) with (wa (M + off)) in *.
  eapply (ctx_model_write m1 _ mb cs acc (M + off) (Z.of_nat (length xs))); [exact C | | | | | lia | lia].
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
  - destruct C as (_ & _ & _ & _ & _ & _ & _ & CI & _). apply mem_inv_store; [exact CI | exact HS].
  - split; [split|].
    + apply bytes_at_write_inside; [exact Hb | lia | lia].
    + rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
    + rewrite upd_bytes_length by lia. exact L.
Qed.

Lemma ctx_memcpy_model : forall m1 m2 mb cs acc off xs, ctx m1 mb cs acc -> 0 <= off ->
  off + Z.of_nat (length xs) <= MD_SIZE ->
  munch [(M + off, M + off + Z.of_nat (length xs))] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  bytes_at rsegs m2 (M + off) xs ->
  ctx m2 (upd_bytes mb (Z.to_nat off) xs) cs acc.
Proof.
  intros m1 m2 mb cs acc off xs C H1 H2 MU WM MI2 HX. pose proof RNG as Rg. pose proof MBND as Mb.
  destruct (ctx_bytes m1 mb cs acc C) as [U L].
  eapply (ctx_model_write m1 m2 mb cs acc (M + off) (Z.of_nat (length xs))); [exact C | exact MU | exact WM | exact MI2 | | lia | lia].
  split.
  - eapply (tk_u8arr_upd _ m1 m2 M mb xs (Z.to_nat off) U MU WM).
    + intros x Hx. destruct (Z.ltb_spec x (M + off)); destruct (Z.ltb_spec x (M + off + Z.of_nat (length xs)));
        try (left; outs). right. lia.
    + rewrite Z2Nat.id by lia. exact HX.
    + lia.
  - rewrite upd_bytes_length by lia. exact L.
Qed.

Lemma ctx_spill : forall m1 m2 mb jl cs acc, ctx m1 mb [CB 40 jl] acc ->
  munch [(SP + -144, SP + -104)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (SP + -144) cs -> cells_size cs = 40%nat ->
  ctx m2 mb cs acc.
Proof.
  intros m1 m2 mb jl cs acc (CM & CN & CB & CL & CLs & CH & CS & CI & CW & CU & CK & CA) MU WM MI2 FL FLs.
  pose proof RNG as Rg. pose proof SEP0 as (S1 & S2 & S3). pose proof MBND as Mb.
  destruct CM as [CMa CMl]. destruct CN as [CNa CNl].
  split; [split; [eapply tw_u8arr_out; [exact CMa | exact MU | exact WM |]; rewrite CMl; outs | exact CMl]|].
  split; [split; [eapply tw_u8arr_out; [exact CNa | exact MU | exact WM |]; rewrite CNl; outs | exact CNl]|].
  split.
  { eapply tw_bufs_out; [exact CB | exact MU | exact WM | |].
    - intros H1 H2 x Hx. rewrite <- (bw_live KD KN H1 H2) in Hx. pose proof (SEPK x Hx). outs.
    - intros H1 H2 x Hx. rewrite <- (bw_live AD AN H1 H2) in Hx. pose proof (SEPA x Hx). outs. }
  split; [exact FL|]. split; [exact FLs|].
  split; [eapply tw_rw_out; [exact CH | exact MU | exact WM |]; rewrite tw_saved_size; outs|].
  split; [eapply tk_stk_transport; [exact CS | exact MU | exact WM |]; intros x Hx; left; outs|].
  split; [exact MI2|]. split; [eapply wmono_trans; eassumption|].
  split; [|split].
  - eapply tw_munch_sub; [exact CU | exact MU | outs].
  - intros E. eapply tw_munch_sub; [exact (CK E) | exact MU | outs].
  - intros E. eapply tw_munch_sub; [exact (CA E) | exact MU | outs].
Qed.

Lemma ctx_attr : forall m1 m2 mb cs accF, ctx m1 mb cs no_attrs ->
  munch [(KD, KD + bw KD KN); (AD, AD + bw AD AN)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  bufs m2 accF KD KN AD AN ->
  (a_kind accF = None -> munch [(AD, AD + bw AD AN)] m1 m2) ->
  (a_alias accF = None -> munch [(KD, KD + bw KD KN)] m1 m2) ->
  ctx m2 mb cs accF.
Proof.
  intros m1 m2 mb cs accF (CM & CN & CB & CL & CLs & CH & CS & CI & CW & CU & CK & CA) MU WM MI2 B2 NK2 NA2.
  pose proof RNG as Rg. pose proof SEP0 as (S1 & S2 & S3). pose proof MBND as Mb.
  destruct CM as [CMa CMl]. destruct CN as [CNa CNl].
  assert (OUT : forall x, ~ (KD <= x < KD + bw KD KN) -> ~ (AD <= x < AD + bw AD AN) ->
            outside [(KD, KD + bw KD KN); (AD, AD + bw AD AN)] x) by outs.
  split; [split; [eapply tw_u8arr_out; [exact CMa | exact MU | exact WM |] | exact CMl]|].
  { intros x Hx. rewrite CMl in Hx. apply OUT; intros Hy; [apply (proj1 (SEPK x Hy)) | apply (proj1 (SEPA x Hy))]; exact Hx. }
  split; [split; [eapply tw_u8arr_out; [exact CNa | exact MU | exact WM |] | exact CNl]|].
  { intros x Hx. rewrite CNl in Hx. apply OUT; intros Hy; [apply (proj1 (proj2 (SEPK x Hy))) | apply (proj1 (proj2 (SEPA x Hy)))]; exact Hx. }
  split; [exact B2|].
  split; [eapply tw_rw_out; [exact CL | exact MU | exact WM |]|].
  { intros x Hx. rewrite CLs in Hx. apply OUT; intros Hy;
      [apply (proj1 (proj2 (proj2 (SEPK x Hy)))) | apply (proj1 (proj2 (proj2 (SEPA x Hy))))]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia. }
  split; [exact CLs|].
  split; [eapply tw_rw_out; [exact CH | exact MU | exact WM |]|].
  { intros x Hx. rewrite tw_saved_size in Hx. apply OUT; intros Hy;
      [apply (proj1 (proj2 (proj2 (SEPK x Hy)))) | apply (proj1 (proj2 (proj2 (SEPA x Hy))))]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia. }
  split.
  { eapply tk_stk_transport; [exact CS | exact MU | exact WM |]. intros x Hx.
    destruct (Z.ltb_spec x KD); destruct (Z.ltb_spec x (KD + bw KD KN));
    destruct (Z.ltb_spec x AD); destruct (Z.ltb_spec x (AD + bw AD AN)); try (left; outs).
    all: right; first [eapply tw_live_mrd_k; [exact B2 | lia] | eapply tw_live_mrd_a; [exact B2 | lia]]. }
  split; [exact MI2|]. split; [eapply wmono_trans; eassumption|].
  split; [|split].
  - eapply tw_munch_sub; [exact CU | exact MU | outs].
  - intros E. eapply tw_munch_sub; [exact (CK eq_refl) | exact (NK2 E) | outs].
  - intros E. eapply tw_munch_sub; [exact (CA eq_refl) | exact (NA2 E) | outs].
Qed.

(* the model block a returning path leaves *)
Definition mres (mb : list byte) : Prop :=
  model_wf mb /\ md_next mb = Z.of_nat (k_next (talk_after K0)) /\ md_socket_errno mb = 0 /\
  md_send_errno mb = k_send (talk_after K0) /\ md_n_mark mb = md_n_mark mbs /\
  md_marks mb = md_marks mbs /\
  md_reqs mb = (if talk_owes K0 then owe (md_reqs mbs) req else md_reqs mbs) /\
  md_n_req mb = Z.of_nat (length (md_reqs mb)).

Lemma ctx_fin : forall m3 mb cs acc
    (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11'
     t3' t4' t5' t6' : word),
  ctx m3 mb cs acc -> a0' = wz (talk_rc_model K0) -> mres mb -> acc = talk_attrs K0 ->
  evt rsegs Qf
    (MS (mkR ra' (Z_to_bv 64 (SP + -144)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
             s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
        F (Z_to_bv 64 0x1584c) fc None m3 (seg_rom rsegs)).
Proof.
  intros m3 mb cs acc ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9'
    s10' s11' t3' t4' t5' t6' C Hrc Hmb Hacc.
  pose proof RNG as Rg. assert (Hlo : 0 <= lo) by (destruct ST as (H & _); exact H).
  destruct C as (CM & CN & CB & CL & CLs & CH & CS & CI & CW & CU & CK & CA).
  eapply F_exit_ok; [reflexivity | lia | exact CH |].
  unfold Qf. eexists _, m3. split; [reflexivity|].
  split; [rewrite <- ESP, Z_to_bv_lit_self; apply regs_preserved_mkR|].
  split; [exact CU|]. split; [exact CW|]. split; [exact CI|].
  split; [eapply tw_stk_fin; [exact CS | exact CL | exact CLs | exact CH | apply tw_saved_size | lia]|].
  intros mbs0 kbs0 req0 HM0 HN0 HR0 HL0.
  assert (E1 : mbs0 = mbs).
  { destruct HM0 as [[H0 _] L0]. destruct MD as [[H1 _] L1]. apply (tk_bytes_at_uniq m M); auto. lia. }
  assert (E2 : kbs0 = kbs).
  { destruct HN0 as [[H0 _] L0]. destruct NK as [[H1 _] L1]. apply (tk_bytes_at_uniq m A_G_NL); auto. lia. }
  assert (E3 : req0 = req) by (apply (tk_bytes_at_uniq m R); auto; lia).
  subst mbs0 kbs0 req0. cbv zeta. fold K0. rewrite <- Hacc.
  destruct Hmb as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
  destruct CB as (B1 & B2 & B3 & B4).
  split; [exact Hrc|].
  split; [exists mb; exact (conj CM (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 (conj W6 (conj W7 W8))))))))|].
  split; [exact B3|]. split; [exact B4|]. split; [exact CK|]. split; [exact CA|].
  split; [exact B1 | exact B2].
Qed.

Lemma tw_negw : forall e, 0 <= e < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 e))) = Z_to_bv 64 (- e).
Proof.
  intros e He. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma K0_eq : K0 = Kst (nk_chunks kbs) (Z.to_nat (md_next mbs)) (nk_end_errno kbs)
                      (md_socket_errno mbs) (md_send_errno mbs).
Proof. reflexivity. Qed.

(* --------------------------------------------------------------------------
   0x1579c: the cursor against n_chunks, then the chunk loop or the end errno
   -------------------------------------------------------------------------- *)
Lemma arm_chunks : forall m2 mb1 jl
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' t3' t4' t5' t6' : word),
  ctx m2 mb1 [CB 40 jl] no_attrs ->
  md_socket_errno mbs = 0 -> md_send_errno mbs = 0 ->
  model_wf mb1 -> md_next mb1 = md_next mbs -> md_socket_errno mb1 = 0 -> md_send_errno mb1 = 0 ->
  md_reqs mb1 = owe (md_reqs mbs) req -> md_n_req mb1 = Z.of_nat (length (md_reqs mb1)) ->
  md_n_mark mb1 = md_n_mark mbs -> md_marks mb1 = md_marks mbs ->
  evt rsegs Qf
    (MS (mkR ra' (Z_to_bv 64 (SP + -144)) gp tp t0' t1' t2' (Z_to_bv 64 AD) (Z_to_bv 64 KD) a0' a1' a2' a3'
             a4' a5' a6' a7' (Z_to_bv 64 AN) (Z_to_bv 64 KN) (Z_to_bv 64 M) s5' s6' s7' s8 s9 s10 s11
             t3' t4' t5' t6')
        F (Z_to_bv 64 0x1579c) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 mb1 jl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' t3' t4' t5' t6'
    C Hs0 Hd0 W1 N1 S1 D1 Q1 NR1 NM1 MK1.
  assert (Hlo : 0 <= lo) by (destruct ST as (H & _); exact H).
  pose proof RNG as Rg. pose proof NWF' as (Nch & Nend). pose proof MWF' as Mw.
  destruct (ctx_bytes _ _ _ _ C) as [U1 L1].
  pose proof (ctx_read4 m2 mb1 _ _ 8 C ltac:(lia) ltac:(unfold MD_SIZE; lia)) as Hn.
  change (fld_u32 mb1 8) with (md_next mb1) in Hn. rewrite N1 in Hn.
  pose proof (tw_nlk_read4 m2 kbs NK_N_CHUNKS (ctx_nlk _ _ _ _ C) ltac:(unfold NK_N_CHUNKS; lia)
                ltac:(unfold NK_N_CHUNKS, NK_SIZE; lia)) as Hc.
  change (fld_u32 kbs NK_N_CHUNKS) with (nk_n_chunks kbs) in Hc.
  replace (Z_to_bv 64 (tG + NK_N_CHUNKS)) with (Z_to_bv 64 466304) in Hc by reflexivity.
  pose proof (tw_nlk_read4 m2 kbs NK_END_ERRNO (ctx_nlk _ _ _ _ C) ltac:(unfold NK_END_ERRNO; lia)
                ltac:(unfold NK_END_ERRNO, NK_SIZE; lia)) as He.
  change (fld_u32 kbs NK_END_ERRNO) with (nk_end_errno kbs) in He.
  replace (Z_to_bv 64 (tG + NK_END_ERRNO)) with (Z_to_bv 64 466312) in He by reflexivity.
  unfold NL_CHUNKS in Nch.
  step. rewrite tk_sx32_small by lia.
  do 5 step. rewrite tk_sx32_small by lia.
  step.
  rewrite tk_lts by lia.
  assert (CS : length (nk_chunks kbs) = Z.to_nat (nk_n_chunks kbs)) by apply tk_chunks_length.
  assert (FU : S (length (k_chunks K0)) = S (Z.to_nat (nk_n_chunks kbs))) by (rewrite K0_eq; cbn; rewrite CS; reflexivity).
  destruct (Z.ltb_spec (md_next mbs) (nk_n_chunks kbs)) as [LT|GE]; cbn [negb].
  - (* a chunk to walk: 0x157b8 .. 0x157cc, then the chunk loop *)
    do 6 step.
    eapply (FCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M kbs mb1
              (S (Z.to_nat (nk_n_chunks kbs))) (md_next mbs));
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | | exact (ctx_nlk _ _ _ _ C) | exact NWF | exact (ctx_bytes _ _ _ _ C) | exact AGM
      | destruct C as (_ & _ & _ & _ & _ & _ & _ & CI & _); exact CI | lia | lia | | ].
    + f_equal. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 12) with 4096.
      unfold tG, A_G_NL. lia.
    + (* the chunk loop answered without an RTM_NEWLINK attribute walk *)
      intros rc v j m3 CL Hrc MU WM MI3 MD3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s5'' s6'' s7''.
      replace (M + 12) with (M + 8 + 4) in MU by lia.
      pose proof (tw_cl_bound _ _ _ _ _ CL) as JB. rewrite CS in JB.
      assert (CL' : chunk_loop (S (length (k_chunks K0))) (k_chunks K0) (k_next K0) = (v, j))
        by (rewrite FU; exact CL).
      destruct (tw_core_main K0 v j Hs0 Hd0 CL') as (TA & TO & TT & TR).
      pose proof (md_set_next_ok mb1 (Z.of_nat j) L1 W1 ltac:(lia)) as (_ & SW & SN & SS & SD & SQ & SR & SM).
      eapply (ctx_fin m3 _ _ no_attrs); [eapply ctx_model_write; [exact C | exact MU | exact WM | exact MI3 | exact MD3 | lia | unfold MD_SIZE; lia] | | | ].
      * rewrite TR. unfold wz. f_equal. rewrite K0_eq; cbn [k_end].
        destruct Hrc as [[-> ->] | [[-> ->] | [[code [-> ->]] | [-> ->]]]]; cbn [tw_rc]; unfold norm_rc;
          try reflexivity.
        all: destruct (Z.ltb_spec 0 (- nk_end_errno kbs)); [lia | reflexivity].
      * unfold mres. rewrite TA, TO. cbn [k_next k_send]. destruct SM as [SM1 SM2].
        refine (conj SW (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
        -- exact SN.
        -- rewrite SS. exact S1.
        -- rewrite SD. exact D1.
        -- rewrite SM1. exact NM1.
        -- rewrite SM2. exact MK1.
        -- rewrite SQ. exact Q1.
        -- rewrite SR, SQ. exact NR1.
      * rewrite TT. destruct Hrc as [[-> _] | [[-> _] | [[code [-> _]] | [-> _]]]]; reflexivity.
    + (* an RTM_NEWLINK of ml >= 36 in chunk c' *)
      intros c' f' off' ml m3 CL Hc' Hml Hoff Hlen Hf MU WM MI3 MD3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6''.
      replace (M + 12) with (M + 8 + 4) in MU by lia.
      replace (off' + NL_HDR + IFI_LEN) with (off' + 32) in CL by (unfold NL_HDR, IFI_LEN; lia).
      replace (ml - NL_HDR - IFI_LEN) with (ml - 32) in CL by (unfold NL_HDR, IFI_LEN; lia).
      assert (CL' : chunk_loop (S (length (k_chunks K0))) (k_chunks K0) (k_next K0)
                    = (NlLink (attr_scan f' (nk_chunk kbs c') (off' + 32) (ml - 32) no_attrs), S (Z.to_nat c')))
        by (rewrite FU; exact CL).
      destruct (tw_core_main K0 _ _ Hs0 Hd0 CL') as (TA & TO & TT & TR).
      pose proof (md_set_next_ok mb1 (c' + 1) L1 W1 ltac:(lia)) as (_ & SW & SN & SS & SD & SQ & SR & SM).
      assert (C3 : ctx m3 (md_set_next mb1 (c' + 1)) [CB 40 jl] no_attrs)
        by (eapply ctx_model_write; [exact C | exact MU | exact WM | exact MI3 | exact MD3 | lia | unfold MD_SIZE; lia]).
      pose proof (tk_chunk_len kbs c' NWF (proj2 (ctx_nlk _ _ _ _ C3)) ltac:(lia)) as [CKL CKM].
      unfold NL_CHUNK_MAX in CKM.
      pose proof C3 as (_ & _ & _ & FL3 & _ & _ & _ & MI3' & _).
      eapply (P_spill _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP (tG + 4096 * c') off' ml KD KN AD AN jl);
        [reflexivity | lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | reflexivity | unfold tG, A_G_NL; lia | lia | lia | lia | lia | lia | lia
        | exact FL3 | exact MI3' | ].
      intros m4 b0 b1 b2 b3 MU4 WM4 MI4 FL4.
      assert (C4 : ctx m4 (md_set_next mb1 (c' + 1)) (spill_cells AN (tG + 4096 * c') KN AD KD) no_attrs)
        by (eapply ctx_spill; [exact C3 | exact MU4 | exact WM4 | exact MI4 | exact FL4 | reflexivity]).
      pose proof (tk_chunk_at m4 kbs c' (ctx_nlk _ _ _ _ C4) NWF ltac:(lia)) as CK4.
      pose proof C4 as (_ & _ & B4 & _ & _ & _ & _ & MI4' & _).
      eapply (FAT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tG + 4096 * c') (nk_chunk kbs c') f' (off' + 32) (ml - 32) SP KD KN AD AN no_attrs);
        [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | lia
        | exact FL4 | exact CK4 | lia | unfold tG, A_G_NL; lia | unfold tG, A_G_NL; lia
        | lia | lia | lia | lia | lia | lia | lia | exact B4 | | exact MI4' | ].
      * (* the buffers are apart from this chunk and from the frame *)
        split; [|split].
        -- intros H1 H2. destruct (BUFK H1 H2) as (_ & G & _ & Fr). unfold apart_gnl, apart in G, Fr |- *.
           unfold tG, NK_SIZE in *. split; lia.
        -- intros H1 H2. destruct (BUFA H1 H2) as (_ & G & _ & Fr). unfold apart_gnl, apart in G, Fr |- *.
           unfold tG, NK_SIZE in *. split; lia.
        -- exact SKA.
      * intros m5. cbv zeta. intros MU5 WM5 MI5 B5 NK5 NA5 ra5 t05 t15 t25 a15 a25 a35 a45 a55 a65 a75
          s25 s35 s45 s75 s85 s105 s115 t35 t45 t55 t65.
        eapply (ctx_fin m5 _ _ (attr_scan f' (nk_chunk kbs c') (off' + 32) (ml - 32) no_attrs));
          [eapply ctx_attr; [exact C4 | exact MU5 | exact WM5 | exact MI5 | exact B5 | exact NK5 | exact NA5] | | | ].
        -- rewrite TR. reflexivity.
        -- unfold mres. rewrite TA, TO. cbn [k_next k_send]. destruct SM as [SM1 SM2].
           refine (conj SW (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
           ++ rewrite SN. lia.
           ++ rewrite SS. exact S1.
           ++ rewrite SD. exact D1.
           ++ rewrite SM1. exact NM1.
           ++ rewrite SM2. exact MK1.
           ++ rewrite SQ. exact Q1.
           ++ rewrite SR, SQ. exact NR1.
        -- rewrite TT. reflexivity.
  - (* no chunk left: 0x15844 lw end_errno; negw *)
    step. rewrite tk_sx32_small by lia. step.
    assert (CL' : chunk_loop (S (length (k_chunks K0))) (k_chunks K0) (k_next K0) = (NlNone, k_next K0)).
    { rewrite K0_eq. cbn [k_chunks k_next chunk_loop]. rewrite tk_nth_chunks_none by lia. reflexivity. }
    destruct (tw_core_main K0 _ _ Hs0 Hd0 CL') as (TA & TO & TT & TR).
    eapply (ctx_fin m2 _ _ no_attrs); [exact C | | | ].
    + rewrite TR. rewrite K0_eq. cbn [tw_rc k_end]. unfold norm_rc.
      destruct (Z.ltb_spec 0 (- nk_end_errno kbs)); [lia|]. unfold wz. apply tw_negw. lia.
    + unfold mres. rewrite TA, TO. rewrite K0_eq. cbn [k_next k_send].
      refine (conj W1 (conj _ (conj S1 (conj D1 (conj NM1 (conj MK1 (conj Q1 NR1))))))).
      rewrite N1, Z2Nat.id by lia. reflexivity.
    + rewrite TT. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   0x1571c: the two errnos of the model block, then owe
   -------------------------------------------------------------------------- *)
Lemma body : forall m1 jl,
  ctx m1 mbs [CB 40 jl] no_attrs -> bytes_at rsegs m1 R req ->
  evt rsegs Qf
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 M) (Z_to_bv 64 R) (Z_to_bv 64 LEN)
             (Z_to_bv 64 KD) (Z_to_bv 64 KN) (Z_to_bv 64 AD) (Z_to_bv 64 AN) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1571c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jl C RQ1.
  assert (Hlo : 0 <= lo) by (destruct ST as (H & _); exact H).
  pose proof RNG as Rg. pose proof MWF' as (Mn & Mx & Ms & Md). pose proof MBND as Mb.
  destruct (ctx_bytes _ _ _ _ C) as [U0 L0].
  pose proof (ctx_read4 m1 mbs _ _ 0 C ltac:(lia) ltac:(unfold MD_SIZE; lia)) as H0.
  change (fld_u32 mbs 0) with (md_socket_errno mbs) in H0.
  step. step. rewrite tk_sx32_small by lia. step.
  rewrite tk_eqb by lia.
  destruct (Z.eqb_spec (md_socket_errno mbs) 0) as [Hs0|Hs0]; cbv iota.
  2: { (* the socket fails once *)
    pose proof (ctx_store_ok m1 mbs _ _ 0 4 C ltac:(lia) ltac:(unfold MD_SIZE; lia)) as HS.
    step.
    pose proof (ctx_store_model m1 mbs _ _ 0 (le4 (Z_to_bv 64 0)) C ltac:(lia)
                  ltac:(rewrite length_le4; unfold MD_SIZE; lia)) as C2.
    rewrite Z.add_0_r in C2. change (Z.to_nat 0) with 0%nat in C2.
    step. step.
    pose proof (md_zero_sock mbs L0 MWF) as (_ & ZW & ZS & ZD & ZN & ZQ & ZR & ZM).
    destruct (tw_core_sock K0 Hs0) as (TR & TT & TA & TO).
    eapply (ctx_fin _ _ _ no_attrs); [exact C2 | | | ].
    - rewrite TR, K0_eq. cbn [k_sock]. unfold norm_rc.
      destruct (Z.ltb_spec 0 (- md_socket_errno mbs)); [lia|]. unfold wz. apply tw_negw. lia.
    - unfold mres. rewrite TA, TO, K0_eq. cbn [k_next k_send]. destruct ZM as [ZM1 ZM2].
      refine (conj ZW (conj _ (conj ZS (conj ZD (conj ZM1 (conj ZM2 (conj ZQ _))))))).
      + rewrite ZN, Z2Nat.id by lia. reflexivity.
      + rewrite ZR, ZQ, md_reqs_length, Z2Nat.id by lia. reflexivity.
    - rewrite TT. reflexivity. }
  pose proof (ctx_read4 m1 mbs _ _ 4 C ltac:(lia) ltac:(unfold MD_SIZE; lia)) as H4.
  change (fld_u32 mbs 4) with (md_send_errno mbs) in H4.
  step. rewrite tk_sx32_small by lia. step.
  rewrite tk_eqb by lia.
  destruct (Z.eqb_spec (md_send_errno mbs) 0) as [Hd0|Hd0]; cbv iota.
  2: { (* the send fails once *)
    pose proof (ctx_store_ok m1 mbs _ _ 4 4 C ltac:(lia) ltac:(unfold MD_SIZE; lia)) as HS.
    step.
    pose proof (ctx_store_model m1 mbs _ _ 4 (le4 (Z_to_bv 64 0)) C ltac:(lia)
                  ltac:(rewrite length_le4; unfold MD_SIZE; lia)) as C2.
    change (Z.to_nat 4) with 4%nat in C2.
    step. step.
    pose proof (md_zero_send mbs L0 MWF) as (_ & ZW & ZD & ZS & ZN & ZQ & ZR & ZM).
    destruct (tw_core_send K0 Hs0 Hd0) as (TR & TT & TA & TO).
    eapply (ctx_fin _ _ _ no_attrs); [exact C2 | | | ].
    - rewrite TR, K0_eq. cbn [k_send]. unfold norm_rc.
      destruct (Z.ltb_spec 0 (- md_send_errno mbs)); [lia|]. unfold wz. apply tw_negw. lia.
    - unfold mres. rewrite TA, TO, K0_eq. cbn [k_next k_send]. destruct ZM as [ZM1 ZM2].
      refine (conj ZW (conj _ (conj _ (conj ZD (conj ZM1 (conj ZM2 (conj ZQ _))))))).
      + rewrite ZN, Z2Nat.id by lia. reflexivity.
      + rewrite ZS. exact Hs0.
      + rewrite ZR, ZQ, md_reqs_length, Z2Nat.id by lia. reflexivity.
    - rewrite TT. reflexivity. }
  (* owe *)
  pose proof (ctx_read4 m1 mbs _ _ 8336 C ltac:(lia) ltac:(unfold MD_SIZE; lia)) as HN.
  change (fld_u32 mbs 8336) with (md_n_req mbs) in HN.
  unfold NL_SENT_MAX in Mn.
  do 9 step. rewrite tk_sx32_small by lia. do 2 step.
  rewrite tk_lts by lia.
  destruct (Z.ltb_spec 15 (md_n_req mbs)) as [N16|N15]; cbv iota.
  - (* the ring is full: nothing owed *)
    assert (NE : md_n_req mbs = 16) by lia.
    eapply (arm_chunks m1 mbs jl); [exact C | exact Hs0 | exact Hd0 | exact MWF | reflexivity
      | exact Hs0 | exact Hd0 | | | reflexivity | reflexivity].
    + unfold owe. rewrite md_reqs_length, NE. reflexivity.
    + rewrite md_reqs_length, Z2Nat.id by lia. reflexivity.
  - (* owe: the request into slot n, then the count and the length *)
    do 5 step.
    set (OFF := MD_REQ + NL_SENT_LEN * md_n_req mbs).
    assert (HOFF : 0 <= OFF /\ OFF + LEN <= 8204) by (unfold OFF, MD_REQ, NL_SENT_LEN in *; lia).
    rewrite (unsigned_lit (md_n_req mbs)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 9) with 512.
    replace (Z_to_bv 64 (M + md_n_req mbs * 512 + 12)) with (Z_to_bv 64 (M + OFF))
      by (f_equal; unfold OFF, MD_REQ, NL_SENT_LEN; lia).
    pose proof (tw_u8arr_sub m1 M mbs OFF LEN U0 ltac:(lia) ltac:(lia) ltac:(unfold MD_SIZE in L0; lia)) as DSTC.
    eapply evt_cut.
    { eapply MEMCPY.
      - rewrite unsigned_lit by lia. exact RQ1.
      - rewrite unsigned_lit by lia. lia.
      - rewrite !unsigned_lit by (unfold MD_SIZE in Mb; lia). exact DSTC.
      - rewrite !unsigned_lit by (unfold MD_SIZE in Mb; lia). pose proof APR as X. unfold apart, MD_SIZE in X. lia.
      - destruct C as (_ & _ & _ & _ & _ & _ & _ & CI & _). exact CI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                    & -> & MU & WM & MI2 & DST & SRC).
    rewrite !unsigned_lit in MU, DST by (unfold MD_SIZE in Mb; lia).
    replace (ret_pc (Z_to_bv 64 87936)) with (Z_to_bv 64 87936) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite <- RQL in MU.
    pose proof (ctx_memcpy_model m1 m2 mbs _ _ OFF req C ltac:(lia) ltac:(unfold MD_SIZE; lia) MU WM MI2
                  (tk_rw_bytes _ _ _ _ DST)) as C2.
    pose proof (ctx_read4 m2 _ _ _ 8336 C2 ltac:(lia) ltac:(unfold MD_SIZE; lia)) as HN2.
    rewrite tw_fld_upd_other in HN2 by (unfold MD_SIZE in L0; lia).
    change (fld_u32 mbs 8336) with (md_n_req mbs) in HN2.
    step. rewrite tk_sx32_small by lia. do 3 step.
    pose proof (ctx_store_ok m2 _ _ _ 8336 4 C2 ltac:(lia) ltac:(unfold MD_SIZE; lia)) as HS1.
    step.
    pose proof (ctx_store_model m2 _ _ _ 8336 (le4 (Z_to_bv 64 (md_n_req mbs + 1))) C2 ltac:(lia)
                  ltac:(rewrite length_le4; unfold MD_SIZE; lia)) as C3.
    step.
    rewrite (unsigned_lit (md_n_req mbs)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (ctx_store_ok _ _ _ _ (8208 + 8 * md_n_req mbs) 8 C3 ltac:(lia) ltac:(unfold MD_SIZE; lia)) as HS2.
    step.
    pose proof (ctx_store_model _ _ _ _ (8208 + 8 * md_n_req mbs) (le8 (Z_to_bv 64 LEN)) C3 ltac:(lia)
                  ltac:(rewrite length_le8; unfold MD_SIZE; lia)) as C4.
    assert (C5 : ctx (write_to_mem (write_to_mem m2 (Z_to_bv 64 (M + 8336)) (le4 (Z_to_bv 64 (md_n_req mbs + 1))))
                        (Z_to_bv 64 (M + (8208 + 8 * md_n_req mbs))) (le8 (Z_to_bv 64 LEN)))
                     (md_owe mbs req (md_n_req mbs) LEN) [CB 40 jl] no_attrs) by exact C4.
    pose proof (md_owe_ok mbs req L0 MWF ltac:(unfold NL_SENT_MAX; lia) ltac:(lia)) as OW.
    cbv zeta in OW. rewrite RQL in OW.
    destruct OW as (_ & OWW & OWQ & OWN & OWS & OWD & OWX & OWM).
    destruct OWM as [OWM1 OWM2].
    eapply (arm_chunks _ (md_owe mbs req (md_n_req mbs) LEN) jl); [exact C5 | exact Hs0 | exact Hd0 | exact OWW
      | exact OWX | rewrite OWS; exact Hs0 | rewrite OWD; exact Hd0 | | | exact OWM1 | exact OWM2].
    + rewrite OWQ. unfold owe. rewrite md_reqs_length.
      destruct (Z.ltb_spec (Z.of_nat (Z.to_nat (md_n_req mbs))) NL_SENT_MAX) as [X|X]; [reflexivity|].
      unfold NL_SENT_MAX in X. lia.
    + rewrite OWN, OWQ, length_app, md_reqs_length. cbn [length]. lia.
Qed.

(* --------------------------------------------------------------------------
   0x156e4: the whole call
   -------------------------------------------------------------------------- *)
Lemma walk_all :
  evt rsegs Qf
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TALK) fc None m (seg_rom rsegs)).
Proof.
  pose proof RNG as Rg. assert (Hlo : 0 <= lo) by (destruct ST as (H & _); exact H).
  destruct (stk_carve rsegs m lo SP 144 ST ltac:(lia)) as [ST1 [junk FR]].
  change (Z.of_nat 144) with 144 in ST1, FR.
  destruct (tk_rw_split m (SP - 144) 144 40 junk ltac:(lia) FR) as [FL FH].
  replace (SP - 144) with (SP + -144) in FL, ST1 by lia.
  replace (SP - 144 + Z.of_nat 40) with (SP + -104) in FH by lia.
  change (144 - 40)%nat with 104%nat in FH.
  apply (evt_eq rsegs Qf _
    (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 M) (Z_to_bv 64 R) (Z_to_bv 64 LEN)
             (Z_to_bv 64 KD) (Z_to_bv 64 KN) (Z_to_bv 64 AD) (Z_to_bv 64 AN) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 TALK) fc None m (seg_rom rsegs))).
  { rewrite <- ESP, <- EM, <- ER, <- ELEN, <- EKD, <- EKN, <- EAD, <- EAN, !Z_to_bv_lit_self. reflexivity. }
  unfold TALK.
  eapply P_pro; [reflexivity | lia | exact FL | exact FH | exact MI | ].
  intros m1 MU WM MI1 FL1 FH1.
  destruct (ctx_init m1 _ MU WM MI1 FL1 FH1 ST1) as [C RQ1].
  exact (body m1 _ C RQ1).
Qed.

End Walk.

(* ==========================================================================
   3. the contract
   ========================================================================== *)

Theorem talk_walk : memcpy_contract -> talk_contract.
Proof.
  intros MEMCPY.
  pose proof F_chunk_ok as FCH.
  pose proof (F_attr_ok (F_take_al_ok MEMCPY) (F_kind_ok (F_take_kd_ok MEMCPY))) as FAT.
  unfold talk_contract. apply leaf_intro.
  - intros r1 r2 m E H.
    assert (A : forall i, arg r1 i = arg r2 i) by (intros i; unfold arg; rewrite E; reflexivity).
    assert (S : spZ r1 = spZ r2) by (unfold spZ; rewrite E; reflexivity).
    unfold frame_apart_gnl, apart_frame in *. rewrite <- !A, <- !S. exact H.
  - intros r1 r2 m E.
    assert (A : forall i, arg r1 i = arg r2 i) by (intros i; unfold arg; rewrite E; reflexivity).
    rewrite !A. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H.
    assert (A : forall i, arg r1 i = arg r2 i) by (intros i; unfold arg; rewrite E; reflexivity).
    assert (S : spZ r1 = spZ r2) by (unfold spZ; rewrite E; reflexivity).
    cbv beta in H |- *. rewrite <- !A, <- !S, <- !E'. exact H.
  - unfold leaf_walk.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros PRE MI ST LO SPB. cbv beta in PRE.
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_a6 in PRE.
    unfold frame_apart_gnl, apart_frame in PRE. rewrite ?mkR_sp in PRE.
    destruct PRE as (mbs & kbs & req & MD & MWF & NK & FAG & NWF & RQ & RQL & LENB & BK & BA & APR & SK & SA & SKA
                     & AGM & AFM & AFR & AFK & AFA).
    eapply (walk_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo mbs kbs req (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
              (bv_unsigned a3) (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6));
      try reflexivity; try eassumption.
    all: try (unfold apart; lia).
    all: try (intros H; specialize (AFK H); unfold apart; lia).
    all: try (intros H; specialize (AFA H); unfold apart; lia).
Qed.

Theorem talk_holds : talk_contract.
Proof. exact (talk_walk memcpy_holds). Qed.

Print Assumptions talk_walk.
Print Assumptions talk_holds.
