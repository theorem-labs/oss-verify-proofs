(* check_state_data (fuzz/fuzz_transport.c:559-569), entry 0x15b58, 35 instructions, against
   check_state_data_contract (check_state_data_c.v), given bcmp_contract (lib/Prog/bcmp_c.v).
   The prologue saves ra, s0, s1 in a 32-byte frame; s1 = &g_fail_next (0x42558); then
     lw GOT.ndata (blt 1, it: abort); lw OW.ndata (bge GOT.ndata, it: abort);
     ld n->body_len, ld OW.dn[GOT.ndata].len (bne: abort);
     bcmp (n->body, OW.dn[GOT.ndata].body, n->body_len) (bnez: abort);
     lw n->counter, lw OW.dn[].counter (bne: abort); lhu n->retry, lhu OW.dn[].retry (bne: abort);
   and restores ra, s0, s1 and returns. The model's Some (check_state_data_m) makes every test go the
   no-abort way; GOT.ndata is 0 or 1 there, so the walk is done once per value, with every world address a
   literal. The world is only read: it is kept as wmem rsegs m' B. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract check_state_data_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model's Some, read as the facts the walk needs ---- *)

Lemma csd_m_some : forall Fr B n B',
  check_state_data_m Fr B n = Some (B', tt) ->
  B' = B /\ GOT_ndata B < OW_ndata B /\ 0 <= GOT_ndata B < 2 /\
  n_body_len n = OW_dn_len B (GOT_ndata B) /\ n_body_len n <= Z.of_nat (length (n_body n)) /\
  n_counter n = OW_dn_counter B (GOT_ndata B) /\ n_retry n = OW_dn_retry B (GOT_ndata B) /\
  exists db, frame_read Fr (OW_dn_body B (GOT_ndata B)) (n_body_len n) = Some db /\
             zs (firstn (Z.to_nat (n_body_len n)) (n_body n)) = zs db.
Proof.
  intros Fr B n B' H. unfold check_state_data_m in H. cbv zeta in H. revert H.
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E1 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E2 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E3 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (match ?x with Some _ => _ | None => None end) = _ -> _ => destruct x as [db|] eqn:E4 end;
    cbv beta iota; [|intros HH; discriminate HH].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E5 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E6 end;
    cbv beta iota; [intros HH; discriminate HH|].
  intros H. injection H as HB.
  apply orb_false_iff in E1. destruct E1 as [E1a E1b]. apply Z.leb_gt in E1a. apply Z.leb_gt in E1b.
  apply Z.ltb_ge in E2. apply negb_false_iff in E3. apply Z.eqb_eq in E3. apply Z.ltb_ge in E5.
  apply orb_false_iff in E6. destruct E6 as [E6 E6c]. apply orb_false_iff in E6. destruct E6 as [E6a E6b].
  apply negb_false_iff in E6a. apply negb_false_iff in E6b. apply negb_false_iff in E6c.
  apply Z.eqb_eq in E6b. apply Z.eqb_eq in E6c.
  unfold beq_bytes in E6a. destruct (list_eq_dec Z.eq_dec _ _) as [Ez|Ez]; [|discriminate E6a].
  split; [symmetry; exact HB|]. split; [lia|]. split; [lia|]. split; [exact E3|]. split; [lia|].
  split; [exact E6b|]. split; [exact E6c|]. exists db. split; [first [exact E4 | reflexivity] | exact Ez].
Qed.

(* ---- bytes, the heap frame, bcmp's model ---- *)

Lemma bat_sub : forall (segs : list Segment) m a bs k n, bytes_at segs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> bytes_at segs m (a + k) (sub bs k n).
Proof.
  intros segs m a bs k n (Ha & Hl & Hb) Hk Hn.
  assert (LS : length (sub bs k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

(* what frame_read read out of the current frame is in memory at the address it read from *)
Lemma frame_read_at : forall m fr p len db,
  bytes_at rsegs m (tf_addr fr) (tf_bytes fr) -> frame_read (Some fr) p len = Some db ->
  0 <= len -> 0 <= p < 2^64 ->
  bytes_at rsegs m p db /\ length db = Z.to_nat len.
Proof.
  intros m fr p len db HB HR Hl Hp. unfold frame_read in HR. revert HR.
  destruct (len =? 0) eqn:E0; intros HR.
  - apply Z.eqb_eq in E0. injection HR as <-. subst len. split; [apply bytes_at_nil; lia | reflexivity].
  - revert HR.
    destruct ((p - tf_addr fr <? 0) || (len <? 0) || (Z.of_nat (length (tf_bytes fr)) <? p - tf_addr fr + len)) eqn:E;
      intros HR; [discriminate HR|].
    injection HR as <-.
    apply orb_false_iff in E. destruct E as [E E3]. apply orb_false_iff in E. destruct E as [E1 E2].
    apply Z.ltb_ge in E1. apply Z.ltb_ge in E3.
    split.
    + replace p with (tf_addr fr + (p - tf_addr fr)) at 1 by lia.
      apply bat_sub; [exact HB | lia | lia].
    + apply length_sub; lia.
Qed.

(* with no current frame, only the empty read succeeds *)
Lemma frame_read_none : forall p len db, frame_read None p len = Some db -> db = [] /\ len = 0.
Proof.
  intros p len db HR. unfold frame_read in HR. revert HR.
  destruct (len =? 0) eqn:E0; intros HR; [|discriminate HR].
  apply Z.eqb_eq in E0. injection HR as <-. split; [reflexivity | exact E0].
Qed.

(* the model's beq_bytes (same unsigned bytes) is bcmp's 0 *)
Lemma memcmp_zs_eq : forall n (l r : list byte), (n <= length l)%nat -> (n <= length r)%nat ->
  zs (firstn n l) = zs (firstn n r) -> memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros l r Hl Hr He; [reflexivity|].
  destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
  cbn in He. injection He as Eab Elr. cbn [memcmp_model]. rewrite Eab, Z.eqb_refl.
  apply IH; cbn in *; [lia | lia | exact Elr].
Qed.

Lemma sgn64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Lemma u_at8_lt : forall bs k, 0 <= u_at bs k 8 < 2^64.
Proof. intros bs k. pose proof (u_at_range bs k 8) as R. change (8 * Z.of_nat 8) with 64 in R. exact R. Qed.

(* ---- tactics ---- *)

(* a closed world offset k under u_at in H, replaced by its value (vm_compute on the closed Z term only) *)
Ltac norm_off H :=
  repeat match type of H with
  | context [u_at ?B ?k ?w] =>
      lazymatch k with
      | Zpos _ => fail
      | Z0 => fail
      | _ => let v := eval vm_compute in k in replace k with v in H by reflexivity
      end
  end.

(* the read of w bytes at p + k of the notice struct NB at p, in the current memory *)
Ltac nbrd p k w :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | H : bytes_at rsegs mm p ?NB, L : length ?NB = 72%nat |- _ =>
      let R := fresh "RD" in
      assert (R : ov_read_bytes rsegs mm (Z_to_bv 64 (p + k)) w = Some (sub NB k w))
        by (exact (bytes_at_read rsegs mm p NB k w H ltac:(lia) ltac:(rewrite L; lia)))
    end
  end.

Theorem check_state_data_holds : bcmp_contract -> check_state_data_contract.
Proof.
  intros BC. unfold bcmp_contract, BCMP in BC.
  unfold check_state_data_contract, check_state_data_ENTRY, check_state_data_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' p n Fr -> HN HF WM HM Hsp ST LO WOS MI.
  destruct HN as (Hp0 & Hp8 & _ & HpS & NB & HNB & LNB & _ & _ & _ & _ & _ & _ & Hbl & Hcnt & Hrty & HBD & _ & HBDs & _).
  apply csd_m_some in HM.
  destruct HM as (-> & Hlt & Hg & Hlen & Hbody & Hc & Hr & db & Hdb & Hzs).
  unfold off_window in HpS, HBDs. unfold w_off_stack in WOS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bytes_at_bound rsegs m p NB HNB) as RNB.
  pose proof (u_at_range NB 56 8) as Rbl. rewrite Hbl in Rbl. change (8 * Z.of_nat 8) with 64 in Rbl.
  pose proof ST as (Hlo & Hhi & _).
  (* the bytes bcmp reads at OW.dn[GOT.ndata].body, as a span that the prologue's stores miss *)
  assert (FRX : exists X Y, bytes_at rsegs m X Y /\
                  (X + Z.of_nat (length Y) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= X) /\
                  forall m', bytes_at rsegs m' X Y ->
                    bytes_at rsegs m' (OW_dn_body B (GOT_ndata B)) db /\ length db = Z.to_nat (n_body_len n)).
  { destruct Fr as [fr|].
    - destruct HF as (_ & HFB & _ & HFS). unfold off_window in HFS.
      exists (tf_addr fr), (tf_bytes fr). split; [exact HFB|]. split; [exact HFS|].
      intros m' HB'. apply (frame_read_at m' fr _ _ db HB' Hdb); [lia | apply u_at8_lt].
    - apply frame_read_none in Hdb. destruct Hdb as [-> E0].
      exists 0, []. split; [apply bytes_at_nil; lia|]. split; [cbn; lia|].
      intros m' _. split; [apply bytes_at_nil; pose proof (u_at8_lt B (A_OW_dn_body (GOT_ndata B))); unfold OW_dn_body; lia|].
      rewrite E0. reflexivity. }
  clear HF Hdb. destruct FRX as (X & Y & HXY & OXY & DBX).
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 32%nat ST.
  do 7 step.                                            (* prologue; s1 = &g_fail_next; lw GOT.ndata *)
  change (s32_at B 65304) with (GOT_ndata B) in *.
  step.                                                 (* li a2, 1 *)
  assert (G : GOT_ndata B = 0 \/ GOT_ndata B = 1) by lia.
  destruct G as [G|G]; rewrite G in *;
    unfold OW_dn_len, OW_dn_counter, OW_dn_retry, OW_dn_body, A_OW_dn_len, A_OW_dn_counter, A_OW_dn_retry,
      A_OW_dn_body, OFF_OW in Hlen, Hc, Hr, DBX;
    norm_off Hlen; norm_off Hc; norm_off Hr; norm_off DBX;
    (* From 0x15b78 (blt GOT.ndata) to the return, run on both GOT.ndata = 0 and = 1 by the ; combinator. *)
    step; if_false;                                       (* blt 1, GOT.ndata *)
    step; step;                                           (* mv s0, a0; lw OW.ndata *)
    change (s32_at B 65532) with (OW_ndata B) in *;
    step;                                                 (* bge GOT.ndata, OW.ndata *)
    assert (SN : bv_signed (Z_to_bv 64 (OW_ndata B)) = OW_ndata B)
      by (apply sgn64; pose proof (s32_range B A_OW_ndata); unfold OW_ndata; lia);
    if_false;
    nbrd p 56 8%nat; step; rewrite wm_ld, Hbl;            (* ld n->body_len *)
    do 5 step;                                            (* &OW.dn[GOT.ndata]; ld .len *)
    rewrite <- Hlen;
    step; if_false;                                       (* bne body_len *)
    nbrd p 48 8%nat; step; rewrite wm_ld;                 (* ld n->body *)
    step;                                                 (* ld OW.dn[].body *)
    step;                                                 (* jal bcmp *)
    destruct (DBX _ HXY) as [Hdbb Ldb];
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := n_body n) (rs := db) (v := 0);
        [ rewrite unsigned_lit by (apply u_at8_lt); exact HBD
        | rewrite unsigned_lit by (apply u_at8_lt); exact Hdbb
        | rewrite unsigned_lit by lia; apply memcmp_zs_eq; [lia | lia |];
          rewrite (firstn_all2 db) by lia; exact Hzs
        | exact MI ]
      | wk_post_call rsegs mm ] end;
    step; if_false;                                       (* bnez a0 *)
    nbrd p 64 4%nat; step; rewrite wm_lw;                 (* lw n->counter *)
    step;                                                 (* lw OW.dn[].counter *)
    unfold s32_at; rewrite Hcnt, Hc;
    step; if_false;                                       (* bne counter *)
    nbrd p 68 2%nat; step; rewrite wm_lhu;                (* lhu n->retry *)
    step;                                                 (* lhu OW.dn[].retry *)
    rewrite Hrty, Hr;
    step; if_false;                                       (* bne retry *)
    step; step; step; step;                               (* ld ra; ld s0; ld s1; addi sp *)
    release_frame FR ST (bv_unsigned sp);
    step;                                                 (* ret *)
    finish; reflexivity.
Qed.
