(* proves diginet_announce_parse_contract from copy_strz_contract, the walk of diginet_announce_parse in fuzz_transport.ubsan. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_announce_parse.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_announce_parse (src/diginet_frame.c:138-151 at 835f336c) in fuzz_transport.ubsan,
   0x18520..0x185dc, 32-byte frame. The two calls of copy_strz (0x185a4: version, 0x185c0: name)
   take copy_strz_contract (U/Prog/copy_strz_c.v): before each call the 40 bytes at ap are cut
   into the field the call writes and the cells around it (uap_rw_cons_at), and joined again at
   the end (uap_rw_join_at). copy_strz_c.v states the field as copy_strz 10 9 s old for the 9
   bytes s at the source; ann_version and ann_name use the whole rest of the body, and uap_n3
   says it is the same field.
   UBSan branches to the trap at 0x185dc, not taken: 0x18548 (f & 7) and 0x1857c (ap & 7) by
   f mod 8 = 0 and ap mod 8 = 0; 0x18590 and 0x185ac (body = 0) by 0 < body; 0x18598 and 0x185b4
   (body + 15, body + 24 wrap) by body + 33 <= 2^64 on code 0.
   The stack from lo to sp stays writable: outside the two footprints memory is unchanged, and
   the frame cells and the 40 bytes at ap are writable at the end (uap_stk_end). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import copy_strz_c diginet_announce_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

(* Comparer note N3: copy_strz 10 9 reads at most 9 bytes of its source. *)
Lemma uap_n3 : forall (X old : list byte), copy_strz 10 9 (firstn 9 X) old = copy_strz 10 9 X old.
Proof.
  intros X old. unfold copy_strz.
  change (copy_len 10 9 (firstn 9 X)) with (strz_len (firstn 9 X)).
  change (copy_len 10 9 X) with (strz_len X).
  assert (E : strz_len (firstn 9 X) = strz_len X) by (unfold strz_len; rewrite firstn_firstn; reflexivity).
  rewrite E. f_equal. rewrite firstn_firstn. rewrite Nat.min_l by apply strz_len_le. reflexivity.
Qed.

Lemma uap_fs : forall (l : list byte) k n kn, kn = (k + n)%nat ->
  firstn n (skipn k l) ++ skipn kn l = skipn k l.
Proof.
  intros l k n kn ->. rewrite <- (firstn_skipn n (skipn k l)) at 2. f_equal.
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma uap_bytes_sub : forall m a l k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(** * Cells *)

(* The 40 bytes at ap as version, name, the 4 bytes not written, unknown, unknown_len. *)
Lemma uap_split40 : forall m A aj, rw_cells rsegs m A [CB 40 aj] ->
  rw_cells rsegs m A [CB 10 (firstn 10 aj); CB 10 (firstn 10 (skipn 10 aj)); CB 4 (firstn 4 (skipn 20 aj));
                      CB 8 (firstn 8 (skipn 24 aj)); CB 8 (skipn 32 aj)].
Proof.
  intros m A aj [[[Hl _] Hb] Hw]. cbn [cell_wf] in Hl.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite !length_firstn, !length_skipn, Hl. repeat split.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite (uap_fs aj 24 8 32 eq_refl), (uap_fs aj 20 4 24 eq_refl), (uap_fs aj 10 10 20 eq_refl).
    rewrite firstn_skipn. exact Hb.
  - cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.

Lemma uap_rw_cons_at : forall m A c cs A', rw_cells rsegs m A (c :: cs) ->
  A' = A + Z.of_nat (csize c) -> rw_cells rsegs m A [c] /\ rw_cells rsegs m A' cs.
Proof.
  intros m A c cs A' [[[Hc Hcs] Hb] (Ha & Hn & Hw)] ->.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite cbytes_length in Hb2 by exact Hc.
  cbn [cells_size] in Hn, Hw.
  split.
  - split; [split|].
    + cbn [cells_wf]. split; [exact Hc | exact I].
    + cbn [cells_bytes]. rewrite app_nil_r. exact Hb1.
    + cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split|].
    + exact Hcs.
    + exact Hb2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

Lemma uap_rw_join_at : forall m A c cs A', A' = A + Z.of_nat (csize c) -> cell_wf c ->
  rw_cells rsegs m A [c] -> rw_cells rsegs m A' cs -> rw_cells rsegs m A (c :: cs).
Proof.
  intros m A c cs A' -> Hc [[_ Hb1] (Ha & Hn & Hw1)] [[Hcs Hb2] (Ha2 & Hn2 & Hw2)].
  cbn [cells_bytes cells_size] in Hb1, Hn, Hw1. rewrite app_nil_r in Hb1.
  split; [split|].
  - cbn [cells_wf]. split; assumption.
  - cbn [cells_bytes]. apply bytes_at_app. split; [exact Hb1|]. rewrite cbytes_length by exact Hc. exact Hb2.
  - cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (csize c))) as [L|L].
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (csize c) + (i - Z.of_nat (csize c))) by lia. apply Hw2. lia.
Qed.

(** * The stack *)

(* A fact about the memory at entry, kept from the step and call tactics. *)
Definition uap_keep (P : Prop) : Prop := P.

Lemma uap_stk_rw : forall m A cs B, rw_cells rsegs m A cs -> B = A + Z.of_nat (cells_size cs) -> stk rsegs m A B.
Proof. intros m A cs B H ->. apply stk_of_rw_cells. exact H. Qed.

(* The stack after the function: outside its two footprints memory is the memory at entry. *)
Lemma uap_stk_end : forall m m' lo hi L1 H1 L2 H2,
  stk rsegs m lo hi -> munch [(L1, H1); (L2, H2)] m m' -> wmono rsegs m m' ->
  stk rsegs m' L1 H1 -> stk rsegs m' L2 H2 -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi L1 H1 L2 H2 (S1 & S2 & S) MU WM (P1 & P2 & P) (Q1 & Q2 & Q).
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Z.ltb_spec a L1); destruct (Z.ltb_spec a H1); destruct (Z.ltb_spec a L2); destruct (Z.ltb_spec a H2);
    try (apply P; lia); try (apply Q; lia).
  all: destruct (S a Ha) as [Hwv [b Hb]]; split; [apply WM; exact Hwv|]; exists b; unfold mrd in *;
       rewrite MU; [exact Hb|]; rewrite wa_unsigned by lia; cbn [outside]; repeat split; lia.
Qed.

(** * Words *)

Lemma uap_eqb_nz : forall x, x <> 0 -> -2^64 < x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x H1 H2. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). apply Z.eqb_neq. rewrite Z.mod_0_l by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma uap_land7 : forall x, x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x H. rewrite unsigned_lit_wrap. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma uap_land7' : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma uap_cmd_test : forall cmd, 0 <= cmd < 2^8 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224) = ann_cmd cmd.
Proof.
  assert (G : forall cmd, 0 <= cmd < 2^8 ->
    Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224)) (ann_cmd cmd) = true).
  { apply (byte_forall (fun cmd =>
      Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224)) (ann_cmd cmd))).
    vm_compute. reflexivity. }
  intros cmd Hc. apply Bool.eqb_prop. exact (G cmd Hc).
Qed.

Lemma uap_ro_of_bytes : forall m A cs, cells_wf cs -> bytes_at rsegs m A (cells_bytes cs) -> ro_cells rsegs m A cs.
Proof. intros m A cs H1 H2. split; assumption. Qed.

Ltac uap_uns := rewrite ?unsigned_lit by lia.
Ltac uap_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uap_uns; solve_cond_rec]
  end.
(* Decide a branch whose condition is a closed term. *)
Ltac uap_brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.
(* The alignment tests f & 7 and ap & 7. *)
Ltac uap_al := rewrite ?uap_land7, ?uap_land7' by assumption; uap_brc.
Ltac uap_curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Theorem diginet_announce_parse_holds : copy_strz_contract -> diginet_announce_parse_contract.
Proof.
  intros CSZ. unfold diginet_announce_parse_contract, DIGINET_ANNOUNCE_PARSE, ANN_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f ap cmd body lo bb aj Hf Hap Hf8 Hap8 Hcmd Hbody BC BF BB CA DF DB ST LO SF SB SA MI.
  assert (RC : ro_cells rsegs m (f + 30) [C1 (b8 cmd)]) by (apply uap_ro_of_bytes; [repeat split | exact BC]).
  assert (RF : ro_cells rsegs m (f + 32) [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb)))]).
  { apply uap_ro_of_bytes; [repeat split|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BF. }
  clear BC BF.
  pose proof (rw_cells_bound rsegs m ap _ CA) as HA. cbn [cells_size csize] in HA.
  pose proof (bytes_at_bound rsegs m body bb BB) as HB.
  pose proof (ro_cells_bound rsegs m (f + 30) _ RC) as HC. cbn [cells_size csize] in HC.
  pose proof (ro_cells_bound rsegs m (f + 32) _ RF) as HF. cbn [cells_size csize] in HF.
  pose proof (u64_range sp) as Rsp.
  assert (Laj : length aj = 40%nat) by (destruct CA as [[[Hl _] _] _]; exact Hl).
  assert (ST0 : uap_keep (stk rsegs m lo (bv_unsigned sp))) by exact ST.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (ap, ap + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* 0x18520: the frame; f = 0, ap = 0, f & 7 *)
  step. step. step. step. step. step.
  step. rewrite (uap_eqb_nz f) by lia; cbv iota.
  step. step. rewrite (uap_eqb_nz ap) by lia; cbv iota.
  step. step. uap_al.
  (* 0x1854c: (cmd & 0xfe) == 0xe0 *)
  step. step. step. step. rewrite uap_cmd_test by lia.
  destruct (ann_cmd cmd) eqn:AC; cbn [negb]; cbv iota.
  2: { step. step. step. step. step. step. step.
       replace (ann_code cmd (Z.of_nat (length bb))) with (-9) by (unfold ann_code; rewrite AC; reflexivity).
       apply evt_done. do 8 eexists. split; [reflexivity|]. cbn [Z.eqb].
       refine (conj MU (conj WM (conj MI (conj _ CA)))).
       eapply uap_stk_end; [exact ST0 | exact MU | exact WM | | ].
       - eapply uap_stk_rw; [exact FR | cbn [cells_size csize Nat.add]; lia].
       - eapply uap_stk_rw; [exact CA | cbn [cells_size csize Nat.add]; lia]. }
  (* 0x1855c: body_len >= 33 *)
  step. step. step.
  destruct (Z.ltb_spec (Z.of_nat (length bb)) 33) as [L33|L33].
  { uap_br false. step. step. step. step. step. step. step.
    replace (ann_code cmd (Z.of_nat (length bb))) with (-4)
      by (unfold ann_code; rewrite AC; cbn [negb];
          replace (Z.of_nat (length bb) <? 33) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    apply evt_done. do 8 eexists. split; [reflexivity|]. cbn [Z.eqb].
    refine (conj MU (conj WM (conj MI (conj _ CA)))).
    eapply uap_stk_end; [exact ST0 | exact MU | exact WM | | ].
    - eapply uap_stk_rw; [exact FR | cbn [cells_size csize Nat.add]; lia].
    - eapply uap_stk_rw; [exact CA | cbn [cells_size csize Nat.add]; lia]. }
  uap_br true.
  assert (Hcode : ann_code cmd (Z.of_nat (length bb)) = 0).
  { unfold ann_code. rewrite AC. cbn [negb].
    replace (Z.of_nat (length bb) <? 33) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  (* 0x18578: ap & 7; unknown and unknown_len; body = 0; body + 15 wraps *)
  step. step. uap_al.
  apply uap_split40 in CA.
  step. step. step. step.
  step. rewrite (uap_eqb_nz body) by lia; cbv iota.
  step. step. uap_br false.
  step. step. step.
  (* 0x185a4: copy_strz (ap, body + 15) *)
  destruct (uap_rw_cons_at _ _ _ _ (ap + 10) CA ltac:(cbn [csize]; lia)) as [CA1 CAr].
  destruct (uap_rw_cons_at _ _ _ _ (ap + 20) CAr ltac:(cbn [csize]; lia)) as [CA2 CA3].
  clear CA CAr.
  pose proof (uap_bytes_sub _ _ _ 15 9 BB ltac:(lia)) as BS1.
  uap_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply CSZ with (s := firstn 9 (skipn 15 bb)) (old := firstn 10 aj) | post_call rsegs mm ]).
  1: { uap_uns. lia. }
  1: { rewrite length_firstn, length_skipn. lia. }
  1: { uap_uns. exact BS1. }
  1: { exact CA1. }
  1: { uap_uns. lia. }
  1: { eassumption. }
  lazymatch goal with H : rw_cells rsegs _ ap [CB 10 (copy_strz _ _ _ _)] |- _ => rename H into CV end.
  (* 0x185a8: body again; body = 0; body + 24 wraps *)
  step. step. rewrite (uap_eqb_nz body) by lia; cbv iota.
  step. step. uap_br false.
  step. step. step.
  (* 0x185c0: copy_strz (ap + 10, body + 24) *)
  pose proof (uap_bytes_sub _ _ _ 24 9 BB ltac:(lia)) as BS2.
  uap_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply CSZ with (s := firstn 9 (skipn 24 bb)) (old := firstn 10 (skipn 10 aj)) | post_call rsegs mm ]).
  1: { uap_uns. lia. }
  1: { rewrite length_firstn, length_skipn. lia. }
  1: { uap_uns. exact BS2. }
  1: { exact CA2. }
  1: { uap_uns. lia. }
  1: { eassumption. }
  lazymatch goal with H : rw_cells rsegs _ (ap + 10) [CB 10 (copy_strz _ _ _ _)] |- _ => rename H into CN end.
  (* 0x185c4: the result 0, the epilogue *)
  step. step. step. step. step. step.
  uap_curmem ltac:(fun mm => assert (CAF : rw_cells rsegs mm ap (ann_cells body bb aj))).
  { unfold ann_cells, ann_version, ann_name.
    rewrite uap_n3 in CV, CN.
    apply (uap_rw_join_at _ _ _ _ (ap + 10)); [cbn [csize]; lia | | exact CV |].
    { cbn [cell_wf]. apply length_copy_strz. rewrite length_firstn. lia. }
    apply (uap_rw_join_at _ _ _ _ (ap + 20)); [cbn [csize]; lia | | exact CN | exact CA3].
    cbn [cell_wf]. apply length_copy_strz. rewrite length_firstn, length_skipn. lia. }
  apply evt_done. cbv beta. rewrite Hcode. do 8 eexists. split; [reflexivity|]. cbn [Z.eqb].
  refine (conj MU (conj WM (conj MI (conj _ CAF)))).
  eapply uap_stk_end; [exact ST0 | exact MU | exact WM | | ].
  - eapply uap_stk_rw; [exact FR | cbn [cells_size csize Nat.add]; lia].
  - eapply uap_stk_rw; [exact CAF | cbn [ann_cells cells_size csize Nat.add]; lia].
Qed.
