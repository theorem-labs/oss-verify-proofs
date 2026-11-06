(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 260 of its 283 lines of code are new or changed and 121 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv memcpy_c LLVMFuzzerTestOneInput_c codec_main_owe_lib codec_main_oweb_lib codec_main_owex_lib.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE11 (SYSEX) of the walk of LLVMFuzzerTestOneInput in the plain image: owe()'s default case
    (fuzz_codec.c:234-250; 0x1483c-0x14848, 0x14894-0x148c4, 0x14944-0x149a8, 0x144f4-0x144f8) with the
    E_ARG / E_REFUSED / E_SPACE / E_RANGE tails 0x14800-0x14804 and 0x14848-0x1484c, and the inlined
    owe_sysex with its memcpy. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac zc G := zify_cond G; repeat (rewrite Z.mod_small in G by lia).
Ltac zmod_lia H :=
  rewrite ?unsigned_lit_wrap in H; try change (2 ^ 64) with 18446744073709551616 in H;
  Z.div_mod_to_equations; lia.

(** ---- owe()'s SYSEX answer ---- *)

Lemma owe11_spec : forall od a b c delta bytes n,
  owe_spec 11 od a b c delta bytes n =
  if 0x7f <? a then (E_ARG, noc)
  else if b =? 0x70 then (E_REFUSED, noc)
  else if 0x7f <? b then (E_RANGE, noc)
  else if 24 <? n + 5 then (E_SPACE, noc)
  else if negb (seven_bit (firstn (Z.to_nat n) bytes)) then (E_RANGE, noc)
  else let '(bs, dp) := owe_sx (u8 a) (u8 b) (firstn (Z.to_nat n) bytes) in (0, (bs, 0, dp)).
Proof. intros. destruct od; reflexivity. Qed.

(** want[0..n + 5) and want_display of a successful SYSEX call. *)
Definition sx_bs (a b : Z) (l : list byte) (n : nat) : list Z :=
  [0xf0; 0x13; u8 (u8 a); u8 (u8 b)] ++ firstn n (zb l) ++ [0xf7].
Definition sx_dp (b : Z) : Z := bit_or_0 ((u8 (u8 b) =? 0x40) || (u8 (u8 b) =? 0x30)) 1.

Lemma owe11_arg : forall k od, k_kind k = 11 -> 0x7f < k_a k -> fst (owe_k k od) = E_ARG.
Proof.
  intros k od HK Ha. unfold owe_k. rewrite HK, owe11_spec.
  destruct (Z.ltb_spec 0x7f (k_a k)); [reflexivity | lia].
Qed.

Lemma owe11_refused : forall k od, k_kind k = 11 -> k_a k <= 0x7f -> k_b k = 0x70 ->
  fst (owe_k k od) = E_REFUSED.
Proof.
  intros k od HK Ha Hb. unfold owe_k. rewrite HK, owe11_spec.
  destruct (Z.ltb_spec 0x7f (k_a k)); [lia|]. destruct (Z.eqb_spec (k_b k) 0x70); [reflexivity | lia].
Qed.

Lemma owe11_range_b : forall k od, k_kind k = 11 -> k_a k <= 0x7f -> k_b k <> 0x70 -> 0x7f < k_b k ->
  fst (owe_k k od) = E_RANGE.
Proof.
  intros k od HK Ha Hb1 Hb2. unfold owe_k. rewrite HK, owe11_spec.
  destruct (Z.ltb_spec 0x7f (k_a k)); [lia|]. destruct (Z.eqb_spec (k_b k) 0x70); [lia|].
  destruct (Z.ltb_spec 0x7f (k_b k)); [reflexivity | lia].
Qed.

Lemma owe11_space : forall k od, k_kind k = 11 -> k_a k <= 0x7f -> k_b k <> 0x70 -> k_b k <= 0x7f ->
  24 < k_n k + 5 -> fst (owe_k k od) = E_SPACE.
Proof.
  intros k od HK Ha Hb1 Hb2 Hn. unfold owe_k. rewrite HK, owe11_spec.
  destruct (Z.ltb_spec 0x7f (k_a k)); [lia|]. destruct (Z.eqb_spec (k_b k) 0x70); [lia|].
  destruct (Z.ltb_spec 0x7f (k_b k)); [lia|]. destruct (Z.ltb_spec 24 (k_n k + 5)); [reflexivity | lia].
Qed.

Lemma owe11_range_s : forall k od, k_kind k = 11 -> k_a k <= 0x7f -> k_b k <> 0x70 -> k_b k <= 0x7f ->
  k_n k + 5 <= 24 -> seven_bit (firstn (Z.to_nat (k_n k)) (zb (k_bytes k))) = false ->
  fst (owe_k k od) = E_RANGE.
Proof.
  intros k od HK Ha Hb1 Hb2 Hn H7. unfold owe_k. rewrite HK, owe11_spec.
  destruct (Z.ltb_spec 0x7f (k_a k)); [lia|]. destruct (Z.eqb_spec (k_b k) 0x70); [lia|].
  destruct (Z.ltb_spec 0x7f (k_b k)); [lia|]. destruct (Z.ltb_spec 24 (k_n k + 5)); [lia|].
  rewrite H7. reflexivity.
Qed.

Lemma owe11_ok : forall k od, k_kind k = 11 -> k_a k <= 0x7f -> k_b k <> 0x70 -> k_b k <= 0x7f ->
  k_n k + 5 <= 24 -> seven_bit (firstn (Z.to_nat (k_n k)) (zb (k_bytes k))) = true ->
  owe_k k od = (0, (sx_bs (k_a k) (k_b k) (k_bytes k) (Z.to_nat (k_n k)), 0, sx_dp (k_b k))).
Proof.
  intros k od HK Ha Hb1 Hb2 Hn H7. unfold owe_k. rewrite HK, owe11_spec.
  destruct (Z.ltb_spec 0x7f (k_a k)); [lia|]. destruct (Z.eqb_spec (k_b k) 0x70); [lia|].
  destruct (Z.ltb_spec 0x7f (k_b k)); [lia|]. destruct (Z.ltb_spec 24 (k_n k + 5)); [lia|].
  rewrite H7. reflexivity.
Qed.

(** ---- bytes ---- *)

Lemma b8_bv : forall x : byte, b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma bz_zb : forall l, bz (zb l) = l.
Proof.
  intros l. unfold bz, zb. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext.
  intros b. apply b8_bv.
Qed.

(** want[0..n + 5) as the stores and memcpy leave it. *)
Lemma sx_bytes : forall (a b : Z) (bys z : list byte) (n : nat) (ch : cell) (a' b' f : byte),
  cbytes ch = [b8 0xf0; b8 0x13] -> a' = b8 (u8 (u8 a)) -> b' = b8 (u8 (u8 b)) -> f = b8 0xf7 ->
  length bys = 24%nat -> (n <= 24)%nat ->
  firstn (length (sx_bs a b bys n))
    (cells_bytes [ch; C1 a'; C1 b'; CB n (firstn n bys); C1 f; CB (19 - n) z]) = bz (sx_bs a b bys n).
Proof.
  intros a b bys z n ch a' b' f Hch Ha Hb Hf Hl Hn. subst a' b' f.
  assert (Lf : length (firstn n bys) = n) by (rewrite length_firstn; lia).
  assert (Lz : length (firstn n (zb bys)) = n) by (rewrite length_firstn; unfold zb; rewrite length_map; lia).
  unfold sx_bs. cbn [cells_bytes]. rewrite Hch. cbn [cbytes app length].
  rewrite length_app, Lz. cbn [length firstn].
  rewrite firstn_app, Lf, firstn_firstn.
  replace (Nat.min (n + 1) n) with n by lia. replace (n + 1 - n)%nat with 1%nat by lia. cbn [firstn].
  unfold bz. cbn [map]. rewrite map_app. cbn [map].
  rewrite <- firstn_map. change (map b8 (zb bys)) with (bz (zb bys)). rewrite bz_zb. reflexivity.
Qed.

(** ---- the frame ---- *)

Lemma rw_at : forall m A B cs, rw_cells rsegs m A cs -> A = B -> rw_cells rsegs m B cs.
Proof. intros m A B cs H ->. exact H. Qed.

Ltac rebase H B := let H' := fresh "H" in pose proof (rw_at _ _ B _ H ltac:(lia)) as H'; clear H; rename H' into H.

(** The 20 bytes of want after the header cut for memcpy(want + 4, bytes, n) and the store of want[4 + n]. *)
Lemma sx_cut : forall m A pre r post n,
  rw_cells rsegs m A (pre ++ CB 20 r :: post) -> cells_size pre = 164%nat -> (n <= 19)%nat ->
  rw_cells rsegs m A pre /\
  (exists x, rw_cells rsegs m (A + 164) [CB n x]) /\
  (exists y, rw_cells rsegs m (A + 164 + Z.of_nat n) [CB 1 y]) /\
  (exists z, rw_cells rsegs m (A + 165 + Z.of_nat n) [CB (19 - n) z]) /\
  rw_cells rsegs m (A + 184) post.
Proof.
  intros m A pre r post n H Hs Hn.
  destruct (rw_cells_app_split _ _ _ _ H) as [H1 H2]. rewrite Hs in H2. change (Z.of_nat 164) with 164 in H2.
  destruct (rw_cells_app_split _ _ [CB 20 r] post H2) as [H3 H5].
  pose proof (rw_cells_split_CB rsegs m _ [] 20 r [] [n; 1%nat; (19 - n)%nat] H3 ltac:(cbn; lia)) as H4.
  cbn [app mk_CB_cells] in H4.
  destruct (rw_cells_app_split _ _ [CB n (firstn n r)] _ H4) as [Q1 Q23].
  destruct (rw_cells_app_split _ _ [CB 1 (firstn 1 (skipn n r))] _ Q23) as [Q2 Q3].
  split; [exact H1|].
  split; [eexists; exact Q1|].
  split; [eexists; eapply rw_at; [exact Q2 | cbn [cells_size csize Nat.add]; lia]|].
  split; [eexists; eapply rw_at; [exact Q3 | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  eapply rw_at; [exact H5 | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

Lemma sx_join : forall m A c1 n x f z c5 B2 B3 B4 B5,
  rw_cells rsegs m A c1 -> cells_size c1 = 164%nat ->
  rw_cells rsegs m B2 [CB n x] -> rw_cells rsegs m B3 [C1 f] -> rw_cells rsegs m B4 [CB (19 - n) z] ->
  rw_cells rsegs m B5 c5 -> (n <= 19)%nat ->
  B2 = A + 164 -> B3 = A + 164 + Z.of_nat n -> B4 = A + 165 + Z.of_nat n -> B5 = A + 184 ->
  rw_cells rsegs m A (c1 ++ [CB n x; C1 f; CB (19 - n) z] ++ c5).
Proof.
  intros m A c1 n x f z c5 B2 B3 B4 B5 H1 Hs H2 H3 H4 H5 Hn E2 E3 E4 E5. subst B2 B3 B4 B5.
  apply rw_cells_app_join; [exact H1|]. rewrite Hs. change (Z.of_nat 164) with 164.
  change ([CB n x; C1 f; CB (19 - n) z] ++ c5) with ([CB n x] ++ ([C1 f] ++ ([CB (19 - n) z] ++ c5))).
  apply rw_cells_app_join; [exact H2|].
  apply rw_cells_app_join; [eapply rw_at; [exact H3 | cbn [cells_size csize Nat.add]; lia]|].
  apply rw_cells_app_join;
    [eapply rw_at; [exact H4 | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  eapply rw_at; [exact H5 | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

(** k.bytes in the frame of a body cut. *)
Lemma body_bytes_at : forall e m k c rem tl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  bytes_at rsegs m (bv_unsigned (e_sp e) + -344) (k_bytes k).
Proof.
  intros e m k c rem tl H. unfold body_cells in H. cbn [kcall_cells app] in H.
  destruct (rw_cells_isolate _ _ _ 10 1 H) as (_ & H2 & _).
  cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in H2.
  apply rw_cells_bytes_at in H2. rewrite app_nil_r in H2.
  change (Z.of_nat 56) with 56 in H2.
  replace (bv_unsigned (e_sp e) + -344) with (bv_unsigned (e_sp e) + -400 + 56) by lia. exact H2.
Qed.

(** ---- registers ---- *)

(** The address register of the store at 0x14998 as a variable. *)
Lemma gen_a0 : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F pc fc m (E : Z),
  0 <= E < 2 ^ 64 ->
  (forall x : word, bv_unsigned x = E ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F pc fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                       s10 s11 t3 t4 t5 t6) F pc fc None m (seg_rom rsegs)).
Proof. intros. apply H0. apply unsigned_lit. exact H. Qed.

(** An equation of words over a function of one Z ranging over [lo, hi), checked by computation. *)
Ltac range_eq x lo hi :=
  lazymatch goal with |- ?L = ?R =>
    let fL := lazymatch eval pattern x in L with ?f x => f end in
    let fR := lazymatch eval pattern x in R with ?g x => g end in
    let H := fresh "RG" in
    pose proof (zall_range (fun y => Z.eqb (bv_unsigned (fL y)) (bv_unsigned (fR y))) lo hi
                  ltac:(vm_compute; reflexivity) x ltac:(lia)) as H;
    cbv beta in H; apply bv_eq; apply Z.eqb_eq; exact H
  end.

(** ---- OWE11 ---- *)

Ltac err_go code LEM F :=
  eapply owe_err_tail with (rc := code);
    [ eassumption | eassumption | eassumption | eassumption | eassumption
    | apply LEM; first [eassumption | lia]
    | cbv [E_ARG E_RANGE E_SPACE E_REFUSED]; lia
    | first [ reflexivity | apply bv_eq; vm_compute; reflexivity ]
    | eassumption | eassumption | eassumption | eassumption | exact F | eassumption ].

Lemma codec_main_owe11 : S_owe11.
Proof.
  unfold S_owe11. intros CMC e fuel HE CH.
  unfold memcpy_contract in CMC.
  unfold owe_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HK HND HRC W0 W1 W2 W3 HC FR HFR.
  replace (owe_pc 11) with 0x1483c by reflexivity.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof HREC as (_ & _ & HRD & _ & _).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & _ & _ & R11).
  specialize (R11 HK). destruct R11 as [Ra8 Rb8].
  assert (LBY : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  pose proof HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  pose proof (body_bytes_at e m1 k c rem tl FR) as BY.
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  (* 0x1483c lw a0, a; li a1, 0x80; bltu a0, a1 -> 0x14894 *)
  zstep. rewrite (sx32_small (k_a k)) by lia.
  zstep. zstep.
  if_cases E1.
  2: { zc E1. assert (Ha8 : 0x7f < k_a k) by (clear - E1 Ra; zmod_lia E1).
       zstep. zstep. err_go E_ARG owe11_arg FR. }
  zc E1. assert (Ha7 : k_a k <= 0x7f) by (clear - E1 Ra; zmod_lia E1). clear E1.
  (* 0x14894 lw s8, b; li a1, 0x70; bne s8, a1 -> 0x148a8 *)
  zstep. rewrite (sx32_small (k_b k)) by lia.
  zstep. zstep.
  if_cases E2.
  2: { zc E2. assert (Hb70 : k_b k = 0x70) by (clear - E2 Rb; zmod_lia E2).
       zstep. zstep. err_go E_REFUSED owe11_refused FR. }
  zc E2. assert (Hb70 : k_b k <> 0x70) by (clear - E2 Rb; zmod_lia E2). clear E2.
  (* 0x148a8 li a1, 0x7f; bltu a1, s8 -> 0x14800 *)
  zstep. zstep.
  if_cases E3.
  { zc E3. assert (Hb8 : 0x7f < k_b k) by (clear - E3 Rb; zmod_lia E3).
    zstep. err_go E_RANGE owe11_range_b FR. }
  zc E3. assert (Hb7 : k_b k <= 0x7f) by (clear - E3 Rb; zmod_lia E3). clear E3.
  (* 0x148b0 ld s5, n; addi a1, s5, -20; li a2, -26; bltu a2, a1 -> 0x14944 *)
  zstep. zstep. zstep. zstep.
  if_cases E4.
  2: { zify_cond E4. assert (Hn20 : 24 < k_n k + 5) by (clear - E4 Rn; zmod_lia E4).
       zstep. zstep. err_go E_SPACE owe11_space FR. }
  zify_cond E4. assert (Hn19 : k_n k <= 19) by (clear - E4 Rn; zmod_lia E4). clear E4.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  (* 0x14944-0x14960: seven_bit (bytes[0..n)) *)
  eapply sysex_check with (n := k_n k) (l := k_bytes k).
  { rewrite USP. replace (bv_unsigned (e_sp e) + -400 + 56) with (bv_unsigned (e_sp e) + -344) by lia. exact BY. }
  { rewrite LBY. change (Z.of_nat 24) with 24. lia. }
  { rewrite USP, LBY. change (Z.of_nat 24) with 24. lia. }
  { (* a byte with bit 7 set: E_RANGE *)
    intros Hbad a1x a2x a3x. zstep. err_go E_RANGE owe11_range_s FR. }
  intros H7 a1x a2x a3x.
  (* 0x14964 ld a1, 8(sp); sh a1, want[0]; sb a0, want[2]; sb s8, want[3] *)
  zstep. zstep. zstep. zstep.
  lazymatch type of FR with
  | rw_cells _ ?mm ?A (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: ?x8 :: ?x9 :: ?x10 :: ?x11 :: ?x12 ::
                       ?x13 :: ?x14 :: ?x15 :: ?x16 :: ?x17 :: ?x18 :: CB 20 ?r :: ?post) =>
      destruct (sx_cut mm A [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18]
                  r post (Z.to_nat (k_n k)) FR eq_refl ltac:(lia)) as (P1 & [jx P2] & [jy P3] & [jz P4] & P5)
  end.
  clear FR.
  rebase P2 (bv_unsigned (e_sp e) + -236).
  rebase P5 (bv_unsigned (e_sp e) + -216).
  pose proof BY as BYN. rewrite <- (firstn_skipn (Z.to_nat (k_n k)) (k_bytes k)) in BYN.
  apply bytes_at_app in BYN. destruct BYN as [BYN _].
  (* 0x14974 a0 = want + 4; a1 = bytes; a2 = n; memcpy *)
  zstep. zstep. zstep. zstep.
  assert (U236 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -236)) = bv_unsigned (e_sp e) + -236)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
    by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (k_n k)) = k_n k) by (apply unsigned_lit; lia).
  call CMC.
  { rewrite U344. exact BYN. }
  { rewrite UN, length_firstn, LBY. lia. }
  { rewrite U236, UN. exact P2. }
  { rewrite U344, U236, UN. left. lia. }
  { assumption. }
  rewrite ?U236, ?U344, ?UN in *.
  repeat match goal with H : bytes_at rsegs _ (bv_unsigned (e_sp e) + -344) (firstn _ _) |- _ => clear H end.
  match goal with H : rw_cells rsegs _ (bv_unsigned (e_sp e) + -236) _ |- _ => rename H into P2 end.
  (* 0x14984 a0 = want + n; s5 = n + 5; a1 = b - 0x30; a2 = 0xf7; sb a2, want[4 + n] *)
  zstep. zstep. zstep. zstep. zstep.
  eapply gen_a0; [ lia | intros xa Hxa ].
  rebase P3 (bv_unsigned xa + 4).
  zstep.
  (* andi a1, a1, -0x11; seqz a0, a1; sd s5, want_len; j 0x144f4; sw a0, want_display; j CHK *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch type of P5 with rw_cells _ _ _ (_ :: _ :: C4 ?v :: _) =>
    replace v with (Z_to_bv 64 (sx_dp (k_b k))) in P5 by (range_eq (k_b k) 0 128) end.
  pose proof (sx_join _ _ _ _ _ _ _ _ _ _ _ _ P1 eq_refl P2 P3 P4 P5
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as FL.
  cbn [app] in FL.
  lazymatch type of FL with rw_cells _ _ _ ?cs =>
    let r := drop16 cs in let w := but_last6 r in
    apply (body_of_flat _ _ _ _ _ _ _ _ w) in FL; [| cbn [cells_size csize]; lia] end.
  rewrite W0, W2 in FL.
  assert (LBS : Z.of_nat (length (sx_bs (k_a k) (k_b k) (k_bytes k) (Z.to_nat (k_n k)))) = k_n k + 5).
  { unfold sx_bs. rewrite !length_app, length_firstn. unfold zb. rewrite length_map, LBY. cbn [length]. lia. }
  rewrite <- LBS in FL.
  eapply (owe_ok_tail e fuel CH)
    with (bs := sx_bs (k_a k) (k_b k) (k_bytes k) (Z.to_nat (k_n k))) (key := 0) (dp := sx_dp (k_b k));
    [ exact HF | exact HREC | exact HRC | | | exact HC | exact FL | ].
  - apply owe11_ok; first [exact HK | exact H7 | lia].
  - apply sx_bytes; [ apply bytes_eq_of_unsigned; vm_compute; reflexivity
                    | rewrite b8_lit, !b8_u8; reflexivity
                    | rewrite b8_lit, !b8_u8; reflexivity
                    | apply bv_eq; vm_compute; reflexivity
                    | exact LBY | lia ].
  - split; [eassumption|]. split; [eassumption|]. split; [unfold LLVM_CODEC_STACK; eassumption|].
    split; eassumption.
Qed.
