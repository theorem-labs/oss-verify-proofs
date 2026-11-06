(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068
X0az X09e X06n X091 X08x X08u X090 X08l X08m X094 X08n X092 X08o
X095 X093 X08z.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X08t.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0yt X0zq X0x1 X0zo X0xf X0xe X0zp X0zl X0zs X0zc X0zd X0zu X0ze X0zt X0zf X0zv X0zr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0zk.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xe OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ze OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zk.

Section NbDecodeCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc bsegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Lemma AF_SMALL : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p.
Proof using AF. exact (af_live_small RT AF). Qed.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis SM5 : stack_malloc_contract RT 5.
Hypothesis SF5 : stack_free_contract RT 5.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis EH : @nbd_EH_cps RT bptr.

Lemma rz_emit_nil : forall c T, realizes bsegs c T -> realizes bsegs c (t_emit [] T).
Proof. intros c T R. eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R. Qed.

Ltac nb_base t := lazymatch t with ?x + _ => nb_base x | _ => t end.
Ltac nb_dj1 :=
first [ exact I | llia
| lazymatch goal with |- ?h <= ?a \/ ?a2 <= ?l =>
let x := nb_base h in let y := nb_base a in
match goal with H : hid ?P |- _ =>
match P with context [x] => match P with context [y] =>
let U := fresh "U" in pose proof (H : P) as U; llia end end
end
end
| cllia ].
Ltac nb_dj := cbn [disjoint_from]; simpl_sizes; repeat (split; [nb_dj1|]); nb_dj1.
Ltac nb_tr MU WM :=
lazymatch type of MU with munch ?W ?m ?m' =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ apply (rw_cells_transport bsegs W m m' A cs) in H; [ | exact MU | exact WM | nb_dj ]
| idtac "note: nb_tr dropping" H; clear H ]
| H : ro_cells bsegs m ?A ?cs |- _ =>
first [ apply (ro_cells_transport bsegs W m m' A cs) in H; [ | exact MU | nb_dj ]
| idtac "note: nb_tr dropping" H; clear H ]
| H : bytes_at bsegs m ?A ?bs |- _ =>
first [ apply (bytes_at_transport bsegs W m m' A bs) in H; [ | exact MU | nb_dj ]
| idtac "note: nb_tr dropping" H; clear H ]
end
end.

Ltac nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU :=
lazymatch type of MU with munch ?W ?m ?m' =>
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; apply (fp_local_munch IO_FP P W m m' L IO_img MU); [| exact Pm];
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SEGTOP_A in Hx; cbn [outside]; repeat split; llia);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.
Ltac nb_io_pres ERR_rep OUT_rep IO_FP IO_img PRES :=
lazymatch type of PRES with rt_pres ?live ?frames ?sp ?m ?m' =>
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (fp_local_pres IO_FP P live frames sp m m' L IO_img PRES Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

Lemma nb_bytes_piece : forall (m m' : mem) d (bs : list byte), wr_at bsegs m d (Z.of_nat (length bs)) -> wmono bsegs m m' -> bytes_at bsegs m' d bs ->
rw_cells bsegs m' d [CB (length bs) bs].
Proof.
intros m m' d bs WR WM BY. split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport bsegs m m' d _ WR WM).
Qed.

Ltac nb_cls_with tac :=
lazymatch goal with |- aclient ?L ?Fr ?sp ?x =>
unfold aclient; cps_unf;
first [ left; tac
| right; right; left; match goal with H : In (?p, ?n) L |- _ => exists p, n; split; [exact H | tac] end
| right; right; right; left; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end
| right; right; right; right; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end ]
end.

Ltac nb_cls := first [ nb_cls_with ltac:(llia) | nb_cls_with ltac:(cllia) ].
Ltac nb_out1 :=
cps_unf;
first [ llia
| match goal with Hx : ?A <= ?x < _ |- ~ (?d <= ?x < _) =>
let a := nb_base A in let b := nb_base d in
match goal with H : hid ?P |- _ => match P with context [a] => match P with context [b] =>
let U := fresh "U" in pose proof (H : P) as U; llia end end end
end
| cllia ].
Ltac nb_trp PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H); [ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [nb_cls | nb_out1] | exact WM ]);
clear H; rename H' into H
| idtac "note: nb_trp dropping" H; clear H ]
end end
| rt_pres ?live ?frames ?sp ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H); [ apply (agree_of_pres live frames sp m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; nb_cls | exact WM ]);
clear H; rename H' into H
| idtac "note: nb_trp dropping" H; clear H ]
end end
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
lazymatch goal with IMG : forall y, in_ranges W y -> client_static y |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx;
split; [nb_cls | apply (outside_img W _ IMG); cps_unf; first [llia | cllia]]
| exact WM ]);
clear H; rename H' into H
| idtac "note: nb_trp dropping" H; clear H ]
end end end
end.
Ltac nb_unpack_tr PRES m :=
nb_trp PRES; pres_transport_g PRES ltac:(ulc); cps_pf_pres PRES;
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv bsegs m |- _ => clear MI end;
try match goal with ST : stk bsegs m _ _ |- _ => clear ST end.
Tactic Notation "nb_unpack" hyp(Hc) "as" simple_intropattern(P) :=
try unfold icpt_postF in Hc;
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_stR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end;
first
[ let m' := lazymatch type of Hc' with ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ => mm end in
match goal with
| PRES : rt_pres _ _ _ ?m m' |- _ => nb_unpack_tr PRES m
| PRES : rt_pres_fp _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
| PRES : rt_pres_ex _ _ _ _ _ ?m m' |- _ => nb_unpack_tr PRES m
end
| idtac "note: nb_unpack: no preservation fact found" ]
end.
Lemma nb_live_checked_src : forall (Σ : rts RT) (m : mem) sp lo p k s n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= s -> s + n <= p + k -> p + k <= lo -> checked_src RT Σ m sp lo s n.
Proof using AF.
intros Σ m sp lo p k s n ART0 INL H1 H2 H3. split; [intros _; split| left; lia].
- apply (acc_sub bsegs m p k s n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
Qed.
Lemma nb_live_checked_dst : forall (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at bsegs m d n -> checked_dst RT Σ m sp d n.
Proof using AF.
intros Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub bsegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.
Lemma nb_wr_at_sub : forall (m : mem) A n A' n', wr_at bsegs m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> wr_at bsegs m A' n'.
Proof. intros m A n A' n' (W0 & W1 & W2) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply W2. lia. Qed.
Lemma nb_client_static_range : forall x, client_static x -> 0x10000 <= x < SEGTOP_A.
Proof.
intros x ((lo & hi & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. unfold SEGTOP_A.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.
Lemma nb_fp_local_pres_ex : forall (W : list (Z * Z)) (P : mem -> Prop) live frames sp d n (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> rt_pres_ex live frames sp d n m m' -> SEGTOP_A <= d -> P m -> P m'.
Proof.
intros W P live frames sp d n m m' L IMG PRES HD Pm. apply (L m m' Pm). intros a Ha. apply PRES; [right; left; exact (IMG _ Ha)|].
pose proof (nb_client_static_range _ (IMG _ Ha)). lia.
Qed.
Ltac nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES :=
lazymatch type of PRES with rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
let HD := fresh "HD" in assert (HD : SEGTOP_A <= d) by (unfold SEGTOP_A; llia);
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (nb_fp_local_pres_ex IO_FP P live frames sp d n m m' L IO_img PRES HD Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP HD
end.

Lemma nb_lsp_tabs_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> lsp_tabs m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
unfold lsp_tabs, A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2.
repeat match goal with |- _ /\ _ => split end;
(apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]).
Qed.
Lemma nb_tabs_acc_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> nb_tabs_acc m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
split.
- apply K; [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode, APP_TOP; lia].
- unfold nb_smrecs, nb_smrec1, nb_smrec2, nb_smrec3, nb_smrec4, nb_smrec5, nb_smrec6, nb_smrec7, nb_smrec8.
repeat (apply Forall_cons; [cbv beta; cbn [smr_ptr];
unfold A_nb_submode1, A_nb_submode2, A_nb_submode3, A_nb_submode4, A_nb_submode5, A_nb_submode6, A_nb_submode7, A_nb_submode8;
apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]|]). apply Forall_nil.
Qed.

Ltac nb_zlits H :=
repeat rewrite <- Z.add_assoc in H;
repeat match type of H with context [Z.add (Zpos ?a) (Zpos ?b)] => let v := eval cbv in (Z.add (Zpos a) (Zpos b)) in change (Z.add (Zpos a) (Zpos b)) with v in H end.
Tactic Notation "nb_uncons" hyp(H) "as" ident(H1) := chunk_uncons H as H1; nb_zlits H.

Lemma nb_fp_local_pres_fp : forall (W : list (Z * Z)) (P : mem -> Prop) live frames sp W' (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> rt_pres_fp live frames sp W' m m' -> (forall y, client_static y -> outside W' y) -> P m -> P m'.
Proof.
intros W P live frames sp W' m m' L IMG PRES HW Pm. apply (L m m' Pm). intros a Ha. apply PRES; [right; left; exact (IMG _ Ha)| exact (HW _ (IMG _ Ha))].
Qed.

Lemma nb_ssp_guard_static : forall x, 0x658cd8 <= x < 0x658cd8 + 8 -> client_static x.
Proof.
intros x Hx. split.
- exists 0x638110, 0x65a578. split; [right; right; left; reflexivity| lia].
- intros (lo & hi & Hin & Hlh). unfold RT_STATIC in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.
Lemma nb_io_ssp_agree : forall (m m' : mem), io_ssp m -> drv_consts m' ->
(forall a : word, 0x658cd8 <= bv_unsigned a < 0x658cd8 + 8 -> m' a = m a) -> io_ssp m'.
Proof.
intros m m' (g & _ & G) DC AG. exists g. split; [exact (proj1 (proj2 DC))|].
apply (ro_cells_agree bsegs m m' _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG. lia.
Qed.

Definition nbd_msg (tw : bool) : list byte := map (fun z => Z_to_bv 8 z) (if tw then MSG_MORE_THAN_TWO_WB else MSG_INVALID_MODE).
Lemma nbd_msg_at : forall (m : mem) (tw : bool), mem_inv bsegs m -> bytes_at bsegs m (if tw then NBD_MSG_TWOWB else NBD_MSG_INVALID) (nbd_msg tw ++ [Z_to_bv 8 0]).
Proof.
intros m tw MI. destruct tw;
[ pose proof (ro_cells_image bsegs m NBD_MSG_TWOWB (nbd_msg true ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold NBD_MSG_TWOWB; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B]
| pose proof (ro_cells_image bsegs m NBD_MSG_INVALID (nbd_msg false ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold NBD_MSG_INVALID; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B] ];
cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B.
Qed.
Lemma nbd_msg_nonul : forall tw : bool, ~ In (Z_to_bv 8 0) (nbd_msg tw).
Proof. intros [|]; rewrite <- X1ch.In0_map_unsigned; vm_compute; intuition discriminate. Qed.
Lemma nbd_msg_unsigned : forall tw : bool, map bv_unsigned (nbd_msg tw) = (if tw then MSG_MORE_THAN_TWO_WB else MSG_INVALID_MODE).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma nbd_fpl_notify_bytes : forall str, fpl_msg FLnotify str 0 = notify_bytes (map bv_unsigned str).
Proof. intros str. reflexivity. Qed.

Lemma nbd_ntail : forall (usp lo : Z) (sl : nbslots) (xra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
mem_inv bsegs m -> stk bsegs m lo (usp + -576) -> SH_HI <= lo -> lo <= usp + -576 -> usp < 2^63 ->
rw_cells bsegs m (usp + -576) (slot_cells sl) ->
evt bsegs (fun ms => ms = MS (mkR xra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (usp + -576)) a0 a1 (v200 sl) a3 a4 a5 a6 a7 (Z_to_bv 64 (-2)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_NBD_X) fc None m (seg_rom bsegs))
(MS (mkR xra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RA_nbd_fprintf) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI ST0 LOS LO SPH FR. unfold PC_NBD_X, RA_nbd_fprintf, slot_cells in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
ato 0xa4450. apply evt_done. reflexivity.
Qed.

Lemma frameW2_slots : forall (m : mem) a ST A OUT f sf (ja jb jc jd je jf jg jh : list byte) (sv : list cell),
rw_cells bsegs m a (nbd_frame_w2 ST A OUT f sf ja jb jc jd je jf jg jh sv) ->
exists s : nbslots, rw_cells bsegs m a (slot_cells s) /\ rw_cells bsegs m (a + 376) sv
/\ v48 s = Z_to_bv 64 f /\ v56 s = Z_to_bv 64 f /\ v200 s = Z_to_bv 64 sf.
Proof.
intros m a ST A OUT f sf ja jb jc jd je jf jg jh sv H. unfold nbd_frame_w2 in H.
apply rw_cells_app in H. destruct H as (H & SV). cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 376) with 376 in SV.
pose proof H as [[WF _] _]. cbn in WF.
destruct WF as (_ & La & _ & _ & _ & Lb & _ & Lc & _ & _ & Ld & _ & _ & Le & _ & Lf & _ & Lg & _ & Lh & _).
destruct (CB_C8s 5 ja La) as (wa & Lwa & Ea). destruct (CB_C8s 2 jb Lb) as (wb & Lwb & Eb). destruct (CB_C8s 9 jc Lc) as (wc & Lwc & Ec).
destruct (CB_C8s 1 jd Ld) as (wd & Lwd & Ed). destruct (CB_C8s 4 je Le) as (we & Lwe & Ee). destruct (CB_C8s 5 jf Lf) as (wf & Lwf & Ef).
destruct (CB_C8s 1 jg Lg) as (wg & Lwg & Eg). destruct (CB_C8s 7 jh Lh) as (wh & Lwh & Eh).
destruct wa as [|a0 [|a1 [|a2 [|a3 [|a4 [|? ?]]]]]]; try discriminate Lwa. destruct wb as [|b0 [|b1 [|? ?]]]; try discriminate Lwb.
destruct wc as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 [|c8 [|? ?]]]]]]]]]]; try discriminate Lwc.
destruct wd as [|d0 [|? ?]]; try discriminate Lwd. destruct we as [|e0 [|e1 [|e2 [|e3 [|? ?]]]]]; try discriminate Lwe.
destruct wf as [|f0 [|f1 [|f2 [|f3 [|f4 [|? ?]]]]]]; try discriminate Lwf. destruct wg as [|g0 [|? ?]]; try discriminate Lwg.
destruct wh as [|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|? ?]]]]]]]]; try discriminate Lwh.
exists (NBS (Z_to_bv 64 0) a0 a1 a2 a3 a4 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2047)) b0 b1 (Z_to_bv 64 ST) c0 c1 c2 c3 c4 c5 c6 c7 c8
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) d0 (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 sf) e0 e1 e2 e3 (Z_to_bv 64 OUT)
f0 f1 f2 f3 f4 (Z_to_bv 64 A) g0 (Z_to_bv 64 0) h0 h1 h2 h3 h4 h5 h6 (Z_to_bv 64 f)).
split; [| split; [exact SV| cbn; repeat split; reflexivity]].
eapply rw_cells_recast; [exact H | cbn; tauto |].
cbn [slot_cells v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368].
rewrite <- Ea, <- Eb, <- Ec, <- Ed, <- Ee, <- Ef, <- Eg, <- Eh. cbn [cells_bytes cbytes map app]. rewrite <- !app_assoc. reflexivity.
Qed.

Theorem nbd_armN : nbd_armN_stmt RT OUT_rep ERR_rep IO_FP.
Proof using All.
intros st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD usp POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO576 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 sf SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg jh rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 jh14 jh24 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E48s E56s E64s E88s E168s E176s E192s E200s E240s E288s E304s E336s E344s E368s BK SB9 SSH9 STT9 c4 a36 a46 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 SMR ARM8 Hc1 OUTK ART PF SMS.

destruct ARM8 as ((a78 & ->) & BREP8 & SL8 & SH8 & QL8).
try clear Hc0. try clear Hc. try clear LOOP.
destruct BREP8 as ((rjb8 & Lrjb8 & BOBJ8) & (bsb8 & BDAT8 & Hbsb8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bsb8)) in BDAT8.
assert (Lbsb8 : Z.of_nat (length bsb8) = sb_buf_size b) by (pose proof OK5 as OK'; unfold bits_ok in OK'; rewrite Hbsb8, zlength_map_unsigned in OK'; clear - OK' SZ5; lia).

destruct (frame_live_apart RT AF Σ m fh kh PD NDs (proj1 ARTe) (proj1 INFHK) ltac:(rewrite <- LV1; exact INPD)) as (HPDF & _).
assert (DOA : hid (D + Z.of_nat (length bsb8) <= OUT \/ OUT + 8000 <= D)) by (unfold hid; clear - HPDF FO1 FO2 PD1 PD2 Lbsb8 SZ5 FSZ; lia). clear HPDF.
unfold nb_rest_pure in RST. rewrite SMS in RST. cbn beta iota zeta in RST. injection RST as <- <- <-.
destruct (af_acc_live RT AF Σ1 m8 S 2968 ltac:(assumption) INL) as (_ & ACS8).
assert (OBS8 : aobj bsegs m8 S 2968) by (split; [ulc|]; split; [ulc| exact ACS8]). clear ACS8.
assert (ACO8 : acc bsegs m8 OUT 8000) by (exact (acc_of_pres_fp RT AF Σ m m m8 usp _ fh kh OUT 8000 (proj1 ARTe) (proj1 INFHK) FO1 FO2 PF OFFW ACO)).
assert (OBO8 : aobj bsegs m8 OUT 640) by (split; [ulc|]; split; [ulc| exact (acc_sub bsegs m8 OUT 8000 OUT 640 ACO8 ltac:(lia) ltac:(lia))]). clear ACO8.
assert (LN1 : IMG_TOP_B <= OUT) by (clear - FPIMG FO1; unfold IMG_TOP_B; cps_unf; lia).
assert (LN2 : OUT + 640 <= lo) by (clear - OL; lia).
assert (LN3 : hidp (OUT + 640 <= SH_LO \/ SH_HI <= OUT)) by (clear - FPHI FO1 FO2 FSZ; unfold hidp, hid in *; cps_unf; lia).
assert (LN4 : hidp (S + 2968 <= OUT \/ OUT + 640 <= S)) by (clear - SOA; unfold hidp, hid in *; lia).
assert (LN5 : hidp (OUT + 640 <= f \/ f + 2048 <= OUT)) by (clear - OFA; unfold hidp, hid in *; lia).
assert (LN6 : hidp (OUT + 640 <= sf \/ sf + 256 <= OUT)) by (clear - OSA; unfold hidp, hid in *; lia).
assert (E56n : v56 (slots_B2n S slA) = Z_to_bv 64 f) by exact E56s.
assert (E64n : v64 (slots_B2n S slA) = Z_to_bv 64 (S + 2047)) by exact E64s.
assert (E88n : v88 (slots_B2n S slA) = Z_to_bv 64 S) by exact E88s.
assert (E168n : v168 (slots_B2n S slA) = Z_to_bv 64 (S + 2032)) by exact E168s.
assert (E176n : v176 (slots_B2n S slA) = Z_to_bv 64 (Z.shiftr (S + 2032) 3 + SHB)) by exact E176s.
assert (E192n : v192 (slots_B2n S slA) = Z_to_bv 64 (S + 2184)) by exact E192s.
assert (E200n : v200 (slots_B2n S slA) = Z_to_bv 64 sf) by exact E200s.
assert (E240n : v240 (slots_B2n S slA) = Z_to_bv 64 OUT) by exact E240s.

apply (rw_cells_split_CB bsegs _ (f + 24) [] 136 _ [] [56; 40; 40]%nat) in FT7a; [| reflexivity]. cbn [mk_CB_cells app] in FT7a.
chunk_uncons FT7a as FT7c. chunk_uncons FT7a as FT7d.
replace (f + 24 + 56) with (f + 80) in FT7d, FT7a by lia. replace (f + 80 + 40) with (f + 120) in FT7a by lia.
destruct (rw_cells_CB_f32 bsegs _ (f + 80) 10 _ FT7d) as (lpc8 & Llpc8 & LP8). clear FT7d.

destruct (f32_split bsegs m8 (S + 32) ex1 334 ltac:(lia) EXB) as (EX8a & EX8b). clear EXB.
replace (S + 32 + 4 * Z.of_nat 334) with (S + 1368) in EX8b by lia.
destruct (f32_split bsegs m8 (S + 1368) (skipn 334 ex1) 160 ltac:(rewrite length_skipn; lia) EX8b) as (EX8c & EX8d). clear EX8b.
replace (S + 1368 + 4 * Z.of_nat 160) with (S + 2008) in EX8d by lia.
assert (Lex8c : length (firstn 160 (skipn 334 ex1)) = 160%nat) by (rewrite length_firstn, length_skipn; lia).
assert (Lexa : length (firstn 334 ex1) = 334%nat) by (rewrite length_firstn; lia).
assert (Lexd : length (skipn 160 (skipn 334 ex1)) = 6%nat) by (rewrite !length_skipn; lia).
generalize dependent (firstn 334 ex1). intros exa EX8a Lexa.
generalize dependent (firstn 160 (skipn 334 ex1)). intros exc EX8c Lex8c.
generalize dependent (skipn 160 (skipn 334 ex1)). intros exd EX8d Lexd. clear ex1 LEX1.
destruct (f32_split bsegs m8 OUT ows 160 ltac:(lia) OC) as (OC8a & OC8b). clear OC.
assert (Lows8 : length (firstn 160 ows) = 160%nat) by (rewrite length_firstn; lia).
assert (Lowb : length (skipn 160 ows) = 1840%nat) by (rewrite length_skipn; lia).
generalize dependent (firstn 160 ows). intros ows0 OC8a Lows8.
generalize dependent (skipn 160 ows). intros owb OC8b Lowb.
assert (ISV8 : match nb_innov_save (set_nb_submodeID st mo) with Some k => 160 <= k /\ 4 * (k + 160) <= 8000 | None => True end) by exact ISV.
Time cps_seg (@nbd_n1 bptr usp lo S A OUT f sf gp (Z_to_bv 64 6524056) (set_nb_submodeID st mo) (slots_B2n S slA) rs7 (j_last_ol_gain j) (j_seed j)
lpc8 exc (j_interp_qlpc j) (j_mem_sp j) ows0
xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 m8
ST8 LB1 LB2 LB3 FPOS F64 BF LB4 LB5 LB6 Esf OBS8 S8 (proj1 SB9) BS1 SSH9 STT9 LB7 LB8 OBO8 OAL LN1 LN2 LN3 LN4 LN5 LN6 SL8 E56n E64n E88n E168n E176n E192n E200n E240n SH8 LP8 Llpc8
HDR8 EX8c Lex8c P3 P5 JL3 P6 JL4 P9 ISV8 P14 OC8a Lows8 CC8 MI8 FRM8).
destruct POST as (m9 & t09 & t19 & t29 & a39 & a49 & a59 & a69 & a79 & t39 & t49 & t59 & t69 & F9 & fc9 & lpc9 & exc9 & msp9 & ows9 & seed9
& MU9 & WM9 & MI9 & ST9 & FRM9 & CC9 & SH9 & LP9 & Llpc9 & HDR9 & EX9 & Lexc9 & MSP9 & Lmsp9 & SEED9 & OC9 & Lows9 & ISW9).
clear SH8 LP8 HDR8 EX8c P6 P14 OC8a OBS8 OBO8 CC8 LN1 LN2 LN3 LN4 LN5 LN6 E56n E64n E88n E168n E176n E192n E200n E240n ISV8.
unfold nbN_W in MU9.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU9.
Time nb_tr MU9 WM9. Time cps_seg_post.
cbn [nb_innov_save set_nb_submodeID] in ISW9.
destruct (nb_innov_save st) as [k|] eqn:ISK.

subst ms.
pose proof ISV as ISVk. cbn [isave_ok] in ISVk. rewrite ISK in ISVk. destruct ISVk as (K1 & K2).
destruct (f32_split bsegs m9 (OUT + 640) owb (Z.to_nat (k - 160)) ltac:(lia) OC8b) as (OW1 & OW2). clear OC8b.
replace (OUT + 640 + 4 * Z.of_nat (Z.to_nat (k - 160))) with (OUT + 4 * k) in OW2 by lia.
destruct (f32_split bsegs m9 (OUT + 4 * k) (skipn (Z.to_nat (k - 160)) owb) 160 ltac:(rewrite length_skipn; lia) OW2) as (OW2a & OW2b). clear OW2.
replace (OUT + 4 * k + 4 * Z.of_nat 160) with (OUT + 4 * k + 640) in OW2b by lia.
assert (Low1 : length (firstn (Z.to_nat (k - 160)) owb) = Z.to_nat (k - 160)) by (rewrite length_firstn; lia).
assert (Low3 : length (skipn 160 (skipn (Z.to_nat (k - 160)) owb)) = (1840 - Z.to_nat (k - 160) - 160)%nat) by (rewrite !length_skipn; lia).
pose proof (proj2 OW2a) as WRM. rewrite cells_size_f32, length_firstn, length_skipn, Lowb in WRM.
replace (Z.of_nat (4 * Nat.min 160 (1840 - Z.to_nat (k - 160)))) with 640 in WRM by lia.
generalize dependent (firstn (Z.to_nat (k - 160)) owb). intros ow1 OW1 Low1.
generalize dependent (skipn 160 (skipn (Z.to_nat (k - 160)) owb)). intros ow3 OW2b Low3.
clear OW2a owb Lowb.
assert (ACO9 : acc bsegs m9 OUT 8000) by (exact (acc_of_pres_fp RT AF Σ m m m9 usp _ fh kh OUT 8000 (proj1 ARTe) (proj1 INFHK) FO1 FO2 PF OFFW ACO)).
repeat match goal with H : ro_cells bsegs _ _ _ |- _ => clear H end.
cps_rt (MST Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (OUT + 4 * k) 640 (Z_to_bv 8 0) lo).
{ clear - FP0 FO1 FO2 BF1 LO576 SPT K1 K2 FSZ. lia. }
{ split; [intros _; split; [exact (acc_sub bsegs m9 OUT 8000 (OUT + 4 * k) 640 ACO9 ltac:(lia) ltac:(lia)) | unfold rng_class; right; left; exists fh, kh; split; [exact INFH| clear - FO1 FO2 K1 K2; lia]]|].
split; [| exact WRM].
intros i Hi. unfold aclient, in_fframe. right; right; right; left. exists fh, kh. split; [exact INFH| clear - FO1 FO2 K1 K2 Hi; lia]. }
{ cps_callok. }
intros kc10 Hc10. unfold icpt_postF in Hc10. clear ACO9.
destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ kc10 Hc10) as (ms10 & PO10 & Hc10'); clear Hc10; cbv beta in PO10.
destruct PO10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
cps_ret RS10.
rewrite (unsigned_lit (usp + -576)) in PRES10, ST10 by ulc.
nb_trp PRES10.
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF).
apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -576) (OUT + 4 * k) 640 m9 m10 PRES10).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x _ Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _). clear - HO K1 K2. lia. }
clear PF. rename PF10 into PF.
nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES10.
try match goal with A0 : ART _ _ m9 |- _ => clear A0 end. try match goal with M0 : mem_inv bsegs m9 |- _ => clear M0 end.
try match goal with S0 : stk bsegs m9 _ _ |- _ => clear S0 end.

assert (ZB : rw_cells bsegs m10 (OUT + 4 * k) [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 640))) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]).
{ apply (nb_bytes_piece m9 m10); [rewrite repeat_length; exact WRM | exact WM10 | exact BY10]. }
rewrite repeat_length in ZB.
destruct (rw_cells_CB_f32 bsegs m10 (OUT + 4 * k) 160 _ ZB) as (zw & Lzw & ZW). clear ZB BY10 WRM PRES10.
assert (OCB : rw_cells bsegs m10 (OUT + 640) (f32 (ow1 ++ zw ++ ow3))).
{ apply (f32_join bsegs m10 (OUT + 640) _ _ OW1). replace (OUT + 640 + 4 * Z.of_nat (length ow1)) with (OUT + 4 * k) by (rewrite Low1; lia).
apply (f32_join bsegs m10 (OUT + 4 * k) _ _ ZW). rewrite Lzw. replace (OUT + 4 * k + 4 * Z.of_nat 160) with (OUT + 4 * k + 640) by lia. exact OW2b. }
assert (LowbN : length (ow1 ++ zw ++ ow3) = 1840%nat) by (rewrite !length_app, Low1, Lzw, Low3; lia).
clear OW1 ZW OW2b.
generalize dependent (ow1 ++ zw ++ ow3). intros owbN OCB LowbN. clear ow1 zw ow3 Low1 Lzw Low3.
rewrite (ret_pc_even RA_nbd_n_memset ltac:(unfold RA_nbd_n_memset; lia) eq_refl) in Hc10'.

destruct (af_acc_live RT AF Σ1 m10 S 2968 ltac:(assumption) INL) as (_ & ACS10).
assert (OBS10 : aobj bsegs m10 S 2968) by (split; [ulc|]; split; [ulc| exact ACS10]). clear ACS10.
assert (LX1 : S + 2968 <= 2^47) by (clear - SB9; lia).
assert (LX2 : 0 <= sf) by (clear - SHF1; lia).
assert (LX3 : sf + 256 <= 2^47) by (clear - SHF2; lia).
assert (LX5 : S + 2968 <= usp + -576) by (clear - BS1 LOR; unfold RT_STACK in LOR; lia).
assert (LX6 : sf + 256 <= usp + -576) by (clear - SHF2 LOS LOR; unfold SH_HI, RT_STACK in *; lia).
assert (E200n : v200 (slots_B2n S slA) = Z_to_bv 64 sf) by exact E200s.
cps_seg (@nbd_n2 bptr usp S f sf gp (Z_to_bv 64 6524056) (set_nb_first (set_nb_submodeID st mo) 1) rs7 (j_last_ol_gain j) (slots_B2n S slA)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 OBS10 S8 SPOS LX1 LB8 LX2 LX3 LB3 LX5 LX6 SL8 E200n HDR9 SH9 MI10).
destruct POST as (m11 & xra11 & t011 & t111 & t211 & a011 & a111 & a311 & a411 & a511 & a611 & a711 & t311 & t411 & t511 & t611 & -> & MU11 & WM11 & MI11 & HDR11 & SH11 & SL11).
clear HDR9 SH9 OBS10 LX1 LX2 LX3 LX5 LX6 E200n SL8. rename SL11 into SL8.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU11.
nb_tr MU11 WM11. cps_seg_post.

assert (EXF : rw_cells bsegs m11 (S + 32) (f32 (exa ++ exc9 ++ exd))).
{ apply (f32_join bsegs m11 (S + 32) _ _ EX8a). rewrite Lexa. replace (S + 32 + 4 * Z.of_nat 334) with (S + 1368) by lia.
apply (f32_join bsegs m11 (S + 1368) _ _ EX9). rewrite Lexc9. replace (S + 1368 + 4 * Z.of_nat 160) with (S + 2008) by lia. exact EX8d. }
assert (LEXF : length (exa ++ exc9 ++ exd) = 500%nat) by (rewrite !length_app, Lexa, Lexc9, Lexd; reflexivity).
assert (OCF : rw_cells bsegs m11 OUT (f32 (ows9 ++ owbN))).
{ apply (f32_join bsegs m11 OUT _ _ OC9). rewrite Lows9. replace (OUT + 4 * Z.of_nat 160) with (OUT + 640) by lia. exact OCB. }
assert (LOCF : length (ows9 ++ owbN) = 2000%nat) by (rewrite length_app, Lows9, LowbN; reflexivity).
assert (E48n : v48 (slots_B2n S slA) = Z_to_bv 64 f) by exact E48s. assert (E56n : v56 (slots_B2n S slA) = Z_to_bv 64 f) by exact E56s.
chunk_cat SW5 STB. apply rw_cells_to_CB in SW5. rewrite cells_size_app, cells_size_f32, LSW5 in SW5. cbn [cells_size csize Nat.add Nat.mul] in SW5.
destruct BK as (BK1 & BK2 & BK3).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes bsegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m11 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] 0
(DecNB (nb_null (set_nb_submodeID st mo))) b1 (ows9 ++ owbN)) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BK3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST10. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact SL8. } { exact E48n. } { exact E56n. } { exact SV5. } { exact FH7. } { exact SH11. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|].
split; [pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IIS0);
exact (conj eq_refl (conj IES (conj IHP (conj (or_intror eq_refl) (conj IVOC (conj IPGB (conj MO5 (conj IDTX (conj IWB (conj IENH (conj ISR IIS0)))))))))))|].
exists (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
assert (JOK' : nb_junk_ok (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)))
by exact (conj LEXF (conj JL2 (conj JL3 (conj Lmsp9 (conj JL5 (conj JL6 (conj JL7 (conj JL8 (conj JL9 (conj JL10 (conj (conj JL11a JL11b) (conj JL12 JL13)))))))))))).
split; [exact JOK'|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK'|].
exact (conj HDR11 (conj EXF (conj P3 (conj P4 (conj P5 (conj MSP9 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj SEED9 (conj CFG8 (conj CBS5 (conj UCB5 (conj P18 P19)))))))))))))))))). }
{ intros _. exact P3. }
{ split; [exists rjb8; split; [exact Lrjb8| exact BOBJ8]|]. split; [exists bsb8; split; [apply (proj2 (u8arr_rw_CB m11 D bsb8)); exact BDAT8| exact Hbsb8]| exact BSIDE8]. }
{ exact OK5. } { exact OCF. } { exact LOCF. } { exact SW5. } { assumption. } { assumption. }
intros c12 Q12. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q12 as (Σ12 & HA12 & EL12 & EF12 & ES12 & EC12 & EP12). exists Σ12. split; [exact HA12|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [exact EL12|]. split; [exact EF12|]. split; [exact ES12|]. split; [rewrite EC12, CR1; lia| exact EP12].

destruct ISW9 as (xra9 & a09 & a19 & a29 & ->).
rename m9 into m10. rename ST9 into ST10. rename MI9 into MI10. rename OC8b into OCB. rename owb into owbN. rename Lowb into LowbN.

destruct (af_acc_live RT AF Σ1 m10 S 2968 ltac:(assumption) INL) as (_ & ACS10).
assert (OBS10 : aobj bsegs m10 S 2968) by (split; [ulc|]; split; [ulc| exact ACS10]). clear ACS10.
assert (LX1 : S + 2968 <= 2^47) by (clear - SB9; lia).
assert (LX2 : 0 <= sf) by (clear - SHF1; lia).
assert (LX3 : sf + 256 <= 2^47) by (clear - SHF2; lia).
assert (LX5 : S + 2968 <= usp + -576) by (clear - BS1 LOR; unfold RT_STACK in LOR; lia).
assert (LX6 : sf + 256 <= usp + -576) by (clear - SHF2 LOS LOR; unfold SH_HI, RT_STACK in *; lia).
assert (E200n : v200 (slots_B2n S slA) = Z_to_bv 64 sf) by exact E200s.
cps_seg (@nbd_n2 bptr usp S f sf gp (Z_to_bv 64 6524056) (set_nb_first (set_nb_submodeID st mo) 1) rs7 (j_last_ol_gain j) (slots_B2n S slA)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 OBS10 S8 SPOS LX1 LB8 LX2 LX3 LB3 LX5 LX6 SL8 E200n HDR9 SH9 MI10).
destruct POST as (m11 & xra11 & t011 & t111 & t211 & a011 & a111 & a311 & a411 & a511 & a611 & a711 & t311 & t411 & t511 & t611 & -> & MU11 & WM11 & MI11 & HDR11 & SH11 & SL11).
clear HDR9 SH9 OBS10 LX1 LX2 LX3 LX5 LX6 E200n SL8. rename SL11 into SL8.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU11.
nb_tr MU11 WM11. cps_seg_post.

assert (EXF : rw_cells bsegs m11 (S + 32) (f32 (exa ++ exc9 ++ exd))).
{ apply (f32_join bsegs m11 (S + 32) _ _ EX8a). rewrite Lexa. replace (S + 32 + 4 * Z.of_nat 334) with (S + 1368) by lia.
apply (f32_join bsegs m11 (S + 1368) _ _ EX9). rewrite Lexc9. replace (S + 1368 + 4 * Z.of_nat 160) with (S + 2008) by lia. exact EX8d. }
assert (LEXF : length (exa ++ exc9 ++ exd) = 500%nat) by (rewrite !length_app, Lexa, Lexc9, Lexd; reflexivity).
assert (OCF : rw_cells bsegs m11 OUT (f32 (ows9 ++ owbN))).
{ apply (f32_join bsegs m11 OUT _ _ OC9). rewrite Lows9. replace (OUT + 4 * Z.of_nat 160) with (OUT + 640) by lia. exact OCB. }
assert (LOCF : length (ows9 ++ owbN) = 2000%nat) by (rewrite length_app, Lows9, LowbN; reflexivity).
assert (E48n : v48 (slots_B2n S slA) = Z_to_bv 64 f) by exact E48s. assert (E56n : v56 (slots_B2n S slA) = Z_to_bv 64 f) by exact E56s.
chunk_cat SW5 STB. apply rw_cells_to_CB in SW5. rewrite cells_size_app, cells_size_f32, LSW5 in SW5. cbn [cells_size csize Nat.add Nat.mul] in SW5.
destruct BK as (BK1 & BK2 & BK3).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes bsegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m11 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] 0
(DecNB (nb_null (set_nb_submodeID st mo))) b1 (ows9 ++ owbN)) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BK3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST10. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact SL8. } { exact E48n. } { exact E56n. } { exact SV5. } { exact FH7. } { exact SH11. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|].
split; [pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IIS0);
exact (conj eq_refl (conj IES (conj IHP (conj (or_intror eq_refl) (conj IVOC (conj IPGB (conj MO5 (conj IDTX (conj IWB (conj IENH (conj ISR IIS0)))))))))))|].
exists (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
assert (JOK' : nb_junk_ok (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)))
by exact (conj LEXF (conj JL2 (conj JL3 (conj Lmsp9 (conj JL5 (conj JL6 (conj JL7 (conj JL8 (conj JL9 (conj JL10 (conj (conj JL11a JL11b) (conj JL12 JL13)))))))))))).
split; [exact JOK'|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK'|].
exact (conj HDR11 (conj EXF (conj P3 (conj P4 (conj P5 (conj MSP9 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj SEED9 (conj CFG8 (conj CBS5 (conj UCB5 (conj P18 P19)))))))))))))))))). }
{ intros _. exact P3. }
{ split; [exists rjb8; split; [exact Lrjb8| exact BOBJ8]|]. split; [exists bsb8; split; [apply (proj2 (u8arr_rw_CB m11 D bsb8)); exact BDAT8| exact Hbsb8]| exact BSIDE8]. }
{ exact OK5. } { exact OCF. } { exact LOCF. } { exact SW5. } { assumption. } { assumption. }
intros c12 Q12. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q12 as (Σ12 & HA12 & EL12 & EF12 & ES12 & EC12 & EP12). exists Σ12. split; [exact HA12|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [exact EL12|]. split; [exact EF12|]. split; [exact ES12|]. split; [rewrite EC12, CR1; lia| exact EP12].
Qed.

End NbDecodeCPS.
End B_TWIN.

Section NbDecodeCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc asegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Lemma AF_SMALL : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p.
Proof using AF. exact (af_live_small RT AF). Qed.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis SM5 : stack_malloc_contract RT 5.
Hypothesis SF5 : stack_free_contract RT 5.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis EH : @nbd_EH_cps RT bptr.

Lemma rz_emit_nil : forall c T, realizes asegs c T -> realizes asegs c (t_emit [] T).
Proof. intros c T R. eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R. Qed.

Ltac nb_base t := lazymatch t with ?x + _ => nb_base x | _ => t end.
Ltac nb_dj1 :=
first [ exact I | llia
| lazymatch goal with |- ?h <= ?a \/ ?a2 <= ?l =>
let x := nb_base h in let y := nb_base a in
match goal with H : hid ?P |- _ =>
match P with context [x] => match P with context [y] =>
let U := fresh "U" in pose proof (H : P) as U; llia end end
end
end
| cllia ].
Ltac nb_dj := cbn [disjoint_from]; simpl_sizes; repeat (split; [nb_dj1|]); nb_dj1.
Ltac nb_tr MU WM :=
lazymatch type of MU with munch ?W ?m ?m' =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
first [ apply (rw_cells_transport asegs W m m' A cs) in H; [ | exact MU | exact WM | nb_dj ]
| idtac "note: nb_tr dropping" H; clear H ]
| H : ro_cells asegs m ?A ?cs |- _ =>
first [ apply (ro_cells_transport asegs W m m' A cs) in H; [ | exact MU | nb_dj ]
| idtac "note: nb_tr dropping" H; clear H ]
| H : bytes_at asegs m ?A ?bs |- _ =>
first [ apply (bytes_at_transport asegs W m m' A bs) in H; [ | exact MU | nb_dj ]
| idtac "note: nb_tr dropping" H; clear H ]
end
end.

Ltac nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU :=
lazymatch type of MU with munch ?W ?m ?m' =>
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; apply (fp_local_munch IO_FP P W m m' L IO_img MU); [| exact Pm];
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SEGTOP_A in Hx; cbn [outside]; repeat split; llia);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.
Ltac nb_io_pres ERR_rep OUT_rep IO_FP IO_img PRES :=
lazymatch type of PRES with rt_pres ?live ?frames ?sp ?m ?m' =>
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (fp_local_pres IO_FP P live frames sp m m' L IO_img PRES Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

Lemma nb_bytes_piece : forall (m m' : mem) d (bs : list byte), wr_at asegs m d (Z.of_nat (length bs)) -> wmono asegs m m' -> bytes_at asegs m' d bs ->
rw_cells asegs m' d [CB (length bs) bs].
Proof.
intros m m' d bs WR WM BY. split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport asegs m m' d _ WR WM).
Qed.

Ltac nb_cls_with tac :=
lazymatch goal with |- aclient ?L ?Fr ?sp ?x =>
unfold aclient; cps_unf;
first [ left; tac
| right; right; left; match goal with H : In (?p, ?n) L |- _ => exists p, n; split; [exact H | tac] end
| right; right; right; left; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end
| right; right; right; right; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end ]
end.

Ltac nb_cls := first [ nb_cls_with ltac:(llia) | nb_cls_with ltac:(cllia) ].
Ltac nb_out1 :=
cps_unf;
first [ llia
| match goal with Hx : ?A <= ?x < _ |- ~ (?d <= ?x < _) =>
let a := nb_base A in let b := nb_base d in
match goal with H : hid ?P |- _ => match P with context [a] => match P with context [b] =>
let U := fresh "U" in pose proof (H : P) as U; llia end end end
end
| cllia ].
Ltac nb_trp PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with WM : wmono asegs m m' |- _ =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (apply (rw_cells_agree asegs m m' A cs H); [ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [nb_cls | nb_out1] | exact WM ]);
clear H; rename H' into H
| idtac "note: nb_trp dropping" H; clear H ]
end end
| rt_pres ?live ?frames ?sp ?m ?m' =>
lazymatch goal with WM : wmono asegs m m' |- _ =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (apply (rw_cells_agree asegs m m' A cs H); [ apply (agree_of_pres live frames sp m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; nb_cls | exact WM ]);
clear H; rename H' into H
| idtac "note: nb_trp dropping" H; clear H ]
end end
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with WM : wmono asegs m m' |- _ =>
lazymatch goal with IMG : forall y, in_ranges W y -> client_static y |- _ =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (apply (rw_cells_agree asegs m m' A cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx;
split; [nb_cls | apply (outside_img W _ IMG); cps_unf; first [llia | cllia]]
| exact WM ]);
clear H; rename H' into H
| idtac "note: nb_trp dropping" H; clear H ]
end end end
end.
Ltac nb_unpack_tr PRES m :=
nb_trp PRES; pres_transport_g PRES ltac:(ulc); cps_pf_pres PRES;
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv asegs m |- _ => clear MI end;
try match goal with ST : stk asegs m _ _ |- _ => clear ST end.
Tactic Notation "nb_unpack" hyp(Hc) "as" simple_intropattern(P) :=
try unfold icpt_postF in Hc;
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_stR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end;
first
[ let m' := lazymatch type of Hc' with ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ => mm end in
match goal with
| PRES : rt_pres _ _ _ ?m m' |- _ => nb_unpack_tr PRES m
| PRES : rt_pres_fp _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
| PRES : rt_pres_ex _ _ _ _ _ ?m m' |- _ => nb_unpack_tr PRES m
end
| idtac "note: nb_unpack: no preservation fact found" ]
end.
Lemma nb_live_checked_src : forall (Σ : rts RT) (m : mem) sp lo p k s n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= s -> s + n <= p + k -> p + k <= lo -> checked_src RT Σ m sp lo s n.
Proof using AF.
intros Σ m sp lo p k s n ART0 INL H1 H2 H3. split; [intros _; split| left; lia].
- apply (acc_sub asegs m p k s n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
Qed.
Lemma nb_live_checked_dst : forall (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at asegs m d n -> checked_dst RT Σ m sp d n.
Proof using AF.
intros Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub asegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.
Lemma nb_wr_at_sub : forall (m : mem) A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> wr_at asegs m A' n'.
Proof. intros m A n A' n' (W0 & W1 & W2) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply W2. lia. Qed.
Lemma nb_client_static_range : forall x, client_static x -> 0x10000 <= x < SEGTOP_A.
Proof.
intros x ((lo & hi & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. unfold SEGTOP_A.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.
Lemma nb_fp_local_pres_ex : forall (W : list (Z * Z)) (P : mem -> Prop) live frames sp d n (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> rt_pres_ex live frames sp d n m m' -> SEGTOP_A <= d -> P m -> P m'.
Proof.
intros W P live frames sp d n m m' L IMG PRES HD Pm. apply (L m m' Pm). intros a Ha. apply PRES; [right; left; exact (IMG _ Ha)|].
pose proof (nb_client_static_range _ (IMG _ Ha)). lia.
Qed.
Ltac nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES :=
lazymatch type of PRES with rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
let HD := fresh "HD" in assert (HD : SEGTOP_A <= d) by (unfold SEGTOP_A; llia);
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; exact (nb_fp_local_pres_ex IO_FP P live frames sp d n m m' L IO_img PRES HD Pm));
pk_io ERR_rep OUT_rep KEEP; clear KEEP HD
end.

Lemma nb_lsp_tabs_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> lsp_tabs m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj asegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
unfold lsp_tabs, A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2.
repeat match goal with |- _ /\ _ => split end;
(apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]).
Qed.
Lemma nb_tabs_acc_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> nb_tabs_acc m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj asegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
split.
- apply K; [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode, APP_TOP; lia].
- unfold nb_smrecs, nb_smrec1, nb_smrec2, nb_smrec3, nb_smrec4, nb_smrec5, nb_smrec6, nb_smrec7, nb_smrec8.
repeat (apply Forall_cons; [cbv beta; cbn [smr_ptr];
unfold A_nb_submode1, A_nb_submode2, A_nb_submode3, A_nb_submode4, A_nb_submode5, A_nb_submode6, A_nb_submode7, A_nb_submode8;
apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]|]). apply Forall_nil.
Qed.

Ltac nb_zlits H :=
repeat rewrite <- Z.add_assoc in H;
repeat match type of H with context [Z.add (Zpos ?a) (Zpos ?b)] => let v := eval cbv in (Z.add (Zpos a) (Zpos b)) in change (Z.add (Zpos a) (Zpos b)) with v in H end.
Tactic Notation "nb_uncons" hyp(H) "as" ident(H1) := chunk_uncons H as H1; nb_zlits H.

Lemma nb_fp_local_pres_fp : forall (W : list (Z * Z)) (P : mem -> Prop) live frames sp W' (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> rt_pres_fp live frames sp W' m m' -> (forall y, client_static y -> outside W' y) -> P m -> P m'.
Proof.
intros W P live frames sp W' m m' L IMG PRES HW Pm. apply (L m m' Pm). intros a Ha. apply PRES; [right; left; exact (IMG _ Ha)| exact (HW _ (IMG _ Ha))].
Qed.

Lemma nb_ssp_guard_static : forall x, 0x650498 <= x < 0x650498 + 8 -> client_static x.
Proof.
intros x Hx. split.
- exists 0x62f8d0, 0x651d38. split; [right; right; left; reflexivity| lia].
- intros (lo & hi & Hin & Hlh). unfold RT_STATIC in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.
Lemma nb_io_ssp_agree : forall (m m' : mem), io_ssp m -> drv_consts m' ->
(forall a : word, 0x650498 <= bv_unsigned a < 0x650498 + 8 -> m' a = m a) -> io_ssp m'.
Proof.
intros m m' (g & _ & G) DC AG. exists g. split; [exact (proj1 (proj2 DC))|].
apply (ro_cells_agree asegs m m' _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG. lia.
Qed.

Definition nbd_msg (tw : bool) : list byte := map (fun z => Z_to_bv 8 z) (if tw then MSG_MORE_THAN_TWO_WB else MSG_INVALID_MODE).
Lemma nbd_msg_at : forall (m : mem) (tw : bool), mem_inv asegs m -> bytes_at asegs m (if tw then NBD_MSG_TWOWB else NBD_MSG_INVALID) (nbd_msg tw ++ [Z_to_bv 8 0]).
Proof.
intros m tw MI. destruct tw;
[ pose proof (ro_cells_image asegs m NBD_MSG_TWOWB (nbd_msg true ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold NBD_MSG_TWOWB; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B]
| pose proof (ro_cells_image asegs m NBD_MSG_INVALID (nbd_msg false ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold NBD_MSG_INVALID; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B] ];
cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B.
Qed.
Lemma nbd_msg_nonul : forall tw : bool, ~ In (Z_to_bv 8 0) (nbd_msg tw).
Proof. intros [|]; rewrite <- X1ch.In0_map_unsigned; vm_compute; intuition discriminate. Qed.
Lemma nbd_msg_unsigned : forall tw : bool, map bv_unsigned (nbd_msg tw) = (if tw then MSG_MORE_THAN_TWO_WB else MSG_INVALID_MODE).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma nbd_fpl_notify_bytes : forall str, fpl_msg FLnotify str 0 = notify_bytes (map bv_unsigned str).
Proof. intros str. reflexivity. Qed.

Lemma nbd_ntail : forall (xra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-2)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_NBD_X) fc None m (seg_rom asegs))
(MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RA_nbd_fprintf) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI. unfold PC_NBD_X, RA_nbd_fprintf.
ato 0xa1a1c. apply evt_done. reflexivity.
Qed.

Theorem nbd_armN : nbd_armN_stmt RT OUT_rep ERR_rep IO_FP.
Proof using All.
intros st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD usp POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 sf SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E24s E32s E40s E48s E136s E152s E168s E240s E256s E296s E304s E312s E336s BK SB9 SSH9 STT9 c4 a36 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 SMR ARM8 Hc1 OUTK ART PF SMS.

destruct ARM8 as (-> & BREP8 & SL8 & SH8 & QL8).
try clear Hc0. try clear Hc. try clear LOOP.
destruct BREP8 as ((rjb8 & Lrjb8 & BOBJ8) & (bsb8 & BDAT8 & Hbsb8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bsb8)) in BDAT8.
assert (Lbsb8 : Z.of_nat (length bsb8) = sb_buf_size b) by (pose proof OK5 as OK'; unfold bits_ok in OK'; rewrite Hbsb8, zlength_map_unsigned in OK'; clear - OK' SZ5; lia).

destruct (frame_live_apart RT AF Σ m fh kh PD NDs (proj1 ARTe) (proj1 INFHK) ltac:(rewrite <- LV1; exact INPD)) as (HPDF & _).
assert (DOA : hid (D + Z.of_nat (length bsb8) <= OUT \/ OUT + 8000 <= D)) by (unfold hid; clear - HPDF FO1 FO2 PD1 PD2 Lbsb8 SZ5 FSZ; lia). clear HPDF.
unfold nb_rest_pure in RST. rewrite SMS in RST. cbn beta iota zeta in RST. injection RST as <- <- <-.
destruct (af_acc_live RT AF Σ1 m8 S 2968 ltac:(assumption) INL) as (_ & ACS8).
assert (OBS8 : aobj asegs m8 S 2968) by (split; [ulc|]; split; [ulc| exact ACS8]). clear ACS8.
assert (ACO8 : acc asegs m8 OUT 8000) by (exact (acc_of_pres_fp RT AF Σ m m m8 usp _ fh kh OUT 8000 (proj1 ARTe) (proj1 INFHK) FO1 FO2 PF OFFW ACO)).
assert (OBO8 : aobj asegs m8 OUT 640) by (split; [ulc|]; split; [ulc| exact (acc_sub asegs m8 OUT 8000 OUT 640 ACO8 ltac:(lia) ltac:(lia))]). clear ACO8.
assert (LN1 : IMG_TOP <= OUT) by (clear - FPIMG FO1; cps_unf; lia).
assert (LN2 : OUT + 640 <= lo) by (clear - OL; lia).
assert (LN3 : hidp (OUT + 640 <= SH_LO \/ SH_HI <= OUT)) by (clear - FPHI FO1 FO2 FSZ; unfold hidp, hid in *; cps_unf; lia).
assert (LN4 : hidp (S + 2968 <= OUT \/ OUT + 640 <= S)) by (clear - SOA; unfold hidp, hid in *; lia).
assert (LN5 : hidp (OUT + 640 <= f \/ f + 2048 <= OUT)) by (clear - OFA; unfold hidp, hid in *; lia).
assert (LN6 : hidp (OUT + 640 <= sf \/ sf + 256 <= OUT)) by (clear - OSA; unfold hidp, hid in *; lia).
assert (E168n : v168 (slots_B2n S slA) = Z_to_bv 64 OUT) by exact E168s.
assert (E240n : v240 (slots_B2n S slA) = Z_to_bv 64 0) by exact E240s.

apply (rw_cells_split_CB asegs _ (f + 24) [] 136 _ [] [56; 40; 40]%nat) in FT7a; [| reflexivity]. cbn [mk_CB_cells app] in FT7a.
chunk_uncons FT7a as FT7c. chunk_uncons FT7a as FT7d.
replace (f + 24 + 56) with (f + 80) in FT7d, FT7a by lia. replace (f + 80 + 40) with (f + 120) in FT7a by lia.
destruct (rw_cells_CB_f32 asegs _ (f + 80) 10 _ FT7d) as (lpc8 & Llpc8 & LP8). clear FT7d.

destruct (f32_split asegs m8 (S + 32) ex1 334 ltac:(lia) EXB) as (EX8a & EX8b). clear EXB.
replace (S + 32 + 4 * Z.of_nat 334) with (S + 1368) in EX8b by lia.
destruct (f32_split asegs m8 (S + 1368) (skipn 334 ex1) 160 ltac:(rewrite length_skipn; lia) EX8b) as (EX8c & EX8d). clear EX8b.
replace (S + 1368 + 4 * Z.of_nat 160) with (S + 2008) in EX8d by lia.
assert (Lex8c : length (firstn 160 (skipn 334 ex1)) = 160%nat) by (rewrite length_firstn, length_skipn; lia).
assert (Lexa : length (firstn 334 ex1) = 334%nat) by (rewrite length_firstn; lia).
assert (Lexd : length (skipn 160 (skipn 334 ex1)) = 6%nat) by (rewrite !length_skipn; lia).
generalize dependent (firstn 334 ex1). intros exa EX8a Lexa.
generalize dependent (firstn 160 (skipn 334 ex1)). intros exc EX8c Lex8c.
generalize dependent (skipn 160 (skipn 334 ex1)). intros exd EX8d Lexd. clear ex1 LEX1.
destruct (f32_split asegs m8 OUT ows 160 ltac:(lia) OC) as (OC8a & OC8b). clear OC.
assert (Lows8 : length (firstn 160 ows) = 160%nat) by (rewrite length_firstn; lia).
assert (Lowb : length (skipn 160 ows) = 1840%nat) by (rewrite length_skipn; lia).
generalize dependent (firstn 160 ows). intros ows0 OC8a Lows8.
generalize dependent (skipn 160 ows). intros owb OC8b Lowb.
assert (ISV8 : match nb_innov_save (set_nb_submodeID st mo) with Some k => 160 <= k /\ 4 * (k + 160) <= 8000 | None => True end) by exact ISV.
Time cps_seg (@nbd_n1 bptr usp lo S OUT f sf gp (Z_to_bv 64 6489176) (set_nb_submodeID st mo) (slots_B2n S slA) rs7 (j_last_ol_gain j) (j_seed j)
lpc8 exc (j_interp_qlpc j) (j_mem_sp j) ows0
xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 m8
ST8 LB1 LB2 LB3 FPOS F64 BF LB4 LB5 LB6 Esf OBS8 S8 BS1 SSH9 STT9 LB7 LB8 OBO8 OAL LN1 LN2 LN3 LN4 LN5 LN6 SL8 E168n E240n SH8 LP8 Llpc8
HDR8 EX8c Lex8c P3 P5 JL3 P6 JL4 P9 ISV8 P14 OC8a Lows8 CC8 MI8 FRM8).
destruct POST as (m9 & t09 & t19 & t29 & a39 & a49 & a59 & a69 & a79 & t39 & t49 & t59 & t69 & F9 & fc9 & lpc9 & exc9 & msp9 & ows9 & seed9
& MU9 & WM9 & MI9 & ST9 & FRM9 & CC9 & SH9 & LP9 & Llpc9 & HDR9 & EX9 & Lexc9 & MSP9 & Lmsp9 & SEED9 & OC9 & Lows9 & ISW9).
clear SH8 LP8 HDR8 EX8c P6 P14 OC8a OBS8 OBO8 CC8 LN1 LN2 LN3 LN4 LN5 LN6 E168n E240n ISV8.
unfold nbN_W in MU9.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU9.
Time nb_tr MU9 WM9. Time cps_seg_post.
cbn [nb_innov_save set_nb_submodeID] in ISW9.
destruct (nb_innov_save st) as [k|] eqn:ISK.

subst ms.
pose proof ISV as ISVk. cbn [isave_ok] in ISVk. rewrite ISK in ISVk. destruct ISVk as (K1 & K2).
destruct (f32_split asegs m9 (OUT + 640) owb (Z.to_nat (k - 160)) ltac:(lia) OC8b) as (OW1 & OW2). clear OC8b.
replace (OUT + 640 + 4 * Z.of_nat (Z.to_nat (k - 160))) with (OUT + 4 * k) in OW2 by lia.
destruct (f32_split asegs m9 (OUT + 4 * k) (skipn (Z.to_nat (k - 160)) owb) 160 ltac:(rewrite length_skipn; lia) OW2) as (OW2a & OW2b). clear OW2.
replace (OUT + 4 * k + 4 * Z.of_nat 160) with (OUT + 4 * k + 640) in OW2b by lia.
assert (Low1 : length (firstn (Z.to_nat (k - 160)) owb) = Z.to_nat (k - 160)) by (rewrite length_firstn; lia).
assert (Low3 : length (skipn 160 (skipn (Z.to_nat (k - 160)) owb)) = (1840 - Z.to_nat (k - 160) - 160)%nat) by (rewrite !length_skipn; lia).
pose proof (proj2 OW2a) as WRM. rewrite cells_size_f32, length_firstn, length_skipn, Lowb in WRM.
replace (Z.of_nat (4 * Nat.min 160 (1840 - Z.to_nat (k - 160)))) with 640 in WRM by lia.
generalize dependent (firstn (Z.to_nat (k - 160)) owb). intros ow1 OW1 Low1.
generalize dependent (skipn 160 (skipn (Z.to_nat (k - 160)) owb)). intros ow3 OW2b Low3.
clear OW2a owb Lowb.
assert (ACO9 : acc asegs m9 OUT 8000) by (exact (acc_of_pres_fp RT AF Σ m m m9 usp _ fh kh OUT 8000 (proj1 ARTe) (proj1 INFHK) FO1 FO2 PF OFFW ACO)).
repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
cps_rt (MST Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (OUT + 4 * k) 640 (Z_to_bv 8 0) lo).
{ clear - FP0 FO1 FO2 BF1 LO544 SPT K1 K2 FSZ. lia. }
{ split; [intros _; split; [exact (acc_sub asegs m9 OUT 8000 (OUT + 4 * k) 640 ACO9 ltac:(lia) ltac:(lia)) | unfold rng_class; right; left; exists fh, kh; split; [exact INFH| clear - FO1 FO2 K1 K2; lia]]|].
split; [| exact WRM].
intros i Hi. unfold aclient, in_fframe. right; right; right; left. exists fh, kh. split; [exact INFH| clear - FO1 FO2 K1 K2 Hi; lia]. }
{ cps_callok. }
intros kc10 Hc10. unfold icpt_postF in Hc10. clear ACO9.
destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ kc10 Hc10) as (ms10 & PO10 & Hc10'); clear Hc10; cbv beta in PO10.
destruct PO10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
cps_ret RS10.
rewrite (unsigned_lit (usp + -544)) in PRES10, ST10 by ulc.
nb_trp PRES10.
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF).
apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -544) (OUT + 4 * k) 640 m9 m10 PRES10).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x _ Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _). clear - HO K1 K2. lia. }
clear PF. rename PF10 into PF.
nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES10.
try match goal with A0 : ART _ _ m9 |- _ => clear A0 end. try match goal with M0 : mem_inv asegs m9 |- _ => clear M0 end.
try match goal with S0 : stk asegs m9 _ _ |- _ => clear S0 end.

assert (ZB : rw_cells asegs m10 (OUT + 4 * k) [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 640))) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]).
{ apply (nb_bytes_piece m9 m10); [rewrite repeat_length; exact WRM | exact WM10 | exact BY10]. }
rewrite repeat_length in ZB.
destruct (rw_cells_CB_f32 asegs m10 (OUT + 4 * k) 160 _ ZB) as (zw & Lzw & ZW). clear ZB BY10 WRM PRES10.
assert (OCB : rw_cells asegs m10 (OUT + 640) (f32 (ow1 ++ zw ++ ow3))).
{ apply (f32_join asegs m10 (OUT + 640) _ _ OW1). replace (OUT + 640 + 4 * Z.of_nat (length ow1)) with (OUT + 4 * k) by (rewrite Low1; lia).
apply (f32_join asegs m10 (OUT + 4 * k) _ _ ZW). rewrite Lzw. replace (OUT + 4 * k + 4 * Z.of_nat 160) with (OUT + 4 * k + 640) by lia. exact OW2b. }
assert (LowbN : length (ow1 ++ zw ++ ow3) = 1840%nat) by (rewrite !length_app, Low1, Lzw, Low3; lia).
clear OW1 ZW OW2b.
generalize dependent (ow1 ++ zw ++ ow3). intros owbN OCB LowbN. clear ow1 zw ow3 Low1 Lzw Low3.
rewrite (ret_pc_even RA_nbd_n_memset ltac:(unfold RA_nbd_n_memset; lia) eq_refl) in Hc10'.

destruct (af_acc_live RT AF Σ1 m10 S 2968 ltac:(assumption) INL) as (_ & ACS10).
assert (OBS10 : aobj asegs m10 S 2968) by (split; [ulc|]; split; [ulc| exact ACS10]). clear ACS10.
assert (LX1 : S + 2968 <= 2^47) by (clear - SB9; lia).
assert (LX2 : 0 <= sf) by (clear - SHF1; lia).
assert (LX3 : sf + 256 <= 2^47) by (clear - SHF2; lia).
cps_seg (@nbd_n2 bptr usp S f sf gp (Z_to_bv 64 6489176) (set_nb_first (set_nb_submodeID st mo) 1) rs7 (j_last_ol_gain j)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 OBS10 S8 SPOS LX1 LB8 LX2 LX3 HDR9 SH9 MI10).
destruct POST as (m11 & xra11 & t011 & t111 & t211 & a011 & a111 & a211 & a311 & a411 & a511 & a611 & a711 & t311 & t411 & t511 & t611 & -> & MU11 & WM11 & MI11 & HDR11 & SH11).
clear HDR9 SH9 OBS10 LX1 LX2 LX3.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU11.
nb_tr MU11 WM11. cps_seg_post.

assert (EXF : rw_cells asegs m11 (S + 32) (f32 (exa ++ exc9 ++ exd))).
{ apply (f32_join asegs m11 (S + 32) _ _ EX8a). rewrite Lexa. replace (S + 32 + 4 * Z.of_nat 334) with (S + 1368) by lia.
apply (f32_join asegs m11 (S + 1368) _ _ EX9). rewrite Lexc9. replace (S + 1368 + 4 * Z.of_nat 160) with (S + 2008) by lia. exact EX8d. }
assert (LEXF : length (exa ++ exc9 ++ exd) = 500%nat) by (rewrite !length_app, Lexa, Lexc9, Lexd; reflexivity).
assert (OCF : rw_cells asegs m11 OUT (f32 (ows9 ++ owbN))).
{ apply (f32_join asegs m11 OUT _ _ OC9). rewrite Lows9. replace (OUT + 4 * Z.of_nat 160) with (OUT + 640) by lia. exact OCB. }
assert (LOCF : length (ows9 ++ owbN) = 2000%nat) by (rewrite length_app, Lows9, LowbN; reflexivity).
apply rw_cells_to_CB in SL8. cbn [cells_size csize slot_cells Nat.add] in SL8.
chunk_cat SW5 STB. apply rw_cells_to_CB in SW5. rewrite cells_size_app, cells_size_f32, LSW5 in SW5. cbn [cells_size csize Nat.add Nat.mul] in SW5.
destruct BK as (BK1 & BK2 & BK3).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes asegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m11 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] 0
(DecNB (nb_null (set_nb_submodeID st mo))) b1 (ows9 ++ owbN)) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BK3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST10. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact SL8. } { exact SV5. } { exact FH7. } { exact SH11. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|].
split; [pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IIS0);
exact (conj eq_refl (conj IES (conj IHP (conj (or_intror eq_refl) (conj IVOC (conj IPGB (conj MO5 (conj IDTX (conj IWB (conj IENH (conj ISR IIS0)))))))))))|].
exists (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
assert (JOK' : nb_junk_ok (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)))
by exact (conj LEXF (conj JL2 (conj JL3 (conj Lmsp9 (conj JL5 (conj JL6 (conj JL7 (conj JL8 (conj JL9 (conj JL10 (conj (conj JL11a JL11b) (conj JL12 JL13)))))))))))).
split; [exact JOK'|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK'|].
exact (conj HDR11 (conj EXF (conj P3 (conj P4 (conj P5 (conj MSP9 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj SEED9 (conj CFG8 (conj CBS5 (conj UCB5 (conj P18 P19)))))))))))))))))). }
{ intros _. exact P3. }
{ split; [exists rjb8; split; [exact Lrjb8| exact BOBJ8]|]. split; [exists bsb8; split; [apply (proj2 (u8arr_rw_CB m11 D bsb8)); exact BDAT8| exact Hbsb8]| exact BSIDE8]. }
{ exact OK5. } { exact OCF. } { exact LOCF. } { exact SW5. } { assumption. } { assumption. }
intros c12 Q12. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q12 as (Σ12 & HA12 & EL12 & EF12 & ES12 & EC12 & EP12). exists Σ12. split; [exact HA12|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [exact EL12|]. split; [exact EF12|]. split; [exact ES12|]. split; [rewrite EC12, CR1; lia| exact EP12].

destruct ISW9 as (xra9 & a09 & a19 & a29 & ->).
rename m9 into m10. rename ST9 into ST10. rename MI9 into MI10. rename OC8b into OCB. rename owb into owbN. rename Lowb into LowbN.

destruct (af_acc_live RT AF Σ1 m10 S 2968 ltac:(assumption) INL) as (_ & ACS10).
assert (OBS10 : aobj asegs m10 S 2968) by (split; [ulc|]; split; [ulc| exact ACS10]). clear ACS10.
assert (LX1 : S + 2968 <= 2^47) by (clear - SB9; lia).
assert (LX2 : 0 <= sf) by (clear - SHF1; lia).
assert (LX3 : sf + 256 <= 2^47) by (clear - SHF2; lia).
cps_seg (@nbd_n2 bptr usp S f sf gp (Z_to_bv 64 6489176) (set_nb_first (set_nb_submodeID st mo) 1) rs7 (j_last_ol_gain j)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 OBS10 S8 SPOS LX1 LB8 LX2 LX3 HDR9 SH9 MI10).
destruct POST as (m11 & xra11 & t011 & t111 & t211 & a011 & a111 & a211 & a311 & a411 & a511 & a611 & a711 & t311 & t411 & t511 & t611 & -> & MU11 & WM11 & MI11 & HDR11 & SH11).
clear HDR9 SH9 OBS10 LX1 LX2 LX3.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU11.
nb_tr MU11 WM11. cps_seg_post.

assert (EXF : rw_cells asegs m11 (S + 32) (f32 (exa ++ exc9 ++ exd))).
{ apply (f32_join asegs m11 (S + 32) _ _ EX8a). rewrite Lexa. replace (S + 32 + 4 * Z.of_nat 334) with (S + 1368) by lia.
apply (f32_join asegs m11 (S + 1368) _ _ EX9). rewrite Lexc9. replace (S + 1368 + 4 * Z.of_nat 160) with (S + 2008) by lia. exact EX8d. }
assert (LEXF : length (exa ++ exc9 ++ exd) = 500%nat) by (rewrite !length_app, Lexa, Lexc9, Lexd; reflexivity).
assert (OCF : rw_cells asegs m11 OUT (f32 (ows9 ++ owbN))).
{ apply (f32_join asegs m11 OUT _ _ OC9). rewrite Lows9. replace (OUT + 4 * Z.of_nat 160) with (OUT + 640) by lia. exact OCB. }
assert (LOCF : length (ows9 ++ owbN) = 2000%nat) by (rewrite length_app, Lows9, LowbN; reflexivity).
apply rw_cells_to_CB in SL8. cbn [cells_size csize slot_cells Nat.add] in SL8.
chunk_cat SW5 STB. apply rw_cells_to_CB in SW5. rewrite cells_size_app, cells_size_f32, LSW5 in SW5. cbn [cells_size csize Nat.add Nat.mul] in SW5.
destruct BK as (BK1 & BK2 & BK3).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes asegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m11 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] 0
(DecNB (nb_null (set_nb_submodeID st mo))) b1 (ows9 ++ owbN)) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BK3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST10. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact SL8. } { exact SV5. } { exact FH7. } { exact SH11. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|].
split; [pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IIS0);
exact (conj eq_refl (conj IES (conj IHP (conj (or_intror eq_refl) (conj IVOC (conj IPGB (conj MO5 (conj IDTX (conj IWB (conj IENH (conj ISR IIS0)))))))))))|].
exists (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
assert (JOK' : nb_junk_ok (NBJ (j_last_ol_gain j) (exa ++ exc9 ++ exd) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) msp9 (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed9 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)))
by exact (conj LEXF (conj JL2 (conj JL3 (conj Lmsp9 (conj JL5 (conj JL6 (conj JL7 (conj JL8 (conj JL9 (conj JL10 (conj (conj JL11a JL11b) (conj JL12 JL13)))))))))))).
split; [exact JOK'|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK'|].
exact (conj HDR11 (conj EXF (conj P3 (conj P4 (conj P5 (conj MSP9 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj SEED9 (conj CFG8 (conj CBS5 (conj UCB5 (conj P18 P19)))))))))))))))))). }
{ intros _. exact P3. }
{ split; [exists rjb8; split; [exact Lrjb8| exact BOBJ8]|]. split; [exists bsb8; split; [apply (proj2 (u8arr_rw_CB m11 D bsb8)); exact BDAT8| exact Hbsb8]| exact BSIDE8]. }
{ exact OK5. } { exact OCF. } { exact LOCF. } { exact SW5. } { assumption. } { assumption. }
intros c12 Q12. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q12 as (Σ12 & HA12 & EL12 & EF12 & ES12 & EC12 & EP12). exists Σ12. split; [exact HA12|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [exact EL12|]. split; [exact EF12|]. split; [exact ES12|]. split; [rewrite EC12, CR1; lia| exact EP12].
Qed.

End NbDecodeCPS.
