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
Hypothesis ARMN : nbd_armN_stmt RT OUT_rep ERR_rep IO_FP.
Hypothesis ARMC : nbd_armC_stmt RT OUT_rep ERR_rep IO_FP.

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

Theorem nbd_armB : nbd_armB_stmt RT OUT_rep ERR_rep IO_FP.
Proof using All.
intros st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret d' b' PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 ERR0 FRM CRD usp POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH OUTC T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO576 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 sf P19 P18 P17 P16 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P2 STB OC SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg jh rb rs MU3 WM3 FRB3 FRS3 P1 P3 P15 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 MI4 ST4 rjb4 Lrjb4 BOBJ bsb4 BDAT Hbsb4 BSIDE4 REM5 jh14 jh24 FR4 OUTK Lbsb4 ART0 PF jsc LJS FJS ECBS sws LSWS SW8 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 LOOP ms c3 POST Hc1.

cbn [nbA_post] in POST.
destruct POST as (m5 & sws5 & F5 & fc5 & xra5 & t05 & t15 & t25 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & t35 & t45 & t55 & t65 & -> & FRM5 & CTX5 & MO5).
destruct CTX5 as (MU5 & WM5 & MI5 & ST5 & CC5 & REP5 & OK5 & SZ5 & SW5 & LSW5 & FR5 & CBS5 & UCB5 & GOT5 & VAR5).
clear BOBJ BDAT SW8 FR4 P16 P17 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4.
unfold nbA_W in MU5.
destruct REP5 as ((rjb5 & Lrjb5 & BOBJ5) & (bsb5 & BDAT5 & Hbsb5) & BSIDE5). unfold bits_cells in BOBJ5. apply (proj1 (u8arr_rw_CB m5 D bsb5)) in BDAT5.
pose proof (bkeep_search (nb_search_fuel b) (nb_stereo_cb st) b) as BK0. rewrite SRCH in BK0. cbn [sres_keep] in BK0. destruct BK0 as (_ & _ & BK03).
assert (Lbsb5 : Z.of_nat (length bsb5) = sb_buf_size b) by (pose proof OK5 as OK'; unfold bits_ok in OK'; rewrite Hbsb5, zlength_map_unsigned in OK'; clear - OK' BK03; lia). clear BK03.
destruct (frameA_slots m5 (usp + -576) S A OUT f sf _ _ _ _ _ _ _ _ _ _ FR5) as (slA & SL5 & SV5 & E0s & E48s & E56s & E64s & E88s & E168s & E176s & E192s & E200s & E240s & E288s & E304s & E336s & E344s & E368s).
clear FR5. replace (usp + -576 + 376) with (usp + -200) in SV5 by lia. unfold nbd_saves in SV5.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU5.
nb_tr MU5 WM5. cps_seg_post.
destruct OUTC as (st2 & RST & ->).
pose proof (bkeep_search (nb_search_fuel b) (nb_stereo_cb st) b) as BK. rewrite SRCH in BK. cbn [sres_keep] in BK.

rewrite <- IES in P15.
destruct (af_acc_live RT AF Σ1 m5 S 2968 ltac:(assumption) INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 2968) by (split; [ulc|]; split; [ulc| exact ACS5]). clear ACS5.
assert (SB9 : 0 < S /\ S + 2968 <= 140737488355328) by (split; ulc).
assert (SSH9 : hidp (S + 2968 <= SH_LO \/ SH_HI <= S)) by (unfold hidp, SH_LO, SH_HI; unfold hid in SHI; clear - SHI; lia).
assert (STT9 : IMG_TOP_B <= S) by (unfold IMG_TOP_B; unfold SEGTOP_A in STOP; lia).
cps_seg (@nbd_b1 bptr usp S A gp (Z_to_bv 64 6524056) S8 SB9 SSH9 STT9 st (j_pad1 j) slA mo).
destruct POST as (m6 & a36 & a46 & -> & MU6 & WM6 & MI6 & P15b & SL6).
clear P15 OBS5 SL5. rename P15b into P15. rename SL6 into SL5.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU6.
nb_tr MU6 WM6. cps_seg_post.

pose proof (proj2 P2) as WR2. rewrite cells_size_f32, JL1 in WR2.
destruct (f32_split bsegs m6 (S + 32) (j_excbuf j) 160 ltac:(lia) P2) as (E1 & E2). clear P2.
replace (S + 32 + 4 * Z.of_nat 160) with (S + 672) in E2 by lia.
set (bs := cells_bytes (f32 (skipn 160 (j_excbuf j)))) in *.
assert (LBS : length bs = 1360%nat) by (unfold bs; rewrite cells_bytes_length by apply cells_wf_f32; rewrite cells_size_f32, length_skipn, JL1; reflexivity).
pose proof (proj2 (proj1 E2)) as SRC. fold bs in SRC.
destruct (f32_split bsegs m6 (S + 672) (skipn 160 (j_excbuf j)) 180 ltac:(rewrite length_skipn; lia) E2) as (E2a & E2b). clear E2.
replace (S + 672 + 4 * Z.of_nat 180) with (S + 1392) in E2b by lia.
rewrite skipn_skipn in E2b. cbn [Nat.add] in E2b.
assert (WRD : wr_at bsegs m6 (S + 32) 1360) by (apply (nb_wr_at_sub m6 (S + 32) (Z.of_nat (4 * 500))); [exact WR2| lia| lia| lia]).
assert (LE2b : length (skipn 340 (j_excbuf j)) = 160%nat) by (rewrite length_skipn, JL1; reflexivity).
generalize dependent (skipn 340 (j_excbuf j)). intros e2b E2b LE2b.
clear WR2 E1 E2a. repeat match goal with H : ro_cells bsegs _ _ _ |- _ => clear H end.
cps_rt (MMV Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 (S + 32) (S + 672) bs lo).
{ rewrite LBS. reflexivity. }
{ apply (nb_live_checked_src Σ1 m6 _ lo S 2968); [assumption| exact INL| lia| rewrite LBS; lia| exact BS1]. }
{ apply (nb_live_checked_dst Σ1 m6 _ S 2968); [assumption| exact INL| lia| rewrite LBS; lia| rewrite LBS; exact WRD]. }
{ cps_callok. }
intros kc7 Hc7. unfold icpt_postF in Hc7. clear SRC.

destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ kc7 Hc7) as (ms7 & PO7 & Hc7'); clear Hc7; cbv beta in PO7.
destruct PO7 as (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & BY7).
cps_ret RS7.
rewrite (unsigned_lit (usp + -576)) in PRES7 by ulc. rewrite LBS in PRES7. change (Z.of_nat 1360) with 1360 in PRES7.
nb_trp PRES7.
assert (PF7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m m7).
{ apply (pres_fp_trans _ _ _ _ m m6 m7 PF).
apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -576) (S + 32) 1360 m6 m7 PRES7).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x _ Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & HS & _). lia. }
clear PF. rename PF7 into PF.
nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES7.
try match goal with A0 : ART _ _ m6 |- _ => clear A0 end. try match goal with M0 : mem_inv bsegs m6 |- _ => clear M0 end.
try match goal with S0 : stk bsegs m6 _ _ |- _ => clear S0 end.

rewrite (unsigned_lit (usp + -576)) in ST7 by ulc.
assert (EXA : rw_cells bsegs m7 (S + 32) (f32 (skipn 160 (j_excbuf j)))).
{ split; [split; [apply cells_wf_f32 | exact BY7]|]. rewrite cells_size_f32, length_skipn, JL1. exact (wr_at_transport bsegs m6 m7 _ _ WRD WM7). }
assert (EXB : rw_cells bsegs m7 (S + 32) (f32 (skipn 160 (j_excbuf j) ++ e2b))).
{ apply (f32_join bsegs m7 (S + 32) _ _ EXA). rewrite length_skipn, JL1. replace (S + 32 + 4 * Z.of_nat (500 - 160)) with (S + 1392) by lia. exact E2b. }
assert (LEX1 : length (skipn 160 (j_excbuf j) ++ e2b) = 500%nat) by (rewrite length_app, length_skipn, JL1, LE2b; reflexivity).
clear EXA E2b BY7 WRD PRES7 LBS. clear bs.
generalize dependent (skipn 160 (j_excbuf j) ++ e2b). intros ex1 EXB LEX1. clear e2b LE2b.

destruct (af_acc_live RT AF Σ1 m7 S 2968 ART7 INL) as (_ & ACS7).
destruct (af_acc_live RT AF Σ1 m7 PD NDs ART7 INPD) as (_ & ACD7).
assert (ACA7 : acc bsegs m7 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m7 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (OBA7 : aobj bsegs m7 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc| exact ACA7]).
assert (OBD7 : aobj bsegs m7 D (sb_buf_size b)) by (split; [clear - PD0 PD1; lia|]; split; [clear - PD2 BLPD LO576 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m7 PD NDs D _ ACD7 PD1 PD2)]).
assert (OBS7 : aobj bsegs m7 S 2968) by (split; [ulc|]; split; [ulc| exact ACS7]).
clear ACS7 ACD7 ACA7.

assert (LB1 : lo <= usp - 576 - 128) by (clear - LOR; lia).
assert (LB2 : SH_HI <= lo) by (clear - LOS; cps_unf; lia).
assert (LB3 : usp < 2^63) by (clear - SPT; lia).
assert (LB4 : f + 2048 <= APP_TOP) by (clear - FTOP; cps_unf; lia).
assert (LB5 : IMG_TOP_B <= f) by (clear - FIMG; unfold IMG_TOP_B; cps_unf; lia).
assert (LB6 : hidp (f + 2048 <= SH_LO \/ SH_HI <= f)) by (clear - FHI; unfold hidp, hid in *; cps_unf; lia).
assert (LB7 : hidp (S + 2968 <= f \/ f + 2048 <= S)) by (clear - FLA; unfold hidp, hid in *; lia).
assert (LB8 : hidp (S + 2968 <= sf \/ sf + 256 <= S)) by (clear - FLA0; unfold hidp, hid in *; lia).
assert (LB9 : IMG_TOP_B <= A) by (clear - FPIMG FA1; unfold IMG_TOP_B; cps_unf; lia).
assert (LB10 : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A)) by (clear - FPHI FA1 FA2 FSZ; unfold hidp, hid, BITS_SIZEOF in *; cps_unf; lia).
assert (LB11 : hidp (A + BITS_SIZEOF <= f \/ f + 2048 <= A)) by (clear - AFA; unfold hidp, hid, BITS_SIZEOF in *; lia).
assert (LB12 : hidp (A + BITS_SIZEOF <= sf \/ sf + 256 <= A)) by (clear - ASA; unfold hidp, hid, BITS_SIZEOF in *; lia).
assert (LB13 : hidp (S + 2968 <= A \/ A + BITS_SIZEOF <= S)) by (clear - SAA; unfold hidp, hid, BITS_SIZEOF in *; lia).
assert (LB14 : D + sb_buf_size b <= lo) by (clear - PD2 BLPD; lia).
assert (LB15 : hidp (D + sb_buf_size b <= f \/ f + 2048 <= D)) by (clear - BDF Lbsb; unfold hidp, hid in *; lia).
assert (LB16 : hidp (D + sb_buf_size b <= sf \/ sf + 256 <= D)) by (clear - BDS Lbsb; unfold hidp, hid in *; lia).

assert (BREP7 : bits_rep bsegs m7 A D b1).
{ split; [exists rjb5; split; [exact Lrjb5| exact BOBJ5]|]. split; [exists bsb5; split; [apply (proj2 (u8arr_rw_CB m7 D bsb5)); exact BDAT5| exact Hbsb5]| exact BSIDE5]. }
clear BOBJ5 BDAT5.
assert (HDR7 : rw_cells bsegs m7 S (nb_hdr_cells A_speex_nb_mode (set_nb_submodeID st mo) (j_last_ol_gain j))) by exact P1. clear P1.
lazymatch type of FRS3 with context [CB 120 ?r] => set (rs7 := r) in FRS3 end. clearbody rs7.
assert (SH7 : rw_cells bsegs m7 sf (nbd_shadow_g true false false false false false false false rs7)) by exact FRS3. clear FRS3.
lazymatch type of FRB3 with rw_cells _ _ _ [C8 ?x; C8 ?y; C8 ?z; CB 2016 ?r] =>
change [C8 x; C8 y; C8 z; CB 2016 r] with ([C8 x; C8 y; C8 z] ++ [CB 2016 r]) in FRB3 end.
apply rw_cells_app in FRB3. destruct FRB3 as [FH7 FT7]. cbn [cells_size csize Nat.add] in FT7. change (Z.of_nat 24) with 24 in FT7.
apply (rw_cells_split_CB bsegs m7 (f + 24) [] 2016 rb [] [136; 40; 1840]%nat) in FT7; [| reflexivity]. cbn [mk_CB_cells app] in FT7.
chunk_uncons FT7 as FT7a. chunk_uncons FT7 as FT7b.
replace (f + 24 + 136) with (f + 160) in FT7b, FT7 by lia. replace (f + 160 + 40) with (f + 200) in FT7 by lia.
destruct (rw_cells_CB_f32 bsegs m7 (f + 160) 10 _ FT7b) as (old7 & Lold7 & QL7). clear FT7b.
unfold cb_cells in UCB5.
pose proof (AF_LIB Σ1 m7 ART7) as LC7. pose proof (nb_lsp_tabs_art Σ1 m7 ART7) as LT7. pose proof (nb_tabs_acc_art Σ1 m7 ART7) as NTA7.
pose proof (af_client_consts RT AF Σ1 m7 ART7) as CC7.
cps_seg (@nbd_b2 bptr usp lo S A D f sf (sb_buf_size b) gp (Z_to_bv 64 6524056) (set_nb_submodeID st mo) b1 slA (j_pad1 j) rs7 old7 (j_last_ol_gain j)
(Z_to_bv 64 RA_nbd_memmove) r13 r14 r15 (Z_to_bv 64 (S + 32)) r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 F5 fc5 m7
ST7 LB1 LB2 LB3 FPOS F64 BF LB4 LB5 LB6 Esf OBS7 S8 (proj1 SB9) BS1 SSH9 LB7 LB8 OBA7 LB9 AL LB10 LB11 LB12 LB13 OBD7 LB14 LB15 LB16 SZ5 BREP7 OK5
SL5 E288s E88s E56s E200s E192s HDR7 P15 SH7 QL7 Lold7 LC7 LT7 NTA7 CC7 MI7 FRM5 ICL MO5).
destruct POST as (m8 & xra8 & t08 & t18 & t28 & a08 & a18 & a28 & a38 & a48 & a58 & a68 & t38 & t48 & t58 & t68 & F8 & fc8 & MU8 & WM8 & MI8 & ST8 & FRM8 & CC8 & HDR8 & CFG8 & ARM8).
clear SL5 HDR7 P15 SH7 QL7 BREP7 OBA7 OBD7 OBS7 LC7 LT7 NTA7 CC7 CC5.
unfold nb_cfg_cells in CFG8.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU8.
nb_tr MU8 WM8. cps_seg_post.
cbn [nb_submodeID set_nb_submodeID] in ARM8.
assert (SMS : submode_at nb_submodes mo = match smrec_at mo with Some r => Some (smr_sm r) | None => None end).
{ clear - MO5. assert (C : mo = 0 \/ mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; reflexivity. }
destruct (smrec_at mo) as [smr|] eqn:SMR.
all: swap 1 2.
exact (ARMN st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO576 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg jh rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 jh14 jh24 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E48s E56s E64s E88s E168s E176s E192s E200s E240s E288s E304s E336s E344s E368s BK SB9 SSH9 STT9 c4 a36 a46 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 SMR ARM8 Hc1 OUTK ART PF SMS).
exact (ARMC st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO576 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg jh rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 jh14 jh24 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E48s E56s E64s E88s E168s E176s E192s E200s E240s E288s E304s E336s E344s E368s BK SB9 SSH9 STT9 c4 a36 a46 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 smr SMR ARM8 Hc1 OUTK ART PF SMS).
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
Hypothesis ARMN : nbd_armN_stmt RT OUT_rep ERR_rep IO_FP.
Hypothesis ARMC : nbd_armC_stmt RT OUT_rep ERR_rep IO_FP.

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

Theorem nbd_armB : nbd_armB_stmt RT OUT_rep ERR_rep IO_FP.
Proof using All.
intros st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret d' b' PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 ERR0 FRM CRD usp POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH OUTC T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 sf P19 P18 P17 P16 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P2 STB OC SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 FRB3 FRS3 P1 P3 P15 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 MI4 ST4 rjb4 Lrjb4 BOBJ bsb4 BDAT Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 FR4 OUTK Lbsb4 ART0 PF jsc LJS FJS ECBS sws LSWS SW8 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 LOOP ms c3 POST Hc1.

cbn [nbA_post] in POST.
destruct POST as (m5 & sws5 & F5 & fc5 & xra5 & t05 & t15 & t25 & a15 & a25 & a35 & a55 & a65 & a75 & t35 & t45 & t55 & t65 & -> & FRM5 & CTX5 & MO5).
destruct CTX5 as (MU5 & WM5 & MI5 & ST5 & CC5 & REP5 & OK5 & SZ5 & SW5 & LSW5 & FR5 & CBS5 & UCB5 & GOT5 & VAR5).
clear BOBJ BDAT SW8 FR4 P16 P17 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4.
unfold nbA_W in MU5.
destruct REP5 as ((rjb5 & Lrjb5 & BOBJ5) & (bsb5 & BDAT5 & Hbsb5) & BSIDE5). unfold bits_cells in BOBJ5. apply (proj1 (u8arr_rw_CB m5 D bsb5)) in BDAT5.
pose proof (bkeep_search (nb_search_fuel b) (nb_stereo_cb st) b) as BK0. rewrite SRCH in BK0. cbn [sres_keep] in BK0. destruct BK0 as (_ & _ & BK03).
assert (Lbsb5 : Z.of_nat (length bsb5) = sb_buf_size b) by (pose proof OK5 as OK'; unfold bits_ok in OK'; rewrite Hbsb5, zlength_map_unsigned in OK'; clear - OK' BK03; lia). clear BK03.
destruct (frameA_slots m5 (usp + -544) S A OUT f _ _ _ _ _ _ _ _ _ FR5) as (slA & SL5 & SV5 & E0s & E24s & E32s & E40s & E48s & E136s & E152s & E168s & E240s & E256s & E296s & E304s & E312s & E336s).
clear FR5. replace (usp + -544 + 344) with (usp + -200) in SV5 by lia. unfold nbd_saves in SV5.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU5.
nb_tr MU5 WM5. cps_seg_post.
destruct OUTC as (st2 & RST & ->).
pose proof (bkeep_search (nb_search_fuel b) (nb_stereo_cb st) b) as BK. rewrite SRCH in BK. cbn [sres_keep] in BK.

rewrite <- IES in P15.
destruct (af_acc_live RT AF Σ1 m5 S 2968 ltac:(assumption) INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 2968) by (split; [ulc|]; split; [ulc| exact ACS5]). clear ACS5.
assert (SB9 : 0 < S /\ S + 2968 <= 140737488355328) by (split; ulc).
assert (SSH9 : hidp (S + 2968 <= SH_LO \/ SH_HI <= S)) by (unfold hidp, SH_LO, SH_HI; unfold hid in SHI; clear - SHI; lia).
assert (STT9 : IMG_TOP <= S) by (unfold IMG_TOP; exact STOP).
cps_seg (@nbd_b1 bptr usp S f sf gp (Z_to_bv 64 6489176) S8 SB9 SSH9 STT9 st (j_pad1 j) mo).
destruct POST as (m6 & a36 & -> & MU6 & WM6 & MI6 & P15b).
clear P15 OBS5. rename P15b into P15.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU6.
nb_tr MU6 WM6. cps_seg_post.

pose proof (proj2 P2) as WR2. rewrite cells_size_f32, JL1 in WR2.
destruct (f32_split asegs m6 (S + 32) (j_excbuf j) 160 ltac:(lia) P2) as (E1 & E2). clear P2.
replace (S + 32 + 4 * Z.of_nat 160) with (S + 672) in E2 by lia.
set (bs := cells_bytes (f32 (skipn 160 (j_excbuf j)))) in *.
assert (LBS : length bs = 1360%nat) by (unfold bs; rewrite cells_bytes_length by apply cells_wf_f32; rewrite cells_size_f32, length_skipn, JL1; reflexivity).
pose proof (proj2 (proj1 E2)) as SRC. fold bs in SRC.
destruct (f32_split asegs m6 (S + 672) (skipn 160 (j_excbuf j)) 180 ltac:(rewrite length_skipn; lia) E2) as (E2a & E2b). clear E2.
replace (S + 672 + 4 * Z.of_nat 180) with (S + 1392) in E2b by lia.
rewrite skipn_skipn in E2b. cbn [Nat.add] in E2b.
assert (WRD : wr_at asegs m6 (S + 32) 1360) by (apply (nb_wr_at_sub m6 (S + 32) (Z.of_nat (4 * 500))); [exact WR2| lia| lia| lia]).
assert (LE2b : length (skipn 340 (j_excbuf j)) = 160%nat) by (rewrite length_skipn, JL1; reflexivity).
generalize dependent (skipn 340 (j_excbuf j)). intros e2b E2b LE2b.
clear WR2 E1 E2a. repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
cps_rt (MMV Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 (S + 32) (S + 672) bs lo).
{ rewrite LBS. reflexivity. }
{ apply (nb_live_checked_src Σ1 m6 _ lo S 2968); [assumption| exact INL| lia| rewrite LBS; lia| exact BS1]. }
{ apply (nb_live_checked_dst Σ1 m6 _ S 2968); [assumption| exact INL| lia| rewrite LBS; lia| rewrite LBS; exact WRD]. }
{ cps_callok. }
intros kc7 Hc7. unfold icpt_postF in Hc7. clear SRC.

destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ kc7 Hc7) as (ms7 & PO7 & Hc7'); clear Hc7; cbv beta in PO7.
destruct PO7 as (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & BY7).
cps_ret RS7.
rewrite (unsigned_lit (usp + -544)) in PRES7 by ulc. rewrite LBS in PRES7. change (Z.of_nat 1360) with 1360 in PRES7.
nb_trp PRES7.
assert (PF7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m m7).
{ apply (pres_fp_trans _ _ _ _ m m6 m7 PF).
apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -544) (S + 32) 1360 m6 m7 PRES7).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x _ Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & HS & _). lia. }
clear PF. rename PF7 into PF.
nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES7.
try match goal with A0 : ART _ _ m6 |- _ => clear A0 end. try match goal with M0 : mem_inv asegs m6 |- _ => clear M0 end.
try match goal with S0 : stk asegs m6 _ _ |- _ => clear S0 end.

rewrite (unsigned_lit (usp + -544)) in ST7 by ulc.
assert (EXA : rw_cells asegs m7 (S + 32) (f32 (skipn 160 (j_excbuf j)))).
{ split; [split; [apply cells_wf_f32 | exact BY7]|]. rewrite cells_size_f32, length_skipn, JL1. exact (wr_at_transport asegs m6 m7 _ _ WRD WM7). }
assert (EXB : rw_cells asegs m7 (S + 32) (f32 (skipn 160 (j_excbuf j) ++ e2b))).
{ apply (f32_join asegs m7 (S + 32) _ _ EXA). rewrite length_skipn, JL1. replace (S + 32 + 4 * Z.of_nat (500 - 160)) with (S + 1392) by lia. exact E2b. }
assert (LEX1 : length (skipn 160 (j_excbuf j) ++ e2b) = 500%nat) by (rewrite length_app, length_skipn, JL1, LE2b; reflexivity).
clear EXA E2b BY7 WRD PRES7 LBS. clear bs.
generalize dependent (skipn 160 (j_excbuf j) ++ e2b). intros ex1 EXB LEX1. clear e2b LE2b.

destruct (af_acc_live RT AF Σ1 m7 S 2968 ART7 INL) as (_ & ACS7).
destruct (af_acc_live RT AF Σ1 m7 PD NDs ART7 INPD) as (_ & ACD7).
assert (ACA7 : acc asegs m7 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m7 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (OBA7 : aobj asegs m7 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc| exact ACA7]).
assert (OBD7 : aobj asegs m7 D (sb_buf_size b)) by (split; [clear - PD0 PD1; lia|]; split; [clear - PD2 BLPD LO544 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m7 PD NDs D _ ACD7 PD1 PD2)]).
assert (OBS7 : aobj asegs m7 S 2968) by (split; [ulc|]; split; [ulc| exact ACS7]).
clear ACS7 ACD7 ACA7.

assert (LB1 : lo <= usp - 544 - 128) by (clear - LOR; lia).
assert (LB2 : SH_HI <= lo) by (clear - LOS; cps_unf; lia).
assert (LB3 : usp < 2^63) by (clear - SPT; lia).
assert (LB4 : f + 2048 <= APP_TOP) by (clear - FTOP; cps_unf; lia).
assert (LB5 : IMG_TOP <= f) by (clear - FIMG; cps_unf; lia).
assert (LB6 : hidp (f + 2048 <= SH_LO \/ SH_HI <= f)) by (clear - FHI; unfold hidp, hid in *; cps_unf; lia).
assert (LB7 : hidp (S + 2968 <= f \/ f + 2048 <= S)) by (clear - FLA; unfold hidp, hid in *; lia).
assert (LB8 : hidp (S + 2968 <= sf \/ sf + 256 <= S)) by (clear - FLA0; unfold hidp, hid in *; lia).
assert (LB9 : IMG_TOP <= A) by (clear - FPIMG FA1; cps_unf; lia).
assert (LB10 : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A)) by (clear - FPHI FA1 FA2 FSZ; unfold hidp, hid, BITS_SIZEOF in *; cps_unf; lia).
assert (LB11 : hidp (A + BITS_SIZEOF <= f \/ f + 2048 <= A)) by (clear - AFA; unfold hidp, hid, BITS_SIZEOF in *; lia).
assert (LB12 : hidp (A + BITS_SIZEOF <= sf \/ sf + 256 <= A)) by (clear - ASA; unfold hidp, hid, BITS_SIZEOF in *; lia).
assert (LB13 : hidp (S + 2968 <= A \/ A + BITS_SIZEOF <= S)) by (clear - SAA; unfold hidp, hid, BITS_SIZEOF in *; lia).
assert (LB14 : D + sb_buf_size b <= lo) by (clear - PD2 BLPD; lia).
assert (LB15 : hidp (D + sb_buf_size b <= f \/ f + 2048 <= D)) by (clear - BDF Lbsb; unfold hidp, hid in *; lia).
assert (LB16 : hidp (D + sb_buf_size b <= sf \/ sf + 256 <= D)) by (clear - BDS Lbsb; unfold hidp, hid in *; lia).

assert (BREP7 : bits_rep asegs m7 A D b1).
{ split; [exists rjb5; split; [exact Lrjb5| exact BOBJ5]|]. split; [exists bsb5; split; [apply (proj2 (u8arr_rw_CB m7 D bsb5)); exact BDAT5| exact Hbsb5]| exact BSIDE5]. }
clear BOBJ5 BDAT5.
assert (HDR7 : rw_cells asegs m7 S (nb_hdr_cells A_speex_nb_mode (set_nb_submodeID st mo) (j_last_ol_gain j))) by exact P1. clear P1.
lazymatch type of FRS3 with context [CB 120 ?r] => set (rs7 := r) in FRS3 end. clearbody rs7.
assert (SH7 : rw_cells asegs m7 sf (nbd_shadow_g true false false false false false false false rs7)) by exact FRS3. clear FRS3.
lazymatch type of FRB3 with rw_cells _ _ _ [C8 ?x; C8 ?y; C8 ?z; CB 2016 ?r] =>
change [C8 x; C8 y; C8 z; CB 2016 r] with ([C8 x; C8 y; C8 z] ++ [CB 2016 r]) in FRB3 end.
apply rw_cells_app in FRB3. destruct FRB3 as [FH7 FT7]. cbn [cells_size csize Nat.add] in FT7. change (Z.of_nat 24) with 24 in FT7.
apply (rw_cells_split_CB asegs m7 (f + 24) [] 2016 rb [] [136; 40; 1840]%nat) in FT7; [| reflexivity]. cbn [mk_CB_cells app] in FT7.
chunk_uncons FT7 as FT7a. chunk_uncons FT7 as FT7b.
replace (f + 24 + 136) with (f + 160) in FT7b, FT7 by lia. replace (f + 160 + 40) with (f + 200) in FT7 by lia.
destruct (rw_cells_CB_f32 asegs m7 (f + 160) 10 _ FT7b) as (old7 & Lold7 & QL7). clear FT7b.
unfold cb_cells in UCB5.
pose proof (AF_LIB Σ1 m7 ART7) as LC7. pose proof (nb_lsp_tabs_art Σ1 m7 ART7) as LT7. pose proof (nb_tabs_acc_art Σ1 m7 ART7) as NTA7.
pose proof (af_client_consts RT AF Σ1 m7 ART7) as CC7.
cps_seg (@nbd_b2 bptr usp lo S A D f sf (sb_buf_size b) gp (Z_to_bv 64 6489176) (set_nb_submodeID st mo) b1 slA (j_pad1 j) rs7 old7 (j_last_ol_gain j)
(Z_to_bv 64 RA_nbd_memmove) r13 r14 r15 (Z_to_bv 64 (S + 32)) r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 F5 fc5 m7
ST7 LB1 LB2 LB3 FPOS F64 BF LB4 LB5 LB6 Esf OBS7 S8 BS1 SSH9 LB7 LB8 OBA7 LB9 AL LB10 LB11 LB12 LB13 OBD7 LB14 LB15 LB16 SZ5 BREP7 OK5
SL5 E256s HDR7 P15 SH7 QL7 Lold7 LC7 LT7 NTA7 CC7 MI7 FRM5 ICL MO5).
destruct POST as (m8 & xra8 & t08 & t18 & t28 & a08 & a18 & a28 & a38 & a48 & a58 & a68 & a78 & t38 & t48 & t58 & t68 & F8 & fc8 & MU8 & WM8 & MI8 & ST8 & FRM8 & CC8 & HDR8 & CFG8 & ARM8).
clear SL5 HDR7 P15 SH7 QL7 BREP7 OBA7 OBD7 OBS7 LC7 LT7 NTA7 CC7 CC5.
unfold nb_cfg_cells in CFG8.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU8.
nb_tr MU8 WM8. cps_seg_post.
cbn [nb_submodeID set_nb_submodeID] in ARM8.
pose proof (smrec_submode mo MO5) as SMS.
destruct (smrec_at mo) as [smr|] eqn:SMR.
all: swap 1 2.
exact (ARMN st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E24s E32s E40s E48s E136s E152s E168s E240s E256s E296s E304s E312s E336s BK SB9 SSH9 STT9 c4 a36 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 SMR ARM8 Hc1 OUTK ART PF SMS).
exact (ARMC st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E24s E32s E40s E48s E136s E152s E168s E240s E256s E296s E304s E312s E336s BK SB9 SSH9 STT9 c4 a36 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 smr SMR ARM8 Hc1 OUTK ART PF SMS).
Qed.

End NbDecodeCPS.
