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
Hypothesis ARMB : nbd_armB_stmt RT OUT_rep ERR_rep IO_FP.
Hypothesis NOTIFY : nbd_notify_stmt RT OUT_rep ERR_rep IO_FP.

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

Theorem nb_decode_cps_main : forall st : nb_state bptr, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st).
Proof using All.
intros st Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD NDs kh ows stb q q' ret d' b' PRUN -> -> -> -> REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (ELBD & S8 & SPOS & INV & j & JOK & CBOK & XST).
pose proof INV as (ICL & IES & IHP & IFST & IVOC & IPGB & IID & IDTX & IWB & IENH & ISR & IISV).
destruct (nbd_prun_inv st b q ret d' b' q' IES PRUN) as (EBS & OUTC).
exists (nbd_bytes st b). split; [exact EBS|].
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [dec_stack dec_frames dec_credit dec_depth] in LOR, FRM, CRD, DEP. unfold NBDEC_STACK, NBDEC_FRAMES, NBDEC_CREDIT in *.

assert (INL : In (S, 2968) (rt_live RT Σ)).
{ specialize (LIVE (nb_blk st, S, NBSTATE_SIZEOF)). rewrite ELBD in LIVE. exact (LIVE ltac:(left; reflexivity)). }
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (WRS0 & ACS).
pose proof (live_facts RT AF Σ m S 2968 ART0 INL) as (_ & _ & SIMG & SHI).
pose proof (AF_SMALL Σ m S 2968 ART0 INL ltac:(lia)) as STOP.

destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fh kh ART0 INFH) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (AF_LIB Σ m ART0) as LC0. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (PMfd_mat_stable F0 fs0) as MSTA. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
subst LBD.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO [(nb_blk st, S, NBSTATE_SIZEOF)]) m) as PF.
unfold dec_W, blocks_ivs, blk_addr, blk_size, NBSTATE_SIZEOF in PF. cbn [map fst snd app] in PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
destruct FA as (FA1 & FA2 & ACA & AAL). destruct FO as (FO1 & FO2 & ACO & OAL). destruct FS as (FS1 & FS2 & ACST & SAL).
assert (LOWZ : Z.of_nat (length ows) = 2000) by (rewrite LOWS; reflexivity).

assert (AL : A + 48 <= lo) by (clear - FA2 BF1; unfold BITS_SIZEOF in FA2; lia).
assert (OL : OUT + 8000 <= lo) by (clear - FO2 BF1; lia).
assert (TL : STEREO + 24 <= lo) by (clear - FS2 BF1; lia).
assert (LO576 : lo <= usp + -576) by (clear - LOR; unfold RT_STACK in LOR; lia).

destruct (frame_live_apart RT AF Σ m fh kh S 2968 ART0 INFH INL) as (HSA & _).
assert (SAA : S + 2968 <= A \/ A + 48 <= S) by (clear - HSA FA1 FA2; unfold BITS_SIZEOF in FA2; lia).
assert (SOA : S + 2968 <= OUT \/ OUT + 8000 <= S) by (clear - HSA FO1 FO2; lia).
assert (STA : S + 2968 <= STEREO \/ STEREO + 24 <= S) by (clear - HSA FS1 FS2; lia).
pose proof (live_apart RT AF Σ m S 2968 PD NDs ART0 INL INPD (PDB (nb_blk st, S, NBSTATE_SIZEOF) (or_introl eq_refl))) as PSA.

destruct (live_below_lo RT AF Σ m _ _ lo ART0 INPD LOW) as (PD0 & BLPD & _).
destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
unfold BITS_SIZEOF in *.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
assert (DSA : S + 2968 <= D \/ D + Z.of_nat (length bsb) <= S) by (clear - PSA PD1 PD2 Lbsb; lia).

pose proof JOK as (JL1 & JL2 & JL3 & JL4 & JL5 & JL6 & JL7 & JL8 & JL9 & JL10 & (JL11a & JL11b) & JL12 & JL13).
eapply nb_pieces_of_cells in XST; [| exact JOK].
destruct XST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
unfold nb_hdr_cells, nb_cfg_cells, nb_ucb_cells, nb_tail_cells, cb_cells in P1, P15, P17, P19.
pose proof (conj INFH I) as INFHK.
pose proof (conj ART0 I) as ARTe.

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) x).
{ intros x Hx. cbn [outside]. unfold SH_LO, SH_HI in Hx.
split; [clear - Hx FPHI FA1 FA2 FSZ; lia|]. split; [clear - Hx FPHI FO1 FO2 FSZ; lia|].
split; [clear - Hx FPHI FS1 FS2 FSZ; lia|]. split; [clear - Hx SHI; lia|].
apply (outside_img IO_FP x IO_img). clear - Hx. unfold SEGTOP_A. lia. }
pose proof (fun so (H : OUT_rep so m) => H) as OUTK.
unfold hidp in HAO, HAS, HOS.
cps_norm. cps_hide.

cps_seg (nbd_w1 usp lo S A OUT).
destruct POST as (m1 & j1 & j2 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU1.
cps_seg_post.

assert (SSP1 : io_ssp m1) by (apply (nb_io_ssp_agree m m1 SSP0 (AF_DRV Σ m1 ltac:(assumption))); intros a Ha; apply MU1; cbn [outside]; split; [clear - Ha LOS LOR; lia| exact I]).
clear SSP0.

cps_rt_sized SM5 0. { cbn; tauto. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
nb_io_pres ERR_rep OUT_rep IO_FP IO_img PRES2.
assert (SSP2 : io_ssp m2) by (apply (nb_io_ssp_agree m1 m2 SSP1 (AF_DRV Σ1 m2 ART2)); intros a Ha; apply PRES2; right; left; exact (nb_ssp_guard_static _ Ha)).
clear SSP1.
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf.

assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact (proj1 INFHK) | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 2048 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 2048) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F64. Z.div_mod_to_equations. lia. }
assert (AFA : A + 48 <= f \/ f + 2048 <= A) by (clear - FFA FA1 FA2; lia).
assert (OFA : OUT + 8000 <= f \/ f + 2048 <= OUT) by (clear - FFA FO1 FO2; lia).
assert (TFA : STEREO + 24 <= f \/ f + 2048 <= STEREO) by (clear - FFA FS1 FS2; lia).
assert (ASA : A + 48 <= sf \/ sf + 256 <= A) by (clear - FPHI SHF1 SHF2 FA1 FA2; unfold hid in FPHI; lia).
assert (OSA : OUT + 8000 <= sf \/ sf + 256 <= OUT) by (clear - FPHI SHF1 SHF2 FO1 FO2; unfold hid in FPHI; lia).
assert (TSA : STEREO + 24 <= sf \/ sf + 256 <= STEREO) by (clear - FPHI SHF1 SHF2 FS1 FS2; unfold hid in FPHI; lia).
assert (BDF : D + Z.of_nat (length bsb) <= f \/ f + 2048 <= D) by (clear - Lbsb PD1 PD2 FLA1; unfold hid in FLA1; lia).
assert (BDS : D + Z.of_nat (length bsb) <= sf \/ sf + 256 <= D) by (clear - Lbsb PD1 PD2 FLA2; unfold hid in FLA2; lia).
cps_hide.

destruct (af_acc_live RT AF Σ1 m2 S 2968 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj bsegs m2 S 2968) by (split; [ulc|]; split; [ulc| exact ACS2]).
rewrite IES in P15.
assert (LSV : length (nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) = 25%nat) by reflexivity.
assert (FSV : Forall (fun c => csize c = 8%nat) (nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (unfold nbd_saves; repeat constructor).
cps_seg (nbd_w2 usp lo S A OUT f sf).
{ unfold hidp, SH_LO, SH_HI. unfold hid in FHI. clear - FHI. lia. }
{ unfold hidp, NBSTATE_SIZEOF, SH_LO, SH_HI. unfold hid in SHI. clear - SHI. lia. }
{ unfold hidp, NBSTATE_SIZEOF. unfold hid in FLA. clear - FLA. lia. }
{ split; ulc. }
destruct POST as (m3 & a1w & ja & jb & jc & jd & je & jf & jg & jh & rb & rs & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3 & P1' & P3' & P15').
clear FR1 FRB FRS P1 P3 P15 MU1. rename P1' into P1. rename P3' into P3. rename P15' into P15.
unfold nbd_frame_w2, nbd_saves in FR3. unfold nbd_fhdr in FRB3. unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS3.
cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in FRS3. cbn [app] in FR3.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU3.
nb_tr MU3 WM3. cps_seg_post.

assert (ACA3 : acc bsegs m3 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m3 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (OBA3 : aobj bsegs m3 A 48) by (split; [ulc|]; split; [ulc| exact ACA3]).
assert (REP3 : bits_rep bsegs m3 A D b).
{ split; [exists rjb; split; [exact Lrjb| exact BOBJ]|]. split; [exists bsb; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb]| exact BSIDE]. }
clear BOBJ BDAT.
pose proof (af_client_consts RT AF Σ1 m3 ART) as CC3.
cps_seg (nbA_pre usp lo S A D OUT f sf gp (Z_to_bv 64 6524056)).
{ split; ulc. }
{ unfold nbd_frame_w2, nbd_saves; cbn [app]. exact FR3. }
destruct POST as (m4 & xra4 & t04 & t14 & t24 & a04 & a14 & a24 & a34 & a44 & a54 & a64 & a74 & t34 & t44 & t54 & t64 & MU4 & WM4 & MI4 & ST4 & REP4 & BR4).
destruct REP4 as ((rjb4 & Lrjb4 & BOBJ) & (bsb4 & BDAT & Hbsb4) & BSIDE4). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m4 D bsb4)) in BDAT.
clear REP3 OBA3 ACA3 CC3.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU4.
assert (Lbsb4 : Z.of_nat (length bsb4) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb4, zlength_map_unsigned in OK'; clear - OK'; lia).
destruct (speex_bits_remaining b <? 5) eqn:REM5.

destruct BR4 as (-> & FR4).
nb_tr MU4 WM4. cps_seg_post.
assert (SR : search_pure (nb_search_fuel b) (nb_stereo_cb st) b = SOret (-1) b) by (unfold nb_search_fuel; cbn [search_pure]; rewrite REM5; reflexivity).
unfold nbd_bytes in *. rewrite SR in OUTC |- *. destruct OUTC as (-> & -> & ->).
destruct (frameW2_slots m4 (usp + -576) S A OUT f sf _ _ _ _ _ _ _ _ _ FR4) as (sl4 & FR4a & FR4b & E48 & E56 & _). clear FR4.
replace (usp + -576 + 376) with (usp + -200) in FR4b by lia.
unfold nbd_fhdr in FRB3.
lazymatch type of FRB3 with rw_cells _ _ _ [C8 ?x; C8 ?y; C8 ?z; CB 2016 ?r] =>
change [C8 x; C8 y; C8 z; CB 2016 r] with ([C8 x; C8 y; C8 z] ++ [CB 2016 r]) in FRB3 end.
apply rw_cells_app in FRB3. destruct FRB3 as [FH3 FT3].
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes bsegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m4 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] (-1) (DecNB st) b ows stb) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST4. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact FR4a. } { exact E48. } { exact E56. } { exact FR4b. } { exact FH3. }
{ unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app]. exact FRS3. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|].
exists (NBJ (j_last_ol_gain j) (j_excbuf j) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
split; [exact JOK|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK|].
rewrite <- IES in P15. exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj P14 (conj P15 (conj P16 (conj P17 (conj P18 P19)))))))))))))))))). }
{ intros E; discriminate E. }
{ split; [exists rjb4; split; [exact Lrjb4| exact BOBJ]|]. split; [exists bsb4; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb4]| exact BSIDE4]. }
{ exact BOK. } { exact OC. } { exact LOWS. } { exact STB. } { assumption. } { assumption. }
intros c3 Q3. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q3 as (Σ3 & HA3 & EL3 & EF3 & ES3 & EC3 & EP3). exists Σ3. split; [exact HA3|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact EL3|]. split; [exact EF3|]. split; [exact ES3|]. split; [rewrite EC3, CR1; lia| exact EP3].

destruct BR4 as (-> & (jh14 & jh24 & FR4)).
nb_tr MU4 WM4. cps_seg_post.
pose proof CBOK as (jsc & LJS & FJS & ECBS).
apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 16]%nat) in STB; [| reflexivity]. cbn [mk_CB_cells app] in STB.
chunk_uncons STB as STB8.
destruct (rw_cells_CB_f32 bsegs m4 STEREO 2 _ STB8) as (sws & LSWS & SW8). clear STB8.
pose proof (AF_DRV Σ1 m4 ltac:(assumption)) as ((GOTE & VARE) & _).
pose proof (AF_ERRV Σ1 m4 ltac:(assumption)) as ACV.
pose proof (af_client_consts RT AF Σ1 m4 ltac:(assumption)) as CC4.
destruct (af_acc_live RT AF Σ1 m4 S 2968 ltac:(assumption) INL) as (_ & ACS4).
destruct (af_acc_live RT AF Σ1 m4 PD NDs ltac:(assumption) ltac:(first [exact INPD | rewrite LV1; exact INPD])) as (_ & ACD4).
assert (ACA4 : acc bsegs m4 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (ACT4 : acc bsegs m4 STEREO 24) by (exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh STEREO 24 (proj1 ARTe) (proj1 INFHK) FS1 FS2 PF OFFW ACST)).
assert (OBA4 : aobj bsegs m4 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc| exact ACA4]).
assert (OBD4 : aobj bsegs m4 D (sb_buf_size b)) by (split; [clear - PD0 PD1; lia|]; split; [clear - PD2 BLPD LO576 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m4 PD NDs D _ ACD4 PD1 PD2)]).
assert (OBS4 : aobj bsegs m4 S 2968) by (split; [ulc|]; split; [ulc| exact ACS4]).
assert (OBT4 : aobj bsegs m4 STEREO 8) by (split; [ulc|]; split; [ulc| exact (acc_sub bsegs m4 STEREO 24 STEREO 8 ACT4 ltac:(lia) ltac:(lia))]).
assert (OBW4 : aobj bsegs m4 A_wb_skip_table 32)
by (apply (aobj_lit RT AF Σ1 m4 A_wb_skip_table 32 ltac:(assumption)); [unfold ACC_LITS, A_wb_skip_table; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_skip_table; lia | unfold A_wb_skip_table, APP_TOP; lia]).
assert (OBE4 : aobj bsegs m4 A_e_ratio_quant 16)
by (apply (aobj_lit RT AF Σ1 m4 A_e_ratio_quant 16 ltac:(assumption)); [unfold ACC_LITS, A_e_ratio_quant; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_e_ratio_quant; lia | unfold A_e_ratio_quant, APP_TOP; lia]).
assert (OBV4 : aobj bsegs m4 NBD_STDERR_VAR 8) by (unfold NBD_STDERR_VAR; split; [lia|]; split; [unfold APP_TOP; lia| exact ACV]).
clear ACS4 ACD4 ACA4 ACT4 ACV.

assert (LH1 : lo <= usp - 576 - 96) by (clear - LO576 LOR; unfold RT_STACK in *; lia).
assert (LH4 : A + BITS_SIZEOF <= lo) by (unfold BITS_SIZEOF; exact AL).
assert (LH5 : IMG_TOP_B <= A) by (unfold IMG_TOP_B; clear - FPIMG FA1; unfold SEGTOP_A in FPIMG; lia).
assert (LH6 : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A)) by (unfold hidp, BITS_SIZEOF, SH_LO, SH_HI; unfold hid in FPHI; clear - FPHI FA1 FA2 FSZ; lia).
assert (LH7 : D + sb_buf_size b <= lo) by (clear - PD2 BLPD; lia).
assert (LH9 : 0 < S /\ S + 2968 <= 140737488355328) by (split; ulc).
assert (LH12 : STEREO + 8 <= lo) by (clear - TL; lia).
assert (LH13 : IMG_TOP_B <= STEREO) by (unfold IMG_TOP_B; clear - FPIMG FS1; unfold SEGTOP_A in FPIMG; lia).
assert (LH14 : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO)) by (unfold hidp, SH_LO, SH_HI; unfold hid in FPHI; clear - FPHI FS1 FS2 FSZ; lia).
assert (LH15 : hidp (S + 2968 <= A \/ A + BITS_SIZEOF <= S)) by (unfold hidp, BITS_SIZEOF; unfold hid in SAA; clear - SAA; lia).
assert (LH16 : hidp (S + 2968 <= STEREO \/ STEREO + 8 <= S)) by (unfold hidp; unfold hid in STA; clear - STA; lia).
assert (LH17 : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO)) by (unfold hidp; unfold hid in HAS; unfold BITS_SIZEOF in *; clear - HAS; lia).
assert (LH18 : hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO)).
{ destruct (frame_live_apart RT AF Σ m fh kh PD NDs (proj1 ARTe) (proj1 INFHK) ltac:(first [exact INPD | rewrite <- LV1; exact INPD])) as (HPDF & _).
unfold hidp. clear - HPDF FS1 FS2 PD1 PD2. lia. }
pose proof (@nbA_loop bptr usp lo S A D OUT STEREO f sf (sb_buf_size b) STDERR_FILE gp (Z_to_bv 64 6524056) (nb_stereo_cb st) jsc (j_cbs j) (j_ucb j)
ja jb jc jd je jf jg jh14 jh24 (nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) m4
LH1 LOS ltac:(lia) LH4 LH5 LH6 LH7 S8 LH9 BS1 SAL LH12 LH13 LH14 LH15 LH16 LH17 LH18 LJS FJS ECBS OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 user_handler_proofA inband_handler_proofA (nb_search_fuel b)) as LOOP.
clear LH1 LH4 LH5 LH6 LH7 LH9 LH12 LH13 LH14 LH15 LH16 LH17 LH18.
cps_seg LOOP.
{ unfold nbA_ctx.
split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [assumption|]. split; [exact ST4|]. split; [exact CC4|].
split; [split; [exists rjb4; split; [exact Lrjb4| exact BOBJ]|]; split; [exists bsb4; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb4]| exact BSIDE4]|].
split; [exact BOK|]. split; [reflexivity|]. split; [exact SW8|]. split; [exact LSWS|].
split; [exact FR4|]. split; [exact P16|]. split; [exact P17|]. split; [exact GOTE| exact VARE]. }
{ apply Z.ltb_ge in REM5. exact REM5. }

unfold nbd_bytes. destruct (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) as [rv b1 | mo b1 | tw b1 |] eqn:SRCH.
4: { destruct OUTC. }

cbn [nbA_post] in POST.
destruct POST as (m5 & sws5 & F5 & fc5 & xra5 & t05 & t15 & t25 & a05 & a15 & a35 & a45 & a55 & a65 & a75 & t35 & t45 & t55 & t65 & -> & FRM5 & CTX5).
destruct CTX5 as (MU5 & WM5 & MI5 & ST5 & CC5 & REP5 & OK5 & SZ5 & SW5 & LSW5 & FR5 & CBS5 & UCB5 & GOT5 & VAR5).
clear BOBJ BDAT SW8 FR4 P16 P17 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4.
unfold nbA_W in MU5.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU5.
nb_tr MU5 WM5. cps_seg_post.
destruct OUTC as (-> & -> & ->).
pose proof (search_ret_m1 (nb_search_fuel b) (nb_stereo_cb st) b) as RM1. rewrite SRCH in RM1. cbn [sres_ret] in RM1. subst rv.
pose proof (bkeep_search (nb_search_fuel b) (nb_stereo_cb st) b) as BK. rewrite SRCH in BK. cbn [sres_keep] in BK. destruct BK as (BK1 & BK2 & BK3).
destruct (frameA_slots m5 (usp + -576) S A OUT f sf _ _ _ _ _ _ _ _ _ _ FR5) as (sl5 & FR5a & FR5b & _ & E48 & E56 & _). clear FR5.
replace (usp + -576 + 376) with (usp + -200) in FR5b by lia.
chunk_cat SW5 STB. apply rw_cells_to_CB in SW5. rewrite cells_size_app, cells_size_f32, LSW5 in SW5. cbn [cells_size csize Nat.add Nat.mul] in SW5.
lazymatch type of FRB3 with rw_cells _ _ _ [C8 ?x; C8 ?y; C8 ?z; CB 2016 ?r] =>
change [C8 x; C8 y; C8 z; CB 2016 r] with ([C8 x; C8 y; C8 z] ++ [CB 2016 r]) in FRB3 end.
apply rw_cells_app in FRB3. destruct FRB3 as [FH5 FT5].
destruct REP5 as ((rjb5 & Lrjb5 & BOBJ5) & (bsb5 & BDAT5 & Hbsb5) & BSIDE5).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes bsegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m5 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] (-1) (DecNB st) b1 ows) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BK3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST5. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact FR5a. } { exact E48. } { exact E56. } { exact FR5b. } { exact FH5. }
{ unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app]. exact FRS3. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|].
exists (NBJ (j_last_ol_gain j) (j_excbuf j) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
split; [exact JOK|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK|].
rewrite <- IES in P15. exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj P14 (conj P15 (conj CBS5 (conj UCB5 (conj P18 P19)))))))))))))))))). }
{ intros E; discriminate E. }
{ split; [exists rjb5; split; [exact Lrjb5| exact BOBJ5]|]. split; [exists bsb5; split; [exact BDAT5| exact Hbsb5]| exact BSIDE5]. }
{ exact OK5. } { exact OC. } { exact LOWS. } { exact SW5. } { assumption. } { assumption. }
intros c5 Q5. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q5 as (Σ5 & HA5 & EL5 & EF5 & ES5 & EC5 & EP5). exists Σ5. split; [exact HA5|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [exact EL5|]. split; [exact EF5|]. split; [exact ES5|]. split; [rewrite EC5, CR1; lia| exact EP5].
exact (ARMB st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret d' b' PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH OUTC T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO576 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 P19 P18 P17 P16 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P2 STB OC SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg jh rb rs MU3 WM3 FRB3 FRS3 P1 P3 P15 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 MI4 ST4 rjb4 Lrjb4 BOBJ bsb4 BDAT Hbsb4 BSIDE4 REM5 jh14 jh24 FR4 OUTK Lbsb4 ART0 PF jsc LJS FJS ECBS sws LSWS SW8 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 LOOP ms c3 POST Hc1).
exact (NOTIFY st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret d' b' PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS tw b1 SRCH OUTC T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO576 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 P19 P18 P17 P16 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P2 STB OC SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg jh rb rs MU3 WM3 FRB3 FRS3 P1 P3 P15 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 MI4 ST4 rjb4 Lrjb4 BOBJ bsb4 BDAT Hbsb4 BSIDE4 REM5 jh14 jh24 FR4 OUTK Lbsb4 ART0 PF jsc LJS FJS ECBS sws LSWS SW8 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 LOOP ms c3 POST Hc1).
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
Hypothesis ARMB : nbd_armB_stmt RT OUT_rep ERR_rep IO_FP.
Hypothesis NOTIFY : nbd_notify_stmt RT OUT_rep ERR_rep IO_FP.

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

Theorem nb_decode_cps_main : forall st : nb_state bptr, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st).
Proof using All.
intros st Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD NDs kh ows stb q q' ret d' b' PRUN -> -> -> -> REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (ELBD & S8 & SPOS & INV & j & JOK & CBOK & XST).
pose proof INV as (ICL & IES & IHP & IFST & IVOC & IPGB & IID & IDTX & IWB & IENH & ISR & IISV).
destruct (nbd_prun_inv st b q ret d' b' q' IES PRUN) as (EBS & OUTC).
exists (nbd_bytes st b). split; [exact EBS|].
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [dec_stack dec_frames dec_credit dec_depth] in LOR, FRM, CRD, DEP. unfold NBDEC_STACK, NBDEC_FRAMES, NBDEC_CREDIT in *.

assert (INL : In (S, 2968) (rt_live RT Σ)).
{ specialize (LIVE (nb_blk st, S, NBSTATE_SIZEOF)). rewrite ELBD in LIVE. exact (LIVE ltac:(left; reflexivity)). }
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (WRS0 & ACS).
pose proof (live_facts RT AF Σ m S 2968 ART0 INL) as (_ & _ & SIMG & SHI).
pose proof (AF_SMALL Σ m S 2968 ART0 INL ltac:(lia)) as STOP.

destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fh kh ART0 INFH) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (AF_LIB Σ m ART0) as LC0. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (PMfd_mat_stable F0 fs0) as MSTA. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
subst LBD.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO [(nb_blk st, S, NBSTATE_SIZEOF)]) m) as PF.
unfold dec_W, blocks_ivs, blk_addr, blk_size, NBSTATE_SIZEOF in PF. cbn [map fst snd app] in PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
destruct FA as (FA1 & FA2 & ACA & AAL). destruct FO as (FO1 & FO2 & ACO & OAL). destruct FS as (FS1 & FS2 & ACST & SAL).
assert (LOWZ : Z.of_nat (length ows) = 2000) by (rewrite LOWS; reflexivity).

assert (AL : A + 48 <= lo) by (clear - FA2 BF1; unfold BITS_SIZEOF in FA2; lia).
assert (OL : OUT + 8000 <= lo) by (clear - FO2 BF1; lia).
assert (TL : STEREO + 24 <= lo) by (clear - FS2 BF1; lia).
assert (LO544 : lo <= usp + -544) by (clear - LOR; unfold RT_STACK in LOR; lia).

destruct (frame_live_apart RT AF Σ m fh kh S 2968 ART0 INFH INL) as (HSA & _).
assert (SAA : S + 2968 <= A \/ A + 48 <= S) by (clear - HSA FA1 FA2; unfold BITS_SIZEOF in FA2; lia).
assert (SOA : S + 2968 <= OUT \/ OUT + 8000 <= S) by (clear - HSA FO1 FO2; lia).
assert (STA : S + 2968 <= STEREO \/ STEREO + 24 <= S) by (clear - HSA FS1 FS2; lia).
pose proof (live_apart RT AF Σ m S 2968 PD NDs ART0 INL INPD (PDB (nb_blk st, S, NBSTATE_SIZEOF) (or_introl eq_refl))) as PSA.

destruct (live_below_lo RT AF Σ m _ _ lo ART0 INPD LOW) as (PD0 & BLPD & _).
destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
unfold BITS_SIZEOF in *.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
assert (DSA : S + 2968 <= D \/ D + Z.of_nat (length bsb) <= S) by (clear - PSA PD1 PD2 Lbsb; lia).

pose proof JOK as (JL1 & JL2 & JL3 & JL4 & JL5 & JL6 & JL7 & JL8 & JL9 & JL10 & (JL11a & JL11b) & JL12 & JL13).
eapply nb_pieces_of_cells in XST; [| exact JOK].
destruct XST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
unfold nb_hdr_cells, nb_cfg_cells, nb_ucb_cells, nb_tail_cells, cb_cells in P1, P15, P17, P19.
pose proof (conj INFH I) as INFHK.
pose proof (conj ART0 I) as ARTe.

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) x).
{ intros x Hx. cbn [outside]. unfold SH_LO, SH_HI in Hx.
split; [clear - Hx FPHI FA1 FA2 FSZ; lia|]. split; [clear - Hx FPHI FO1 FO2 FSZ; lia|].
split; [clear - Hx FPHI FS1 FS2 FSZ; lia|]. split; [clear - Hx SHI; lia|].
apply (outside_img IO_FP x IO_img). clear - Hx. unfold SEGTOP_A. lia. }
pose proof (fun so (H : OUT_rep so m) => H) as OUTK.
unfold hidp in HAO, HAS, HOS.
cps_norm. cps_hide.

cps_seg (nbd_w1 usp lo S A OUT).
destruct POST as (m1 & j1 & j2 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU1.
cps_seg_post.

assert (SSP1 : io_ssp m1) by (apply (nb_io_ssp_agree m m1 SSP0 (AF_DRV Σ m1 ltac:(assumption))); intros a Ha; apply MU1; cbn [outside]; split; [clear - Ha LOS LOR; lia| exact I]).
clear SSP0.

cps_rt_sized SM5 0. { cbn; tauto. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
nb_io_pres ERR_rep OUT_rep IO_FP IO_img PRES2.
assert (SSP2 : io_ssp m2) by (apply (nb_io_ssp_agree m1 m2 SSP1 (AF_DRV Σ1 m2 ART2)); intros a Ha; apply PRES2; right; left; exact (nb_ssp_guard_static _ Ha)).
clear SSP1.
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf.

assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact (proj1 INFHK) | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 2048 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 2048) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F64. Z.div_mod_to_equations. lia. }
assert (AFA : A + 48 <= f \/ f + 2048 <= A) by (clear - FFA FA1 FA2; lia).
assert (OFA : OUT + 8000 <= f \/ f + 2048 <= OUT) by (clear - FFA FO1 FO2; lia).
assert (TFA : STEREO + 24 <= f \/ f + 2048 <= STEREO) by (clear - FFA FS1 FS2; lia).
assert (ASA : A + 48 <= sf \/ sf + 256 <= A) by (clear - FPHI SHF1 SHF2 FA1 FA2; unfold hid in FPHI; lia).
assert (OSA : OUT + 8000 <= sf \/ sf + 256 <= OUT) by (clear - FPHI SHF1 SHF2 FO1 FO2; unfold hid in FPHI; lia).
assert (TSA : STEREO + 24 <= sf \/ sf + 256 <= STEREO) by (clear - FPHI SHF1 SHF2 FS1 FS2; unfold hid in FPHI; lia).
assert (BDF : D + Z.of_nat (length bsb) <= f \/ f + 2048 <= D) by (clear - Lbsb PD1 PD2 FLA1; unfold hid in FLA1; lia).
assert (BDS : D + Z.of_nat (length bsb) <= sf \/ sf + 256 <= D) by (clear - Lbsb PD1 PD2 FLA2; unfold hid in FLA2; lia).
cps_hide.

destruct (af_acc_live RT AF Σ1 m2 S 2968 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj asegs m2 S 2968) by (split; [ulc|]; split; [ulc| exact ACS2]).
rewrite IES in P15.
assert (LSV : length (nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) = 25%nat) by reflexivity.
assert (FSV : Forall (fun c => csize c = 8%nat) (nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (unfold nbd_saves; repeat constructor).
cps_seg (nbd_w2 usp lo S A OUT f sf).
{ unfold hidp, SH_LO, SH_HI. unfold hid in FHI. clear - FHI. lia. }
{ unfold hidp, NBSTATE_SIZEOF, SH_LO, SH_HI. unfold hid in SHI. clear - SHI. lia. }
{ unfold hidp, NBSTATE_SIZEOF. unfold hid in FLA. clear - FLA. lia. }
{ split; ulc. }
destruct POST as (m3 & a1w & ja & jb & jc & jd & je & jf & jg & rb & rs & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3 & P1' & P3' & P15').
clear FR1 FRB FRS P1 P3 P15 MU1. rename P1' into P1. rename P3' into P3. rename P15' into P15.
unfold nbd_frame_w2, nbd_saves in FR3. unfold nbd_fhdr in FRB3. unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS3.
cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in FRS3. cbn [app] in FR3.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU3.
nb_tr MU3 WM3. cps_seg_post.

assert (ACA3 : acc asegs m3 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m3 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (OBA3 : aobj asegs m3 A 48) by (split; [ulc|]; split; [ulc| exact ACA3]).
assert (REP3 : bits_rep asegs m3 A D b).
{ split; [exists rjb; split; [exact Lrjb| exact BOBJ]|]. split; [exists bsb; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb]| exact BSIDE]. }
clear BOBJ BDAT.
pose proof (af_client_consts RT AF Σ1 m3 ART) as CC3.
cps_seg (nbA_pre usp lo S A D OUT f sf gp (Z_to_bv 64 6489176)).
{ split; ulc. }
{ unfold nbd_frame_w2, nbd_saves; cbn [app]. exact FR3. }
destruct POST as (m4 & xra4 & t04 & t14 & t24 & a04 & a14 & a24 & a34 & a44 & a54 & a64 & a74 & t34 & t44 & t54 & t64 & MU4 & WM4 & MI4 & ST4 & REP4 & BR4).
destruct REP4 as ((rjb4 & Lrjb4 & BOBJ) & (bsb4 & BDAT & Hbsb4) & BSIDE4). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m4 D bsb4)) in BDAT.
clear REP3 OBA3 ACA3 CC3.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU4.
assert (Lbsb4 : Z.of_nat (length bsb4) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb4, zlength_map_unsigned in OK'; clear - OK'; lia).
destruct (speex_bits_remaining b <? 5) eqn:REM5.

destruct BR4 as (-> & FR4).
nb_tr MU4 WM4. cps_seg_post.
assert (SR : search_pure (nb_search_fuel b) (nb_stereo_cb st) b = SOret (-1) b) by (unfold nb_search_fuel; cbn [search_pure]; rewrite REM5; reflexivity).
unfold nbd_bytes in *. rewrite SR in OUTC |- *. destruct OUTC as (-> & -> & ->).
unfold nbd_frame_w2 in FR4. apply rw_cells_app in FR4. destruct FR4 as [FR4a FR4b]. cbn [cells_size csize Nat.add] in FR4b. change (Z.of_nat 344) with 344 in FR4b.
replace (usp + -544 + 344) with (usp + -200) in FR4b by lia.
apply rw_cells_to_CB in FR4a. cbn [cells_size csize Nat.add] in FR4a.
unfold nbd_fhdr in FRB3.
lazymatch type of FRB3 with rw_cells _ _ _ [C8 ?x; C8 ?y; C8 ?z; CB 2016 ?r] =>
change [C8 x; C8 y; C8 z; CB 2016 r] with ([C8 x; C8 y; C8 z] ++ [CB 2016 r]) in FRB3 end.
apply rw_cells_app in FRB3. destruct FRB3 as [FH3 FT3].
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes asegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m4 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] (-1) (DecNB st) b ows stb) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST4. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact FR4a. } { exact FR4b. } { exact FH3. }
{ unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app]. exact FRS3. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|].
exists (NBJ (j_last_ol_gain j) (j_excbuf j) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
split; [exact JOK|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK|].
rewrite <- IES in P15. exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj P14 (conj P15 (conj P16 (conj P17 (conj P18 P19)))))))))))))))))). }
{ intros E; discriminate E. }
{ split; [exists rjb4; split; [exact Lrjb4| exact BOBJ]|]. split; [exists bsb4; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb4]| exact BSIDE4]. }
{ exact BOK. } { exact OC. } { exact LOWS. } { exact STB. } { assumption. } { assumption. }
intros c3 Q3. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q3 as (Σ3 & HA3 & EL3 & EF3 & ES3 & EC3 & EP3). exists Σ3. split; [exact HA3|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact EL3|]. split; [exact EF3|]. split; [exact ES3|]. split; [rewrite EC3, CR1; lia| exact EP3].

destruct BR4 as (-> & (ja4 & jb4 & jc4 & jh4 & FR4)).
nb_tr MU4 WM4. cps_seg_post.
pose proof CBOK as (jsc & LJS & FJS & ECBS).
apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 16]%nat) in STB; [| reflexivity]. cbn [mk_CB_cells app] in STB.
chunk_uncons STB as STB8.
destruct (rw_cells_CB_f32 asegs m4 STEREO 2 _ STB8) as (sws & LSWS & SW8). clear STB8.
pose proof (AF_DRV Σ1 m4 ltac:(assumption)) as ((GOTE & VARE) & _).
pose proof (AF_ERRV Σ1 m4 ltac:(assumption)) as ACV.
pose proof (af_client_consts RT AF Σ1 m4 ltac:(assumption)) as CC4.
destruct (af_acc_live RT AF Σ1 m4 S 2968 ltac:(assumption) INL) as (_ & ACS4).
destruct (af_acc_live RT AF Σ1 m4 PD NDs ltac:(assumption) ltac:(first [exact INPD | rewrite LV1; exact INPD])) as (_ & ACD4).
assert (ACA4 : acc asegs m4 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (ACT4 : acc asegs m4 STEREO 24) by (exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh STEREO 24 (proj1 ARTe) (proj1 INFHK) FS1 FS2 PF OFFW ACST)).
assert (OBA4 : aobj asegs m4 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc| exact ACA4]).
assert (OBD4 : aobj asegs m4 D (sb_buf_size b)) by (split; [clear - PD0 PD1; lia|]; split; [clear - PD2 BLPD LO544 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m4 PD NDs D _ ACD4 PD1 PD2)]).
assert (OBS4 : aobj asegs m4 S 2968) by (split; [ulc|]; split; [ulc| exact ACS4]).
assert (OBT4 : aobj asegs m4 STEREO 8) by (split; [ulc|]; split; [ulc| exact (acc_sub asegs m4 STEREO 24 STEREO 8 ACT4 ltac:(lia) ltac:(lia))]).
assert (OBW4 : aobj asegs m4 A_wb_skip_table 32)
by (apply (aobj_lit RT AF Σ1 m4 A_wb_skip_table 32 ltac:(assumption)); [unfold ACC_LITS, A_wb_skip_table; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_skip_table; lia | unfold A_wb_skip_table, APP_TOP; lia]).
assert (OBE4 : aobj asegs m4 A_e_ratio_quant 16)
by (apply (aobj_lit RT AF Σ1 m4 A_e_ratio_quant 16 ltac:(assumption)); [unfold ACC_LITS, A_e_ratio_quant; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_e_ratio_quant; lia | unfold A_e_ratio_quant, APP_TOP; lia]).
assert (OBV4 : aobj asegs m4 NBD_STDERR_VAR 8) by (unfold NBD_STDERR_VAR; split; [lia|]; split; [unfold APP_TOP; lia| exact ACV]).
clear ACS4 ACD4 ACA4 ACT4 ACV.

assert (LH1 : lo <= usp - 544 - 96) by (clear - LO544 LOR; unfold RT_STACK in *; lia).
assert (LH4 : A + BITS_SIZEOF <= lo) by (unfold BITS_SIZEOF; exact AL).
assert (LH5 : IMG_TOP <= A) by (unfold IMG_TOP; clear - FPIMG FA1; unfold SEGTOP_A in FPIMG; lia).
assert (LH6 : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A)) by (unfold hidp, BITS_SIZEOF, SH_LO, SH_HI; unfold hid in FPHI; clear - FPHI FA1 FA2 FSZ; lia).
assert (LH7 : D + sb_buf_size b <= lo) by (clear - PD2 BLPD; lia).
assert (LH9 : 0 < S /\ S + 2968 <= 140737488355328) by (split; ulc).
assert (LH12 : STEREO + 8 <= lo) by (clear - TL; lia).
assert (LH13 : IMG_TOP <= STEREO) by (unfold IMG_TOP; clear - FPIMG FS1; unfold SEGTOP_A in FPIMG; lia).
assert (LH14 : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO)) by (unfold hidp, SH_LO, SH_HI; unfold hid in FPHI; clear - FPHI FS1 FS2 FSZ; lia).
assert (LH15 : hidp (S + 2968 <= A \/ A + BITS_SIZEOF <= S)) by (unfold hidp, BITS_SIZEOF; unfold hid in SAA; clear - SAA; lia).
assert (LH16 : hidp (S + 2968 <= STEREO \/ STEREO + 8 <= S)) by (unfold hidp; unfold hid in STA; clear - STA; lia).
assert (LH17 : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO)) by (unfold hidp; unfold hid in HAS; unfold BITS_SIZEOF in *; clear - HAS; lia).
assert (LH18 : hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO)).
{ destruct (frame_live_apart RT AF Σ m fh kh PD NDs (proj1 ARTe) (proj1 INFHK) ltac:(first [exact INPD | rewrite <- LV1; exact INPD])) as (HPDF & _).
unfold hidp. clear - HPDF FS1 FS2 PD1 PD2. lia. }
pose proof (@nbA_loop bptr usp lo S A D OUT STEREO f sf (sb_buf_size b) STDERR_FILE gp (Z_to_bv 64 6489176) (nb_stereo_cb st) jsc (j_cbs j) (j_ucb j)
ja4 jb4 jc4 jc jd je jf jh4 (nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) m4
LH1 LOS ltac:(lia) LH4 LH5 LH6 LH7 S8 LH9 BS1 SAL LH12 LH13 LH14 LH15 LH16 LH17 LH18 LJS FJS ECBS OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 (nb_search_fuel b)) as LOOP.
clear LH1 LH4 LH5 LH6 LH7 LH9 LH12 LH13 LH14 LH15 LH16 LH17 LH18.
cps_seg LOOP.
{ unfold nbA_ctx.
split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [assumption|]. split; [exact ST4|]. split; [exact CC4|].
split; [split; [exists rjb4; split; [exact Lrjb4| exact BOBJ]|]; split; [exists bsb4; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb4]| exact BSIDE4]|].
split; [exact BOK|]. split; [reflexivity|]. split; [exact SW8|]. split; [exact LSWS|].
split; [exact FR4|]. split; [exact P16|]. split; [exact P17|]. split; [exact GOTE| exact VARE]. }
{ apply Z.ltb_ge in REM5. exact REM5. }

unfold nbd_bytes. destruct (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) as [rv b1 | mo b1 | tw b1 |] eqn:SRCH.
4: { destruct OUTC. }

cbn [nbA_post] in POST.
destruct POST as (m5 & sws5 & F5 & fc5 & xra5 & t05 & t15 & t25 & a05 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & t35 & t45 & t55 & t65 & -> & FRM5 & CTX5).
destruct CTX5 as (MU5 & WM5 & MI5 & ST5 & CC5 & REP5 & OK5 & SZ5 & SW5 & LSW5 & FR5 & CBS5 & UCB5 & GOT5 & VAR5).
clear BOBJ BDAT SW8 FR4 P16 P17 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4.
unfold nbA_W in MU5.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU5.
nb_tr MU5 WM5. cps_seg_post.
destruct OUTC as (-> & -> & ->).
pose proof (search_ret_m1 (nb_search_fuel b) (nb_stereo_cb st) b) as RM1. rewrite SRCH in RM1. cbn [sres_ret] in RM1. subst rv.
pose proof (bkeep_search (nb_search_fuel b) (nb_stereo_cb st) b) as BK. rewrite SRCH in BK. cbn [sres_keep] in BK. destruct BK as (BK1 & BK2 & BK3).
unfold nbd_frame_A in FR5. apply rw_cells_app in FR5. destruct FR5 as [FR5a FR5b]. cbn [cells_size csize Nat.add] in FR5b. change (Z.of_nat 344) with 344 in FR5b.
replace (usp + -544 + 344) with (usp + -200) in FR5b by lia.
apply rw_cells_to_CB in FR5a. cbn [cells_size csize Nat.add] in FR5a.
chunk_cat SW5 STB. apply rw_cells_to_CB in SW5. rewrite cells_size_app, cells_size_f32, LSW5 in SW5. cbn [cells_size csize Nat.add Nat.mul] in SW5.
lazymatch type of FRB3 with rw_cells _ _ _ [C8 ?x; C8 ?y; C8 ?z; CB 2016 ?r] =>
change [C8 x; C8 y; C8 z; CB 2016 r] with ([C8 x; C8 y; C8 z] ++ [CB 2016 r]) in FRB3 end.
apply rw_cells_app in FRB3. destruct FRB3 as [FH5 FT5].
destruct REP5 as ((rjb5 & Lrjb5 & BOBJ5) & (bsb5 & BDAT5 & Hbsb5) & BSIDE5).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes asegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ1 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m5 lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] (-1) (DecNB st) b1 ows) | ].
{ exact FRS1. } { exact LV1. } { exact SP1. } { exact PO1. } { exact (proj1 ARTe). } { first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BK3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ assumption. } { eassumption. } { eassumption. } { exact ST5. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact FR5a. } { exact FR5b. } { exact FH5. }
{ unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app]. exact FRS3. }
{ cbn [decst_rep]. split; [reflexivity|]. unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|].
exists (NBJ (j_last_ol_gain j) (j_excbuf j) (S + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
split; [exact JOK|]. split; [exact CBOK|].
apply nb_cells_of_pieces; [exact JOK|].
rewrite <- IES in P15. exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10 (conj P11 (conj P12 (conj P13 (conj P14 (conj P15 (conj CBS5 (conj UCB5 (conj P18 P19)))))))))))))))))). }
{ intros E; discriminate E. }
{ split; [exists rjb5; split; [exact Lrjb5| exact BOBJ5]|]. split; [exists bsb5; split; [exact BDAT5| exact Hbsb5]| exact BSIDE5]. }
{ exact OK5. } { exact OC. } { exact LOWS. } { exact SW5. } { assumption. } { assumption. }
intros c5 Q5. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q5 as (Σ5 & HA5 & EL5 & EF5 & ES5 & EC5 & EP5). exists Σ5. split; [exact HA5|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [exact EL5|]. split; [exact EF5|]. split; [exact ES5|]. split; [rewrite EC5, CR1; lia| exact EP5].
exact (ARMB st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret d' b' PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH OUTC T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 P19 P18 P17 P16 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P2 STB OC SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 FRB3 FRS3 P1 P3 P15 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 MI4 ST4 rjb4 Lrjb4 BOBJ bsb4 BDAT Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 FR4 OUTK Lbsb4 ART0 PF jsc LJS FJS ECBS sws LSWS SW8 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 LOOP ms c3 POST Hc1).
exact (NOTIFY st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret d' b' PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 ERR0 FRM CRD POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS tw b1 SRCH OUTC T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 P19 P18 P17 P16 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P2 STB OC SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 FRB3 FRS3 P1 P3 P15 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 MI4 ST4 rjb4 Lrjb4 BOBJ bsb4 BDAT Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 FR4 OUTK Lbsb4 ART0 PF jsc LJS FJS ECBS sws LSWS SW8 GOTE VARE CC4 OBA4 OBD4 OBS4 OBT4 OBW4 OBE4 OBV4 LOOP ms c3 POST Hc1).
Qed.

End NbDecodeCPS.
