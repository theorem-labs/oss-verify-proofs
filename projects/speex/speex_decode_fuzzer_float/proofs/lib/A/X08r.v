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

Theorem nbd_armC : nbd_armC_stmt RT OUT_rep ERR_rep IO_FP.
Proof using All.
intros st Σ F0 fs0 ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S A D b lo fh PD NDs kh ows stb q q' ret b' st2 PRUN REP DEP ISV NEST LIVE LAL8 NDUP rjb Lrjb m1 bsb Hbsb BSIDE BOK Σ1 INPD PD1 PD2 PDB LOWS FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2 m2 m3 m4 m5 m6 m7 m8 ERR0 FRM CRD usp POA FRM0 LOW LOR SPT SPA S8 SPOS INV j JOK CBOK ICL IES IHP IFST IVOC IPGB IID IDTX IWB IENH ISR IISV EBS mo b1 SRCH RST T c Hk ESP INL BS1 LOS WRS0 ACS SIMG SHI STOP BF1 BF2 FP0 FP64 FPIMG FPHI FSZ LC0 CC0 MSTA FDO SPL LOWZ AL OL TL LO544 HSA SAA SOA STA PSA PD0 BLPD Lbsb BDLO DSA JL1 JL2 JL3 JL4 JL5 JL6 JL7 JL8 JL9 JL10 JL11a JL11b JL12 JL13 INFHK ARTe OFFW c0 j1 j2 WM1 Hc0 cc2 f FRS1 LV1 SP1 CR1 FPOS F64 FTOP PO1 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 WM2 PRES2 sf SSP2 NAF INFH INF BF BF0 F1 F2 FIMG FHI SHF SHF0 SHF1 SHF2 SHF3 FLA FLA0 FLA1 FLA2 Esf jF jS FS64 CLH FFA AFA OFA TFA ASA OSA TSA BDF BDS ACS2 OBS2 LSV FSV c1 a1w ja jb jc jd je jf jg rb rs MU3 WM3 c2 xra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 MU4 WM4 rjb4 Lrjb4 bsb4 Hbsb4 BSIDE4 REM5 ja4 jb4 jc4 jh4 Lbsb4 jsc LJS FJS ECBS sws LSWS LOOP c3 sws5 F5 fc5 xra5 t05 t15 t25 a15 a25 a35 a55 a65 a75 t35 t45 t55 t65 FRM5 MU5 WM5 rjb5 Lrjb5 bsb5 Hbsb5 BSIDE5 OK5 SZ5 LSW5 MO5 Lbsb5 slA E0s E24s E32s E40s E48s E136s E152s E168s E240s E256s E296s E304s E312s E336s BK SB9 SSH9 STT9 c4 a36 MU6 WM6 Hc kc7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 WM7 SV5 UCB5 CBS5 SW5 P3 rs7 FH7 FT7a FT7 OC STB P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P18 P19 ex1 EXB LEX1 LB1 LB2 LB3 LB4 LB5 LB6 LB7 LB8 LB9 LB10 LB11 LB12 LB13 LB14 LB15 LB16 old7 Lold7 ms c5 xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 MU8 WM8 MI8 ST8 FRM8 CC8 HDR8 CFG8 smr SMR ARM8 Hc1 OUTK ART PF SMS.

destruct ARM8 as (-> & BREP8 & BOK8 & SL8 & SH8 & (ql8 & QL8 & Lql8)).
try clear Hc0. try clear Hc. try clear LOOP.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH8. cbn [map repeat app] in SH8.
unfold nb_rest_pure in RST. rewrite SMS in RST. cbn beta iota zeta in RST.
lazymatch type of RST with (match ?e with Some _ => _ | None => _ end) = _ => destruct e as [[stE bE]|] eqn:SUBF; [| discriminate RST] end.
injection RST as <- <- <-.
destruct BREP8 as ((rjb8 & Lrjb8 & BOBJ8) & (bsb8 & BDAT8 & Hbsb8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bsb8)) in BDAT8.
pose proof (bkeep_lsp (sm_lsp_unquant (smr_sm smr)) b1) as BKL.
assert (Lbsb8 : Z.of_nat (length bsb8) = sb_buf_size b)
by (pose proof BOK8 as OK'; unfold bits_ok in OK'; rewrite Hbsb8, zlength_map_unsigned in OK'; destruct BKL as (_ & _ & BKL3); clear - OK' SZ5 BKL3; lia).
destruct (af_acc_live RT AF Σ1 m8 S 2968 ltac:(assumption) INL) as (_ & ACS8).
assert (OBS8 : aobj asegs m8 S 2968) by (split; [ulc|]; split; [ulc| exact ACS8]). clear ACS8.
assert (FST8 : nb_first (set_nb_submodeID st mo) = 0 \/ nb_first (set_nb_submodeID st mo) = 1) by exact IFST.
assert (E160 : v160 (slots_B2 S f slA) = Z_to_bv 64 (f + 160)) by reflexivity.
cps_seg (@nbd_c1 bptr usp lo S f sf gp (Z_to_bv 64 6489176) (set_nb_submodeID st mo) (slots_B2 S f slA) (j_last_ol_gain j)
xra8 t08 t18 t28 a08 a18 a28 a38 a48 a58 a68 a78 t38 t48 t58 t68 F8 fc8 m8 LB3 LO544 LB2 OBS8 S8 BS1 SL8 E160 HDR8 FST8 MI8).
destruct POST as (m9 & MU9 & WM9 & MI9 & SL9 & HDR9 & ARMC).
unfold nb_hdr_cells in HDR9.
clear SL8 HDR8 OBS8 FST8 E160.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU9.
nb_tr MU9 WM9. cps_seg_post.
cbn [nb_first set_nb_submodeID] in ARMC.
destruct (nb_first st =? 0) eqn:FST0.
all: swap 1 2.

subst ms.
set (bq := cells_bytes (f32 ql8)) in *.
assert (Lbq : length bq = 40%nat) by (unfold bq; rewrite cells_bytes_length by apply cells_wf_f32; rewrite cells_size_f32, Lql8; reflexivity).
pose proof (proj2 (proj1 QL8)) as SRCQ. fold bq in SRCQ.
pose proof (proj2 P4) as WRQ. rewrite cells_size_f32, JL2 in WRQ.
repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
cps_rt (MCP Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (S + 2040) (f + 160) bq lo).
{ rewrite Lbq. reflexivity. }
{ split; [intros _; split|].
- replace (Z.of_nat (length bq)) with (8 * Z.of_nat 5) by (rewrite Lbq; reflexivity).
replace (f + 160) with (f + 8 * Z.of_nat (length (map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 4; -14; -14; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14]))) by (cbn; lia).
exact (shadow_acc m9 f sf _ (map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 4; -14; -14; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14]) _ 5%nat SH8 eq_refl Esf F64 ltac:(lia)).
- unfold rng_class. right; left. exists f, 5%nat. split; [exact INF| rewrite Lbq; fs_lit; clear - F1; lia].
- left. rewrite Lbq. clear - BF. lia. }
{ apply (nb_live_checked_dst Σ1 m9 _ S 2968); [assumption| exact INL| lia| rewrite Lbq; lia| rewrite Lbq; exact WRQ]. }
{ cps_callok. }
intros kc10 Hc10. unfold icpt_postF in Hc10.
destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ kc10 Hc10) as (ms10 & PO10 & Hc10'); clear Hc10; cbv beta in PO10.
destruct PO10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
cps_ret RS10.
rewrite (unsigned_lit (usp + -544)) in PRES10, ST10 by ulc. rewrite Lbq in PRES10. change (Z.of_nat 40) with 40 in PRES10.
clear P4.
nb_trp PRES10.
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF).
apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -544) (S + 2040) 40 m9 m10 PRES10).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x _ Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & HS & _). lia. }
clear PF. rename PF10 into PF.
nb_io_pres_ex ERR_rep OUT_rep IO_FP IO_img PRES10.
try match goal with A0 : ART _ _ m9 |- _ => clear A0 end. try match goal with M0 : mem_inv asegs m9 |- _ => clear M0 end.
try match goal with S0 : stk asegs m9 _ _ |- _ => clear S0 end.

assert (P4 : rw_cells asegs m10 (S + 2040) (f32 ql8)).
{ split; [split; [apply cells_wf_f32 | exact BY10]|]. rewrite cells_size_f32, Lql8. exact (wr_at_transport asegs m9 m10 _ _ WRQ WM10). }
clear BY10 WRQ SRCQ PRES10 Lbq. clear bq.
pose proof Lql8 as JL2n. clear JL2. set (oq := ql8) in P4, JL2n. clearbody oq. rename JL2n into JL2.
rewrite (ret_pc_even RA_nbd_memcpy ltac:(unfold RA_nbd_memcpy; lia) eq_refl) in Hc10'.

destruct (af_acc_live RT AF Σ1 m10 S 2968 ltac:(assumption) INL) as (_ & ACS10).
assert (OBS10 : aobj asegs m10 S 2968) by (split; [ulc|]; split; [ulc| exact ACS10]). clear ACS10.
destruct (af_acc_live RT AF Σ1 m10 PD NDs ltac:(assumption) INPD) as (_ & ACD10).
assert (ACA10 : acc asegs m10 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m10 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (OBA10 : aobj asegs m10 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc| exact ACA10]).
assert (OBD10 : aobj asegs m10 D (sb_buf_size b)) by (split; [clear - PD0 PD1; lia|]; split; [clear - PD2 BLPD LO544 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m10 PD NDs D _ ACD10 PD1 PD2)]).
clear ACD10 ACA10.
pose proof (AF_LIB Σ1 m10 ltac:(assumption)) as LC10. pose proof (nb_tabs_acc_art Σ1 m10 ltac:(assumption)) as NTA10.
pose proof (af_client_consts RT AF Σ1 m10 ltac:(assumption)) as CC10.
assert (LD1 : hidp (S + 2968 <= D \/ D + sb_buf_size b <= S)) by (clear - DSA Lbsb; unfold hidp, hid in *; lia).
assert (BREP10 : bits_rep asegs m10 A D (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)).
{ split; [exists rjb8; split; [exact Lrjb8| exact BOBJ8]|]. split; [exists bsb8; split; [apply (proj2 (u8arr_rw_CB m10 D bsb8)); exact BDAT8| exact Hbsb8]| exact BSIDE8]. }
clear BOBJ8 BDAT8.
assert (SZL : sb_buf_size (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) = sb_buf_size b) by (destruct BKL as (_ & _ & BKL3); rewrite BKL3; exact SZ5).
assert (ED48 : v48 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (S + 2120)) by exact E48s.
assert (ED256 : v256 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 A) by exact E256s.
assert (ED288 : v288 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (S + 2248)) by reflexivity.
assert (ED296 : v296 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (Z.shiftr (S + 2240) 3 + SHB)) by reflexivity.
assert (ED304 : v304 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (S + 2240)) by reflexivity.
assert (ED312 : v312 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (Z.shiftr (S + 2248) 3 + SHB)) by reflexivity.
cps_seg (@nbd_cd bptr usp lo S A D f sf (sb_buf_size b) gp (Z_to_bv 64 6489176) m10 LB1 LB2 LB3 FPOS F64 BF LB4 LB5 LB6 Esf OBS10 S8 BS1 STT9 SSH9 LB7 LB8
OBA10 LB9 AL LB10 LB11 LB12 LB13 OBD10 LB14 LB15 LB16 LD1 LC10 NTA10
(set_nb_submodeID st mo) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) smr (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) (j_pad1 j) (j_pad2 j) rs7
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 m10 (munch_refl _ m10) (wmono_refl asegs m10) MI10 ST10 CC10 FRM8 BREP10 BOK8 SZL SL9
ED48 ED256 ED288 ED296 ED304 ED312 CFG8 P19 SH8 SMR).
destruct POST as (m11 & xra11 & t011 & t111 & t211 & a011 & a111 & a211 & a311 & a411 & a511 & t311 & t411 & t511 & t611 & F11 & fc11
& -> & MU11 & WM11 & MI11 & ST11 & CC11 & FRM11 & BREP11 & BOK11 & SZ11 & SL11 & CFG11 & TAIL11 & SH11).
clear SL9 CFG8 P19 SH8 BREP10 OBS10 OBA10 OBD10 LC10 NTA10 CC10 LD1 SZL ED48 ED256 ED288 ED296 ED304 ED312.
unfold nb_cfg_cells in CFG11. unfold nb_tail_cells in TAIL11.
unfold nbD_W in MU11.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU11.
nb_tr MU11 WM11. cps_seg_post.

pose proof (segD_st_keep (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1))
as (KB & KF & KC & KSR & KIS & KPG & KES & KSM & KLE & KSC & KVO & KWB & KHP & KDTX).
set (stD := segD_st (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) in *.
set (bD := segD_bits (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) in *.
assert (HDRD : rw_cells asegs m11 S (nb_hdr_cells A_speex_nb_mode stD (j_last_ol_gain j))) by (unfold nb_hdr_cells; rewrite KF, KC, KSR; exact HDR9).
assert (P9D : rw_cells asegs m11 (S + 2184) [C8 (Z_to_bv 64 (nb_isave_ptr OUT stD))]) by (unfold nb_isave_ptr; rewrite KIS; exact P9).
assert (P13D : rw_cells asegs m11 (S + 2224) [C4 (Z_to_bv 64 (nb_pitch_gain_buf_idx stD))]) by (rewrite KPG; exact P13).
assert (CFGD : rw_cells asegs m11 (S + 2232) (nb_cfg_cells NB_SUBMODES_PTR stD (j_pad1 j))) by (unfold nb_cfg_cells; rewrite KES, KSM, KLE; exact CFG11).
assert (TAILD : rw_cells asegs m11 (S + 2948) (nb_tail_cells stD (j_pad2 j))) by exact TAIL11.
clear HDR9 P9 P13 CFG11 TAIL11.
set (jE := NBJ (j_last_ol_gain j) ex1 (S + 1368) oq (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
assert (JOKE : nb_junk_ok jE) by exact (conj LEX1 (conj JL2 (conj JL3 (conj JL4 (conj JL5 (conj JL6 (conj JL7 (conj JL8 (conj JL9 (conj JL10 (conj (conj JL11a JL11b) (conj JL12 JL13)))))))))))).
assert (NBPE : nb_pieces asegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler m11 S OUT STEREO stD jE)
by exact (conj HDRD (conj EXB (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9D (conj P10 (conj P11 (conj P12 (conj P13D (conj P14 (conj CFGD (conj CBS5 (conj UCB5 (conj P18 TAILD)))))))))))))))))).

apply (rw_cells_split_CB asegs _ (f + 24) [] 136 _ [] [8; 4; 12; 12; 20; 40; 40]%nat) in FT7a; [| reflexivity]. cbn [mk_CB_cells app] in FT7a.
nb_uncons FT7a as FG0. nb_uncons FT7a as FGp. nb_uncons FT7a as FG1. nb_uncons FT7a as FGg. nb_uncons FT7a as FG2. nb_uncons FT7a as FGl.
apply (rw_cells_split_CB asegs _ (f + 200) [] 1840 _ [] [40; 40; 40; 160; 64; 160; 64; 160; 64; 40; 1008]%nat) in FT7; [| reflexivity]. cbn [mk_CB_cells app] in FT7.
nb_uncons FT7 as FH0. nb_uncons FT7 as FHa. nb_uncons FT7 as FH1. nb_uncons FT7 as FHi. nb_uncons FT7 as FH2. nb_uncons FT7 as FHe.
nb_uncons FT7 as FH3. nb_uncons FT7 as FHj. nb_uncons FT7 as FH4. nb_uncons FT7 as FHq.
clear FG0 FG1 FG2 FT7a FH0 FH1 FH2 FH3 FH4 FT7.
destruct (rw_cells_CB_f32 asegs m11 (f + 32) 1 _ FGp) as ([|fpw [|]] & Lfp & FFp); [discriminate Lfp| | discriminate Lfp]. clear FGp Lfp.
destruct (rw_cells_CB_f32 asegs m11 (f + 48) 3 _ FGg) as (fpg & Lfpg & FFg). clear FGg.
destruct (rw_cells_CB_f32 asegs m11 (f + 80) 10 _ FGl) as (flpc & Lflpc & FFl). clear FGl.
destruct (rw_cells_CB_f32 asegs m11 (f + 240) 10 _ FHa) as (fak & Lfak & FFa). clear FHa.
destruct (rw_cells_CB_f32 asegs m11 (f + 320) 40 _ FHi) as (finn & Lfinn & FFi). clear FHi.
destruct (rw_cells_CB_f32 asegs m11 (f + 544) 40 _ FHe) as (fexc & Lfexc & FFe). clear FHe.
destruct (rw_cells_CB_f32 asegs m11 (f + 768) 40 _ FHj) as (finn2 & Lfinn2 & FFj). clear FHj.
destruct (rw_cells_CB_f32 asegs m11 (f + 992) 10 _ FHq) as (fiq & Lfiq & FFq). clear FHq.
set (ffE := NBF fpw fpg flpc ql8 fak finn fexc finn2 fiq).
assert (FFOK : ff_ok ffE) by exact (conj Lfpg (conj Lflpc (conj Lql8 (conj Lfak (conj Lfinn (conj Lfexc (conj Lfinn2 Lfiq))))))).
assert (FFAT : fframe_at m11 f ffE) by exact (conj FH7 (conj FFp (conj FFg (conj FFl (conj QL8 (conj FFa (conj FFi (conj FFe (conj FFj FFq))))))))).
clear FH7 FFp FFg FFl QL8 FFa FFi FFe FFj FFq.

destruct (frame_live_apart RT AF Σ m fh kh PD NDs (proj1 ARTe) (proj1 INFHK) ltac:(rewrite <- LV1; exact INPD)) as (HPDF & _).
assert (DOA : hid (D + sb_buf_size b <= OUT \/ OUT + 8000 <= D)) by (unfold hid; clear - HPDF FO1 FO2 PD1 PD2 FSZ; lia).
assert (DSTA : hid (D + sb_buf_size b <= STEREO \/ STEREO + 8 <= D)) by (unfold hid; clear - HPDF FS1 FS2 PD1 PD2 FSZ; lia).
clear HPDF.
pose proof BSIDE as (BS_A8 & BS_A0 & BS_D0 & _ & _ & BS_AD).
set (X := NBX S OUT 2000 A D (sb_buf_size b) STEREO lo usp f sf gp (Z_to_bv 64 6489176) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m st b).
assert (NXOK : nbx_ok X).
{ unfold nbx_ok, X, NBD_FRAME, NBSTATE_SIZEOF, BITS_SIZEOF; cbn [x_st x_out x_nout x_A x_D x_dsz x_stereo x_lo x_usp x_ff x_sf x_b0 x_st0].
change (4 * Z.of_nat 2000) with 8000.
split; [exact SPA|]. split; [exact LB3|]. split; [exact LB2|]. split; [clear - LO544; lia|].
split; [exact FPOS|]. split; [exact F64|]. split; [reflexivity|]. split; [exact BF|]. split; [exact LB5|]. split; [exact LB6|].
split; [clear - SHF1; unfold SH_LO; lia|]. split; [clear - SHF2; unfold SH_HI; lia|]. split; [exact BF0|].
split; [exact S8|]. split; [exact SPOS|]. split; [exact BS1|]. split; [exact SSH9|]. split; [unfold hidp; right; exact STT9|].
split; [exact OAL|]. split; [clear - FPIMG FO1; cps_unf; lia|]. split; [exact OL|]. split; [lia|].
split; [clear - FPHI FO1 FO2 FSZ; unfold hidp, hid in *; cps_unf; lia|].
split; [exact BS_A8|]. split; [exact LB9|]. split; [exact AL|]. split; [exact LB10|].
split; [exact BS_D0|]. split; [exact LB14|]. split; [reflexivity|].
split; [exact SAL|]. split; [clear - FPIMG FS1; cps_unf; lia|]. split; [clear - TL; lia|].
split; [clear - FPHI FS1 FS2 FSZ; unfold hidp, hid in *; cps_unf; lia|].
split; [pose proof ISV as ISV'; cbn [isave_ok] in ISV'; destruct (nb_innov_save st) as [k|]; [clear - ISV'; lia| exact I]|].
split; [exact SOA|]. split; [exact SAA|]. split; [clear - DSA Lbsb; unfold hidp, hid in *; lia|]. split; [clear - STA; unfold hidp, hid in *; lia|].
split; [exact LB7|]. split; [exact LB8|].
split; [clear - HAO; unfold hidp, hid in *; lia|]. split; [clear - DOA; unfold hidp, hid in *; lia|]. split; [clear - HOS; unfold hidp, hid in *; lia|]. split; [exact OFA|]. split; [exact OSA|].
split; [clear - BS_AD; unfold hidp, BITS_SIZEOF in *; lia|]. split; [clear - HAS; unfold hidp, hid in *; lia|]. split; [exact LB11|]. split; [exact LB12|].
split; [clear - DSTA; unfold hidp, hid in *; lia|]. split; [exact LB15|]. split; [exact LB16|].
split; [clear - TFA; unfold hidp, hid in *; lia|]. split; [clear - TSA; unfold hidp, hid in *; lia|]. exact SHF3. }

assert (INVD : nb_inv stD).
{ pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold nb_inv.
rewrite KC, KES, KHP, KF, KVO, KPG, KSM, KWB, KLE, KSR, KIS.
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj MO5 (conj _ (conj I9 (conj I10 (conj I11 I12))))))))))).
destruct KDTX as [E|[E|E]]; rewrite E; [left; reflexivity| right; reflexivity| exact I8]. }
assert (NSIG : nbsig RT Σ1 X (rt_frames RT Σ) PD NDs fh kh).
{ unfold nbsig, X, NBD_FCLASS, NBD_FRAME, NBSTATE_SIZEOF, BITS_SIZEOF; cbn [x_st x_out x_nout x_A x_D x_dsz x_stereo x_lo x_usp x_ff x_sf].
change (4 * Z.of_nat 2000) with 8000.
split; [exact FRS1|]. split; [exact INL|]. split; [exact INPD|]. split; [exact PD1|]. split; [exact PD2|].
split; [intros E; apply (PDB (nb_blk st, S, NBSTATE_SIZEOF)); [left; reflexivity| cbn; symmetry; exact E]|].
split; [exact (proj1 INFHK)|]. split; [exact FO1|]. split; [exact FO2|]. split; [exact FA1|]. split; [exact FA2|].
split; [exact FS1|]. split; [clear - FS2; lia|].
split; [apply (pois_above_le _ usp); [exact POA| lia]|].
split; [exact LOW|]. split; [clear - LOR; unfold RT_STACK, NBD_CALLEE_STACK in *; lia|]. exact SPT. }
assert (NACC : nbacc X m11).
{ unfold nbacc, X, BITS_SIZEOF; cbn [x_out x_nout x_A x_stereo]. change (4 * Z.of_nat 2000) with 8000.
split; [exact (acc_of_pres_fp RT AF Σ m m m11 usp _ fh kh OUT 8000 (proj1 ARTe) (proj1 INFHK) FO1 FO2 PF OFFW ACO)|].
split; [exact (acc_of_pres_fp RT AF Σ m m m11 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)|].
exact (acc_sub asegs m11 STEREO 24 STEREO 8 (acc_of_pres_fp RT AF Σ m m m11 usp _ fh kh STEREO 24 (proj1 ARTe) (proj1 INFHK) FS1 FS2 PF OFFW ACST) ltac:(lia) ltac:(lia)). }
assert (LBRP : sm_lbr_pitch (smr_sm smr) = -1 /\ segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) = 0
\/ sm_lbr_pitch (smr_sm smr) <> -1 /\ 17 <= segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) <= 144).
{ unfold segD_olp. destruct (Z.eqb_spec (sm_lbr_pitch (smr_sm smr)) (-1)) as [E|E]; cbn [negb].
- left. split; [exact E| reflexivity].
- right. split; [exact E|]. pose proof (ub_ok (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) 7 BOK8 ltac:(lia)) as (_ & _ & UV). change (2 ^ 7) with 128 in UV. lia. }
lazymatch goal with HC : ASTA _ _ _ (eq ?ms) _ |- realizes asegs _ _ =>
assert (ATE : at_E_A X smr mo (segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) 40 0 stD bD ms) end.
{ unfold at_E_A. exists F11, fc11, m11, xra11, t011, t111, t211, a011, a111, a211, a311, a411, a511, t311, t411, t511, t611, jE, ows, sws5,
(slots_D S f (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA))), ffE.
split; [reflexivity|]. split; [exact FRM11|].
split.
{ unfold nbctx. split; [exact MI11|]. split; [exact ST11|]. split; [exact NBPE|]. split; [exact JOKE|].
split; [rewrite KSC; exact CBOK|]. split; [exact INVD|]. split; [exact BREP11|]. split; [exact BOK11|]. split; [exact SZ11|].
split; [exact OC|]. split; [exact LOWS|]. split; [exact SW5|]. split; [exact LSW5|].
split; [exact (conj SL11 SV5)|]. split; [exact FFAT|]. split; [exact FFOK|]. split; [exists rs7; exact SH11|].
split; [exact CC11|]. split; [exact (AF_LIB Σ1 m11 ART)|]. split; [reflexivity| exact KIS]. }
split; [unfold slots_E; repeat split;
first [reflexivity | exact E0s | exact E24s | exact E32s | exact E40s | exact E48s | exact E136s | exact E152s | exact E168s | exact E240s
| exact E256s | exact E296s | exact E304s | exact E312s | exact E336s]|].
split; [exact SMR|]. split; [exact KSM|]. split; [lia|]. split; [exact LBRP| lia]. }
assert (LTPN : sm_ltp_unquant (smr_sm smr) <> None)
by (intro E; cbn [subframes_pure] in SUBF; unfold subframe_pure in SUBF; rewrite E in SUBF; cbn beta iota in SUBF; discriminate SUBF).
assert (INNN : sm_innovation_unquant (smr_sm smr) <> None)
by (intro E; cbn [subframes_pure] in SUBF; unfold subframe_pure in SUBF; rewrite E in SUBF; cbn beta iota in SUBF; destruct (sm_ltp_unquant (smr_sm smr)); discriminate SUBF).
assert (FRMX : (length (rt_frames RT Σ1) < FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; clear - FRM; lia).
assert (CRDX : NBD_EH_CREDIT <= rt_credit RT Σ1) by (rewrite CR1; unfold NBD_EH_CREDIT; clear - CRD; lia).
pose proof (EH Σ1 (PMfd F0 fs0) X (rt_frames RT Σ) PD NDs fh kh smr mo (segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) stD bD _
FDO MSTA eq_refl NXOK ATE NSIG NACC ART FRMX CRDX LTPN INNN) as EH1.
rewrite SUBF in EH1.
cps_rt EH1.

intros c12 (Σ12 & HA12 & EL12 & EF12 & ES12 & EC12 & EP12).
destruct (ASTA_unpack RT Σ12 (PMfd F0 fs0) _ c12 HA12) as (ms12 & PO12 & Hc12); clear HA12; cbv beta in PO12.
destruct PO12 as (AX12 & ART12 & NACC12 & WM12 & PF12).
destruct AX12 as (Fx & fcx & mX & xrax & xt0 & xt1 & xt2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xs5 & xs6 & xs7 & xs8 & xs11 & xt3 & xt4 & xt5 & xt6
& jX & owsX & swsX & sX & ffX & -> & FRMX2 & CTXX).
cbn [ms_mem MS] in ART12, NACC12, WM12, PF12.
destruct CTXX as (MIX & STX & NBPX & JOKX & CBOKX & INVX & BREPX & BOKX & SZX & OCX & LOWSX & SWX & LSWX & (SLX & SVX) & FFX & FFOKX & (rsX & SHX) & CCX & LCX & JEXC & JISV).
unfold X in STX, NBPX, BREPX, SZX, OCX, LOWSX, SWX, SLX, SVX, FFX, SHX, JEXC, JISV.
cbn [x_st x_out x_nout x_A x_D x_dsz x_stereo x_lo x_usp x_ff x_sf x_gp x_tp x_ra x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_F x_m0 x_st0 x_b0]
in STX, NBPX, BREPX, SZX, OCX, LOWSX, SWX, SLX, SVX, FFX, SHX, JEXC, JISV.

assert (STBX : rw_cells asegs mX (STEREO + 8) [CB 16 (firstn 16 (skipn 8 stb))]).
{ apply (rw_cells_agree asegs m11 mX _ _ STB); [| exact WM12]. apply (agree_of_pres_fp _ _ _ _ m11 mX _ PF12). intros ?x ?Hx. cps_sizes Hx. split; [nb_cls|].
unfold nbW_EH, X. cbn [x_st x_out x_nout x_A x_ff x_sf x_usp outside]. unfold NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. change (4 * Z.of_nat 2000) with 8000.
unfold hid in STA, HOS, HAS, TFA, TSA.
repeat split; intros ?HH; [clear - Hx HH STA; lia | clear - Hx HH HOS; lia | clear - Hx HH HAS; lia | clear - Hx HH TFA; lia | clear - Hx HH TSA; lia | clear - Hx HH TL LO544; lia]. }
assert (KEEPX : forall P, fp_local IO_FP P -> P m11 -> P mX).
{ intros P0 L0 Pm0. apply (nb_fp_local_pres_fp IO_FP P0 _ _ _ _ m11 mX L0 IO_img PF12); [| exact Pm0].
intros y Hy. pose proof (nb_client_static_range _ Hy) as R. unfold nbW_EH, X. cbn [x_st x_out x_nout x_A x_ff x_sf x_usp outside].
unfold NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME, SEGTOP_A in *. change (4 * Z.of_nat 2000) with 8000.
repeat split; intros ?HH; [clear - R HH STOP | clear - R HH FO1 FPIMG | clear - R HH FA1 FPIMG | clear - R HH FIMG | clear - R HH SHF1 | clear - R HH LO544 BF FIMG]; lia. }
pk_io ERR_rep OUT_rep KEEPX. clear KEEPX.

assert (PFX : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m mX).
{ apply (pres_fp_trans _ _ _ _ m m11 mX PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp - 544) (nbW_EH X) m11 mX PF12).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx Ho. unfold nbW_EH, X. cbn [x_st x_out x_nout x_A x_ff x_sf x_usp outside] in Ho |- *.
destruct Ho as (HA & HO & HT & HS & _). pose proof (NAF x Hx) as (NF & NSF). pose proof (SPL x Hx) as HSP.
unfold NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. change (4 * Z.of_nat 2000) with 8000.
repeat split; [exact HS| exact HO| exact HA| exact NF| exact NSF| clear - HSP LOW SP1 LO544; lia]. }
clear PF. rename PFX into PF.
apply rw_cells_to_CB in SLX. cbn [cells_size csize slot_cells Nat.add] in SLX.
chunk_cat SWX STBX. apply rw_cells_to_CB in SWX. rewrite cells_size_app, cells_size_f32, LSWX in SWX. cbn [cells_size csize Nat.add Nat.mul] in SWX.
pose proof NBPX as (_ & _ & EXPX & _). rewrite JEXC in EXPX.
pose proof FFX as (FHX & _).
pose proof (subframes_blk _ _ _ _ _ _ _ _ SUBF) as BLKE.
pose proof (bkeep_trans _ _ _ (bkeep_trans _ _ _ (bkeep_trans _ _ _ BK BKL) (bkeep_segD (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)))
(bkeep_subframes _ _ _ _ _ _ _ _ SUBF)) as (BKE1 & BKE2 & BKE3).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes asegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ12 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mX lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] 0
(DecNB (nb_end stE)) bE owsX) | ].
{ rewrite EF12. exact FRS1. } { rewrite EL12. exact LV1. } { rewrite ES12. exact SP1. } { rewrite EP12. exact PO1. } { exact (proj1 ARTe). }
{ first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BKE3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ exact ART12. } { exact MIX. } { exact FRMX2. } { exact STX. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact SLX. } { exact SVX. } { exact FHX. } { exact SHX. }
{ cbn [decst_rep]. split; [cbn [nb_blk nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first]; rewrite BLKE, KB; reflexivity|].
unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|]. split; [exact INVX|].
exists jX. split; [exact JOKX|]. split; [exact CBOKX|]. apply nb_cells_of_pieces; [exact JOKX| exact NBPX]. }
{ intros _. exact EXPX. }
{ exact BREPX. } { exact BOKX. } { exact OCX. } { exact LOWSX. } { exact SWX. } { assumption. } { assumption. }
intros c13 Q13. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q13 as (Σ13 & HA13 & EL13 & EF13 & ES13 & EC13 & EP13). exists Σ13. split; [exact HA13|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT, NBD_EH_CREDIT in *.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BKE1|]. split; [exact BKE2|]. split; [exact BKE3|].
split; [exact EL13|]. split; [exact EF13|]. split; [exact ES13|].
split; [rewrite EC13; clear - EC12 CR1; lia| exact EP13].

destruct ARMC as (a0c & a1c & a2c & ->).
rename m9 into m10. rename MI9 into MI10. rename ST8 into ST10.
generalize dependent (j_old_qlsp j). intros oq JL2 P4.

destruct (af_acc_live RT AF Σ1 m10 S 2968 ltac:(assumption) INL) as (_ & ACS10).
assert (OBS10 : aobj asegs m10 S 2968) by (split; [ulc|]; split; [ulc| exact ACS10]). clear ACS10.
destruct (af_acc_live RT AF Σ1 m10 PD NDs ltac:(assumption) INPD) as (_ & ACD10).
assert (ACA10 : acc asegs m10 A 48) by (exact (acc_of_pres_fp RT AF Σ m m m10 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)).
assert (OBA10 : aobj asegs m10 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc| exact ACA10]).
assert (OBD10 : aobj asegs m10 D (sb_buf_size b)) by (split; [clear - PD0 PD1; lia|]; split; [clear - PD2 BLPD LO544 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m10 PD NDs D _ ACD10 PD1 PD2)]).
clear ACD10 ACA10.
pose proof (AF_LIB Σ1 m10 ltac:(assumption)) as LC10. pose proof (nb_tabs_acc_art Σ1 m10 ltac:(assumption)) as NTA10.
pose proof (af_client_consts RT AF Σ1 m10 ltac:(assumption)) as CC10.
assert (LD1 : hidp (S + 2968 <= D \/ D + sb_buf_size b <= S)) by (clear - DSA Lbsb; unfold hidp, hid in *; lia).
assert (BREP10 : bits_rep asegs m10 A D (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)).
{ split; [exists rjb8; split; [exact Lrjb8| exact BOBJ8]|]. split; [exists bsb8; split; [apply (proj2 (u8arr_rw_CB m10 D bsb8)); exact BDAT8| exact Hbsb8]| exact BSIDE8]. }
clear BOBJ8 BDAT8.
assert (SZL : sb_buf_size (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) = sb_buf_size b) by (destruct BKL as (_ & _ & BKL3); rewrite BKL3; exact SZ5).
assert (ED48 : v48 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (S + 2120)) by exact E48s.
assert (ED256 : v256 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 A) by exact E256s.
assert (ED288 : v288 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (S + 2248)) by reflexivity.
assert (ED296 : v296 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (Z.shiftr (S + 2240) 3 + SHB)) by reflexivity.
assert (ED304 : v304 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (S + 2240)) by reflexivity.
assert (ED312 : v312 (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) = Z_to_bv 64 (Z.shiftr (S + 2248) 3 + SHB)) by reflexivity.
cps_seg (@nbd_cd bptr usp lo S A D f sf (sb_buf_size b) gp (Z_to_bv 64 6489176) m10 LB1 LB2 LB3 FPOS F64 BF LB4 LB5 LB6 Esf OBS10 S8 BS1 STT9 SSH9 LB7 LB8
OBA10 LB9 AL LB10 LB11 LB12 LB13 OBD10 LB14 LB15 LB16 LD1 LC10 NTA10
(set_nb_submodeID st mo) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) smr (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA)) (j_pad1 j) (j_pad2 j) rs7
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 m10 (munch_refl _ m10) (wmono_refl asegs m10) MI10 ST10 CC10 FRM8 BREP10 BOK8 SZL SL9
ED48 ED256 ED288 ED296 ED304 ED312 CFG8 P19 SH8 SMR).
destruct POST as (m11 & xra11 & t011 & t111 & t211 & a011 & a111 & a211 & a311 & a411 & a511 & t311 & t411 & t511 & t611 & F11 & fc11
& -> & MU11 & WM11 & MI11 & ST11 & CC11 & FRM11 & BREP11 & BOK11 & SZ11 & SL11 & CFG11 & TAIL11 & SH11).
clear SL9 CFG8 P19 SH8 BREP10 OBS10 OBA10 OBD10 LC10 NTA10 CC10 LD1 SZL ED48 ED256 ED288 ED296 ED304 ED312.
unfold nb_cfg_cells in CFG11. unfold nb_tail_cells in TAIL11.
unfold nbD_W in MU11.
nb_io_munch ERR_rep OUT_rep IO_FP IO_img MU11.
nb_tr MU11 WM11. cps_seg_post.

pose proof (segD_st_keep (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1))
as (KB & KF & KC & KSR & KIS & KPG & KES & KSM & KLE & KSC & KVO & KWB & KHP & KDTX).
set (stD := segD_st (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) in *.
set (bD := segD_bits (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) in *.
assert (HDRD : rw_cells asegs m11 S (nb_hdr_cells A_speex_nb_mode stD (j_last_ol_gain j))) by (unfold nb_hdr_cells; rewrite KF, KC, KSR; exact HDR9).
assert (P9D : rw_cells asegs m11 (S + 2184) [C8 (Z_to_bv 64 (nb_isave_ptr OUT stD))]) by (unfold nb_isave_ptr; rewrite KIS; exact P9).
assert (P13D : rw_cells asegs m11 (S + 2224) [C4 (Z_to_bv 64 (nb_pitch_gain_buf_idx stD))]) by (rewrite KPG; exact P13).
assert (CFGD : rw_cells asegs m11 (S + 2232) (nb_cfg_cells NB_SUBMODES_PTR stD (j_pad1 j))) by (unfold nb_cfg_cells; rewrite KES, KSM, KLE; exact CFG11).
assert (TAILD : rw_cells asegs m11 (S + 2948) (nb_tail_cells stD (j_pad2 j))) by exact TAIL11.
clear HDR9 P9 P13 CFG11 TAIL11.
set (jE := NBJ (j_last_ol_gain j) ex1 (S + 1368) oq (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
assert (JOKE : nb_junk_ok jE) by exact (conj LEX1 (conj JL2 (conj JL3 (conj JL4 (conj JL5 (conj JL6 (conj JL7 (conj JL8 (conj JL9 (conj JL10 (conj (conj JL11a JL11b) (conj JL12 JL13)))))))))))).
assert (NBPE : nb_pieces asegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler m11 S OUT STEREO stD jE)
by exact (conj HDRD (conj EXB (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9D (conj P10 (conj P11 (conj P12 (conj P13D (conj P14 (conj CFGD (conj CBS5 (conj UCB5 (conj P18 TAILD)))))))))))))))))).

apply (rw_cells_split_CB asegs _ (f + 24) [] 136 _ [] [8; 4; 12; 12; 20; 40; 40]%nat) in FT7a; [| reflexivity]. cbn [mk_CB_cells app] in FT7a.
nb_uncons FT7a as FG0. nb_uncons FT7a as FGp. nb_uncons FT7a as FG1. nb_uncons FT7a as FGg. nb_uncons FT7a as FG2. nb_uncons FT7a as FGl.
apply (rw_cells_split_CB asegs _ (f + 200) [] 1840 _ [] [40; 40; 40; 160; 64; 160; 64; 160; 64; 40; 1008]%nat) in FT7; [| reflexivity]. cbn [mk_CB_cells app] in FT7.
nb_uncons FT7 as FH0. nb_uncons FT7 as FHa. nb_uncons FT7 as FH1. nb_uncons FT7 as FHi. nb_uncons FT7 as FH2. nb_uncons FT7 as FHe.
nb_uncons FT7 as FH3. nb_uncons FT7 as FHj. nb_uncons FT7 as FH4. nb_uncons FT7 as FHq.
clear FG0 FG1 FG2 FT7a FH0 FH1 FH2 FH3 FH4 FT7.
destruct (rw_cells_CB_f32 asegs m11 (f + 32) 1 _ FGp) as ([|fpw [|]] & Lfp & FFp); [discriminate Lfp| | discriminate Lfp]. clear FGp Lfp.
destruct (rw_cells_CB_f32 asegs m11 (f + 48) 3 _ FGg) as (fpg & Lfpg & FFg). clear FGg.
destruct (rw_cells_CB_f32 asegs m11 (f + 80) 10 _ FGl) as (flpc & Lflpc & FFl). clear FGl.
destruct (rw_cells_CB_f32 asegs m11 (f + 240) 10 _ FHa) as (fak & Lfak & FFa). clear FHa.
destruct (rw_cells_CB_f32 asegs m11 (f + 320) 40 _ FHi) as (finn & Lfinn & FFi). clear FHi.
destruct (rw_cells_CB_f32 asegs m11 (f + 544) 40 _ FHe) as (fexc & Lfexc & FFe). clear FHe.
destruct (rw_cells_CB_f32 asegs m11 (f + 768) 40 _ FHj) as (finn2 & Lfinn2 & FFj). clear FHj.
destruct (rw_cells_CB_f32 asegs m11 (f + 992) 10 _ FHq) as (fiq & Lfiq & FFq). clear FHq.
set (ffE := NBF fpw fpg flpc ql8 fak finn fexc finn2 fiq).
assert (FFOK : ff_ok ffE) by exact (conj Lfpg (conj Lflpc (conj Lql8 (conj Lfak (conj Lfinn (conj Lfexc (conj Lfinn2 Lfiq))))))).
assert (FFAT : fframe_at m11 f ffE) by exact (conj FH7 (conj FFp (conj FFg (conj FFl (conj QL8 (conj FFa (conj FFi (conj FFe (conj FFj FFq))))))))).
clear FH7 FFp FFg FFl QL8 FFa FFi FFe FFj FFq.

destruct (frame_live_apart RT AF Σ m fh kh PD NDs (proj1 ARTe) (proj1 INFHK) ltac:(rewrite <- LV1; exact INPD)) as (HPDF & _).
assert (DOA : hid (D + sb_buf_size b <= OUT \/ OUT + 8000 <= D)) by (unfold hid; clear - HPDF FO1 FO2 PD1 PD2 FSZ; lia).
assert (DSTA : hid (D + sb_buf_size b <= STEREO \/ STEREO + 8 <= D)) by (unfold hid; clear - HPDF FS1 FS2 PD1 PD2 FSZ; lia).
clear HPDF.
pose proof BSIDE as (BS_A8 & BS_A0 & BS_D0 & _ & _ & BS_AD).
set (X := NBX S OUT 2000 A D (sb_buf_size b) STEREO lo usp f sf gp (Z_to_bv 64 6489176) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m st b).
assert (NXOK : nbx_ok X).
{ unfold nbx_ok, X, NBD_FRAME, NBSTATE_SIZEOF, BITS_SIZEOF; cbn [x_st x_out x_nout x_A x_D x_dsz x_stereo x_lo x_usp x_ff x_sf x_b0 x_st0].
change (4 * Z.of_nat 2000) with 8000.
split; [exact SPA|]. split; [exact LB3|]. split; [exact LB2|]. split; [clear - LO544; lia|].
split; [exact FPOS|]. split; [exact F64|]. split; [reflexivity|]. split; [exact BF|]. split; [exact LB5|]. split; [exact LB6|].
split; [clear - SHF1; unfold SH_LO; lia|]. split; [clear - SHF2; unfold SH_HI; lia|]. split; [exact BF0|].
split; [exact S8|]. split; [exact SPOS|]. split; [exact BS1|]. split; [exact SSH9|]. split; [unfold hidp; right; exact STT9|].
split; [exact OAL|]. split; [clear - FPIMG FO1; cps_unf; lia|]. split; [exact OL|]. split; [lia|].
split; [clear - FPHI FO1 FO2 FSZ; unfold hidp, hid in *; cps_unf; lia|].
split; [exact BS_A8|]. split; [exact LB9|]. split; [exact AL|]. split; [exact LB10|].
split; [exact BS_D0|]. split; [exact LB14|]. split; [reflexivity|].
split; [exact SAL|]. split; [clear - FPIMG FS1; cps_unf; lia|]. split; [clear - TL; lia|].
split; [clear - FPHI FS1 FS2 FSZ; unfold hidp, hid in *; cps_unf; lia|].
split; [pose proof ISV as ISV'; cbn [isave_ok] in ISV'; destruct (nb_innov_save st) as [k|]; [clear - ISV'; lia| exact I]|].
split; [exact SOA|]. split; [exact SAA|]. split; [clear - DSA Lbsb; unfold hidp, hid in *; lia|]. split; [clear - STA; unfold hidp, hid in *; lia|].
split; [exact LB7|]. split; [exact LB8|].
split; [clear - HAO; unfold hidp, hid in *; lia|]. split; [clear - DOA; unfold hidp, hid in *; lia|]. split; [clear - HOS; unfold hidp, hid in *; lia|]. split; [exact OFA|]. split; [exact OSA|].
split; [clear - BS_AD; unfold hidp, BITS_SIZEOF in *; lia|]. split; [clear - HAS; unfold hidp, hid in *; lia|]. split; [exact LB11|]. split; [exact LB12|].
split; [clear - DSTA; unfold hidp, hid in *; lia|]. split; [exact LB15|]. split; [exact LB16|].
split; [clear - TFA; unfold hidp, hid in *; lia|]. split; [clear - TSA; unfold hidp, hid in *; lia|]. exact SHF3. }

assert (INVD : nb_inv stD).
{ pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold nb_inv.
rewrite KC, KES, KHP, KF, KVO, KPG, KSM, KWB, KLE, KSR, KIS.
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj MO5 (conj _ (conj I9 (conj I10 (conj I11 I12))))))))))).
destruct KDTX as [E|[E|E]]; rewrite E; [left; reflexivity| right; reflexivity| exact I8]. }
assert (NSIG : nbsig RT Σ1 X (rt_frames RT Σ) PD NDs fh kh).
{ unfold nbsig, X, NBD_FCLASS, NBD_FRAME, NBSTATE_SIZEOF, BITS_SIZEOF; cbn [x_st x_out x_nout x_A x_D x_dsz x_stereo x_lo x_usp x_ff x_sf].
change (4 * Z.of_nat 2000) with 8000.
split; [exact FRS1|]. split; [exact INL|]. split; [exact INPD|]. split; [exact PD1|]. split; [exact PD2|].
split; [intros E; apply (PDB (nb_blk st, S, NBSTATE_SIZEOF)); [left; reflexivity| cbn; symmetry; exact E]|].
split; [exact (proj1 INFHK)|]. split; [exact FO1|]. split; [exact FO2|]. split; [exact FA1|]. split; [exact FA2|].
split; [exact FS1|]. split; [clear - FS2; lia|].
split; [apply (pois_above_le _ usp); [exact POA| lia]|].
split; [exact LOW|]. split; [clear - LOR; unfold RT_STACK, NBD_CALLEE_STACK in *; lia|]. exact SPT. }
assert (NACC : nbacc X m11).
{ unfold nbacc, X, BITS_SIZEOF; cbn [x_out x_nout x_A x_stereo]. change (4 * Z.of_nat 2000) with 8000.
split; [exact (acc_of_pres_fp RT AF Σ m m m11 usp _ fh kh OUT 8000 (proj1 ARTe) (proj1 INFHK) FO1 FO2 PF OFFW ACO)|].
split; [exact (acc_of_pres_fp RT AF Σ m m m11 usp _ fh kh A 48 (proj1 ARTe) (proj1 INFHK) FA1 FA2 PF OFFW ACA)|].
exact (acc_sub asegs m11 STEREO 24 STEREO 8 (acc_of_pres_fp RT AF Σ m m m11 usp _ fh kh STEREO 24 (proj1 ARTe) (proj1 INFHK) FS1 FS2 PF OFFW ACST) ltac:(lia) ltac:(lia)). }
assert (LBRP : sm_lbr_pitch (smr_sm smr) = -1 /\ segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) = 0
\/ sm_lbr_pitch (smr_sm smr) <> -1 /\ 17 <= segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) <= 144).
{ unfold segD_olp. destruct (Z.eqb_spec (sm_lbr_pitch (smr_sm smr)) (-1)) as [E|E]; cbn [negb].
- left. split; [exact E| reflexivity].
- right. split; [exact E|]. pose proof (ub_ok (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1) 7 BOK8 ltac:(lia)) as (_ & _ & UV). change (2 ^ 7) with 128 in UV. lia. }
lazymatch goal with HC : ASTA _ _ _ (eq ?ms) _ |- realizes asegs _ _ =>
assert (ATE : at_E_A X smr mo (segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) 40 0 stD bD ms) end.
{ unfold at_E_A. exists F11, fc11, m11, xra11, t011, t111, t211, a011, a111, a211, a311, a411, a511, t311, t411, t511, t611, jE, ows, sws5,
(slots_D S f (sset 8 (Z_to_bv 64 (S + 8)) (slots_B2 S f slA))), ffE.
split; [reflexivity|]. split; [exact FRM11|].
split.
{ unfold nbctx. split; [exact MI11|]. split; [exact ST11|]. split; [exact NBPE|]. split; [exact JOKE|].
split; [rewrite KSC; exact CBOK|]. split; [exact INVD|]. split; [exact BREP11|]. split; [exact BOK11|]. split; [exact SZ11|].
split; [exact OC|]. split; [exact LOWS|]. split; [exact SW5|]. split; [exact LSW5|].
split; [exact (conj SL11 SV5)|]. split; [exact FFAT|]. split; [exact FFOK|]. split; [exists rs7; exact SH11|].
split; [exact CC11|]. split; [exact (AF_LIB Σ1 m11 ART)|]. split; [reflexivity| exact KIS]. }
split; [unfold slots_E; repeat split;
first [reflexivity | exact E0s | exact E24s | exact E32s | exact E40s | exact E48s | exact E136s | exact E152s | exact E168s | exact E240s
| exact E256s | exact E296s | exact E304s | exact E312s | exact E336s]|].
split; [exact SMR|]. split; [exact KSM|]. split; [lia|]. split; [exact LBRP| lia]. }
assert (LTPN : sm_ltp_unquant (smr_sm smr) <> None)
by (intro E; cbn [subframes_pure] in SUBF; unfold subframe_pure in SUBF; rewrite E in SUBF; cbn beta iota in SUBF; discriminate SUBF).
assert (INNN : sm_innovation_unquant (smr_sm smr) <> None)
by (intro E; cbn [subframes_pure] in SUBF; unfold subframe_pure in SUBF; rewrite E in SUBF; cbn beta iota in SUBF; destruct (sm_ltp_unquant (smr_sm smr)); discriminate SUBF).
assert (FRMX : (length (rt_frames RT Σ1) < FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; clear - FRM; lia).
assert (CRDX : NBD_EH_CREDIT <= rt_credit RT Σ1) by (rewrite CR1; unfold NBD_EH_CREDIT; clear - CRD; lia).
pose proof (EH Σ1 (PMfd F0 fs0) X (rt_frames RT Σ) PD NDs fh kh smr mo (segD_olp (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)) stD bD _
FDO MSTA eq_refl NXOK ATE NSIG NACC ART FRMX CRDX LTPN INNN) as EH1.
rewrite SUBF in EH1.
cps_rt EH1.

intros c12 (Σ12 & HA12 & EL12 & EF12 & ES12 & EC12 & EP12).
destruct (ASTA_unpack RT Σ12 (PMfd F0 fs0) _ c12 HA12) as (ms12 & PO12 & Hc12); clear HA12; cbv beta in PO12.
destruct PO12 as (AX12 & ART12 & NACC12 & WM12 & PF12).
destruct AX12 as (Fx & fcx & mX & xrax & xt0 & xt1 & xt2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xs5 & xs6 & xs7 & xs8 & xs11 & xt3 & xt4 & xt5 & xt6
& jX & owsX & swsX & sX & ffX & -> & FRMX2 & CTXX).
cbn [ms_mem MS] in ART12, NACC12, WM12, PF12.
destruct CTXX as (MIX & STX & NBPX & JOKX & CBOKX & INVX & BREPX & BOKX & SZX & OCX & LOWSX & SWX & LSWX & (SLX & SVX) & FFX & FFOKX & (rsX & SHX) & CCX & LCX & JEXC & JISV).
unfold X in STX, NBPX, BREPX, SZX, OCX, LOWSX, SWX, SLX, SVX, FFX, SHX, JEXC, JISV.
cbn [x_st x_out x_nout x_A x_D x_dsz x_stereo x_lo x_usp x_ff x_sf x_gp x_tp x_ra x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_F x_m0 x_st0 x_b0]
in STX, NBPX, BREPX, SZX, OCX, LOWSX, SWX, SLX, SVX, FFX, SHX, JEXC, JISV.

assert (STBX : rw_cells asegs mX (STEREO + 8) [CB 16 (firstn 16 (skipn 8 stb))]).
{ apply (rw_cells_agree asegs m11 mX _ _ STB); [| exact WM12]. apply (agree_of_pres_fp _ _ _ _ m11 mX _ PF12). intros ?x ?Hx. cps_sizes Hx. split; [nb_cls|].
unfold nbW_EH, X. cbn [x_st x_out x_nout x_A x_ff x_sf x_usp outside]. unfold NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. change (4 * Z.of_nat 2000) with 8000.
unfold hid in STA, HOS, HAS, TFA, TSA.
repeat split; intros ?HH; [clear - Hx HH STA; lia | clear - Hx HH HOS; lia | clear - Hx HH HAS; lia | clear - Hx HH TFA; lia | clear - Hx HH TSA; lia | clear - Hx HH TL LO544; lia]. }
assert (KEEPX : forall P, fp_local IO_FP P -> P m11 -> P mX).
{ intros P0 L0 Pm0. apply (nb_fp_local_pres_fp IO_FP P0 _ _ _ _ m11 mX L0 IO_img PF12); [| exact Pm0].
intros y Hy. pose proof (nb_client_static_range _ Hy) as R. unfold nbW_EH, X. cbn [x_st x_out x_nout x_A x_ff x_sf x_usp outside].
unfold NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME, SEGTOP_A in *. change (4 * Z.of_nat 2000) with 8000.
repeat split; intros ?HH; [clear - R HH STOP | clear - R HH FO1 FPIMG | clear - R HH FA1 FPIMG | clear - R HH FIMG | clear - R HH SHF1 | clear - R HH LO544 BF FIMG]; lia. }
pk_io ERR_rep OUT_rep KEEPX. clear KEEPX.

assert (PFX : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: (S, S + 2968) :: IO_FP) m mX).
{ apply (pres_fp_trans _ _ _ _ m m11 mX PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp - 544) (nbW_EH X) m11 mX PF12).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx Ho. unfold nbW_EH, X. cbn [x_st x_out x_nout x_A x_ff x_sf x_usp outside] in Ho |- *.
destruct Ho as (HA & HO & HT & HS & _). pose proof (NAF x Hx) as (NF & NSF). pose proof (SPL x Hx) as HSP.
unfold NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. change (4 * Z.of_nat 2000) with 8000.
repeat split; [exact HS| exact HO| exact HA| exact NF| exact NSF| clear - HSP LOW SP1 LO544; lia]. }
clear PF. rename PFX into PF.
apply rw_cells_to_CB in SLX. cbn [cells_size csize slot_cells Nat.add] in SLX.
chunk_cat SWX STBX. apply rw_cells_to_CB in SWX. rewrite cells_size_app, cells_size_f32, LSWX in SWX. cbn [cells_size csize Nat.add Nat.mul] in SWX.
pose proof NBPX as (_ & _ & EXPX & _). rewrite JEXC in EXPX.
pose proof FFX as (FHX & _).
pose proof (subframes_blk _ _ _ _ _ _ _ _ SUBF) as BLKE.
pose proof (bkeep_trans _ _ _ (bkeep_trans _ _ _ (bkeep_trans _ _ _ BK BKL) (bkeep_segD (set_nb_submodeID st mo) (smr_sm smr) (lsp_bits (sm_lsp_unquant (smr_sm smr)) b1)))
(bkeep_subframes _ _ _ _ _ _ _ _ SUBF)) as (BKE1 & BKE2 & BKE3).
match goal with HC : ASTA RT _ _ (eq _) ?cc |- realizes asegs ?cc _ => refine (rz_cps RT _ _ _ _ _ cc HC _ _) end;
[ eapply (nbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SF5 Σ Σ12 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mX lo S OUT STEREO A D f fh PD NDs kh [(nb_blk st, S, NBSTATE_SIZEOF)] 0
(DecNB (nb_end stE)) bE owsX) | ].
{ rewrite EF12. exact FRS1. } { rewrite EL12. exact LV1. } { rewrite ES12. exact SP1. } { rewrite EP12. exact PO1. } { exact (proj1 ARTe). }
{ first [exact POA | rewrite <- PO1; exact POA]. } { exact NAF. } { first [exact LIVE | intros x Hx; rewrite <- LV1; exact (LIVE x Hx)]. }
{ first [exact INPD | rewrite <- LV1; exact INPD]. } { exact PD1. } { rewrite BKE3. exact PD2. } { exact (proj1 INFHK). }
{ exact FA1. } { exact FA2. } { exact ACA. } { exact FO1. } { exact FO2. } { exact ACO. } { exact FS1. } { exact FS2. } { exact ACST. }
{ exact ART12. } { exact MIX. } { exact FRMX2. } { exact STX. }
{ rewrite <- SP1. exact LOW. } { clear - LOR. unfold RT_STACK in *. lia. } { exact SPT. } { exact SPA. }
{ exact PF. } { cps_wmono. } { exact SLX. } { exact SVX. } { exact FHX. } { exact SHX. }
{ cbn [decst_rep]. split; [cbn [nb_blk nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first]; rewrite BLKE, KB; reflexivity|].
unfold nbstate_rep. split; [exact S8|]. split; [exact SPOS|]. split; [exact INVX|].
exists jX. split; [exact JOKX|]. split; [exact CBOKX|]. apply nb_cells_of_pieces; [exact JOKX| exact NBPX]. }
{ intros _. exact EXPX. }
{ exact BREPX. } { exact BOKX. } { exact OCX. } { exact LOWSX. } { exact SWX. } { assumption. } { assumption. }
intros c13 Q13. cbn [Spec.X1nu.evw map]. apply rz_emit_nil. apply Hk.
destruct Q13 as (Σ13 & HA13 & EL13 & EF13 & ES13 & EC13 & EP13). exists Σ13. split; [exact HA13|].
cbn [dec_depth dec_mode dec_nestedR dec_credit]. unfold NBDEC_CREDIT, NBD_EH_CREDIT in *.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact BKE1|]. split; [exact BKE2|]. split; [exact BKE3|].
split; [exact EL13|]. split; [exact EF13|]. split; [exact ES13|].
split; [rewrite EC13; clear - EC12 CR1; lia| exact EP13].
Qed.

End NbDecodeCPS.
