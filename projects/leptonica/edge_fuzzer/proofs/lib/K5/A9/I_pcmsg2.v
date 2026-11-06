(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import StrFun.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcdint I_pcdstr I_pcfmt I_pcdzu I_pcmsg.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.  (* [comment removed for export] *)

Lemma bytes_at_sub : forall m A (bs : list byte) i k, bytes_at asegs m A bs -> (i + k <= length bs)%nat ->
  bytes_at asegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k H Hik. rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Definition MSG_PRE : list Z := [37; 115; 58; 37; 122; 117; 58; 32].     (* [comment removed for export] *)
Definition FMA (t1 : list Z) : list Z := MSG_PRE ++ t1 ++ [37; 115].

Lemma msgA_pieces : forall m A t1, cstr_at m A (zb8 (FMA t1)) ->
  bytes_at asegs m A (zb8 [37; 115; 58]) /\ bytes_at asegs m (A + 2) (zb8 [58])
  /\ bytes_at asegs m (A + 3) (zb8 [37; 122; 117; 58]) /\ bytes_at asegs m (A + 6) (zb8 ([58; 32] ++ t1))
  /\ bytes_at asegs m (A + 8 + Z.of_nat (length t1)) (zb8 [37; 115; 0]).
Proof.
  intros m A t1 (BY & _). unfold FMA, MSG_PRE in BY.
  assert (L : length (zb8 ([37; 115; 58; 37; 122; 117; 58; 32] ++ t1 ++ [37; 115]) ++ [z8]) = (11 + length t1)%nat).
  { rewrite length_app, length_zb8, !length_app. cbn [length]. lia. }
  split; [pose proof (bytes_at_sub m A _ 0 3 BY ltac:(lia)) as B; cbn [firstn skipn zb8 map app Z.of_nat] in B |- *;
          rewrite Z.add_0_r in B; exact B|].
  split; [pose proof (bytes_at_sub m A _ 2 1 BY ltac:(lia)) as B; cbn [firstn skipn zb8 map app Z.of_nat] in B |- *; exact B|].
  split; [pose proof (bytes_at_sub m A _ 3 4 BY ltac:(lia)) as B; cbn [firstn skipn zb8 map app Z.of_nat] in B |- *; exact B|].
  replace (zb8 ([37; 115; 58; 37; 122; 117; 58; 32] ++ t1 ++ [37; 115]) ++ [z8])
    with (zb8 [37; 115; 58; 37; 122; 117] ++ (zb8 ([58; 32] ++ t1) ++ zb8 [37; 115; 0])) in BY.
  2:{ rewrite !zb8_app. cbn [zb8 map app]. rewrite <- !app_assoc. reflexivity. }
  apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [B4 B5].
  rewrite !length_zb8, length_app in B5. cbn [length] in B4, B5. rewrite length_zb8 in B4. cbn [length] in B4.
  split; [exact B4|]. replace (A + 8 + Z.of_nat (length t1)) with (A + Z.of_nat 6 + Z.of_nat (S (S (length t1)))) by lia. exact B5.
Qed.

Definition FMB (t1 t2 : list Z) : list Z := MSG_PRE ++ t1 ++ [37; 115] ++ t2 ++ [37; 115].

Lemma msgB_pieces : forall m A t1 nx t2, cstr_at m A (zb8 (FMB t1 (nx :: t2))) ->
  bytes_at asegs m A (zb8 [37; 115; 58]) /\ bytes_at asegs m (A + 2) (zb8 [58])
  /\ bytes_at asegs m (A + 3) (zb8 [37; 122; 117; 58]) /\ bytes_at asegs m (A + 6) (zb8 ([58; 32] ++ t1))
  /\ bytes_at asegs m (A + 8 + Z.of_nat (length t1)) (zb8 [37; 115; nx])
  /\ bytes_at asegs m (A + 10 + Z.of_nat (length t1)) (zb8 (nx :: t2))
  /\ bytes_at asegs m (A + 10 + Z.of_nat (length t1) + Z.of_nat (length (nx :: t2))) (zb8 [37; 115; 0]).
Proof.
  intros m A t1 nx t2 (BY & _). unfold FMB, MSG_PRE in BY.
  assert (L : length (zb8 ([37; 115; 58; 37; 122; 117; 58; 32] ++ t1 ++ [37; 115] ++ (nx :: t2) ++ [37; 115]) ++ [z8])
              = (14 + length t1 + length t2)%nat).
  { rewrite length_app, length_zb8, !length_app. cbn [length]. lia. }
  split; [pose proof (bytes_at_sub m A _ 0 3 BY ltac:(lia)) as B; cbn [firstn skipn zb8 map app Z.of_nat] in B |- *;
          rewrite Z.add_0_r in B; exact B|].
  split; [pose proof (bytes_at_sub m A _ 2 1 BY ltac:(lia)) as B; cbn [firstn skipn zb8 map app Z.of_nat] in B |- *; exact B|].
  split; [pose proof (bytes_at_sub m A _ 3 4 BY ltac:(lia)) as B; cbn [firstn skipn zb8 map app Z.of_nat] in B |- *; exact B|].
  replace (zb8 ([37; 115; 58; 37; 122; 117; 58; 32] ++ t1 ++ [37; 115] ++ (nx :: t2) ++ [37; 115]) ++ [z8])
    with (zb8 [37; 115; 58; 37; 122; 117] ++ (zb8 ([58; 32] ++ t1) ++ ((zb8 [37; 115] ++ zb8 (nx :: t2)) ++ zb8 [37; 115; 0]))) in BY.
  2:{ rewrite !zb8_app. cbn [zb8 map app]. rewrite <- !app_assoc. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [B4 BY].
  apply bytes_at_app in BY. destruct BY as [B56 B7].
  assert (E1 : Z.of_nat (length (zb8 ([58; 32] ++ t1))) = 2 + Z.of_nat (length t1))
    by (unfold zb8; rewrite length_map, length_app; cbn [length]; lia).
  assert (E2 : Z.of_nat (length (zb8 [37; 115] ++ zb8 (nx :: t2))) = 3 + Z.of_nat (length t2))
    by (unfold zb8; rewrite length_app, !length_map; cbn [length]; lia).
  rewrite E1 in B56, B7. rewrite E2 in B7.
  split; [exact B4|].
  split.
  { pose proof (bytes_at_sub m _ _ 0 3 B56 ltac:(unfold zb8; rewrite length_app, !length_map; cbn [length]; lia)) as B.
    cbn [firstn skipn zb8 map app Z.of_nat] in B |- *. rewrite Z.add_0_r in B.
    replace (A + 8 + Z.of_nat (length t1)) with (A + Z.of_nat 6 + (2 + Z.of_nat (length t1))) by lia. exact B. }
  split.
  { apply bytes_at_app in B56. destruct B56 as [_ B6]. cbn [length zb8 map] in B6.
    replace (A + 10 + Z.of_nat (length t1)) with (A + Z.of_nat 6 + (2 + Z.of_nat (length t1)) + Z.of_nat 2) by lia. exact B6. }
  replace (A + 10 + Z.of_nat (length t1) + Z.of_nat (length (nx :: t2)))
    with (A + Z.of_nat 6 + (2 + Z.of_nat (length t1)) + (3 + Z.of_nat (length t2))) by (cbn [length]; lia). exact B7.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Local Ltac tr_below B MU := apply (bytes_at_agree asegs _ _ _ _ B); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
  cbn [outside]; rewrite ?length_zb8, ?length_app in Hx; cbn [length zb8 map] in Hx; lia.

(* [comment removed for export] *)
Local Ltac str_facts m MU SLOT CSS CHKS PCX SLOT1 CS1 CHK1 PCX1 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SLOT1 : ro_cells asegs mm _ _) by
      (apply (ro_cells_agree asegs m mm _ _ SLOT); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside cells_size csize Nat.add] in *; lia);
    assert (CS1 : cstr_at mm _ _) by
      (apply (cstr_agree m mm _ _ CSS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia);
    assert (CHK1 : chk_ok mm _ _) by
      (eapply chk_ok_agree; [exact CHKS | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.

Lemma pcom_msgA_spec : forall (A : Z) (t1 : list Z) (ap S1 S2 : Z) (str1 str2 : list byte) (lo : Z)
    ra sp gp tp t0 t1' t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap -> txt_ok t1 = true ->
  cstr_at m A (zb8 (FMA t1)) -> A + Z.of_nat (length t1) + 11 <= lo ->
  ro_cells asegs m ap [C8 (Z_to_bv 64 S1)] -> ro_cells asegs m (ap + 16) [C8 (Z_to_bv 64 S2)] ->
  bv_unsigned sp <= ap -> ap + 24 < 2^63 ->
  cstr_at m S1 str1 -> 0 < S1 -> (S1 + Z.of_nat (length str1) + 1 <= lo \/ bv_unsigned sp <= S1) ->
  S1 + Z.of_nat (length str1) + 1 < 2^47 -> chk_ok m S1 (Z.of_nat (length str1) + 1) ->
  cstr_at m S2 str2 -> 0 < S2 -> (S2 + Z.of_nat (length str2) + 1 <= lo \/ bv_unsigned sp <= S2) ->
  S2 + Z.of_nat (length str2) + 1 < 2^47 -> chk_ok m S2 (Z.of_nat (length str2) + 1) ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  chk_ok m A (Z.of_nat (length t1) + 11) -> pctx m -> mem_inv asegs m ->
  evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa73a8) (RT_iface.frm_clear fc) None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> OK1 CS AB SL1 SL3 QAP APH CSS1 S10 SSEP1 SH1 CHKS1 CSS2 S20 SSEP2 SH2 CHKS2 ST LO LOLO SPH S16 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  unfold kHighShadowEnd in LOLO.
  pose proof (cstr_bound _ _ _ CS) as (A0 & _).
  pose proof (msgA_pieces m A t1 CS) as PP.
  pose proof (conj SL1 I) as SL1b. pose proof (conj SL3 I) as SL3b. clear SL1 SL3.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LF : Z.of_nat (length (zb8 (FMA t1))) = Z.of_nat (length t1) + 10).
  { unfold FMA, MSG_PRE. rewrite length_zb8, !length_app. cbn [length]. lia. }
  call (pcom_head_spec RIP q A ap (zb8 (FMA t1)) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
    | exact CS | unfold FMA, MSG_PRE; rewrite length_zb8, !length_app; cbn [length]; lia | rewrite LF; lia | rewrite LF; replace (Z.of_nat (length t1) + 10 + 1) with (Z.of_nat (length t1) + 11) by lia; exact CHK
    | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  (* [comment removed for export] *)
  str_facts m MU (proj1 SL1b) CSS1 CHKS1 PCX SLa CSa CHKa PCXa.
  call (pcom_dstr_spec RIP q A ap 58 S1 str1 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | tr_below (proj1 PP) MU | assumption | exact SLa | lia | lia
    | exact CSa | exact S10 | lia | exact SH1 | exact CHKa | exact PCXa | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | lia
    | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd2 & DIR2) end.
  call (pcom_setup_spec q jd2); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR2 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec [58] (A + 2)); [reflexivity | reflexivity | reflexivity | tr_below (proj1 (proj2 PP)) MU
                                                         | assumption] |].
  intros ms' (a0' & ->). replace (A + 2 + Z.of_nat (length [58])) with (A + 3) by (cbn; lia).
  (* [comment removed for export] *)
  call (pcom_dzu_spec q (A + 3) (ap + 8) 58 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | tr_below (proj1 (proj2 (proj2 PP))) MU | assumption | assumption | lia | lia | lia | lia | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd3 & DIR3) end.
  call (pcom_setup_spec q jd3); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR3 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec ([58; 32] ++ t1) (A + 3 + 3)); [reflexivity | reflexivity | cbn [txt_ok forallb]; exact OK1
                                                         | replace (A + 3 + 3) with (A + 6) by lia; tr_below (proj1 (proj2 (proj2 (proj2 PP)))) MU
                                                         | assumption] |].
  intros ms' (a0'' & ->).
  replace (A + 3 + 3 + Z.of_nat (length ([58; 32] ++ t1))) with (A + 8 + Z.of_nat (length t1)) by (rewrite length_app; cbn [length]; lia).
  replace (ap + 8 + 8) with (ap + 16) by lia.
  (* [comment removed for export] *)
  str_facts m MU (proj1 SL3b) CSS2 CHKS2 PCX SLb CSb CHKb PCXb.
  call (pcom_dstr_last_spec RIP q (A + 8 + Z.of_nat (length t1)) (ap + 16) S2 str2 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | tr_below (proj2 (proj2 (proj2 (proj2 PP)))) MU | assumption | exact SLb | lia | lia
    | exact CSb | exact S20 | lia | exact SH2 | exact CHKb | exact PCXb | assumption | lia | (unfold kHighShadowEnd; lia) | lia | lia
    | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd4 & DIR4) end.
  call (pcom_end2_spec q ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [ reflexivity | exact FRh | lia | assumption | ].
  release_frame FRa PC (q + -2216). release_frame DIR4 PC (q + -2176). release_frame FRb PC (q + -104).
  unfold pcom_saved in FRh. release_frame FRh PC q.
  apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

Lemma pcom_msgB_spec : forall (A : Z) (t1 : list Z) (nx : Z) (t2 : list Z) (ap S1 S2 S3 : Z) (str1 str2 str3 : list byte) (lo : Z)
    ra sp gp tp t0 t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap -> txt_ok t1 = true -> txt_ok (nx :: t2) = true ->
  cstr_at m A (zb8 (FMB t1 (nx :: t2))) -> A + Z.of_nat (length t1) + Z.of_nat (length t2) + 14 <= lo ->
  ro_cells asegs m ap [C8 (Z_to_bv 64 S1)] -> ro_cells asegs m (ap + 16) [C8 (Z_to_bv 64 S2)] ->
  ro_cells asegs m (ap + 24) [C8 (Z_to_bv 64 S3)] ->
  bv_unsigned sp <= ap -> ap + 32 < 2^63 ->
  cstr_at m S1 str1 -> 0 < S1 -> (S1 + Z.of_nat (length str1) + 1 <= lo \/ bv_unsigned sp <= S1) ->
  S1 + Z.of_nat (length str1) + 1 < 2^47 -> chk_ok m S1 (Z.of_nat (length str1) + 1) ->
  cstr_at m S2 str2 -> 0 < S2 -> (S2 + Z.of_nat (length str2) + 1 <= lo \/ bv_unsigned sp <= S2) ->
  S2 + Z.of_nat (length str2) + 1 < 2^47 -> chk_ok m S2 (Z.of_nat (length str2) + 1) ->
  cstr_at m S3 str3 -> 0 < S3 -> (S3 + Z.of_nat (length str3) + 1 <= lo \/ bv_unsigned sp <= S3) ->
  S3 + Z.of_nat (length str3) + 1 < 2^47 -> chk_ok m S3 (Z.of_nat (length str3) + 1) ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  chk_ok m A (Z.of_nat (length t1) + Z.of_nat (length t2) + 14) -> pctx m -> mem_inv asegs m ->
  evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa73a8) (RT_iface.frm_clear fc) None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> OK1 OK2 CS AB SL1 SL2 SL3 QAP APH CSS1 S10 SSEP1 SH1 CHKS1 CSS2 S20 SSEP2 SH2 CHKS2
    CSS3 S30 SSEP3 SH3 CHKS3 ST LO LOLO SPH S16 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  unfold kHighShadowEnd in LOLO.
  pose proof (cstr_bound _ _ _ CS) as (A0 & _).
  pose proof (msgB_pieces m A t1 nx t2 CS) as PP.
  pose proof (conj SL1 I) as SL1b. pose proof (conj SL2 I) as SL2b. pose proof (conj SL3 I) as SL3b. clear SL1 SL2 SL3.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (NX : 0 < nx < 256).
  { cbn [txt_ok forallb] in OK2. apply andb_prop in OK2. destruct OK2 as [H _]. apply andb_prop in H. destruct H as [H _].
    apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. }
  assert (LF : Z.of_nat (length (zb8 (FMB t1 (nx :: t2)))) = Z.of_nat (length t1) + Z.of_nat (length t2) + 13).
  { unfold FMB, MSG_PRE. rewrite length_zb8, !length_app. cbn [length]. lia. }
  call (pcom_head_spec RIP q A ap (zb8 (FMB t1 (nx :: t2))) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
    | exact CS | unfold FMB, MSG_PRE; rewrite length_zb8, !length_app; cbn [length]; lia | rewrite LF; lia
    | rewrite LF; replace (Z.of_nat (length t1) + Z.of_nat (length t2) + 13 + 1) with (Z.of_nat (length t1) + Z.of_nat (length t2) + 14) by lia; exact CHK
    | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  (* [comment removed for export] *)
  str_facts m MU (proj1 SL1b) CSS1 CHKS1 PCX SLa CSa CHKa PCXa.
  call (pcom_dstr_spec RIP q A ap 58 S1 str1 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | tr_below (proj1 PP) MU | assumption | exact SLa | lia | lia
    | exact CSa | exact S10 | lia | exact SH1 | exact CHKa | exact PCXa | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | lia
    | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd2 & DIR2) end.
  call (pcom_setup_spec q jd2); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR2 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec [58] (A + 2)); [reflexivity | reflexivity | reflexivity | tr_below (proj1 (proj2 PP)) MU
                                                         | assumption] |].
  intros ms' (a0a & ->). replace (A + 2 + Z.of_nat (length [58])) with (A + 3) by (cbn; lia).
  (* [comment removed for export] *)
  call (pcom_dzu_spec q (A + 3) (ap + 8) 58 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | tr_below (proj1 (proj2 (proj2 PP))) MU | assumption | assumption | lia | lia | lia | lia | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd3 & DIR3) end.
  call (pcom_setup_spec q jd3); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR3 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec ([58; 32] ++ t1) (A + 3 + 3)); [reflexivity | reflexivity | cbn [txt_ok forallb]; exact OK1
                                                         | replace (A + 3 + 3) with (A + 6) by lia; tr_below (proj1 (proj2 (proj2 (proj2 PP)))) MU
                                                         | assumption] |].
  intros ms' (a0b & ->).
  replace (A + 3 + 3 + Z.of_nat (length ([58; 32] ++ t1))) with (A + 8 + Z.of_nat (length t1)) by (rewrite length_app; cbn [length]; lia).
  replace (ap + 8 + 8) with (ap + 16) by lia.
  (* [comment removed for export] *)
  str_facts m MU (proj1 SL2b) CSS2 CHKS2 PCX SLb CSb CHKb PCXb.
  call (pcom_dstr_spec RIP q (A + 8 + Z.of_nat (length t1)) (ap + 16) nx S2 str2 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | exact NX | tr_below (proj1 (proj2 (proj2 (proj2 (proj2 PP))))) MU | assumption | exact SLb | lia | lia
    | exact CSb | exact S20 | lia | exact SH2 | exact CHKb | exact PCXb | assumption | lia | (unfold kHighShadowEnd; lia) | lia | lia
    | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd4 & DIR4) end.
  call (pcom_setup_spec q jd4); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR4 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec (nx :: t2) (A + 8 + Z.of_nat (length t1) + 2)); [reflexivity | reflexivity | exact OK2
                                                         | replace (A + 8 + Z.of_nat (length t1) + 2) with (A + 10 + Z.of_nat (length t1)) by lia;
                                                           tr_below (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PP)))))) MU
                                                         | assumption] |].
  intros ms' (a0c & ->).
  replace (A + 8 + Z.of_nat (length t1) + 2 + Z.of_nat (length (nx :: t2))) with (A + 10 + Z.of_nat (length t1) + Z.of_nat (length (nx :: t2))) by lia.
  replace (ap + 16 + 8) with (ap + 24) by lia.
  (* [comment removed for export] *)
  str_facts m MU (proj1 SL3b) CSS3 CHKS3 PCX SLc CSc CHKc PCXc.
  call (pcom_dstr_last_spec RIP q (A + 10 + Z.of_nat (length t1) + Z.of_nat (length (nx :: t2))) (ap + 24) S3 str3 lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | tr_below (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PP)))))) MU | assumption | exact SLc | lia | lia
    | exact CSc | exact S30 | lia | exact SH3 | exact CHKc | exact PCXc | assumption | lia | (unfold kHighShadowEnd; lia) | cbn [length] in *; lia | lia
    | assumption | ].
  lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd5 & DIR5) end.
  call (pcom_end2_spec q ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [ reflexivity | exact FRh | lia | assumption | ].
  release_frame FRa PC (q + -2216). release_frame DIR5 PC (q + -2176). release_frame FRb PC (q + -104).
  unfold pcom_saved in FRh. release_frame FRh PC q.
  apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

End WithRIP.
