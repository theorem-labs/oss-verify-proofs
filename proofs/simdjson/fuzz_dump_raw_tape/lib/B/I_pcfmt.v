(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcdint I_pcdstr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma img_bytes : forall m a l, mem_inv bsegs m -> 0 <= a -> a + Z.of_nat (length l) <= 2^64 ->
  ro_bytes_b bsegs a (zb8 l) = true -> bytes_at bsegs m a (zb8 l).
Proof.
  intros m a l MI H0 H1 HB. apply ro_bytes_at; [exact MI | lia | unfold zb8; rewrite length_map; lia|].
  apply ro_bytes_b_sound. exact HB.
Qed.
Ltac img_tac := apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity].

Definition pcom_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - PCOM_DEPTH, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma txt_ok_bytes : forall l, txt_ok l = true -> forallb (fun c => (0 <? c) && (c <? 256)) l = true.
Proof.
  induction l as [|c l IH]; intros H; [reflexivity|]. cbn [txt_ok forallb] in *. apply andb_prop in H. destruct H as [H1 H2].
  apply andb_prop in H1. destruct H1 as [H1 _]. rewrite H1. cbn. apply IH. exact H2.
Qed.

Lemma txt_ok_app : forall l1 l2, txt_ok (l1 ++ l2) = txt_ok l1 && txt_ok l2.
Proof. intros l1 l2. unfold txt_ok. apply forallb_app. Qed.

Lemma length_zb8 : forall l, length (zb8 l) = length l.
Proof. intros l. unfold zb8. apply length_map. Qed.

Lemma zb8_app : forall l1 l2, zb8 (l1 ++ l2) = zb8 l1 ++ zb8 l2.
Proof. intros l1 l2. unfold zb8. apply map_app. Qed.

Lemma fmt_pieces : forall m A l1 c nx l2,
  cstr_at m A (zb8 (l1 ++ [37; c] ++ nx :: l2)) ->
  bytes_at bsegs m A (zb8 l1) /\ bytes_at bsegs m (A + Z.of_nat (length l1)) (zb8 [37; c; nx])
  /\ bytes_at bsegs m (A + Z.of_nat (length l1) + 2) (zb8 (nx :: l2))
  /\ bytes_at bsegs m (A + Z.of_nat (length l1) + 2 + Z.of_nat (length (nx :: l2))) [z8].
Proof.
  intros m A l1 c nx l2 (BY & _).
  rewrite !zb8_app in BY. rewrite <- !app_assoc in BY.
  apply (proj1 (bytes_at_app bsegs m A _ _)) in BY. destruct BY as [B1 BY]. rewrite length_zb8 in BY.
  split; [exact B1|].
  cbn [zb8 map app] in BY |- *.
  pose proof BY as BY'.
  apply (proj1 (bytes_at_app bsegs m _ [Z_to_bv 8 37; Z_to_bv 8 c; Z_to_bv 8 nx] _)) in BY'. destruct BY' as [B2 _].
  split; [exact B2|].
  apply (proj1 (bytes_at_app bsegs m _ [Z_to_bv 8 37; Z_to_bv 8 c] _)) in BY. destruct BY as [_ BY]. cbn [length Z.of_nat] in BY.
  change (Z.of_nat 2) with 2 in BY.
  apply (proj1 (bytes_at_app bsegs m _ (Z_to_bv 8 nx :: map (Z_to_bv 8) l2) _)) in BY. destruct BY as [B3 B4].
  split; [exact B3|]. cbn [length] in B4 |- *. rewrite length_map in B4. exact B4.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Ltac tr_below B MU := apply (bytes_at_agree bsegs _ _ _ _ B); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
  cbn [outside]; rewrite ?length_zb8 in Hx; cbn [length zb8 map] in Hx; lia.

Lemma pcom_fint_spec : forall (A : Z) (l1 : list Z) (c nx : Z) (l2 : list Z) (ap lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  txt_ok l1 = true -> txt_ok (nx :: l2) = true -> (c = 100 \/ c = 117) ->
  cstr_at m A (zb8 (l1 ++ [37; c] ++ nx :: l2)) -> A + Z.of_nat (length l1) + Z.of_nat (length l2) + 4 <= lo ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> 0 <= ap < 2^63 ->
  chk_ok m A (Z.of_nat (length l1) + Z.of_nat (length l2) + 4) -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros -> -> OK1 OK2 CC CS AB ST LO LOLO SPH S16 AP0 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  unfold kHighShadowEnd in LOLO.
  pose proof (cstr_bound _ _ _ CS) as (A0 & _).
  pose proof (fmt_pieces m A l1 c nx l2 CS) as PP.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (NX : 0 < nx < 256).
  { cbn [txt_ok forallb] in OK2. apply andb_prop in OK2. destruct OK2 as [H _]. apply andb_prop in H. destruct H as [H _].
    apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. }
  assert (LF : Z.of_nat (length (zb8 (l1 ++ [37; c] ++ nx :: l2))) = Z.of_nat (length l1) + Z.of_nat (length l2) + 3).
  { rewrite length_zb8, !length_app. cbn [length]. lia. }
  call (pcom_head_spec RIP q A ap (zb8 (l1 ++ [37; c] ++ nx :: l2)) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
    | exact CS | rewrite length_zb8, !length_app; cbn [length]; lia | rewrite LF; lia | rewrite LF; replace (Z.of_nat (length l1) + Z.of_nat (length l2) + 3 + 1) with (Z.of_nat (length l1) + Z.of_nat (length l2) + 4) by lia; exact CHK
    | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec l1 A); [reflexivity | reflexivity | exact OK1 | tr_below (proj1 PP) MU | assumption] |].
  intros ms' (a0' & ->).
  call (pcom_dint_spec q (A + Z.of_nat (length l1)) ap c nx lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | exact CC | exact NX | tr_below (proj1 (proj2 PP)) MU | assumption | exact ST | lia | lia | lia | lia | assumption | ].
  lazymatch goal with H : exists junk, rw_cells bsegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd2 & DIR2) end.
  call (pcom_setup_spec q jd2); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR2 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec (nx :: l2) (A + Z.of_nat (length l1) + 2)); [reflexivity | reflexivity | exact OK2 | tr_below (proj1 (proj2 (proj2 PP))) MU | assumption] |].
  intros ms' (a0'' & ->).
  lazymatch goal with H : rw_cells bsegs _ (q + -2216) DIR0 |- _ => rename H into DIR3 end.
  call (pcom_end_spec q (A + Z.of_nat (length l1) + 2 + Z.of_nat (length (nx :: l2))) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
    [ reflexivity | reflexivity | reflexivity | reflexivity | tr_below (proj2 (proj2 (proj2 PP))) MU
    | eapply (cells_byte _ _ _ 36%nat z8); [exact DIR3 | reflexivity | lia] | exact FRh | lia | assumption | ].
  release_frame FRa PC (q + -2216). unfold DIR0 in DIR3. release_frame DIR3 PC (q + -2176). release_frame FRb PC (q + -104).
  unfold pcom_saved in FRh. release_frame FRh PC q.
  apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

Lemma pcom_fstr_spec : forall (A : Z) (l1 : list Z) (nx : Z) (l2 : list Z) (ap S : Z) (str : list byte) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  txt_ok l1 = true -> txt_ok (nx :: l2) = true ->
  cstr_at m A (zb8 (l1 ++ [37; 115] ++ nx :: l2)) -> A + Z.of_nat (length l1) + Z.of_nat (length l2) + 4 <= lo ->
  ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
  cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
  chk_ok m S (Z.of_nat (length str) + 1) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  chk_ok m A (Z.of_nat (length l1) + Z.of_nat (length l2) + 4) -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros -> -> OK1 OK2 CS AB SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  unfold kHighShadowEnd in LOLO.
  pose proof (cstr_bound _ _ _ CS) as (A0 & _).
  pose proof (fmt_pieces m A l1 115 nx l2 CS) as PP.
  pose proof (conj SLOT I) as SLOTb. clear SLOT.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (NX : 0 < nx < 256).
  { cbn [txt_ok forallb] in OK2. apply andb_prop in OK2. destruct OK2 as [H _]. apply andb_prop in H. destruct H as [H _].
    apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. }
  assert (LF : Z.of_nat (length (zb8 (l1 ++ [37; 115] ++ nx :: l2))) = Z.of_nat (length l1) + Z.of_nat (length l2) + 3).
  { rewrite length_zb8, !length_app. cbn [length]. lia. }
  call (pcom_head_spec RIP q A ap (zb8 (l1 ++ [37; 115] ++ nx :: l2)) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
    | exact CS | rewrite length_zb8, !length_app; cbn [length]; lia | rewrite LF; lia | rewrite LF; replace (Z.of_nat (length l1) + Z.of_nat (length l2) + 3 + 1) with (Z.of_nat (length l1) + Z.of_nat (length l2) + 4) by lia; exact CHK
    | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec l1 A); [reflexivity | reflexivity | exact OK1 | tr_below (proj1 PP) MU | assumption] |].
  intros ms' (a0' & ->).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SLOT1 : ro_cells bsegs mm ap [C8 (Z_to_bv 64 S)]) by
      (apply (ro_cells_agree bsegs m mm _ _ (proj1 SLOTb)); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside cells_size csize Nat.add] in *; lia);
    assert (CS1 : cstr_at mm S str) by
      (apply (cstr_agree m mm S str CSS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia);
    assert (CHK1 : chk_ok mm S (Z.of_nat (length str) + 1)) by
      (eapply chk_ok_agree; [exact CHKS | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
  call (pcom_dstr_spec RIP q (A + Z.of_nat (length l1)) ap nx S str lo);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | exact NX | tr_below (proj1 (proj2 PP)) MU | assumption | exact SLOT1 | lia | lia
    | exact CS1 | exact S0 | lia | exact SH | exact CHK1 | exact PCX1 | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | lia
    | assumption | ].
  lazymatch goal with H : exists junk, rw_cells bsegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd2 & DIR2) end.
  call (pcom_setup_spec q jd2); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR2 | exact S16 | lia | assumption | ].
  eapply evt_cut; [eapply (pcom_scan_spec (nx :: l2) (A + Z.of_nat (length l1) + 2)); [reflexivity | reflexivity | exact OK2 | tr_below (proj1 (proj2 (proj2 PP))) MU | assumption] |].
  intros ms' (a0'' & ->).
  lazymatch goal with H : rw_cells bsegs _ (q + -2216) DIR0 |- _ => rename H into DIR3 end.
  call (pcom_end_spec q (A + Z.of_nat (length l1) + 2 + Z.of_nat (length (nx :: l2))) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
    [ reflexivity | reflexivity | reflexivity | reflexivity | tr_below (proj2 (proj2 (proj2 PP))) MU
    | eapply (cells_byte _ _ _ 36%nat z8); [exact DIR3 | reflexivity | lia] | exact FRh | lia | assumption | ].
  release_frame FRa PC (q + -2216). unfold DIR0 in DIR3. release_frame DIR3 PC (q + -2176). release_frame FRb PC (q + -104).
  unfold pcom_saved in FRh. release_frame FRh PC q.
  apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

Lemma pcom_toobig_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ap lo : Z),
  a1 = Z_to_bv 64 0x1ad48 -> a2 = Z_to_bv 64 ap ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> 0 <= ap < 2^63 ->
  chk_ok m 0x1ad48 33 -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros E1 E2 ST LO LOLO SPH S16 AP0 CHK PCX MI.
  apply (pcom_fint_spec 0x1ad48 [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32] 117 32
           [98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10] ap lo);
    [ exact E1 | exact E2 | reflexivity | reflexivity | right; reflexivity | apply cstr_f_toobig; exact MI
    | unfold kHighShadowEnd in LOLO; cbn [length Z.of_nat]; lia | exact ST | exact LO | exact LOLO | exact SPH | exact S16 | exact AP0
    | exact CHK | exact PCX | exact MI ].
Qed.

Lemma pcom_emit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ap lo : Z),
  a1 = Z_to_bv 64 0x14f66 -> a2 = Z_to_bv 64 ap ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> 0 <= ap < 2^63 ->
  chk_ok m 0x14f66 4 -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros E1 E2 ST LO LOLO SPH S16 AP0 CHK PCX MI.
  apply (pcom_fint_spec 0x14f66 [] 100 10 [] ap lo);
    [ exact E1 | exact E2 | reflexivity | reflexivity | left; reflexivity | apply cstr_f_emit; exact MI
    | unfold kHighShadowEnd in LOLO; cbn [length Z.of_nat]; lia | exact ST | exact LO | exact LOLO | exact SPH | exact S16 | exact AP0
    | exact CHK | exact PCX | exact MI ].
Qed.

Definition L_USAGE1 : list Z := [117; 115; 97; 103; 101; 58; 32].
Definition L_USAGE2 : list Z := [73; 78; 80; 85; 84; 10].
Definition L_COPEN1 : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].
Definition L_RERR1 : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32].

Ltac fstr_inst A l1 nx l2 CSTR :=
  intros until lo; intros E1 E2 SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI;
  eapply (pcom_fstr_spec A l1 nx l2);
    [ exact E1 | exact E2 | reflexivity | reflexivity | apply CSTR; exact MI
    | unfold kHighShadowEnd in LOLO; cbn [length Z.of_nat L_USAGE1 L_USAGE2 L_COPEN1 L_RERR1]; lia
    | exact SLOT | exact QAP | exact APH | exact CSS | exact S0 | exact SSEP | exact SH | exact CHKS
    | exact ST | exact LO | exact LOLO | exact SPH | exact S16 | exact CHK | exact PCX | exact MI ].

Lemma pcom_usage_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
  a1 = Z_to_bv 64 0x162fa -> a2 = Z_to_bv 64 ap ->
  ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
  cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
  chk_ok m S (Z.of_nat (length str) + 1) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> chk_ok m 0x162fa 17 -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP. fstr_inst 0x162fa L_USAGE1 32 L_USAGE2 cstr_f_usage. Qed.

Lemma pcom_copen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
  a1 = Z_to_bv 64 0x1f488 -> a2 = Z_to_bv 64 ap ->
  ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
  cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
  chk_ok m S (Z.of_nat (length str) + 1) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> chk_ok m 0x1f488 21 -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP. fstr_inst 0x1f488 L_COPEN1 10 (@nil Z) cstr_f_copen. Qed.

Lemma pcom_rerr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
  a1 = Z_to_bv 64 0x1f49d -> a2 = Z_to_bv 64 ap ->
  ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
  cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
  chk_ok m S (Z.of_nat (length str) + 1) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> chk_ok m 0x1f49d 23 -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e190) fc None m (seg_rom bsegs)).
Proof using RIP. fstr_inst 0x1f49d L_RERR1 10 (@nil Z) cstr_f_rerr. Qed.
End WithRIP.
