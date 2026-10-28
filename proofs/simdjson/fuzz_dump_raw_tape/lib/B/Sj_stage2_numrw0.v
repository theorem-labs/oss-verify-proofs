(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_iface Sj_num_akit
  Sj_stage2_defs Sj_stage2_main Sj_stage2_world Sj_stage2_numw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma mcost_mono : forall a b, 0 <= a <= b -> mcost a <= mcost b.
Proof. intros a b H. unfold mcost. destruct (Z.leb_spec a 64512), (Z.leb_spec b 64512); lia. Qed.

Lemma intervals_apart : forall A n B k, 0 < n -> 0 < k -> (forall x, A <= x < A + n -> ~ (B <= x < B + k)) -> A + n <= B \/ B + k <= A.
Proof.
  intros A n B k Hn Hk H. destruct (Z_le_dec (A + n) B) as [L|L]; [left; exact L|]. right.
  destruct (Z_le_dec (B + k) A) as [L2|L2]; [exact L2|]. exfalso.
  destruct (Z_le_dec B A) as [L3|L3].
  - apply (H A ltac:(lia)). lia.
  - apply (H B ltac:(lia)). lia.
Qed.

Lemma u32arr_agree_nw : forall (m m' : mem) a ws, u32arr bsegs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> u32arr bsegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA. split.
  - apply (bytes_at_agree bsegs m m' a _ Hb). rewrite u32s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
  - exact (wr_at_agree_nw bsegs m m' a _ Hw HA).
Qed.
Lemma u8arr_agree_nw : forall (m m' : mem) A bs, u8arr bsegs m A bs ->
  agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m' -> u8arr bsegs m' A bs.
Proof.
  intros m m' A bs [HB HW] AG. split; [exact (bytes_at_agree bsegs m m' A bs HB AG) | exact (wr_at_agree_nw bsegs m m' A _ HW AG)].
Qed.

Lemma tape_img_agree_nw : forall E tws sbs (m m' : mem), tape_img E tws sbs m ->
  agree_on (fun x => e_TAPE E <= x < e_TAPE E + 8 * e_tcap E) m m' -> agree_on (fun x => e_SBUF E <= x < e_SBUF E + e_scap E) m m' ->
  tape_img E tws sbs m'.
Proof.
  intros E tws sbs m m' (T1 & T2 & T3 & T4 & S1 & S2 & SB) A1 A2.
  pose proof (Zle_0_nat (length tws)). pose proof (Zle_0_nat (length sbs)).
  split; [|split; [|split; [exact T3|split; [exact T4|split; [|split; [|exact SB]]]]]].
  - apply (bytes_at_agree bsegs m m' _ _ T1). eapply agree_sub; [exact A1|]. intros x Hx. cbv beta in *. rewrite twords_length in Hx. lia.
  - apply (bytes_at_agree bsegs m m' _ _ T2). eapply agree_sub; [exact A2|]. intros x Hx. cbv beta in *. rewrite zbytes_length in Hx. lia.
  - exact (stk_agree_nw bsegs m m' _ _ S1 A1).
  - exact (stk_agree_nw bsegs m m' _ _ S2 A2).
Qed.

Lemma MEMI_transport : forall (E0 : s2env) (mb m1 m' : mem) nxt sl sc fc fc',
  env_ok E0 -> Forall (fun c => csize c = 8%nat) sl -> length sl = 29%nat ->
  MEMI (env_at E0 mb) nxt sl sc fc m1 ->
  agree_on (s2_region E0) m1 m' -> mem_inv bsegs m' -> stk bsegs m' (e_lo E0) (e_spa E0) -> frm0 fc' ->
  MEMI (env_at E0 m') nxt sl sc fc' m'.
Proof.
  intros E0 mb m1 m' nxt sl sc fc fc' OK0 HCS HL HM AG MI' ST' F0.
  do 29 (destruct sl as [|? sl]; [discriminate HL|]). destruct sl; [|discriminate HL]. clear HL.
  repeat match goal with H : Forall _ (_ :: _) |- _ => let E8 := fresh "E8" in inversion H as [|? ? E8 H']; clear H; subst; rename H' into HCS' end.
  pose proof (ok_iwl _ OK0) as EK_iwl2. s2_env OK0.
  s2_open_mem HM. wE_norm. cbn [env_at e_spa e_sp e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA e_iws e_bs e_tcap e_scap e_j0 e_j256 e_lo] in *.
  Ltac reg_pick0 := unfold s2_region;
    first [ left; lia | right; left; lia | do 2 right; left; lia | do 3 right; left; lia | do 4 right; left; lia | do 5 right; left; lia
          | do 6 right; left; lia | do 7 right; left; lia | do 8 right; left; lia | do 9 right; lia ].
  lazymatch type of FR with rw_cells _ _ _ ?l =>
    assert (SZ : Z.of_nat (cells_size l) = 312) by (cbn [cells_size csize]; repeat match goal with H : csize _ = 8%nat |- _ => rewrite H; clear H end; reflexivity) end.
  apply (rw_cells_agree_nw bsegs m1 m') in FR; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite SZ in Hx; reg_pick0].
  apply (rw_cells_agree_nw bsegs m1 m') in SAV; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; reg_pick0].
  apply (stk_agree_nw bsegs m1 m') in GAP; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick0].
  apply (wr_at_agree_nw bsegs m1 m') in FFW; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick0].
  apply (rw_cells_agree_nw bsegs m1 m') in IMPL; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; reg_pick0].
  apply (rw_cells_agree_nw bsegs m1 m') in DOCC; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; reg_pick0].
  apply (u32arr_agree_nw m1 m') in IDXA; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick0].
  apply (bytes_at_agree bsegs m1 m') in BUFRO; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite PBL in Hx; reg_pick0].
  apply (wr_at_agree_nw bsegs m1 m') in TAPEW; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick0].
  apply (wr_at_agree_nw bsegs m1 m') in SBUFW; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick0].
  apply (u32arr_agree_nw m1 m') in OCA; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite OCL in Hx; reg_pick0].
  apply (u8arr_agree_nw m1 m') in IAA; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite IAL in Hx; reg_pick0].
  apply (tape_img_agree_nw _ _ _ m1 m') in TIMG; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; cbn [e_TAPE e_SBUF e_tcap e_scap s2_ghost env_at] in Hx; reg_pick0 | eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; cbn [e_TAPE e_SBUF e_tcap e_scap s2_ghost env_at] in Hx; reg_pick0].
  unfold MEMI. cbn [env_at e_spa e_sp e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA e_iws e_bs e_tcap e_scap e_j0 e_j256 e_lo e_m0].
  unfold fr_cells, saved_cells, impl_cells, doc_cells, s2_W.
  cbn [env_at e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
       e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0].
  split; [exact F0|]. split; [exact FR|]. split; [exact SAV|]. split; [exact GAP|]. split; [exact FFW|]. split; [exact IMPL|]. split; [exact DOCC|].
  split; [exact IDXA|]. split; [exact BUFRO|]. split; [exact TAPEW|]. split; [exact SBUFW|].
  split; [exists ocs; split; [exact OCA| split; [exact OCL| exact OCR]]|].
  split; [exists ias; split; [exact IAA| split; [exact IAL| exact IAR]]|].
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST'| exact TIMG].
Qed.

Lemma MEMI_transport_out : forall (E0 : s2env) (mb m1 m' : mem) nxt c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c272 c288 j304 v sc fc fc',
  env_ok E0 -> Forall (fun c => csize c = 8%nat) [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288] ->
  MEMI (env_at E0 mb) nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; CB 8 j304] sc fc m1 ->
  agree_on (fun x => s2_region E0 x /\ ~ (e_spa E0 + 304 <= x < e_spa E0 + 304 + 8)) m1 m' ->
  rw_cells bsegs m' (e_spa E0 + 304) [C8 v] -> mem_inv bsegs m' -> stk bsegs m' (e_lo E0) (e_spa E0) -> frm0 fc' ->
  MEMI (env_at E0 m') nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; C8 v] sc fc' m'.
Proof.
  intros E0 mb m1 m' nxt c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c272 c288 j304 v sc fc fc' OK0 HCS HM AG OUTC MI' ST' F0.
  repeat match goal with H : Forall _ (_ :: _) |- _ => let E8 := fresh "E8" in inversion H as [|? ? E8 H']; clear H; subst; rename H' into HCS' end.
  pose proof (ok_iwl _ OK0) as EK_iwl2. s2_env OK0.
  s2_open_mem HM. wE_norm. cbn [env_at e_spa e_sp e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA e_iws e_bs e_tcap e_scap e_j0 e_j256 e_lo] in *.
  lazymatch type of FR with rw_cells _ _ _ ?l => rewrite (app_removelast_last (CB 0 []) (l := l)) in FR by discriminate end.
  cbn [removelast last] in FR. apply rw_cells_app in FR. destruct FR as [FRa _].
  lazymatch type of FRa with rw_cells _ _ _ ?l =>
    assert (SZ : Z.of_nat (cells_size l) = 304) by (cbn [cells_size csize]; repeat match goal with H : csize _ = 8%nat |- _ => rewrite H; clear H end; reflexivity) end.
  Ltac reg_pick1 := split; [reg_pick0 | lia].
  apply (rw_cells_agree_nw bsegs m1 m') in FRa; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite SZ in Hx; reg_pick1].
  apply (rw_cells_agree_nw bsegs m1 m') in SAV; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; reg_pick1].
  apply (stk_agree_nw bsegs m1 m') in GAP; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick1].
  apply (wr_at_agree_nw bsegs m1 m') in FFW; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick1].
  apply (rw_cells_agree_nw bsegs m1 m') in IMPL; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; reg_pick1].
  apply (rw_cells_agree_nw bsegs m1 m') in DOCC; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; reg_pick1].
  apply (u32arr_agree_nw m1 m') in IDXA; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick1].
  apply (bytes_at_agree bsegs m1 m') in BUFRO; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite PBL in Hx; reg_pick1].
  apply (wr_at_agree_nw bsegs m1 m') in TAPEW; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick1].
  apply (wr_at_agree_nw bsegs m1 m') in SBUFW; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; reg_pick1].
  apply (u32arr_agree_nw m1 m') in OCA; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite OCL in Hx; reg_pick1].
  apply (u8arr_agree_nw m1 m') in IAA; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite IAL in Hx; reg_pick1].
  apply (tape_img_agree_nw _ _ _ m1 m') in TIMG; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; cbn [e_TAPE e_SBUF e_tcap e_scap s2_ghost env_at] in Hx; reg_pick1 | eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; cbn [e_TAPE e_SBUF e_tcap e_scap s2_ghost env_at] in Hx; reg_pick1].
  assert (FR' : rw_cells bsegs m' (e_spa E0)
                  ([c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200;
                    C8 (Z_to_bv 64 (e_THIS E0 + 16)); C8 (Z_to_bv 64 (e_THIS E0 + 8)); C8 (Z_to_bv 64 (SHA (e_THIS E0 + 16))); C8 (Z_to_bv 64 (SHA (e_THIS E0 + 8)));
                    C8 (Z_to_bv 64 (SHA (e_THIS E0 + 88))); C8 (Z_to_bv 64 (e_THIS E0 + 88)); C8 (Z_to_bv 64 (e_THIS E0)); C8 (Z_to_bv 64 (e_FF E0)); c272;
                    C8 (Z_to_bv 64 2147450880); c288; C8 (Z_to_bv 64 (e_FF E0))] ++ [C8 v])).
  { apply rw_cells_app. split; [exact FRa|]. rewrite SZ. exact OUTC. }
  unfold MEMI. unfold fr_cells, saved_cells, impl_cells, doc_cells, s2_W.
  cbn [env_at e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
       e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0].
  split; [exact F0|]. split; [exact FR'|]. split; [exact SAV|]. split; [exact GAP|]. split; [exact FFW|]. split; [exact IMPL|]. split; [exact DOCC|].
  split; [exact IDXA|]. split; [exact BUFRO|]. split; [exact TAPEW|]. split; [exact SBUFW|].
  split; [exists ocs; split; [exact OCA| split; [exact OCL| exact OCR]]|].
  split; [exists ias; split; [exact IAA| split; [exact IAL| exact IAR]]|].
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST'| exact TIMG].
Qed.

Section Apart.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma newchunk_apart : forall (Σ Σ1 : rts RT) (m1 : mem) p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> 0 < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ Σ1 m1 p n usp a ART1 LV FRS SP0 LU Hn Ha Hin.
  assert (INP : In (p, n) (rt_live RT Σ1)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INP) as (P0 & P1 & P2). rewrite SP0 in P1.
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW. rewrite SP0 in SPR, SPW.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). ul.
  - destruct H as (p2 & n2 & Hin2 & Hp2).
    pose proof (af_live_disj RT AF Σ1 m1 p n p2 n2 [] (rt_live RT Σ) ART1 LV Hin2). lia.
  - destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & FD). specialize (FD p n INP).
    assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia). lia.
  - destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). specialize (SL p n INP). lia.
Qed.
End Apart.
