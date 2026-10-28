(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1im X1ip X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.
Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.

Definition HFRAME : Z := 8832.

Notation oP := 32 (only parsing).      Notation oNBR := 16 (only parsing).   Notation oBREM := 24 (only parsing).
Notation oEXTRA := 40 (only parsing).  Notation oGFS := 48 (only parsing).   Notation oLOOK := 56 (only parsing).
Notation oRATE := 60 (only parsing).   Notation oSTEREO := 64 (only parsing). Notation oOS := 88 (only parsing).
Notation oOP := 496 (only parsing).    Notation oOG := 544 (only parsing).   Notation oOY := 576 (only parsing).
Notation oBITS := 608 (only parsing).  Notation oFSZ := 656 (only parsing).  Notation oOUT := 664 (only parsing).
Notation oCBK := 8664 (only parsing).  Notation oENH := 8708 (only parsing). Notation oSAV := 8712 (only parsing).

Definition A_CHUNK : Z := 0x1c1ec.
Definition A_PAGE1 : Z := 0x1c224.
Definition A_PAGEB : Z := 0x1c240.
Definition A_PKT0  : Z := 0x1c3b8.
Definition A_PKT   : Z := 0x1c3c4.
Definition A_DEC   : Z := 0x1c46c.
Definition A_PKTX  : Z := 0x1c6c8.
Definition A_PAGEN : Z := 0x1c710.
Definition A_CHUNKX : Z := 0x1c728.
Definition A_CLEAN : Z := 0x1c734.
Definition A_RET0  : Z := 0x1c790.

Lemma agree_of_cmod : forall W LB SP m m', cmod W LB SP m m' ->
agree_on rsegs (fun a => rclient_addr LB SP a /\ outside W a) m m'.
Proof. intros W LB SP m m' H a Ha [C O]. exact (H a Ha C O). Qed.

Lemma agree_of_pres_except : forall client X m m', pres_except rsegs client X m m' ->
agree_on rsegs (fun a => client a /\ ~ in_ivs X a) m m'.
Proof. intros client X m m' H a Ha [C NX]. exact (H a Ha C NX). Qed.

Lemma agree_of_rheap_pres : forall LB SP m m', rheap_pres LB SP m m' -> agree_on rsegs (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H a Ha C. exact (H a Ha C). Qed.

Lemma u8arr_agree : forall P m m' A bs,
agree_on rsegs P m m' -> u8arr rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr rsegs m' A bs.
Proof.
intros P m m' A bs AG [B W] HR. split; [eapply bytes_at_agree; eauto|]. eapply wr_at_agree; eauto.
Qed.
Lemma u8ro_agree : forall P m m' A bs,
agree_on rsegs P m m' -> u8ro rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8ro rsegs m' A bs.
Proof. intros P m m' A bs AG B HR. unfold u8ro in *. eapply bytes_at_agree; eauto. Qed.
Lemma u32arr_agree : forall P m m' A ws,
agree_on rsegs P m m' -> u32arr rsegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr rsegs m' A ws.
Proof.
intros P m m' A ws AG [B W] HR. split; [eapply bytes_at_agree; eauto; rewrite u32s_length; intros; apply HR; lia|]. eapply wr_at_agree; eauto.
Qed.
Lemma u64arr_agree : forall P m m' A ws,
agree_on rsegs P m m' -> u64arr rsegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr rsegs m' A ws.
Proof.
intros P m m' A ws AG [B W] HR. split; [eapply bytes_at_agree; eauto; rewrite u64s_length; intros; apply HR; lia|]. eapply wr_at_agree; eauto.
Qed.

Lemma pres_except_of_agree : forall (P client : Z -> Prop) X m m',
agree_on rsegs P m m' -> (forall a, 0 <= a < 2^64 -> client a -> ~ in_ivs X a -> P a) -> pres_except rsegs client X m m'.
Proof. intros P client X m m' AG H a Ha C NX. exact (AG a Ha (H a Ha C NX)). Qed.

Lemma ssp_cells_agree : forall P m m' c, agree_on rsegs P m m' ->
(forall a, (RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8) -> P a) -> ssp_cells m c -> ssp_cells m' c.
Proof.
intros P m m' c AG HP [G1 G2]. split.
- eapply rw_cells_agree; [exact AG| exact G1|]. intros a Ha. apply HP. unfold X1fl.got_ssp in Ha. cbn [cells_size csize Nat.add] in Ha. left. unfold RGOT_SSP. lia.
- eapply rw_cells_agree; [exact AG| exact G2|]. intros a Ha. apply HP. unfold X1fl.ssp_guard in Ha. cbn [cells_size csize Nat.add] in Ha. right. unfold RSSP_GUARD. lia.
Qed.

Lemma sync_rep_agree : forall P m m' A D (sy : sync_st bptr) bytes,
agree_on rsegs P m m' -> sync_rep m A D sy bytes ->
(forall a, A <= a < A + 32 -> P a) -> (forall a, D <= a < D + Z.of_nat (length bytes) -> P a) ->
sync_rep m' A D sy bytes.
Proof.
intros P m m' A D sy bytes AG sfH_; first [ sf_destruct 4%nat sfH_ as OBJ FOK DAT SEP | sf_fb; destruct sfH_ as (OBJ & FOK & DAT & SEP) ]; intros HA HD. split; [|split; [exact FOK| split; [|exact SEP]]].
- eapply rw_cells_agree; [exact AG| exact OBJ| exact HA].
- unfold sync_data in *. destruct (sy_data sy); [| exact DAT]. first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ].
split; [exact D1|]. split; [eapply u8arr_agree; [exact AG| exact ARR| exact HD]|]. auto.
Qed.

Lemma bits_rep_agree : forall P m m' A D (b : bits_st bptr),
agree_on rsegs P m m' -> bits_rep rsegs m A D b -> bits_ok b ->
(forall a, A <= a < A + 48 -> P a) -> (forall a, D <= a < D + sb_buf_size b -> P a) ->
bits_rep rsegs m' A D b.
Proof.
intros P m m' A D b AG ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE) OK HA HD.
split; [| split; [| exact SIDE]].
- exists rj. split; [exact Lrj|]. eapply rw_cells_agree; [exact AG| exact OBJ|]. rewrite bits_cells_size by exact Lrj. exact HA.
- exists bs. split; [| exact Hbs]. eapply u8arr_agree; [exact AG| exact ARR|].
assert (L : Z.of_nat (length bs) = sb_buf_size b). { unfold bits_ok in OK. rewrite Hbs, zlength_map_unsigned in OK. lia. }
rewrite L. exact HD.
Qed.

Lemma c8_junk4 : forall m A (w0 w1 w2 w3 : word),
rw_cells rsegs m A [C8 w0; C8 w1; C8 w2; C8 w3] ->
rw_cells rsegs m A [CB 8 (le8 w0); CB 8 (le8 w1); CB 8 (le8 w2); CB 8 (le8 w3)].
Proof. intros. eapply X0pw.rw_cells_recast; [exact H| cbn [cells_wf]; unfold cell_wf; rewrite !length_le8; tauto| reflexivity| reflexivity]. Qed.
Lemma c8_junk6 : forall m A (w0 w1 w2 w3 w4 w5 : word),
rw_cells rsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5] ->
rw_cells rsegs m A [CB 8 (le8 w0); CB 8 (le8 w1); CB 8 (le8 w2); CB 8 (le8 w3); CB 8 (le8 w4); CB 8 (le8 w5)].
Proof. intros. eapply X0pw.rw_cells_recast; [exact H| cbn [cells_wf]; unfold cell_wf; rewrite !length_le8; tauto| reflexivity| reflexivity]. Qed.

Record hcx := HCX {
x_sp : word;
x_ra : word; x_gp : word;
x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word;
x_s6 : word; x_s7 : word; x_s8 : word; x_s9 : word; x_s10 : word; x_s11 : word;
x_st0 : PState; x_m0 : mem;
x_LB0 : list block;
x_pb : bptr; x_P : Z; x_payload : list Z;
x_AB : Z; x_lo : Z }.
Notation usp c := (bv_unsigned (x_sp c)).
Notation hsp c := (bv_unsigned (x_sp c) + -8832).
Notation aLOW c := (bv_unsigned (x_sp c) + -8832).  Notation aSTEREO c := (bv_unsigned (x_sp c) + -8752).
Notation aOS c := (bv_unsigned (x_sp c) + -8728).   Notation aOP c := (bv_unsigned (x_sp c) + -8320).
Notation aOG c := (bv_unsigned (x_sp c) + -8272).   Notation aOY c := (bv_unsigned (x_sp c) + -8240).
Notation aBITS c := (bv_unsigned (x_sp c) + -8208). Notation aFSZ c := (bv_unsigned (x_sp c) + -8160).
Notation aOUT c := (bv_unsigned (x_sp c) + -8152).  Notation aCBK c := (bv_unsigned (x_sp c) + -152).
Notation aENH c := (bv_unsigned (x_sp c) + -108).   Notation aSAV c := (bv_unsigned (x_sp c) + -104).

Definition hcx_ok {RCEIL : RunCeiling} (c : hcx) : Prop :=
Forall (fun z => 0 <= z < 256) (x_payload c) /\ 0 < x_P c /\ x_P c mod 16 = 0 /\ zlength (x_payload c) <= 2^26 /\
((x_payload c <> [] /\ In (x_pb c, x_P c, zlength (x_payload c)) (x_LB0 c)) \/ (x_payload c = [] /\ x_P c = REMPTY)) /\
usp c <= x_AB c /\ x_AB c < 2^62 /\ alloc_ceiling <= x_lo c /\ x_lo c <= usp c - RFUZZ_STACK /\ usp c mod 16 = 0 /\
usp c < 2^64.

Record hax := HAX {
a_LB : list block;
a_D : Z; a_sybytes : list byte;
a_Bd : Z; a_L : Z; a_Gv : Z; a_nB : Z; a_nL : Z; a_nG : Z;
a_hdr : list byte; a_lws : list word; a_gws : list word; a_body : list byte;
a_Dc : Z;
a_S : Z; a_LBD : list block }.

Definition opt_blk (o : option bptr) (A n : Z) : list block := match o with Some p => [(p, A, n)] | None => [] end.
Definition owned (x : hax) (h : hstate bptr) : list block :=
(match h_st h with Some _ => a_LBD x | None => [] end)
++ [(sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))]
++ opt_blk (os_body_data (h_os h)) (a_Bd x) (a_nB x)
++ opt_blk (os_lacing_vals (h_os h)) (a_L x) (a_nL x)
++ opt_blk (os_granule_vals (h_os h)) (a_Gv x) (a_nG x)
++ opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h)).

Definition owned_pre (x : hax) (h : hstate bptr) : list block :=
(match h_st h with Some _ => a_LBD x | None => [] end)
++ [(sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))]
++ opt_blk (os_body_data (h_os h)) (a_Bd x) (a_nB x)
++ opt_blk (os_lacing_vals (h_os h)) (a_L x) (a_nL x)
++ opt_blk (os_granule_vals (h_os h)) (a_Gv x) (a_nG x).
Lemma owned_split : forall x h, owned x h = owned_pre x h ++ opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h)).
Proof. intros. unfold owned, owned_pre. rewrite <- !app_assoc. reflexivity. Qed.

Definition low_cells (c : hcx) (h : hstate bptr) (j16 : list byte) (cn cb : cell) (jsk lk : list byte) : list cell :=
[CB 16 j16; cb; cn; CB 16 jsk; C8 (wz (x_P c)); C8 (wz (h_granule_frame_size h)); C8 (wz (h_last_granule h));
CB 4 lk; C4 (wz (h_rate h))].
Definition lk_ok (h : hstate bptr) (lk : list byte) : Prop :=
h_st h <> None -> exists L, lk = le4 (wz L) /\ 40 <= L <= 1342177280.
Definition sav_cells (c : hcx) : list cell :=
[C8 (x_s11 c); C8 (x_s10 c); C8 (x_s9 c); C8 (x_s8 c); C8 (x_s7 c); C8 (x_s6 c); C8 (x_s5 c); C8 (x_s4 c);
C8 (x_s3 c); C8 (x_s2 c); C8 (x_s1 c); C8 (x_s0 c); C8 (x_ra c)].
Definition fsz_cells (h : hstate bptr) (pad : list byte) : list cell := [CB 4 pad; C4 (wz (h_frame_size h))].

Definition stream_rep {RCEIL : RunCeiling} (m : mem) (c : hcx) (x : hax) (h : hstate bptr) : Prop :=
let os := h_os h in
rw_cells rsegs m (aOS c) (stream_cells (a_Bd x) (a_L x) (a_Gv x) (a_hdr x) os) /\ length (a_hdr x) = 284%nat
/\ stream_fields_ok os /\ stream_inv os /\ body_inv os /\ lacing_vals_ok (os_lacing os) /\ granules_ok (os_granules os)
/\ u32arr rsegs m (a_L x) (a_lws x) /\ u64arr rsegs m (a_Gv x) (a_gws x) /\ u8arr rsegs m (a_Bd x) (a_body x)
/\ wpre (os_lacing os) (a_lws x)
/\ Z.of_nat (length (a_lws x)) = os_lacing_storage os /\ Z.of_nat (length (a_gws x)) = os_lacing_storage os
/\ Z.of_nat (length (a_body x)) = os_body_storage os
/\ firstn (length (os_body os)) (ubytes (a_body x)) = os_body os /\ (length (os_body os) <= length (a_body x))%nat
/\ a_nB x = os_body_storage os /\ a_nL x = 4 * os_lacing_storage os /\ a_nG x = 8 * os_lacing_storage os
/\ (os_body_data os = None <-> a_Bd x = 0) /\ (os_lacing_vals os = None <-> a_L x = 0) /\ (os_granule_vals os = None <-> a_Gv x = 0)
/\ (os_body_data os <> None -> rblock_range (a_Bd x) (a_nB x))
/\ (os_lacing_vals os <> None -> rblock_range (a_L x) (a_nL x))
/\ (os_granule_vals os <> None -> rblock_range (a_Gv x) (a_nG x))

/\ a_Bd x + Z.of_nat (length (a_body x)) <= alloc_ceiling
/\ a_L x + 4 * Z.of_nat (length (a_lws x)) <= alloc_ceiling
/\ a_Gv x + 8 * Z.of_nat (length (a_gws x)) <= alloc_ceiling

/\ (os_body_data os = None -> os_body_storage os = 0)
/\ (os_lacing_vals os = None -> os_lacing_storage os = 0)
/\ (os_granule_vals os = None -> os_lacing_storage os = 0)

/\ (os_body_data os <> None -> 16384 <= os_body_storage os)
/\ (os_lacing_vals os <> None -> 1024 <= os_lacing_storage os)

/\ ((os_body_data os <> None /\ os_lacing_vals os <> None /\ os_granule_vals os <> None) \/ os = stream_zero).

Definition stream_blks (x : hax) (h : hstate bptr) : list block :=
opt_blk (os_body_data (h_os h)) (a_Bd x) (a_nB x)
++ opt_blk (os_lacing_vals (h_os h)) (a_L x) (a_nL x)
++ opt_blk (os_granule_vals (h_os h)) (a_Gv x) (a_nG x).

Definition os_piece {RCEIL : RunCeiling} (m : mem) (c : hcx) (x : hax) (h : hstate bptr) : Prop :=
if h_stream_init h =? 0 then (exists osj, rw_cells rsegs m (aOS c) [CB 408 osj]) /\ h_os h = stream_zero
/\ a_Bd x = 0 /\ a_L x = 0 /\ a_Gv x = 0
else stream_rep m c x h.

Definition dec_piece {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(m : mem) (c : hcx) (x : hax) (h : hstate bptr) : Prop :=
match h_st h with
| None => a_S x = 0 /\ a_LBD x = []
| Some d => dec_rep (aSTEREO c) m (a_S x) d (a_LBD x) /\ 0 < a_S x < 2^63
/\ (forall b, In b (a_LBD x) -> rblock_range (blk_addr b) (blk_size b))
end.

Definition hsync_ok (sy : sync_st bptr) : Prop :=
sync_inv2 sy /\ 0 <= sy_storage sy /\ (sy_data sy = None -> sy_storage sy = 0).
Lemma hsync_init_ok : hsync_ok ogg_sync_init.
Proof. split; [apply ogg_sync_init_inv2|]. cbn. split; [lia|]. intros _. reflexivity. Qed.

Definition hpend (h : hstate bptr) : Z := sy_fill (h_oy h) - sy_returned (h_oy h).
Definition hconsumed (c : hcx) (h : hstate bptr) : Z := (zlength (x_payload c) - h_bytes_remaining h) - hpend h.
Definition hbudget (c : hcx) (h : hstate bptr) : Prop :=
0 <= hpend h /\ 0 <= hconsumed c h
/\ os_lacing_fill (h_os h) <= hconsumed c h /\ os_body_fill (h_os h) <= hconsumed c h
/\ os_lacing_storage (h_os h) <= 1568 + hconsumed c h /\ os_body_storage (h_os h) <= 17408 + 2 * hconsumed c h

/\ h_packet_count h <= 162 * hconsumed c h
/\ h_packet_count h + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * hconsumed c h.

Definition hpure {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) : Prop :=
hsync_ok (h_oy h) /\ bits_ok (h_bits h) /\ sb_owner (h_bits h) = 1
/\ (sy_data (h_oy h) <> None -> rblock_range (a_D x) (sy_storage (h_oy h)) /\ 4096 <= sy_storage (h_oy h))
/\ Z.of_nat (length (a_sybytes x)) = sy_storage (h_oy h)
/\ rblock_range (a_Dc x) (sb_buf_size (h_bits h)) /\ 2000 <= sb_buf_size (h_bits h)
/\ 0 <= h_frame_size h <= 640 /\ h_granule_frame_size h = h_frame_size h
/\ 1 <= h_nframes h <= 10 /\ -2^31 <= h_channels h < 2^31 /\ -2^31 <= h_rate h < 2^31
/\ -2^31 <= h_extra_headers h < 2^31 - 1 /\ -2^31 <= h_speex_serialno h < 2^31
/\ 0 <= h_packet_count h < 2^31 - 1 /\ -2^63 <= h_last_granule h < 2^63
/\ (h_stream_init h = 0 \/ h_stream_init h = 1) /\ (h_eos h = 0 \/ h_eos h = 1)
/\ 0 <= h_bytes_remaining h <= zlength (x_payload c) /\ zlength (x_payload c) <= MAX_FUZZ_SIZE
/\ match h_st h with Some _ => h_packet_count h <> 0 | None => h_packet_count h = 0 end

/\ hbudget c h.

Definition hglob {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (st : PState) (m : mem) : Prop :=
RHEAP st (a_LB x) m /\ Permutation (a_LB x) (owned x h ++ x_LB0 c)
/\ bytes_at rsegs m (x_P c) (to_bytes (x_payload c))
/\ rtables_pristine m /\ stderr_wfile m
/\ (exists errv : word, rw_cells rsegs m RERRNO [C4 errv])
/\ rauxv_ok m (x_AB c) /\ mem_inv rsegs m /\ stk rsegs m (x_lo c) (hsp c)
/\ pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m
/\ ps_so st = ps_so (x_st0 c).

Definition hrep {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (x : hax) (h : hstate bptr) (st : PState) (m : mem) (cn cb : cell) : Prop :=
(exists j16 jsk lk, rw_cells rsegs m (aLOW c) (low_cells c h j16 cn cb jsk lk) /\ lk_ok h lk) /\ csize cn = 8%nat /\ csize cb = 8%nat
/\ (exists stb, rw_cells rsegs m (aSTEREO c) [CB 24 stb])
/\ os_piece m c x h
/\ (exists opj, rw_cells rsegs m (aOP c) [CB 48 opj])
/\ (exists ogj, rw_cells rsegs m (aOG c) [CB 32 ogj])
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h)
/\ (exists pad, rw_cells rsegs m (aFSZ c) (fsz_cells h pad))
/\ (exists outb, u8arr rsegs m (aOUT c) outb /\ Z.of_nat (length outb) = 8000)
/\ (exists hij, rw_cells rsegs m (aCBK c) [CB 48 hij])
/\ rw_cells rsegs m (aSAV c) (sav_cells c)
/\ dec_piece dec_rep m c x h
/\ hglob c x h st m
/\ hpure c x h.

Definition HFIN {RCEIL : RunCeiling} (c : hcx) (st : PState) (ms : machine_state) : Prop :=
harness_post (x_ra c) (x_sp c) (x_gp c) (wz RATP) (x_s0 c) (x_s1 c) (x_s2 c) (x_s3 c) (x_s4 c) (x_s5 c)
(x_s6 c) (x_s7 c) (x_s8 c) (x_s9 c) (x_s10 c) (x_s11 c) (x_st0 c) (x_LB0 c) (x_AB c) (x_lo c) (x_m0 c) 0 st ms.

Definition hregs (c : hcx) (h : hstate bptr) (S : Z) (s0 s1 s3 s5 s8 s10 : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(wz S) s3 (wz (h_extra_headers h)) s5 (wz (h_eos h)) (wz (h_packet_count h)) s8 (wz (h_nframes h)) s10
(wz (h_channels h)) t3 t4 t5 t6.

Definition CUTC {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (jn jb : list byte) (s0w s3w s8w : word),
ms = MS (hregs c h (a_S x) s0w (wz (h_bytes_remaining h)) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz A_CHUNK) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb).

Definition low_ok (h : hstate bptr) (nbr brem0 : Z) : Prop :=
brem0 - nbr = h_bytes_remaining h /\ 0 <= nbr <= 200 /\ nbr <= brem0 <= 4096.

Definition PG1 {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (jb : list byte) (nbr brem0 : Z) (s3w s8w : word),
ms = MS (hregs c h (a_S x) (wz nbr) (wz brem0) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz A_PAGE1) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m (C8 (wz nbr)) (CB 8 jb) /\ low_ok h nbr brem0.

Definition PGN {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (s0w s3w s5w s8w : word),
ms = MS (hregs c h (a_S x) s0w (wz brem0) s3w s5w s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz A_PAGEN) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1
/\ hrep dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) /\ low_ok h nbr brem0.

Definition PGX {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (jb : list byte) (nbr brem0 : Z) (s0w s3w s8w : word),
ms = MS (hregs c h (a_S x) s0w (wz brem0) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz A_CHUNKX) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m (C8 (wz nbr)) (CB 8 jb) /\ low_ok h nbr brem0.

Definition PGPOST {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop) (c : hcx) (h0 : hstate bptr)
(o : outcome bptr) (st : PState) (ms : machine_state) : Prop :=
match o with Cont h => PGX dec_rep c h st ms /\ h_bytes_remaining h = h_bytes_remaining h0 | Returned => HFIN c st ms end.

Definition CLN {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 q8 q9 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (cn cb : cell),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 q8 q9
(wz (a_S x)) (wz (aBITS c)) (wz (h_stream_init h)) (wz (aOS c)) (wz (aOY c)) a5 a6 a7
q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz 0x1c78c) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m cn cb.

Lemma rw_cells_cut : forall m A cs1 cs2 A2,
rw_cells rsegs m A (cs1 ++ cs2) -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m A2 cs2.
Proof. intros m A cs1 cs2 A2 H ->. apply rw_cells_app. exact H. Qed.

Lemma stk_carve_u8 : forall m lo hi n,
stk rsegs m lo hi -> 0 <= n -> lo <= hi - n ->
stk rsegs m lo (hi - n) /\ exists bs, u8arr rsegs m (hi - n) bs /\ Z.of_nat (length bs) = n.
Proof.
intros m lo hi n ST Hn Hle. pose proof ST as (S1 & S2 & S3).
destruct (stk_split rsegs m lo (hi - n) hi ST ltac:(lia)) as [SL SH]. split; [exact SL|].
destruct (stk_bytes rsegs m (hi - n) hi SH ltac:(lia)) as (bs & L & B). exists bs.
assert (LZ : Z.of_nat (length bs) = n) by (rewrite L, Z2Nat.id; lia).
split; [| exact LZ]. split; [exact B|]. split; [lia|]. split; [lia|]. intros i Hi. apply S3. lia.
Qed.

Lemma stk_carve_cb : forall m lo hi (k : nat),
stk rsegs m lo hi -> lo <= hi - Z.of_nat k ->
stk rsegs m lo (hi - Z.of_nat k) /\ exists bs, rw_cells rsegs m (hi - Z.of_nat k) [CB k bs].
Proof. intros m lo hi k ST Hle. exact (stk_carve rsegs m lo hi k ST Hle). Qed.

Lemma bytes_at_app3 : forall m A (a b d : list byte) B D,
bytes_at rsegs m A a -> bytes_at rsegs m B b -> bytes_at rsegs m D d ->
B = A + Z.of_nat (length a) -> D = B + Z.of_nat (length b) ->
bytes_at rsegs m A (a ++ b ++ d).
Proof.
intros m A a b d B D Ha Hb Hd -> ->. apply bytes_at_app. split; [exact Ha|]. apply bytes_at_app. split; [exact Hb|].
rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite Nat2Z.inj_add, Z.add_assoc. exact Hd.
Qed.

Lemma wr_at_app3 : forall m A na nb nd,
0 <= na -> 0 <= nb -> 0 <= nd ->
wr_at rsegs m A na -> wr_at rsegs m (A + na) nb -> wr_at rsegs m (A + na + nb) nd -> wr_at rsegs m A (na + nb + nd).
Proof.
intros m A na nb nd Ha Hb Hd Wa Wb Wd. apply wr_at_app; [lia| lia|]. split; [| replace (A + (na + nb)) with (A + na + nb) by lia; exact Wd].
apply wr_at_app; [lia| lia|]. split; assumption.
Qed.

Lemma out_merge : forall m A B D (ja : list byte) (w : word) (jb : list byte),
u8arr rsegs m A ja -> Z.of_nat (length ja) = 2024 ->
rw_cells rsegs m B [C8 w] ->
u8arr rsegs m D jb -> Z.of_nat (length jb) = 5968 ->
B = A + 2024 -> D = A + 2032 ->
exists outb, u8arr rsegs m A outb /\ Z.of_nat (length outb) = 8000.
Proof.
intros m A B D ja w jb [Ba Wa] La [[_ Bw] Ww] [Bb Wb] Lb -> ->.
cbn [cells_bytes cbytes app] in Bw. rewrite app_nil_r in Bw. cbn [cells_size csize Nat.add] in Ww. change (Z.of_nat 8) with 8 in Ww.
exists (ja ++ le8 w ++ jb).
assert (L : Z.of_nat (length (ja ++ le8 w ++ jb)) = 8000) by (rewrite !app_length, length_le8; lia).
split; [| exact L]. split.
- eapply bytes_at_app3; [exact Ba| exact Bw| exact Bb| lia| rewrite length_le8; lia].
- rewrite L. replace 8000 with (2024 + 8 + 5968) by reflexivity.
apply wr_at_app3; try lia; [rewrite <- La; exact Wa| exact Ww| replace (A + 2024 + 8) with (A + 2032) by lia; rewrite <- Lb; exact Wb].
Qed.

Lemma land64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Tactic Notation "callx" tactic3(t) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ t | post_call segs m ]
end.

Lemma hclient_mono : forall (c : hcx) LBc a,
(forall b, In b (x_LB0 c) -> In b LBc) -> rclient_addr (x_LB0 c) (usp c) a -> rclient_addr LBc (hsp c) a.
Proof.
intros c LBc a HL [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma hclient_not_frame {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) st LB m a,
hcx_ok c -> RHEAP st LB m -> (forall b, In b (x_LB0 c) -> In b LB) ->
rclient_addr (x_LB0 c) (usp c) a -> a < x_lo c \/ usp c <= a.
Proof.
intros RBR c st LB m a CX HP HL [H|[H|(b & Hb & Hr)]].
- right; exact H.
- left. first [ sf_destruct 9%nat CX as _ _ _ _ _ _ _ CEIL _ | sf_fb; destruct CX as (_ & _ & _ & _ & _ & _ & _ & CEIL & _) ]. unfold alloc_ceiling in CEIL. lia.
- left. pose proof (RBR _ _ _ b HP (HL b Hb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ].
first [ sf_destruct 9%nat CX as _ _ _ _ _ _ _ CEIL _ | sf_fb; destruct CX as (_ & _ & _ & _ & _ & _ & _ & CEIL & _) ]. lia.
Qed.

Lemma pres_except_step {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) st LB m0 m m' (Pc : Z -> Prop),
hcx_ok c -> RHEAP st LB m -> (forall b, In b (x_LB0 c) -> In b LB) ->
pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X m0 m ->
agree_on rsegs Pc m m' ->
(forall a, rclient_addr (x_LB0 c) (usp c) a -> a < x_lo c \/ usp c <= a -> ~ in_ivs rharness_X a -> Pc a) ->
pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X m0 m'.
Proof.
intros RBR c st LB m0 m m' Pc CX HP HL PE AG H.
eapply pres_except_trans; [exact PE|]. eapply pres_except_of_agree; [exact AG|].
intros a Ha Hc Hx. apply H; [exact Hc| | exact Hx]. eapply hclient_not_frame; eauto.
Qed.

Lemma pres_except_frame {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) st LB m0 m m' W,
hcx_ok c -> RHEAP st LB m -> (forall b, In b (x_LB0 c) -> In b LB) ->
pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X m0 m ->
agree_on rsegs (fun a => outside W a) m m' ->
Forall (fun iv => x_lo c <= fst iv /\ snd iv <= usp c) W ->
pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X m0 m'.
Proof.
intros RBR c st LB m0 m m' W CX HP HL PE AG HW.
eapply pres_except_trans; [exact PE|]. eapply pres_except_of_agree; [exact AG|].
intros a Ha Hc Hx. cbn beta. pose proof (hclient_not_frame RBR c st LB m a CX HP HL Hc) as D.
clear -D HW. induction HW as [|[lo1 hi1] W HH HW IH]; cbn; [exact I|]. cbn in HH. split; [lia| exact IH].
Qed.

Lemma pay_keep {RCEIL : RunCeiling} : forall (c : hcx) P m m',
hcx_ok c -> agree_on rsegs P m m' -> bytes_at rsegs m (x_P c) (to_bytes (x_payload c)) ->
(x_payload c <> [] -> In (x_pb c, x_P c, zlength (x_payload c)) (x_LB0 c) ->
forall a, x_P c <= a < x_P c + zlength (x_payload c) -> P a) ->
bytes_at rsegs m' (x_P c) (to_bytes (x_payload c)).
Proof.
intros c P m m' CX AG PAY H. first [ sf_destruct 6%nat CX as _ _ _ _ PIN _ | sf_fb; destruct CX as (_ & _ & _ & _ & PIN & _) ].
eapply bytes_at_agree; [exact AG| exact PAY|]. rewrite to_bytes_length. intros a Ha.
destruct PIN as [[NE IN]|[E _]]; [apply (H NE IN); unfold zlength; lia|]. rewrite E in Ha. cbn in Ha. lia.
Qed.

Ltac xport AG side :=
lazymatch type of AG with
| agree_on _ ?P ?m ?m' =>
repeat match goal with
| H : bytes_at _ m (x_P ?c) (to_bytes (x_payload ?c)), CX : hcx_ok ?c |- _ =>
first [ apply (fun X => pay_keep c P m m' CX AG X) in H; [| intros ?NE ?IN; side]
| idtac "xport: dropping" H; clear H ]
| H : rw_cells _ m ?A ?cs |- _ =>
first [ apply (rw_cells_agree rsegs P m m' A cs AG) in H; [| cbn [cells_size csize Nat.add Nat.mul]; simpl_sizes; side]
| idtac "xport: dropping" H; clear H ]
| H : bytes_at _ m ?A ?bs |- _ =>
first [ apply (bytes_at_agree rsegs P m m' A bs AG) in H; [| simpl_sizes; side]
| idtac "xport: dropping" H; clear H ]
| H : u8arr _ m ?A ?bs |- _ =>
first [ apply (u8arr_agree P m m' A bs AG) in H; [| simpl_sizes; simpl_arr_sizes; side]
| idtac "xport: dropping" H; clear H ]
| H : u8ro _ m ?A ?bs |- _ =>
first [ apply (u8ro_agree P m m' A bs AG) in H; [| simpl_sizes; simpl_arr_sizes; side]
| idtac "xport: dropping" H; clear H ]
| H : u32arr _ m ?A ?ws |- _ =>
first [ apply (u32arr_agree P m m' A ws AG) in H; [| simpl_sizes; simpl_arr_sizes; side]
| idtac "xport: dropping" H; clear H ]
| H : u64arr _ m ?A ?ws |- _ =>
first [ apply (u64arr_agree P m m' A ws AG) in H; [| simpl_sizes; simpl_arr_sizes; side]
| idtac "xport: dropping" H; clear H ]
| H : wr_at _ m ?A ?n |- _ =>
first [ apply (wr_at_agree rsegs P m m' A n AG) in H; [| side] | idtac "xport: dropping" H; clear H ]
| H : sync_rep m ?A ?D ?sy ?bytes |- _ =>
first [ apply (sync_rep_agree P m m' A D sy bytes AG) in H; [| side| side] | idtac "xport: dropping" H; clear H ]
| H : bits_rep _ m ?A ?D ?b, OK : bits_ok ?b |- _ =>
first [ apply (fun X => bits_rep_agree P m m' A D b AG X OK) in H; [| side| side] | idtac "xport: dropping" H; clear H ]
| H : rtables_pristine m |- _ =>
first [ apply (rtables_pristine_agree P m m' AG) in H; [| side] | idtac "xport: dropping" H; clear H ]
| H : stderr_wfile m |- _ =>
first [ apply (stderr_wfile_agree P m m' AG) in H; [| side] | idtac "xport: dropping" H; clear H ]
| H : ssp_cells m ?c |- _ =>
first [ apply (ssp_cells_agree P m m' c AG) in H; [| side] | idtac "xport: dropping" H; clear H ]
end
end.

Ltac hlia := first [ lia | unfold rblock_range, RERRNO, RTABLES_LO, RTABLES_HI, RAUXV_CELL, REMPTY, RGOT_SSP, RSSP_GUARD, alloc_ceiling in *; lia ].
Ltac side_conj :=
lazymatch goal with
| |- _ /\ _ => split; side_conj
| |- outside _ _ => cbn [outside fst snd]; hlia
| |- ~ in_ivs _ _ => cbn [in_ivs fst snd]; hlia
| |- rclient_addr _ _ _ => unfold rclient_addr;
first [ left; hlia
| right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; hlia
| right; right; eexists; split; [ solve [eauto 12 using in_eq, in_cons] | cbn [blk_addr blk_size fst snd]; hlia ] ]
| |- stderr_addr _ -> _ => unfold stderr_addr; intros ?; side_conj
| |- _ => first [ hlia | assumption ]
end.
Ltac side1 :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn beta; cbn [cells_size csize Nat.add Nat.mul length] in Ha; fold_of_nat_lits_in Ha;
rewrite ?Z2Nat.id in Ha by lia; try unfold stderr_addr in Ha; side_conj.

Definition in_frame (c : hcx) (W : list (Z * Z)) : Prop :=
Forall (fun iv => hsp c <= fst iv /\ snd iv <= usp c) W.

Lemma hglob_frame {RCEIL : RunCeiling} : rheap_frame_stmt -> rheap_block_range_stmt ->
forall (c : hcx) x h st mb m W,
hcx_ok c -> hglob c x h st mb ->
munch W mb m -> wmono rsegs mb m -> in_frame c W ->
mem_inv rsegs m -> stk rsegs m (x_lo c) (hsp c) ->
hglob c x h st m.
Proof.
intros RHF RBR c x h st mb m W CX sfH_; first [ sf_destruct 11%nat sfH_ as HP PERM PAY TP SEW [errv ERR] AUX _ _ PE SO | sf_fb; destruct sfH_ as (HP & PERM & PAY & TP & SEW & [errv ERR] & AUX & _ & _ & PE & SO) ]; intros MU WM FW MI ST. unfold in_frame in FW.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ]. unfold RFUZZ_STACK in LO.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (HL : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (OUTF : forall a, (a < x_lo c \/ usp c <= a) -> outside W a).
{ intros a Ha. clear -Ha FW LO. induction FW as [|[lo1 hi1] W' HH FW IH]; cbn; [exact I|]. cbn in HH. split; [lia| exact IH]. }
split. { eapply RHF; [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros [lo1 hi1] HH. left. cbn in *. lia. }
split; [exact PERM|].
split. { eapply bytes_at_agree; [exact AG| exact PAY|]. intros a Ha. apply OUTF.
pose proof (bytes_at_bound _ _ _ _ PAY) as PB. rewrite to_bytes_length in PB, Ha.
destruct PIN as [[NE IN]|[E EP]].
- left. pose proof (RBR _ _ _ _ HP (HL _ IN)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. unfold zlength in *. lia.
- left. rewrite EP in Ha. rewrite E in Ha. cbn in Ha. unfold REMPTY in *. lia. }
split. { eapply rtables_pristine_agree; [exact AG| | exact TP]. intros a Ha. apply OUTF. left. unfold RTABLES_HI in Ha. lia. }
split. { eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. apply OUTF. left. unfold stderr_addr in Ha. lia. }
split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply OUTF. left. cbn in Ha. unfold RERRNO in Ha. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros [lo1 hi1] HH. cbn in *. unfold RAUXV_CELL. lia. }
split; [exact MI|]. split; [exact ST|].
split. { eapply (pres_except_frame RBR c st (a_LB x)); [exact CX| exact HP| exact HL| exact PE| exact AG|].
eapply Forall_impl; [| exact FW]. intros [lo1 hi1] HH. cbn in *. lia. }
exact SO.
Qed.

Lemma pay_range {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) st LB m,
hcx_ok c -> RHEAP st LB m -> (forall b, In b (x_LB0 c) -> In b LB) ->
x_P c + zlength (x_payload c) <= alloc_ceiling \/ zlength (x_payload c) = 0.
Proof.
intros RBR c st LB m CX HP HL. first [ sf_destruct 6%nat CX as _ _ _ _ PIN _ | sf_fb; destruct CX as (_ & _ & _ & _ & PIN & _) ].
destruct PIN as [[NE IN]|[E _]].
- left. pose proof (RBR _ _ _ _ HP (HL _ IN)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. exact B4.
- right. rewrite E. reflexivity.
Qed.

Lemma bits_init_leaf : forall (s s' : PState) (b : bits_st bptr),
in_leaves (speex_bits_init raw_calloc s) (Ok (Some b, s')) ->
sb_owner b = 1 /\ sb_buf_size b = 2000 /\ sb_nbBits b = 0 /\ sb_charPtr b = 0 /\ sb_bitPtr b = 0 /\ sb_overflow b = 0.
Proof.
intros s s' b H. unfold speex_bits_init in H. apply in_leaves_mbind in H. first [ rename H into sfR_; sf_destruct 4%nat sfR_ as r s1 _ H | sf_fb; destruct H as (r & s1 & _ & H) ].
destruct r as [p|]; apply in_leaves_mret in H; inversion H; subst; cbn; repeat split; reflexivity.
Qed.

Lemma sync_buffer_leaf : forall (sy sy' : sync_st bptr) (size : Z) (s s' : PState) (res : option (bptr * Z)),
0 <= size -> hsync_ok sy ->
in_leaves (ogg_sync_buffer raw_malloc raw_realloc raw_free sy size s) (Ok ((res, sy'), s')) ->
hsync_ok sy' /\
((res = None /\ sy' = ogg_sync_init) \/
(sy_returned sy' = 0 /\ sy_fill sy' = sy_fill sy - sy_returned sy /\
sy_unsynced sy' = sy_unsynced sy /\ sy_headerbytes sy' = sy_headerbytes sy /\ sy_bodybytes sy' = sy_bodybytes sy /\
match res with
| Some (q, off) => off = sy_fill sy' /\ sy_data sy' = Some q /\ sy_fill sy' + size <= sy_storage sy' /\
((sy_data sy' = sy_data sy /\ sy_storage sy' = sy_storage sy) \/ sy_storage sy' = size + sy_fill sy' + 4096)
| None => size = 0 /\ sy_data sy' = sy_data sy /\ sy_storage sy' = sy_storage sy
end)).
Proof.
intros sy sy' size s s' res Hsz (Hinv & Hst & Hnul) H. pose proof Hinv as [[R1 R2] _].
unfold ogg_sync_buffer in H.
destruct (ogg_sync_check sy) eqn:Hck. { unfold ogg_sync_check in Hck. apply Z.ltb_lt in Hck. lia. }
set (sy1 := if negb (sy_returned sy =? 0) then _ else sy) in H.
assert (E1 : sync_inv2 sy1 /\ sy_data sy1 = sy_data sy /\ sy_fill sy1 = sy_fill sy - sy_returned sy /\ sy_storage sy1 = sy_storage sy /\
sy_returned sy1 = 0 /\
sy_unsynced sy1 = sy_unsynced sy /\ sy_headerbytes sy1 = sy_headerbytes sy /\ sy_bodybytes sy1 = sy_bodybytes sy).
{ subst sy1. destruct (Z.eqb_spec (sy_returned sy) 0) as [Ez|Ez]; cbn [negb].
- split; [exact Hinv|]. rewrite Ez. rewrite Z.sub_0_r. repeat split; auto.
- pose proof (sync_compact_inv2 sy Hinv) as C. cbn in C. split; [exact C|]. repeat split; auto. }
first [ sf_destruct 8%nat E1 as I1 Ed Ef Es Er Eu Eh Ebo | sf_fb; destruct E1 as (I1 & Ed & Ef & Es & Er & Eu & Eh & Ebo) ].
assert (OK1 : hsync_ok sy1). { split; [exact I1|]. rewrite Es, Ed. split; [exact Hst| exact Hnul]. }
assert (CLR : forall s1 : PState, in_leaves (mbind (ogg_sync_clear raw_free sy1) (fun sy'0 => mret (@None (bptr * Z), sy'0)) s1) (Ok ((res, sy'), s')) ->
hsync_ok sy' /\ (res = None /\ sy' = ogg_sync_init)).
{ intros s1 HL. apply in_leaves_mbind in HL. first [ sf_destruct 4%nat HL as a s2 HA HB | sf_fb; destruct HL as (a & s2 & HA & HB) ]. apply in_leaves_mret in HB. inversion HB; subst.
unfold ogg_sync_clear in HA. destruct (sy_data sy1).
- apply in_leaves_mbind in HA. first [ sf_destruct 4%nat HA as u s3 _ HC | sf_fb; destruct HA as (u & s3 & _ & HC) ]. apply in_leaves_mret in HC. inversion HC; subst. split; [apply hsync_init_ok| auto].
- apply in_leaves_mret in HA. inversion HA; subst. split; [apply hsync_init_ok| auto]. }
destruct (sy_storage sy1 - sy_fill sy1 <? size) eqn:Hgrow.
- destruct (X1qz.INT_MAX - 4096 - sy_fill sy1 <? size) eqn:Hbig.
+ destruct (CLR _ H) as [A B]. split; [exact A| left; exact B].
+ apply in_leaves_mbind in H. first [ rename H into sfR_; sf_destruct 4%nat sfR_ as ret s2 _ H | sf_fb; destruct H as (ret & s2 & _ & H) ].
destruct ret as [q|].
* apply in_leaves_mret in H. inversion H; subst. cbn. split.
{ split; [apply sync_inv2_set_block; exact I1|]. cbn. split; [lia| intros; discriminate]. }
right. rewrite Er, Ef, Eu, Eh, Ebo. do 7 (split; [reflexivity|]). split; [lia|]. right. lia.
* destruct (CLR _ H) as [A B]. split; [exact A| left; exact B].
- apply in_leaves_mret in H. inversion H; subst. apply Z.ltb_ge in Hgrow.
split; [exact OK1|]. right. rewrite Er, Ef, Eu, Eh, Ebo. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
destruct (sy_data sy1) as [p|] eqn:Edd.
+ rewrite <- Ef. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. left. split; [congruence| exact Es].
+ assert (Hz : sy_storage sy = 0) by (apply Hnul; congruence). repeat split; try lia; congruence.
Qed.

Lemma u8arr_window : forall m D bs i n,
u8arr rsegs m D bs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length bs) ->
u8arr rsegs m D (firstn (Z.to_nat i) bs)
/\ rw_cells rsegs m (D + i) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))]
/\ u8arr rsegs m (D + i + n) (skipn (Z.to_nat (i + n)) bs).
Proof.
intros m D bs i n [B W] Hi Hn Hin.
rewrite <- (firstn_skipn (Z.to_nat i) bs) in B. apply bytes_at_app in B. destruct B as [B1 B23].
rewrite firstn_length_le in B23 by lia. rewrite Z2Nat.id in B23 by lia.
rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) bs)) in B23. apply bytes_at_app in B23. destruct B23 as [B2 B3].
rewrite firstn_length_le in B3 by (rewrite skipn_length; lia). rewrite Z2Nat.id in B3 by lia.
rewrite skipn_skipn in B3. replace (Z.to_nat n + Z.to_nat i)%nat with (Z.to_nat (i + n)) in B3 by lia.
pose proof W as (W0 & W1 & Wi).
split; [| split].
- split; [exact B1|]. rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk. apply Wi. lia.
- split; [split|].
+ cbn. rewrite firstn_length_le by (rewrite skipn_length; lia). split; [reflexivity| exact I].
+ cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B2.
+ cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + k) with (D + (i + k)) by lia. apply Wi. lia.
- split; [exact B3|]. rewrite skipn_length. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + n + k) with (D + (i + n + k)) by lia. apply Wi. lia.
Qed.

Lemma u8arr_unwindow : forall m D (a : list byte) n (mid : list byte) (b : list byte) i,
u8arr rsegs m D a -> Z.of_nat (length a) = i ->
rw_cells rsegs m (D + i) [CB (Z.to_nat n) mid] -> 0 <= n ->
u8arr rsegs m (D + i + n) b ->
u8arr rsegs m D (a ++ mid ++ b) /\ Z.of_nat (length (a ++ mid ++ b)) = i + n + Z.of_nat (length b).
Proof.
intros m D a n mid b i [Ba Wa] La [[Hwf Bm] Wm] Hn [Bb Wb].
cbn in Hwf. destruct Hwf as [Lm _]. cbn [cells_bytes cbytes app] in Bm. rewrite app_nil_r in Bm.
cbn [cells_size csize Nat.add] in Wm. rewrite Nat.add_0_r, Z2Nat.id in Wm by lia.
assert (L : Z.of_nat (length (a ++ mid ++ b)) = i + n + Z.of_nat (length b)) by (rewrite !app_length; lia).
split; [| exact L]. split.
- eapply bytes_at_app3; [exact Ba| exact Bm| exact Bb| lia| lia].
- rewrite L. apply wr_at_app3; try lia; [rewrite <- La; exact Wa| exact Wm| exact Wb].
Qed.

Lemma stream_rep_agree {RCEIL : RunCeiling} : forall P m m' c x h,
agree_on rsegs P m m' -> stream_rep m c x h ->
(forall a, aOS c <= a < aOS c + 408 -> P a) -> (forall a, a < alloc_ceiling -> P a) ->
stream_rep m' c x h.
Proof.
intros P m m' c x h AG SR HA HB.
first [ sf_destruct 11%nat SR as OS LH F1 F2 F3 F4 F5 UL UG UB REST | sf_fb; destruct SR as (OS & LH & F1 & F2 & F3 & F4 & F5 & UL & UG & UB & REST) ].
pose proof REST as sfP_; first [ sf_destruct 19%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 C2 C3 | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & C3) ].
split. { eapply rw_cells_agree; [exact AG| exact OS|]. rewrite stream_cells_size by exact LH. exact HA. }
split; [exact LH|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
split. { eapply u32arr_agree; [exact AG| exact UL|]. intros a Ha. apply HB. lia. }
split. { eapply u64arr_agree; [exact AG| exact UG|]. intros a Ha. apply HB. lia. }
split. { eapply u8arr_agree; [exact AG| exact UB|]. intros a Ha. apply HB. lia. }
exact REST.
Qed.

Lemma os_piece_agree {RCEIL : RunCeiling} : forall P m m' c x h,
agree_on rsegs P m m' -> os_piece m c x h ->
(forall a, aOS c <= a < aOS c + 408 -> P a) -> (forall a, a < alloc_ceiling -> P a) ->
os_piece m' c x h.
Proof.
intros P m m' c x h AG OSP HA HB. unfold os_piece in *. destruct (h_stream_init h =? 0).
- destruct OSP as ([osj OS] & R). split; [| exact R]. exists osj. eapply rw_cells_agree; [exact AG| exact OS|]. cbn. intros; apply HA; lia.
- eapply stream_rep_agree; eauto.
Qed.

Lemma dec_piece_agree {RCEIL : RunCeiling} : forall dec_rep P m m' c x h,
dec_rep_frame_stmt dec_rep ->
agree_on rsegs P m m' -> dec_piece dec_rep m c x h -> (forall a, a < alloc_ceiling -> P a) ->
dec_piece dec_rep m' c x h.
Proof.
intros dec_rep P m m' c x h DRF AG DP HB. unfold dec_piece in *. destruct (h_st h) as [d|]; [| exact DP].
destruct DP as (DR & HS & BR). split; [| split; [exact HS| exact BR]].
eapply DRF; [exact DR|]. intros a Ha (b & Hb & Hr). apply AG; [exact Ha|]. apply HB.
pose proof (BR b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. lia.
Qed.

Lemma hrep_relow {RCEIL : RunCeiling} : forall dec_rep c x h st m m' cn cb cn' cb' j16 jsk lk,
dec_rep_frame_stmt dec_rep -> rheap_frame_stmt -> rheap_block_range_stmt -> hcx_ok c ->
hrep dec_rep c x h st m cn cb ->
munch [(aLOW c, aLOW c + 80)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
rw_cells rsegs m' (aLOW c) (low_cells c h j16 cn' cb' jsk lk) -> lk_ok h lk -> csize cn' = 8%nat -> csize cb' = 8%nat ->
hrep dec_rep c x h st m' cn' cb'.
Proof.
intros dec_rep c x h st m m' cn cb cn' cb' j16 jsk lk DRF RHF RBR CX HR MU WM MI LOW' LKO E1 E2.
first [ sf_destruct 16%nat HR as _ _ _ (stb & STB) OSP (opj & OPK) (ogj & OGJ) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct HR as (_ & _ & _ & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ]. unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof PURE as sfP_; first [ sf_destruct 8%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ _ | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & _) ].
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (ST' : stk rsegs m' (x_lo c) (hsp c)).
{ first [ sf_destruct 10%nat HG as _ _ _ _ _ _ _ _ ST _ | sf_fb; destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _) ]. eapply stk_transport_disjoint; [| exact MU| exact WM|]; [exact ST|]. cbn. lia. }
assert (HG' : hglob c x h st m').
{ eapply hglob_frame; [exact RHF| exact RBR| exact CX| exact HG| exact MU| exact WM| | exact MI| exact ST'].
unfold in_frame. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
split; [exists j16, jsk, lk; split; [exact LOW'| exact LKO]|]. split; [exact E1|]. split; [exact E2|].
split. { exists stb. eapply rw_cells_agree; [exact AG| exact STB| side1]. }
split. { eapply os_piece_agree; [exact AG| exact OSP| side1| intros a Ha; cbn; unfold alloc_ceiling in Ha; lia]. }
split. { exists opj. eapply rw_cells_agree; [exact AG| exact OPK| side1]. }
split. { exists ogj. eapply rw_cells_agree; [exact AG| exact OGJ| side1]. }
split. { eapply sync_rep_agree; [exact AG| exact SY| side1|].
intros a Ha. cbn. destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(_ & _ & _ & B4 & _) _]. rewrite ?SYLEN in Ha. unfold alloc_ceiling in B4. lia.
- first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (_ & Eb & _). rewrite ?Eb, <- ?SYLEN in Ha. cbn in Ha. lia. }
split. { eapply bits_rep_agree; [exact AG| exact BI| exact BOK| side1|]. intros a Ha. cbn. first [ sf_destruct 5%nat BBR as _ _ _ B4 _ | sf_fb; destruct BBR as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. lia. }
split. { exists pad. eapply rw_cells_agree; [exact AG| exact FSZ| unfold fsz_cells; side1]. }
split. { exists outb. split; [| exact LOUT]. eapply u8arr_agree; [exact AG| exact OUT|]. intros a Ha. cbn. lia. }
split. { exists hij. eapply rw_cells_agree; [exact AG| exact HI| side1]. }
split. { eapply rw_cells_agree; [exact AG| exact SAV| unfold sav_cells; side1]. }
split. { eapply dec_piece_agree; [exact DRF| exact AG| exact DEC|]. intros a Ha. cbn. unfold alloc_ceiling in Ha. lia. }
split; [exact HG'| exact PURE].
Qed.

Lemma lb_remove_cons : forall p b L, lb_remove p (b :: L) = if bptr_eqb (blk_id b) p then lb_remove p L else b :: lb_remove p L.
Proof. intros. unfold lb_remove. cbn. destruct (bptr_eqb (blk_id b) p); cbn; [destruct (decide False) as [X|X]; [destruct X| reflexivity] | destruct (decide True) as [X|X]; [reflexivity| exfalso; exact (X I)]]. Qed.
Lemma lb_remove_nil : forall p, lb_remove p [] = [].
Proof. reflexivity. Qed.
Lemma lb_remove_app : forall p l1 l2, lb_remove p (l1 ++ l2) = lb_remove p l1 ++ lb_remove p l2.
Proof. intros. induction l1 as [|b l1 IH]; [reflexivity|]. cbn [app]. rewrite !lb_remove_cons, IH. destruct (bptr_eqb (blk_id b) p); reflexivity. Qed.
Lemma lb_remove_other : forall p L, (forall b, In b L -> blk_id b <> p) -> lb_remove p L = L.
Proof.
intros p L H. induction L as [|b L IH]; [reflexivity|]. rewrite lb_remove_cons.
destruct (bptr_eqb (blk_id b) p) eqn:E.
- exfalso. apply bptr_eqb_eq in E. exact (H b (or_introl eq_refl) E).
- f_equal. apply IH. intros b' Hb'. apply H. right. exact Hb'.
Qed.
Lemma lb_remove_self : forall p A n, lb_remove p [(p, A, n)] = [].
Proof. intros. rewrite lb_remove_cons. unfold blk_id. cbn [fst]. rewrite bptr_eqb_refl. reflexivity. Qed.
Lemma filter_perm_lb : forall p (l l' : list block), Permutation l l' -> Permutation (lb_remove p l) (lb_remove p l').
Proof.
intros p l l' P. induction P as [|x l l' P IH| x y l| l l' l'' P1 IH1 P2 IH2].
- apply Permutation_refl.
- rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id x) p); [exact IH| apply perm_skip; exact IH].
- rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id y) p), (bptr_eqb (blk_id x) p); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
- eapply Permutation_trans; eauto.
Qed.
Lemma nodup_ids_perm : forall LB L, Permutation LB L -> List.NoDup (map blk_id LB) -> List.NoDup (map blk_id L).
Proof. intros LB L P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.
Lemma nodup_ids_app_mid : forall l1 p A n l2,
List.NoDup (map blk_id (l1 ++ (p, A, n) :: l2)) ->
(forall b, In b l1 -> blk_id b <> p) /\ (forall b, In b l2 -> blk_id b <> p).
Proof.
intros l1 p A n l2 ND. rewrite map_app in ND. cbn in ND. apply NoDup_remove in ND. destruct ND as [_ NI].
rewrite <- map_app in NI. split; intros b Hb E; apply NI; rewrite in_map_iff; exists b; (split; [exact E|]); apply in_app_iff; auto.
Qed.
Lemma perm_lb_remove : forall LB l1 p A n l2,
List.NoDup (map blk_id LB) -> Permutation LB (l1 ++ (p, A, n) :: l2) ->
Permutation (lb_remove p LB) (l1 ++ l2).
Proof.
intros LB l1 p A n l2 ND P.
pose proof (nodup_ids_app_mid l1 p A n l2 (nodup_ids_perm _ _ P ND)) as [H1 H2].
eapply Permutation_trans; [apply filter_perm_lb; exact P|].
rewrite lb_remove_app. change ((p, A, n) :: l2) with ([(p, A, n)] ++ l2).
rewrite lb_remove_app, lb_remove_self, (lb_remove_other p l1 H1), (lb_remove_other p l2 H2). apply Permutation_refl.
Qed.
Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1 l2 x. induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|].
cbn in ND. inversion ND as [|a' l' NI ND']; subst. destruct H1 as [<-|H1].
- apply NI. apply in_app_iff. right. exact H2.
- exact (IH ND' H1 H2).
Qed.
Lemma in_lb_remove_LB0 : forall LB owned LB0 p b,
List.NoDup (map blk_id LB) -> Permutation LB (owned ++ LB0) -> In p (map blk_id owned) -> In b LB0 -> In b (lb_remove p LB).
Proof.
intros LB owned LB0 p b ND P Hp Hb.
assert (ND2 : List.NoDup (map blk_id owned ++ map blk_id LB0)) by (rewrite <- map_app; exact (nodup_ids_perm _ _ P ND)).
apply lb_remove_keep.
- eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_app_iff. right. exact Hb.
- intros E. eapply (nodup_app_disj _ _ p ND2 Hp). rewrite <- E. apply in_map_iff. exists b. auto.
Qed.

Lemma blocks_apart {RCEIL : RunCeiling} : rheap_blocks_disjoint_stmt -> forall st LB m l1 b1 l2 b2,
RHEAP st LB m -> List.NoDup (map blk_id LB) -> Permutation LB (l1 ++ b1 :: l2) -> In b2 (l1 ++ l2) ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
intros RBD st LB m l1 b1 l2 b2 HP ND P H2.
destruct b1 as [[p1 A1] n1].
pose proof (nodup_ids_app_mid l1 p1 A1 n1 l2 (nodup_ids_perm _ _ P ND)) as [N1 N2].
assert (I1 : In (p1, A1, n1) LB). { eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_app_iff. right. left. reflexivity. }
assert (I2 : In b2 LB). { eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_app_iff in H2. apply in_app_iff. destruct H2; [left; assumption| right; right; assumption]. }
eapply RBD; [exact HP| exact I1| exact I2|]. cbn. intros E. apply in_app_iff in H2. destruct H2 as [H2|H2]; [exact (N1 _ H2 (eq_sym E))| exact (N2 _ H2 (eq_sym E))].
Qed.

Lemma in_block_single : forall p A n a, A <= a < A + n -> in_block [(p, A, n)] a.
Proof. intros p A n a H. exists (p, A, n). split; [left; reflexivity| cbn; lia]. Qed.
Lemma in_block_app_l : forall L1 L2 a, in_block L1 a -> in_block (L1 ++ L2) a.
Proof. intros L1 L2 a (b & Hb & R). exists b. split; [apply in_app_iff; left; exact Hb| exact R]. Qed.
Lemma in_block_app_r : forall L1 L2 a, in_block L2 a -> in_block (L1 ++ L2) a.
Proof. intros L1 L2 a (b & Hb & R). exists b. split; [apply in_app_iff; right; exact Hb| exact R]. Qed.

Lemma stream_rep_agree2 {RCEIL : RunCeiling} : forall P m m' c x h,
agree_on rsegs P m m' -> stream_rep m c x h ->
(forall a, aOS c <= a < aOS c + 408 -> P a) -> (forall a, in_block (stream_blks x h) a -> P a) ->
stream_rep m' c x h.
Proof.
intros P m m' c x h AG SR HA HB.
first [ sf_destruct 34%nat SR as OS LH F1 F2 F3 F4 F5 UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct SR as (OS & LH & F1 & F2 & F3 & F4 & F5 & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
split. { eapply rw_cells_agree; [exact AG| exact OS|]. rewrite stream_cells_size by exact LH. exact HA. }
split; [exact LH|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
unfold stream_blks in HB.
split. { eapply u32arr_agree; [exact AG| exact UL|]. intros a Ha. apply HB.
destruct (os_lacing_vals (h_os h)) as [p|] eqn:EQ; [| rewrite (E2 eq_refl) in L1; lia].
apply in_block_app_r, in_block_app_l. apply in_block_single. rewrite N2, <- L1. lia. }
split. { eapply u64arr_agree; [exact AG| exact UG|]. intros a Ha. apply HB.
destruct (os_granule_vals (h_os h)) as [p|] eqn:EQ; [| rewrite (E3 eq_refl) in L2; lia].
apply in_block_app_r, in_block_app_r. apply in_block_single. rewrite N3, <- L2. lia. }
split. { eapply u8arr_agree; [exact AG| exact UB|]. intros a Ha. apply HB.
destruct (os_body_data (h_os h)) as [p|] eqn:EQ; [| rewrite (E1 eq_refl) in L3; lia].
apply in_block_app_l. apply in_block_single. rewrite N1, <- L3. lia. }
repeat (split; [assumption|]). exact G3.
Qed.

Lemma os_piece_agree2 {RCEIL : RunCeiling} : forall P m m' c x h,
agree_on rsegs P m m' -> os_piece m c x h ->
(forall a, aOS c <= a < aOS c + 408 -> P a) -> (forall a, in_block (stream_blks x h) a -> P a) ->
os_piece m' c x h.
Proof.
intros P m m' c x h AG OSP HA HB. unfold os_piece in *. destruct (h_stream_init h =? 0).
- destruct OSP as ([osj OS] & R). split; [| exact R]. exists osj. eapply rw_cells_agree; [exact AG| exact OS|]. cbn. intros; apply HA; lia.
- eapply stream_rep_agree2; eauto.
Qed.

Lemma dec_piece_agree2 {RCEIL : RunCeiling} : forall dec_rep P m m' c x h,
dec_rep_frame_stmt dec_rep ->
agree_on rsegs P m m' -> dec_piece dec_rep m c x h -> (forall a, in_block (a_LBD x) a -> P a) ->
dec_piece dec_rep m' c x h.
Proof.
intros dec_rep P m m' c x h DRF AG DP HB. unfold dec_piece in *. destruct (h_st h) as [d|]; [| exact DP].
destruct DP as (DR & HS & BR). split; [| split; [exact HS| exact BR]].
eapply DRF; [exact DR|]. intros a Ha HIB. apply AG; [exact Ha|]. apply HB. exact HIB.
Qed.

Lemma stream_blks_init0 {RCEIL : RunCeiling} : forall m c x h, os_piece m c x h -> h_stream_init h = 0 -> stream_blks x h = [].
Proof.
intros m c x h OSP E. unfold os_piece in OSP. rewrite E in OSP. cbn in OSP. destruct OSP as (_ & Eos & _).
unfold stream_blks. rewrite Eos. reflexivity.
Qed.

Lemma sync_call_P {RCEIL : RunCeiling} : rheap_blocks_disjoint_stmt -> rheap_block_range_stmt -> forall (c : hcx) x h st m,
hcx_ok c -> RHEAP st (a_LB x) m -> List.NoDup (map blk_id (a_LB x)) -> Permutation (a_LB x) (owned x h ++ x_LB0 c) ->
(sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0) ->
forall b2, In b2 (owned_pre x h ++ x_LB0 c) -> forall a, blk_addr b2 <= a < blk_addr b2 + blk_size b2 ->
rclient_addr (lb_remove_opt (sy_data (h_oy h)) (a_LB x)) (hsp c) a
/\ outside [(hsp c - 32, hsp c); (aOY c, aOY c + 32); (a_D x, a_D x + sy_storage (h_oy h))] a.
Proof.
intros RBD RBR c x h st m CX HP ND PERM NUL b2 Hb2 a Ha.
pose proof CX as sfP_; first [ sf_destruct 10%nat sfP_ as _ _ _ _ _ _ _ CEIL LO _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & CEIL & LO & _) ]. unfold RFUZZ_STACK in LO. unfold alloc_ceiling in CEIL.
rewrite owned_split, <- app_assoc in PERM.
assert (I2 : In b2 (a_LB x)).
{ eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff in Hb2. rewrite !in_app_iff. destruct Hb2; [left; assumption| right; right; assumption]. }
pose proof (RBR _ _ _ _ HP I2) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4.
destruct (sy_data (h_oy h)) as [p|] eqn:ED; cbn [opt_blk lb_remove_opt] in PERM |- *.
- pose proof (nodup_ids_app_mid _ _ _ _ _ (nodup_ids_perm _ _ PERM ND)) as [N1 N2].
pose proof (blocks_apart RBD st (a_LB x) m _ _ _ b2 HP ND PERM Hb2) as AP. cbn [blk_addr blk_size fst snd] in AP.
split.
+ right; right. exists b2. split; [| exact Ha]. apply lb_remove_keep; [exact I2|].
apply in_app_iff in Hb2. destruct Hb2 as [H|H]; [exact (N1 _ H)| exact (N2 _ H)].
+ cbn. lia.
- destruct (NUL eq_refl) as [-> E0]. rewrite E0. split.
+ right; right. exists b2. auto.
+ cbn. lia.
Qed.

Definition hax_sync (x : hax) (LB' : list block) (D' : Z) (bytes' : list byte) : hax :=
HAX LB' D' bytes' (a_Bd x) (a_L x) (a_Gv x) (a_nB x) (a_nL x) (a_nG x) (a_hdr x) (a_lws x) (a_gws x) (a_body x) (a_Dc x) (a_S x) (a_LBD x).

Lemma owned_pre_sync : forall x LB' D' bytes' h oy1,
owned_pre (hax_sync x LB' D' bytes') (set_ogg h oy1 (h_os h)) = owned_pre x h.
Proof. intros. reflexivity. Qed.

Lemma perm_remove_sync : forall (c : hcx) x h,
List.NoDup (map blk_id (a_LB x)) -> Permutation (a_LB x) (owned x h ++ x_LB0 c) ->
Permutation (lb_remove_opt (sy_data (h_oy h)) (a_LB x)) (owned_pre x h ++ x_LB0 c).
Proof.
intros c x h ND PERM. rewrite owned_split, <- app_assoc in PERM.
destruct (sy_data (h_oy h)) as [p|]; cbn [opt_blk lb_remove_opt app] in *.
- eapply perm_lb_remove; [exact ND| exact PERM].
- exact PERM.
Qed.

Lemma perm_after_sync_buffer {RCEIL : RunCeiling} : forall (c : hcx) x h (oy1 : sync_st bptr) D' bytes' LB' (st' : PState),
List.NoDup (map blk_id (a_LB x)) -> Permutation (a_LB x) (owned x h ++ x_LB0 c) ->
( (LB' = a_LB x /\ D' = a_D x /\ sy_data oy1 = sy_data (h_oy h) /\ sy_storage oy1 = sy_storage (h_oy h))
\/ (exists q, sy_data oy1 = Some q /\ LB' = (q, D', sy_storage oy1) :: lb_remove_opt (sy_data (h_oy h)) (a_LB x)
/\ rblock_range D' (sy_storage oy1) /\ (sy_data (h_oy h) <> None -> rtop_known st' q))
\/ (oy1 = ogg_sync_init /\ D' = 0 /\ LB' = lb_remove_opt (sy_data (h_oy h)) (a_LB x)) ) ->
Permutation LB' (owned (hax_sync x LB' D' bytes') (set_ogg h oy1 (h_os h)) ++ x_LB0 c).
Proof.
intros c x h oy1 D' bytes' LB' st' ND PERM CASES.
rewrite owned_split, owned_pre_sync. cbn [a_D hax_sync h_oy set_ogg].
destruct CASES as [(-> & -> & E3 & E4) | [(q & E1 & -> & _ & _) | (-> & -> & ->)]].
- rewrite E3, E4, <- owned_split. exact PERM.
- rewrite E1. cbn [opt_blk]. rewrite <- app_assoc. apply Permutation_cons_app. apply perm_remove_sync; assumption.
- cbn. rewrite app_nil_r. apply perm_remove_sync; assumption.
Qed.

Lemma map_unsigned_to_bytes : forall l, Forall (fun z => 0 <= z < 256) l -> map bv_unsigned (to_bytes l) = l.
Proof.
intros l H. unfold to_bytes. rewrite map_map. induction H as [|z l Hz H IH]; cbn; [reflexivity|].
rewrite IH. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells rsegs m A [CB 0 []].
Proof.
intros m A HA. split; [split|].
- cbn. split; [reflexivity| exact I].
- cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma firstn_firstn_le : forall {X} (l : list X) n k, (n <= k)%nat -> firstn n (firstn k l) = firstn n l.
Proof. intros X l n k H. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma sync_rep_write : forall m m' A D (sy : sync_st bptr) (bytes : list byte) (q : bptr) (nb : Z) (src : list byte),
sync_rep m A D sy bytes -> sync_inv sy -> sy_data sy = Some q -> 0 <= nb -> sy_fill sy + nb <= sy_storage sy ->
Z.of_nat (length src) = nb ->
rw_cells rsegs m' A (sync_cells D sy) ->
u8arr rsegs m' D (firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes) ->
sync_rep m' A D (sync_write sy (sy_fill sy) (ubytes src))
(firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes).
Proof.
intros m m' A D sy bytes q nb src sfH_; first [ sf_destruct 4%nat sfH_ as OBJ FOK DAT SEP | sf_fb; destruct sfH_ as (OBJ & FOK & DAT & SEP) ]; intros INV ED Hnb Hroom Lsrc OBJ' ARR'.
unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 5%nat DAT as Dpos ARR LEN PRE LE | sf_fb; destruct DAT as (Dpos & ARR & LEN & PRE & LE) ].
pose proof INV as (I1 & I2 & _). pose proof FOK as sfP_; first [ sf_destruct 4%nat sfP_ as Fs Ff Fr _ | sf_fb; destruct sfP_ as (Fs & Ff & Fr & _) ]. unfold int31 in Fs, Ff, Fr. unfold zlength in I2.
assert (LB : Z.of_nat (length (firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes)) = sy_storage sy).
{ rewrite !app_length, firstn_length_le, skipn_length by lia. lia. }
split; [| split; [| split]].
- unfold sync_write. cbn. exact OBJ'.
- unfold sync_fields_ok, sync_write in *. cbn. exact FOK.
- unfold sync_data, sync_write. cbn. rewrite ED. split; [exact Dpos|]. split; [exact ARR'|]. split; [exact LB|].
assert (L1 : length (ztake (sy_fill sy) (sy_buf sy) ++ ubytes src) = (Z.to_nat (sy_fill sy) + length src)%nat).
{ rewrite app_length. unfold ztake, ubytes. rewrite firstn_length_le, map_length by lia. reflexivity. }
split.
+ rewrite L1. unfold ubytes. rewrite !map_app. rewrite firstn_app. rewrite map_length, firstn_length_le by lia.
replace (Z.to_nat (sy_fill sy) + length src - Z.to_nat (sy_fill sy))%nat with (length src) by lia.
rewrite (@firstn_all2 _ _ (map bv_unsigned (take (Z.to_nat (sy_fill sy)) bytes))) by (rewrite map_length, firstn_length_le by lia; lia).
rewrite firstn_app, map_length, Nat.sub_diag, firstn_O, app_nil_r.
rewrite (@firstn_all2 _ _ (map bv_unsigned src)) by (rewrite map_length; lia).
f_equal. unfold ztake. rewrite <- PRE. rewrite firstn_firstn_le by lia. rewrite firstn_map. reflexivity.
+ rewrite L1, !app_length, firstn_length_le, skipn_length by lia. lia.
- destruct SEP as [S1|S2]; [left| right; exact S2]. lia.
Qed.

Lemma stream_blks_range {RCEIL : RunCeiling} : forall m c x h, os_piece m c x h ->
forall a, in_block (stream_blks x h) a -> exists A n, rblock_range A n /\ A <= a < A + n.
Proof.
intros m c x h OSP a (b & Hb & Ra). unfold os_piece in OSP. unfold stream_blks in Hb.
destruct (h_stream_init h =? 0).
- destruct OSP as (_ & Eos & _). rewrite Eos in Hb. cbn in Hb. destruct Hb.
- first [ sf_destruct 26%nat OSP as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 R2 R3 _ | sf_fb; destruct OSP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R1 & R2 & R3 & _) ].
rewrite !in_app_iff in Hb. destruct Hb as [Hb|[Hb|Hb]].
+ destruct (os_body_data (h_os h)) eqn:E; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in Ra. exists (a_Bd x), (a_nB x). split; [apply R1; congruence| exact Ra].
+ destruct (os_lacing_vals (h_os h)) eqn:E; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in Ra. exists (a_L x), (a_nL x). split; [apply R2; congruence| exact Ra].
+ destruct (os_granule_vals (h_os h)) eqn:E; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in Ra. exists (a_Gv x), (a_nG x). split; [apply R3; congruence| exact Ra].
Qed.

Lemma dec_blks_range {RCEIL : RunCeiling} : forall dec_rep m c x h, dec_piece dec_rep m c x h ->
forall a, in_block (a_LBD x) a -> exists A n, rblock_range A n /\ A <= a < A + n.
Proof.
intros dec_rep m c x h DP a (b & Hb & Ra). unfold dec_piece in DP. destruct (h_st h).
- destruct DP as (_ & _ & BR). exists (blk_addr b), (blk_size b). split; [apply BR; exact Hb| exact Ra].
- destruct DP as [_ E]. rewrite E in Hb. destruct Hb.
Qed.

Ltac xportx AG side :=
lazymatch type of AG with
| agree_on _ ?P ?m ?m' =>
repeat match goal with
| H : os_piece m ?c ?x ?h |- _ =>
let SBR := fresh "SBR" in
pose proof (stream_blks_range m c x h H) as SBR;
first [ apply (os_piece_agree2 P m m' c x h AG) in H;
[| side
| let a := fresh "a" in let Ha := fresh "Ha" in let RB := fresh "RB" in
intros a Ha; pose proof (SBR a Ha) as sfP_; sf_curry 4%nat sfP_; intros ? ? RB ?; sf_clear sfP_; sf_fix_order; unfold rblock_range in RB; cbn beta; side_conj ]
| idtac "xportx: dropping" H; clear H ];
clear SBR
| H : dec_piece ?dr m ?c ?x ?h, DRF : dec_rep_frame_stmt ?dr |- _ =>
let SBR := fresh "SBR" in
pose proof (dec_blks_range dr m c x h H) as SBR;
first [ apply (dec_piece_agree2 dr P m m' c x h DRF AG) in H;
[| let a := fresh "a" in let Ha := fresh "Ha" in let RB := fresh "RB" in
intros a Ha; pose proof (SBR a Ha) as sfP_; sf_curry 4%nat sfP_; intros ? ? RB ?; sf_clear sfP_; sf_fix_order; unfold rblock_range in RB; cbn beta; side_conj ]
| idtac "xportx: dropping" H; clear H ];
clear SBR
end;
xport AG side
end.

Lemma low_junkify : forall m A c h j16 (a b : word) jsk lk,
rw_cells rsegs m A (low_cells c h j16 (C8 a) (C8 b) jsk lk) ->
rw_cells rsegs m A (low_cells c h j16 (CB 8 (le8 a)) (CB 8 (le8 b)) jsk lk).
Proof.
intros m A c h j16 a b jsk lk H. pose proof H as [[WF _] _]. unfold low_cells in *. cbn in WF.
eapply X0pw.rw_cells_recast; [exact H| | reflexivity| reflexivity].
cbn. cbn in WF. repeat split; try reflexivity; tauto.
Qed.
Lemma low_junkify_cn : forall m A c h j16 (a : word) cb jsk lk,
rw_cells rsegs m A (low_cells c h j16 (C8 a) cb jsk lk) ->
rw_cells rsegs m A (low_cells c h j16 (CB 8 (le8 a)) cb jsk lk).
Proof.
intros m A c h j16 a cb jsk lk H. pose proof H as [[WF _] _]. unfold low_cells in *. cbn in WF.
eapply X0pw.rw_cells_recast; [exact H| | reflexivity| reflexivity].
cbn. cbn in WF. repeat split; try reflexivity; tauto.
Qed.
Lemma low_junkify_cb : forall m A c h j16 cn (b : word) jsk lk,
rw_cells rsegs m A (low_cells c h j16 cn (C8 b) jsk lk) ->
rw_cells rsegs m A (low_cells c h j16 cn (CB 8 (le8 b)) jsk lk).
Proof.
intros m A c h j16 cn b jsk lk H. pose proof H as [[WF _] _]. unfold low_cells in *. cbn in WF.
eapply X0pw.rw_cells_recast; [exact H| | reflexivity| reflexivity].
cbn. cbn in WF. repeat split; try reflexivity; tauto.
Qed.

Lemma lookahead_pow2 : forall {ptr : Type} (d : dec_state ptr),
exists k, 0 <= k /\ fst (speex_decoder_ctl d CtlGetLookahead) = NB_SUBFRAME_SIZE * 2 ^ k.
Proof.
intros ptr d. induction d as [st|st low IH].
- exists 0. split; [lia|]. cbn. reflexivity.
- destruct IH as (k & Hk & E). exists (k + 1). split; [lia|]. cbn [speex_decoder_ctl].
destruct (speex_decoder_ctl low CtlGetLookahead) as [v low'] eqn:EL. cbn [fst] in E |- *. rewrite E.
rewrite Z.pow_add_r, Z.pow_1_r by lia. ring.
Qed.

Lemma lookahead_range : forall {ptr : Type} (d : dec_state ptr),
-2^31 <= fst (speex_decoder_ctl d CtlGetLookahead) < 2^31 ->
40 <= fst (speex_decoder_ctl d CtlGetLookahead) <= 1342177280.
Proof.
intros ptr d R. destruct (lookahead_pow2 d) as (k & Hk & E). rewrite E in R |- *. unfold NB_SUBFRAME_SIZE in *.
assert (K : k <= 25).
{ destruct (Z_le_gt_dec k 25) as [|G]; [assumption|]. exfalso.
assert (2 ^ 26 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia. }
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
assert (2 ^ k <= 2 ^ 25) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma hcx_usp16 {RCEIL : RunCeiling} : forall c, hcx_ok c -> usp c mod 16 = 0.
Proof. intros c (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma usp_off_mod : forall n u k, 0 < n -> (n | 16) -> u mod 16 = 0 -> k mod n = 0 -> (u + k) mod n = 0.
Proof.
intros n u k Hn Hd Hu Hk. rewrite Zplus_mod, Hk, (Znumtheory.Zmod_div_mod n 16 u Hn ltac:(lia) Hd), Hu.
reflexivity.
Qed.

Lemma usp_ctl_ptr_ok : forall u k arg, u mod 16 = 0 -> 0 < u + k ->
match arg with ArgCallback => k mod 8 = 0 | _ => k mod 4 = 0 end -> ctl_arg_ptr_ok (u + k) arg.
Proof.
intros u k arg Hu Hp Hk. unfold ctl_arg_ptr_ok.
destruct arg; (split; [exact Hp|]); (apply usp_off_mod; [lia| | exact Hu| exact Hk]); first [exists 2; reflexivity| exists 4; reflexivity].
Qed.

Ltac ctl_ptr_tac CX := first
[ apply usp_ctl_ptr_ok; [apply (hcx_usp16 _ CX)| lia| reflexivity]
| apply usp_off_mod; [lia| exists 1; reflexivity| apply (hcx_usp16 _ CX)| reflexivity] ].

Lemma lts_succ_false : forall v, -2^63 <= v -> v + 1 < 2^63 -> bv_lts (Z_to_bv 64 (v + 1)) (Z_to_bv 64 v) = false.
Proof. intros v H1 H2. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.
