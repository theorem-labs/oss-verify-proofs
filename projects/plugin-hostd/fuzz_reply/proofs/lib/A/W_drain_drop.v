(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT DROP of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x835ac .. 0x836bc / 0x83a4c, 3 call sites), the statement W_drain_cx.v dr_drop_stmt.
   The Section header below is W_drain_cx.v's, verbatim.

   DE 0x835ac is the byte loop left: the round's n bytes sit in the relay's buffer after s->used and the
   reference splitter has taken them.  This segment is fuzz_recv's tail and the relay's first memchr
   (relay.c:202-204, fuzz_reply.c:262-272):
     0x835b8  h->pending_off += n                                      (sd 0x835c0)
     0x83600  pending_off == v[0].n ?  list_drop(&h->pending, 0) inlined:
                free(v[0].s)                      (CALL free 0x83618, AFREE, the live-state rule)
                memmove(v, v + 16, 16 (pend.n-1)) (CALL __asan_memmove 0x83648, AMEMMOVE)
                h->pending.n -= 1                 (sw 0x83654)
                h->pending_off = 0                (sd 0x83664)
     0x83668  n < 0 and n == 0 refuted (DE carries 0 < dnum s1 and the round's cap bound)
              s->used += n                        (sd 0x83684)
              memchr(s->buf, 0, s->used)          (CALL memchr 0x836a4, AMEMCHR)
     found -> DLL p = 0, q the NUL (0x836bc);  none -> DLR p = 0 (0x83a48 mv s10,s8; 0x83a4c).
   The two arms of the first test join at 0x83668; the segment is three stages over the intermediate cut
   DQ at that join (drop_keep, drop_whole, drop_tail), as the plain proof's read_tail_keep /
   read_tail_drop / read_tail (lib/Prog/drain_b.v:5780, 7169, 7375).
   The pure model lemmas dm_* below are this file's own copies. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_dropb_cx W_drain_tr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
(* aout_at's three read-only cells are program globals off the allocator's statics, so an allocator or program
   call keeps them (found by GsFree at free #2: they are not in G_DR; send_line's W_send_line_cx.v HGO) *)
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
(* errno's 4 bytes are writable image bytes in the segments' own view (a .bss cell of the RW LOAD), so aout_at's
   errno cell stays writable across an allocator call whatever the call leaves present (the allocator rules keep
   errno's view but exclude it from presence; found by DropWhole at free #1).  Decided at the pinned placement. *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ================================================================================================
   The symbolic state at the DE cut (0x835ac).  Atoms: 2 = sp, 19 = n (s3), 21 = SHADOW_OFF (s5),
   23 = &g_s[j] (s7); extras 32 = SA, 33 = h->pending.v, 34 = v[0].n, 35 = h->pending.n,
   36 = h->pending_off, 37 = s->buf, 38 = s->used, 39 = v[0].s.
   g_s is carried as TWO regions: [16, 28) whose write window is h->pending.n and [32, 40) whose
   write window is h->pending_off.  h->pending.cap (at 28) is in neither, so the run's frame keeps
   its bytes.  The only other write windows are s->used (SA + 24) and the one frame slot 192(sp).
   ================================================================================================ *)
Definition dr_shA (m : nat) (c : Z) : cval :=
  CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0)).
Definition dr_r_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 336 192 200
  [ YP09.mkChunk 32 (CVal 8 (SOff 23 24));
    YP09.mkChunk 40 (dr_shA 23 24);
    YP09.mkChunk 48 (CVal 8 (SOff 32 24));
    YP09.mkChunk 56 (CVal 8 (SOff 32 0));
    YP09.mkChunk 64 (CVal 8 (SOff 32 32));
    YP09.mkChunk 80 (dr_shA 23 16);
    YP09.mkChunk 176 (dr_shA 32 0);
    YP09.mkChunk 192 (dr_shA 23 32);
    YP09.mkChunk 200 (CVal 8 (SOff 32 16));
    YP09.mkChunk 208 (CVal 8 (SOff 32 8));
    YP09.mkChunk 216 (dr_shA 32 16);
    YP09.mkChunk 224 (dr_shA 32 24) ].
Definition dr_r_gsA : YP09.region := YP09.mkRegion (Some 23%nat) 16 28 24 28
  [ YP09.mkChunk 16 (CVal 8 (SOff 33 0));
    YP09.mkChunk 24 (CVal 4 (SOff 35 0)) ].
Definition dr_r_gsC : YP09.region := YP09.mkRegion (Some 23%nat) 32 40 32 40
  [ YP09.mkChunk 32 (CVal 8 (SOff 36 0)) ].
Definition dr_r_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 24 32
  [ YP09.mkChunk 16 (CVal 8 (SOff 37 0));
    YP09.mkChunk 24 (CVal 8 (SOff 38 0)) ].
Definition dr_r_vec : YP09.region := YP09.mkRegion (Some 33%nat) 0 16 0 0
  [ YP09.mkChunk 0 (CVal 8 (SOff 39 0));
    YP09.mkChunk 8 (CVal 8 (SOff 34 0)) ].
Definition dr_regions : smem := [ dr_r_frame; dr_r_gsA; dr_r_gsC; dr_r_sa; dr_r_vec ].
Definition DRLOW : Z := 140737479966720.
Definition dr_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0); (19%nat, mkAF 1 16384 0);
    (23%nat, mkAF 0x10000 0x5fb000 3); (32%nat, mkAF 4096 DRLOW 0);
    (33%nat, mkAF 4096 DRLOW 3); (37%nat, mkAF 4096 DRLOW 3) ] [] [].
Definition ss_drop : sstate := mkSS A_dr_fed sr_atoms dr_regions None dr_facts.
Definition BxD : sv := SOff 21 0.
Definition DRspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition SHD : list shent := [ mkSHE 32 0 56; mkSHE 23 0 96; mkSHE 33 0 16 ].
Definition dr_extra (SA pv v0n pn off buf used v0s : Z) : list word :=
  map (Z_to_bv 64) [SA; pv; v0n; pn; off; buf; used; v0s].

(* ---- reading an 8-byte little-endian field out of a byte array (W_list_free.v lf_le8_val) ---- *)
Lemma dr_nth_le_bytes : forall n z k, (k < n)%nat ->
nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma dr_le8_val : forall m a (w : word), garr8 SEGS m a (bzs (Mem.le8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hlen : (k < length (bzs (Mem.le8 w)))%nat) by (unfold bzs; rewrite length_map, Mem.length_le8; exact Hk).
rewrite (garr8_mbyte SEGS m a _ k H Hlen). f_equal.
assert (Hn : nth k (bzs (Mem.le8 w)) 0 = bz (nth k (Mem.le8 w) (Z_to_bv 8 0))).
{ unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by exact Hlen. apply List.map_nth. }
rewrite Hn.
unfold Mem.le8, word_to_le_bytes, bz. rewrite dr_nth_le_bytes by lia. rewrite Z_to_bv_bv_unsigned.
pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 8) with 64 by lia. rewrite (Z.mod_small (bv_unsigned w)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma dr_len_text_recs : forall l, length (concat (map text_rec l)) = (16 * length l)%nat.
Proof.
induction l as [|r l IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
(* the head record's two fields, at v and v + 8 *)
Lemma dr_head_fields : forall m v (r0 : Z * list byte) rs0 junk,
garr8 SEGS m v (bzs (concat (map text_rec (r0 :: rs0)) ++ junk)) ->
val_mem SEGS m v 8 (bv_unsigned (Z_to_bv 64 (fst r0))) /\
val_mem SEGS m (v + 8) 8 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length (snd r0))))).
Proof.
intros m v r0 rs0 junk H.
cbn [map concat] in H. unfold text_rec at 1 in H. unfold bzs in H.
rewrite <- !app_assoc, map_app in H. apply garr8_app in H as [H1 H].
rewrite length_map, Mem.length_le8 in H. change (Z.of_nat 8) with 8 in H.
rewrite map_app in H. apply garr8_app in H as [H2 _].
split; [exact (dr_le8_val m v _ H1) | exact (dr_le8_val m (v + 8) _ H2)].
Qed.

(* ---- The relay entry's two 8-byte fields s->buf (offset 16) and s->used (offset 24), read out of
   the 56 bytes of the entry (RelayRep.v entry_bytes: le4 fd ++ le4 eof ++ le4 skip ++ pad1(4) ++
   le8 buf ++ le8 used ++ le8 cap ++ le8 hp ++ le4 nheld ++ pad2(4)). ---- *)
Lemma dr_entry_fields : forall m SA e,
length (re_pad1 e) = 4%nat ->
garr8 SEGS m SA (bzs (entry_bytes e)) ->
val_mem SEGS m (SA + 16) 8 (bv_unsigned (Z_to_bv 64 (re_buf e))) /\
val_mem SEGS m (SA + 24) 8 (bv_unsigned (Z_to_bv 64 (re_used e))).
Proof.
intros m SA e Hp1 H. unfold entry_bytes, bzs in H.
rewrite map_app in H. apply garr8_app in H as [_ H].     (* past le4 fd *)
rewrite length_map, Mem.length_le4 in H.
rewrite map_app in H. apply garr8_app in H as [_ H].     (* past le4 eof *)
rewrite length_map, Mem.length_le4 in H.
rewrite map_app in H. apply garr8_app in H as [_ H].     (* past le4 skip *)
rewrite length_map, Mem.length_le4 in H.
rewrite map_app in H. apply garr8_app in H as [_ H].     (* past pad1 *)
rewrite length_map, Hp1 in H.
replace (SA + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (SA + 16) in H by lia.
rewrite map_app in H. apply garr8_app in H as [H1 H].    (* le8 buf *)
rewrite length_map, Mem.length_le8 in H.
replace (SA + 16 + Z.of_nat 8) with (SA + 24) in H by lia.
rewrite map_app in H. apply garr8_app in H as [H2 _].    (* le8 used *)
split; [exact (dr_le8_val m (SA + 16) _ H1) | exact (dr_le8_val m (SA + 24) _ H2)].
Qed.

(* ---- A live block lies off the image, and two distinct live blocks are apart (W_drain_rest.v
   rs_blk_noimg / rs_blk_apart).  Together they give the three numeric separations the symbolic
   state's regions need: g_s[j] against the relay's table block and against the pending vector,
   and those two against each other. ---- *)
Lemma dr_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & H1 & _ & H3). exists sg. split; [exact H1 | exact H3]. Qed.

Lemma dr_blk_noimg : forall ly S (W : world SEGS) mem md q m a,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md q m a HAR Hin Ha Himg.
exact (blk_img SEGS B LAWS ly S W mem md q m a HAR Hin Ha Himg).
Qed.

(* two intervals with no common point are apart *)
Lemma dr_apart_of_disj : forall x nx y ny, 0 < nx -> 0 < ny ->
(forall a, x <= a < x + nx -> ~ (y <= a < y + ny)) -> x + nx <= y \/ y + ny <= x.
Proof.
intros x nx y ny Hx Hy H.
destruct (Z.le_gt_cases (x + nx) y) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases (y + ny) x) as [|H2]; [right; lia|].
exfalso. apply (H (Z.max x y)); lia.
Qed.

(* ---- The entry state at the DE cut, as a statement: both arms take it, and it is proved from the
   facts DE and DBASE carry.  (The premises are the ones the symbolic state's five regions, seven
   atom facts and three shadow entries need; `in_app` comes from al_blocks on the two heap blocks.) *)
Definition drop_entry_stmt : Prop :=
forall (W : world SEGS) regs mem SA HA pv v0n pn off buf used v0s n,
alloc_ceiling <= spZ regs -> spZ regs + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regs ->
spZ regs mod 16 = 0 ->
(forall o, 192 <= o < 200 -> writable_at SEGS (arm W mem) (spZ regs + o)) ->
getr regs 21 = w64 SHADOW_OFF -> getr regs 23 = w64 HA -> getr regs 19 = w64 n ->
1 <= n <= 16384 ->
0x10000 <= HA -> HA + 96 <= 0x5fb000 -> HA mod 8 = 0 ->
(forall o, 16 <= o < 40 -> writable_at SEGS (arm W mem) (HA + o)) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF HA 96 ->
val_mem SEGS (arm W mem) (HA + 16) 8 pv -> val_mem SEGS (arm W mem) (HA + 24) 4 pn ->
val_mem SEGS (arm W mem) (HA + 32) 8 off -> 0 <= pn < 2 ^ 32 -> 0 <= off < 2 ^ 64 ->
4096 <= SA -> SA + 56 <= alloc_ceiling ->
(forall o, 24 <= o < 32 -> writable_at SEGS (arm W mem) (SA + o)) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF SA 56 ->
val_mem SEGS (arm W mem) (SA + 16) 8 buf -> val_mem SEGS (arm W mem) (SA + 24) 8 used ->
0 <= used < 2 ^ 64 -> in_app SA 56 ->
4096 <= pv -> pv + 16 <= alloc_ceiling -> pv mod 8 = 0 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF pv 16 ->
val_mem SEGS (arm W mem) pv 8 v0s -> val_mem SEGS (arm W mem) (pv + 8) 8 v0n ->
0 <= v0s < 2 ^ 64 -> 0 <= v0n < 2 ^ 64 -> in_app pv 16 ->
4096 <= buf -> buf + 1 <= alloc_ceiling -> buf mod 8 = 0 ->
val_mem SEGS (arm W mem) (spZ regs + 32) 8 (HA + 24) ->
val_mem SEGS (arm W mem) (spZ regs + 40) 8 (shadow_addr (HA + 24)) ->
val_mem SEGS (arm W mem) (spZ regs + 48) 8 (SA + 24) ->
val_mem SEGS (arm W mem) (spZ regs + 56) 8 SA ->
val_mem SEGS (arm W mem) (spZ regs + 64) 8 (SA + 32) ->
val_mem SEGS (arm W mem) (spZ regs + 80) 8 (shadow_addr (HA + 16)) ->
val_mem SEGS (arm W mem) (spZ regs + 176) 8 (shadow_addr SA) ->
val_mem SEGS (arm W mem) (spZ regs + 192) 8 (shadow_addr (HA + 32)) ->
val_mem SEGS (arm W mem) (spZ regs + 200) 8 (SA + 16) ->
val_mem SEGS (arm W mem) (spZ regs + 208) 8 (SA + 8) ->
val_mem SEGS (arm W mem) (spZ regs + 216) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W mem) (spZ regs + 224) 8 (shadow_addr (SA + 24)) ->
(HA + 96 <= SA \/ SA + 56 <= HA) -> (HA + 96 <= pv \/ pv + 16 <= HA) ->
(SA + 56 <= pv \/ pv + 16 <= SA) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (dr_extra SA pv v0n pn off buf used v0s))) ss_drop
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_fed)) mem (seg_rom SEGS)))
/\ sh_ok SEGS BxD SHD (Eimg (Ereg regs (dr_extra SA pv v0n pn off buf used v0s))) (arm W mem).

(* ================================================================================================
   The two arms of the `h->pending_off == v[0].n` test at 0x83600, both landing on the shared cut
   DDM at 0x83668 (W_drain_dropb_cx.v), and the composition with the second half dr_dropb_stmt.
   ================================================================================================ *)


(* ---- The entry state at the DE cut. ---- *)
(* ---- helpers (W_drain_rest.v rs_den, rs_div8, rs_U_srl, rs_U_shadow, rs_shadow_range, renamed) ---- *)
Lemma de_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma de_div8 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma de_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. pose proof (de_div8 (v + c) Hc). lia.
Qed.

Lemma de_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SB ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 21 0)) = SHADOW_OFF + (v + c) / 8.
Proof.
intros E n v c Hn H21 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (de_U_srl E n v c Hn Hv Hc), (U_atom E 21 SB H21) by (unfold SB; lia).
pose proof (de_div8 (v + c) Hc) as Hd.
replace SB with SHADOW_OFF by reflexivity.
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma de_shadow_range : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (de_div8 x ltac:(lia)). lia. Qed.

(* a frame slot holding the shadow address of atom m plus c *)
Lemma de_chunk_sh : forall E mem base off m v c,
ew E m = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SB -> 0 <= v < 2 ^ 47 -> 0 <= v + c < 2 ^ 47 ->
val_mem SEGS mem (base + off) 8 (shadow_addr (v + c)) ->
YP09.chunk_ok SEGS E mem base (YP09.mkChunk off (dr_shA m c)).
Proof.
intros E mem base off m v c Hm H21 Hv Hc M. unfold dr_shA.
pose proof (de_shadow_range (v + c) Hc) as SR.
apply (chunk_ok_val SEGS E mem base off 8 _ (shadow_addr (v + c))); [| zside | zside | exact M].
apply de_den. rewrite (de_U_shadow E m v c Hm H21) by lia. unfold shadow_addr. reflexivity.
Qed.


Lemma drop_entry : drop_entry_stmt.
Proof.
unfold drop_entry_stmt.
intros W regs mem SA HA pv v0n pn off buf used v0s n
  Hceil Htop Hlo Hal Hwf R21 R23 R19 Hn
  HA1 HA2 HA3 HwG RaG Mpv Mpn Moff Hpn Hoff
  HSA1 HSA2 HwS RaS Mbuf Mused Hused AppS
  Hpv1 Hpv2 Hpv3 RaV Mv0s Mv0n Hv0s Hv0n AppV
  Hb1 Hb2 Hb3
  F32 F40 F48 F56 F64 F80 F176 F192 F200 F208 F216 F224
  D1 D2 D3.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
unfold DRAIN_FRAME in Htop.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (dr_extra SA pv v0n pn off buf used v0s))).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E19 : ew E 19 = Z_to_bv 64 n)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E23 : ew E 23 = Z_to_bv 64 HA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pv)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v0n)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 pn)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 off)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 buf)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 used)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 v0s)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UHA : bv_unsigned (ew E 23) = HA) by (rewrite E23; apply unsigned_lit_small; lia).
assert (USA : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Upv : bv_unsigned (ew E 33) = pv) by (rewrite E33; apply unsigned_lit_small; lia).
split.
- unfold ss_drop. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold dr_regions, dr_r_frame, dr_r_gsA, dr_r_gsC, dr_r_sa, dr_r_vec.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwf; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ (spZ regs) 32 8 (SOff 23 24) (HA + 24));
           [rewrite (den_atom E 23 HA 24 E23) by lia; reflexivity | zside | zside | exact F32].
      -- apply (de_chunk_sh E _ (spZ regs) 40 23 HA 24 E23 E21); [lia | lia | exact F40].
      -- apply (chunk_ok_val SEGS E _ (spZ regs) 48 8 (SOff 32 24) (SA + 24));
           [rewrite (den_atom E 32 SA 24 E32) by lia; reflexivity | zside | zside | exact F48].
      -- apply (chunk_ok_val SEGS E _ (spZ regs) 56 8 (SOff 32 0) SA);
           [rewrite (den_atom0 E 32 SA E32) by lia; reflexivity | zside | zside | exact F56].
      -- apply (chunk_ok_val SEGS E _ (spZ regs) 64 8 (SOff 32 32) (SA + 32));
           [rewrite (den_atom E 32 SA 32 E32) by lia; reflexivity | zside | zside | exact F64].
      -- apply (de_chunk_sh E _ (spZ regs) 80 23 HA 16 E23 E21); [lia | lia | exact F80].
      -- apply (de_chunk_sh E _ (spZ regs) 176 32 SA 0 E32 E21); [lia | lia | rewrite Z.add_0_r; exact F176].
      -- apply (de_chunk_sh E _ (spZ regs) 192 23 HA 32 E23 E21); [lia | lia | exact F192].
      -- apply (chunk_ok_val SEGS E _ (spZ regs) 200 8 (SOff 32 16) (SA + 16));
           [rewrite (den_atom E 32 SA 16 E32) by lia; reflexivity | zside | zside | exact F200].
      -- apply (chunk_ok_val SEGS E _ (spZ regs) 208 8 (SOff 32 8) (SA + 8));
           [rewrite (den_atom E 32 SA 8 E32) by lia; reflexivity | zside | zside | exact F208].
      -- apply (de_chunk_sh E _ (spZ regs) 216 32 SA 16 E32 E21); [lia | lia | exact F216].
      -- apply (de_chunk_sh E _ (spZ regs) 224 32 SA 24 E32 E21); [lia | lia | exact F224].
    * rewrite UHA. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwG; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ HA 16 8 (SOff 33 0) pv);
           [rewrite (den_atom0 E 33 pv E33) by lia; reflexivity | zside | zside | exact Mpv].
      -- apply (chunk_ok_val SEGS E _ HA 24 4 (SOff 35 0) pn);
           [rewrite (den_atom0 E 35 pn E35) by lia; reflexivity | zside | zside | exact Mpn].
    * rewrite UHA. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwG; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ HA 32 8 (SOff 36 0) off);
        [rewrite (den_atom0 E 36 off E36) by lia; reflexivity | zside | zside | exact Moff].
    * rewrite USA. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwS; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 37 0) buf);
           [rewrite (den_atom0 E 37 buf E37) by lia; reflexivity | zside | zside | exact Mbuf].
      -- apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 38 0) used);
           [rewrite (den_atom0 E 38 used E38) by lia; reflexivity | zside | zside | exact Mused].
    * rewrite Upv. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ pv 0 8 (SOff 39 0) v0s);
           [rewrite (den_atom0 E 39 v0s E39) by lia; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mv0s].
      -- apply (chunk_ok_val SEGS E _ pv 8 8 (SOff 34 0) v0n);
           [rewrite (den_atom0 E 34 v0n E34) by lia; reflexivity | zside | zside | exact Mv0n].
  + apply pairwise_disjoint_of_extents.
    unfold dr_regions, dr_r_frame, dr_r_gsA, dr_r_gsC, dr_r_sa, dr_r_vec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UHA, USA, Upv.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [dr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E21, E19, UHA, USA, Upv, E37, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold DRLOW.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- assert (UB : U E BxD = SHADOW_OFF) by (unfold BxD; rewrite (U_atom E 21 SB E21) by (unfold SB; lia); reflexivity).
  unfold sh_ok, SHD. constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E BxD 32 SA 56 SA 0 56); [exact RaS | exact UB | | lia | lia |].
    * apply (U_atom E 32 SA E32). lia.
    * intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in AppS. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E BxD 23 HA 96 HA 0 96); [exact RaG | exact UB | | lia | lia |].
    * apply (U_atom E 23 HA E23). lia.
    * intros x Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E BxD 33 pv 16 pv 0 16); [exact RaV | exact UB | | lia | lia |].
    * apply (U_atom E 33 pv E33). lia.
    * intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in AppV. unfold SHADOW_OFF. lia.
Qed.


(* ================================================================================================
   The arm where the 0x83600 test FAILS (no list_drop): one store, h->pending_off = off + n, then the
   fall-through to the join 0x83668.  The entry state is drop_entry (above), bound here as DROPENTRY.
   ================================================================================================ *)
(* ---- This arm's helpers. ---- *)
(* two different live blocks are apart (W_drain_rest.v rs_blk_apart / rs_ablocks_nodup) *)
Lemma dk_pw_in2 : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [In] in Hx, Hy. destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso; apply Hne; reflexivity.
- left. exact (HF y Hy).
- right. exact (HF x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.
Lemma dk_pw_nodup : forall l : list (Z * Z), (forall x, In x l -> 1 <= snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hpw; [apply List.NoDup_nil|].
destruct Hpw as [Hx Hl]. apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx. pose proof (Hx x Hin) as Z. pose proof (Hpos x (or_introl eq_refl)).
  unfold zdisjoint in Z. lia.
- apply IH; [intros y Hy; apply Hpos; right; exact Hy | exact Hl].
Qed.
Lemma dk_nodup_map_inj : forall {X Y} (f : X -> Y) (l : list X) x y,
List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z l IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|w ws Hz Hnd']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y Hnd' Hx Hy Hf)].
- exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
Qed.
Lemma dk_blk_apart : forall ly S (W : world SEGS) mem md p n q m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S W mem md p n q m HAR Hp Hq Hne.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof (dk_pw_nodup _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (dk_nodup_map_inj f _ _ _ Hnd Hp Hq E))).
destruct (dk_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold zdisjoint, f in X; cbn [fst snd] in X; lia.
Qed.
Lemma dk_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hp : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (dk_pw_nodup _ Hpos Hpw)).
Qed.

(* a byte of g_s is a byte of G_DR, so an image byte *)
Lemma dk_inG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> inG (G_DR B RG) a.
Proof.
intros a Ha. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma dk_gs_img : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> in_img SEGS a.
Proof. intros a Ha. exact (proj1 (HG a (dk_inG a Ha))). Qed.

(* two memories whose views agree on n bytes at a holding v agree on every byte of them *)
Lemma dk_aview_of_vm : forall (W : world SEGS) m m' a (n : nat) v x,
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v -> a <= x < a + Z.of_nat n ->
aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x.
Proof.
intros W m m' a n v x H1 H2 Hx. unfold aview. replace x with (a + (x - a)) by lia.
unfold arm in H1, H2. rewrite (val_mem_agree SEGS _ _ a n v H1 H2 (x - a)) by lia. reflexivity.
Qed.

(* the sum the 0x83600 test compares *)
Lemma dk_U_add : forall E a b x y, U E a = x -> U E b = y -> 0 <= x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof.
intros E a b x y Ha Hb Hr. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.

(* a 16-aligned address is 8-aligned *)
Lemma dk_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. destruct H as (k & ->).
replace (k * 16) with ((2 * k) * 8) by ring. apply Z_mod_mult.
Qed.

Lemma dk_den : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma dk_Urange : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. pose proof (U_range E e) as H. unfold M64 in H. exact H. Qed.

Lemma dk_in_dec : forall a n x, (a <= x < a + n) \/ ~ (a <= x < a + n).
Proof.
intros a n x. destruct (Z_le_gt_dec a x); destruct (Z_lt_ge_dec x (a + n)); [left; lia | right; lia | right; lia | right; lia].
Qed.

(* ---- The memory core across the one store h->pending_off = off + n: every byte off [HA + 32, HA + 40)
   is kept.  A live block is off the image, g_s is in it; aout's cells are apart from g_s (HRGD). ---- *)
Definition dk_out (HA a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (HA + 32 <= a < HA + 40).

(* the harness source with its pending offset set to o *)
Definition dk_setoff (h : hsrc) (o : Z) : hsrc :=
HS (hs_fd h) (hs_open h) (hs_closed h) (hs_eintr h) (hs_pending h) o (hs_partial h) (hs_pjunk h)
  (hs_npartial h) (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).

Lemma dk_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma dk_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dk_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dk_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (bzs (entry_bytes e)) = 56%nat.
Proof.
intros e H1 H2. unfold entry_bytes, bzs. rewrite length_map, !length_app, H1, H2, !Mem.length_le8, !Mem.length_le4.
reflexivity.
Qed.

Lemma dk_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dk_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dk_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dk_blk_out : forall ly S (W : world SEGS) mem md q n a HA,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a < q + req_size n ->
rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC -> dk_out HA a.
Proof.
intros ly S W mem md q n a HA HAR Hin Ha H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
split; [clear - H4096 Hceil Ha C1; lia|]. intros Hx.
apply (dr_blk_noimg ly S W mem md q n a HAR Hin Ha). apply dk_gs_img. clear - Hx H1 H2; lia.
Qed.

Lemma dk_aentry_fp_out : forall ly S (W : world SEGS) mem md e HA,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e -> rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> dk_out HA a.
Proof.
intros ly S W mem md e HA HAR HE H1 H2 r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & HU8 & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
  apply (dk_blk_out ly S W mem md (re_buf e) (re_cap e) a HA HAR Hin); [|exact H1 | exact H2].
  pose proof (dk_req_ge (re_cap e)) as Hrq. clear - Ha Hj HU HU8 Hrq. lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. clear - Ha; lia.
    * unfold bzs in Ha. rewrite length_map, dk_key_ptrs_len in Ha.
      apply (dk_blk_out ly S W mem md (re_hp e) (re_kh e) a HA HAR Hin); [|exact H1 | exact H2].
      pose proof (dk_req_ge (re_kh e)) as Hrq. unfold re_nheld in Hk1. clear - Ha Hk1 Hrq. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (dk_blk_out ly S W mem md _ _ a HA HAR Hin); [|exact H1 | exact H2].
    pose proof (dk_req_ge (Z.of_nat (length (key_text k)) + 1)) as Hrq. clear - Ha Hrq. lia.
Qed.

Lemma dk_alist_fp_out : forall ly S (W : world SEGS) mem md LA l lines HA,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines -> rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
(forall a, LA <= a < LA + 16 -> dk_out HA a) ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> dk_out HA a.
Proof.
intros ly S W mem md LA l lines HA HAR HL H1 H2 HLA r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. exact (HLA a Ha).
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dk_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
    apply (dk_blk_out ly S W mem md (hl_v l) (AREC * hl_cap l) a HA HAR Hin); [|exact H1 | exact H2].
    pose proof (dk_req_ge (AREC * hl_cap l)) as Hrq.
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (dk_blk_out ly S W mem md _ _ a HA HAR Hin); [|exact H1 | exact H2].
    pose proof (dk_req_ge (Z.of_nat (length (snd q)) + 1)) as Hrq. clear - Ha Hrq. lia.
Qed.

Ltac dk_in := repeat (first [left; reflexivity | right]).

Lemma dk_aout_fp_out : forall ly S (W : world SEGS) mem md c O mx no cap out HA,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> dk_out HA a.
Proof.
intros ly S W mem md c O mx no cap out HA HAR HOUT H1 H2 r Hr a Ha.
pose proof (dk_zpw _ 2 3 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dk_zpw _ 2 4 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dk_zpw _ 2 5 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dk_zpw _ 2 6 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dk_zpw _ 2 7 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dk_zpw _ 2 8 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dk_zpw _ 2 9 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dk_zpw _ 2 10 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
pose proof (dk_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D11.
cbn [nth] in D3, D4, D5, D6, D7, D8, D9, D10, D11.
unfold zdisj in D3, D4, D5, D6, D7, D8, D9, D10, D11.
cbn [fst snd] in D3, D4, D5, D6, D7, D8, D9, D10, D11.
assert (GLB : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> 0 <= a < 2 ^ 64).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI) as HL. unfold kLowMemEnd in HL. clear - HL. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). split; [clear - Ha Hs1 Hs2; lia | clear - Ha D7 H1 H2; lia].
- split; [apply (GLB (rg_nout RG) 8); [unfold G_DR, G_SL; dk_in | exact Ha] | clear - Ha D8 H1 H2; lia].
- split; [apply (GLB (rg_capout RG) 8); [unfold G_DR, G_SL; dk_in | exact Ha] | clear - Ha D9 H1 H2; lia].
- split; [apply (GLB (rg_out RG) 8); [unfold G_DR, G_SL; dk_in | exact Ha] | clear - Ha D10 H1 H2; lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  split; [clear - Ha H9; lia | clear - Ha D3 H1 H2; lia].
- split; [apply (GLB (rg_client_broken RG) 1); [unfold G_DR, G_SL; dk_in | exact Ha] | clear - Ha D4 H1 H2; lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  split; [clear - Ha H12; lia | clear - Ha D6 H1 H2; lia].
- split; [apply (GLB (rg_send_eintr RG) 1); [unfold G_DR, G_SL; dk_in | exact Ha] | clear - Ha D5 H1 H2; lia].
- split; [apply (GLB (as_errno B) 4); [unfold G_DR, G_SL; dk_in | exact Ha] | clear - Ha D11 H1 H2; lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; clear - Hc Hc0; lia|].
  apply (dk_blk_out ly S W mem md out cap a HA HAR Hin); [|exact H1 | exact H2].
  pose proof (dk_req_ge cap) as Hrq. clear - Ha Hrq. lia.
Qed.

(* W_drain_next.v dn_aentry_okx_kept *)
Lemma dk_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
aentry_okx B ly S W mem e ->
akept W mem W' mem' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* W_drain_next.v dn_frame_kept: drain's frame, every slot in [sp, sp + 336) *)
Lemma dk_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in HF |- *. cbv zeta in HF |- *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi).
replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

(* asrc_at with the pending offset set to o' (the 8 bytes at HA + 32 now hold o') *)
Lemma dk_asrc_off : forall ly S (W : world SEGS) m m' md HA h o',
AR SEGS B ly S W m md -> asrc_at B ly S W m HA h ->
(forall b, In b (asrc_blks h) -> In b (ablocks B ly S)) ->
rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
(forall a, dk_out HA a -> abyte_kept W m W m' a) ->
(forall a, writable_at SEGS (arm W m) a -> writable_at SEGS (arm W m') a) ->
val_mem SEGS (arm W m') (HA + 32) 8 o' ->
(exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r))) ->
asrc_at B ly S W m' HA (dk_setoff h o').
Proof.
intros ly S W m m' md HA h o' HAR HS HBL H1 H2 KO KW Vo Ho.
pose proof asan_consts as (C1 & _).
pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2, H2.
pose proof HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18
  & S19 & S20 & S21 & S22 & S23 & S24).
assert (Hvm : forall a n v, HA <= a -> (a + Z.of_nat n <= HA + 32 \/ HA + 40 <= a) -> a + Z.of_nat n <= HA + 96 ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v).
{ intros a n v Ha Hn1 Hn2 Hv. apply (akept_vm W m); [|exact Hv].
  intros x Hx. apply KO. split; [clear - Hx Ha Hn2 Hg1 Hg2 H1 H2; lia | clear - Hx Hn1; lia]. }
assert (KL : forall LA l lines, alist_at B ly S W m LA l lines ->
  (HA + 40 <= LA \/ LA + 16 <= HA + 32) -> HA <= LA -> LA + 16 <= HA + 96 ->
  (forall b, In b (alist_blks l) -> In b (ablocks B ly S)) -> alist_at B ly S W m' LA l lines).
{ intros LA l lines HL Hl1 Hl2 Hl3 HBl.
  apply (alist_at_kept B ly S W m); [exact HL | | exact HBl].
  intros r Hr x Hx. apply KO.
  refine (dk_alist_fp_out ly S W m md LA l lines HA HAR HL H1 _ _ r Hr x Hx); [unfold ASRC; exact H2|].
  intros y Hy. split; [clear - Hy Hl2 Hl3 Hg1 Hg2 H1 H2; lia | clear - Hy Hl1; lia]. }
unfold dk_setoff, asrc_at.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad hs_expected
  hs_held].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S1]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S2]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S3]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S4]|].
split; [intros i Hi; apply KW; exact (S5 i Hi)|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|]. split; [exact S9|].
split; [apply KL; [exact S10 | right; lia | lia | lia |
  intros b Hb; apply HBL; right; apply in_or_app; left; exact Hb]|].
split; [exact Vo|].
split; [apply Hvm; [lia | right; lia | cbn; lia | exact S12]|].
split; [apply Hvm; [lia | right; lia | cbn; lia | exact S13]|].
split; [apply Hvm; [lia | right; lia | cbn; lia | exact S14]|].
split; [right; exact Ho|].
split; [exact S16|]. split; [exact S17|]. split; [exact S18|]. split; [exact S19|].
split.
{ apply (akept_garr8 W m); [|exact S20]. intros x Hx. apply KO.
  unfold bzs in Hx. rewrite length_map, S19 in Hx.
  apply (dk_blk_out ly S W m md (hs_partial h) APARTIAL x HA HAR S18); [|exact H1 | unfold ASRC; exact H2].
  pose proof (dk_req_ge APARTIAL) as Hrq. clear - Hx Hrq. lia. }
split; [exact S21|].
split; [apply KL; [exact S22 | left; lia | lia | lia |
  intros b Hb; apply HBL; right; apply in_or_app; right; apply in_or_app; left; exact Hb]|].
split; [apply KL; [exact S23 | left; lia | lia | lia |
  intros b Hb; apply HBL; right; apply in_or_app; right; apply in_or_app; right; exact Hb]|].
exact S24.
Qed.

(* DMEM across the store: the memory m2 keeps every byte off [HA + 32, HA + 40), which holds o' *)
Lemma dk_dmem_off : forall cx ly1 S1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 m2 md2 o',
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
(forall a, dk_out (dHA RG cx) a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
val_mem SEGS (arm W1 m2) (dHA RG cx + 32) 8 o' ->
(exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r))) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k1 e1 (dk_setoff h1 o') s' out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 m2 md2 o' Hst Htop HG1 HG2 Hj Hno Hoc HM HJ2 KV KP Vo Ho.
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof asan_consts as (C1 & _).
assert (Hj3 : Z.of_nat (dxj cx) <= 3) by (clear - Hj; lia).
assert (HAb : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 4 * ASRC)
  by (unfold dHA, ASRC; clear - Hj3; lia).
destruct HAb as (HA1 & HA2).
assert (KB : forall a, dk_out (dHA RG cx) a -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha. split; [exact (KV a Ha)|]. unfold arm. apply writable_kept. exact (KP a). }
assert (KW : forall a, writable_at SEGS (arm W1 m1) a -> writable_at SEGS (arm W1 m2) a)
  by (intros a; unfold arm; apply writable_kept; exact (KP a)).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (INB : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1))
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (SAO : forall x, dxSA cx <= x < dxSA cx + AENT -> dk_out (dHA RG cx) x).
{ intros x Hx. apply (dk_blk_out ly1 S1 W1 m1 md1 (dxG cx) ATABLE x _ HAR HTB); [|exact HA1 | exact HA2].
  rewrite RQT. unfold ATABLE, AENT in Hx, HG2 |- *. clear - Hx HG1 HG2. lia. }
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _).
unfold DMEM. rewrite Hno, Hoc.
split; [exact HJ2|].
split.
{ intros a Ha. pose proof (pa_img_range a (dr_rom_img a Ha)) as Hai.
  rewrite KV; [exact (Hrom a Ha)|]. split; [clear - Hai; lia|]. intros Hx. apply (HGR a); [|exact Ha].
  apply dk_inG. clear - Hx HA1 HA2; lia. }
split; [intros a Ha1 Ha2 Ha3 Hp; apply KP; exact (Hpres a Ha1 Ha2 Ha3 Hp)|].
split; [exact Hframes|].
split.
{ apply (dk_frame_kept cx W1 m1 W1 m2); [|exact HFR]. intros a Ha. apply KB.
  unfold ESTACK in Hst. split; [clear - Ha Hst Htop C1; lia | clear - Ha Hst HA2 Hg2 C1; lia]. }
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx. apply KB. apply SAO.
  rewrite (dk_entry_len e1 Hpad1 Hpad2) in Hx. unfold AENT. clear - Hx; lia. }
split; [apply (akept_awr W1 m1); [intros x Hx; apply KB; apply SAO; exact Hx | exact Hawr]|].
split.
{ apply (dk_aentry_okx_kept ly1 S1 W1 m1); [exact HOKX | | intros b Hb; apply INB; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KB. exact (dk_aentry_fp_out ly1 S1 W1 m1 md1 e1 _ HAR HOKX HA1 HA2 r Hr x Hx). }
split.
{ apply (dk_asrc_off ly1 S1 W1 m1 m2 md1); [exact HAR | exact Hsrc | | exact HA1 | exact HA2 | exact KB | exact KW
    | exact Vo | exact Ho].
  intros b Hb. apply INB. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Ho'). exists f, o.
  assert (Hij' : Z.of_nat i <> Z.of_nat (dxj cx)) by (clear - Hij; lia).
  assert (Hi3 : Z.of_nat i <= 3) by (clear - Hi; lia).
  split; [|split; [|exact Ho']]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx; apply KB;
  unfold dk_out, dHA; unfold ASRC in Hx, Hg2 |- *; cbn in Hx;
  (split; [clear - Hx Hg1 Hg2 Hi3; lia | clear - Hx Hij' Hj3 Hi3; lia]). }
split.
{ intros x Hx Hn. destruct (Hgsk x Hx Hn) as [A1 A2].
  assert (Hxo : dk_out (dHA RG cx) x)
    by (unfold dk_out; unfold ASRC in Hx, Hg2, Hn; split; [clear - Hx Hg1 Hg2; lia | clear - Hn; lia]).
  destruct (KB x Hxo) as [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1); [exact Hout | |
    intros b Hb; apply INB; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KB. exact (dk_aout_fp_out ly1 S1 W1 m1 md1 _ _ _ _ _ _ _ HAR Hout HA1 HA2 r Hr x Hx). }
split; [exact Hlivout | exact Hperm].
Qed.

Let DROPENTRY :
forall (W : world SEGS) regs mem SA HA pv v0n pn off buf used v0s n,
alloc_ceiling <= spZ regs -> spZ regs + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regs ->
spZ regs mod 16 = 0 ->
(forall o, 192 <= o < 200 -> writable_at SEGS (arm W mem) (spZ regs + o)) ->
getr regs 21 = w64 SHADOW_OFF -> getr regs 23 = w64 HA -> getr regs 19 = w64 n ->
1 <= n <= 16384 ->
0x10000 <= HA -> HA + 96 <= 0x5fb000 -> HA mod 8 = 0 ->
(forall o, 16 <= o < 40 -> writable_at SEGS (arm W mem) (HA + o)) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF HA 96 ->
val_mem SEGS (arm W mem) (HA + 16) 8 pv -> val_mem SEGS (arm W mem) (HA + 24) 4 pn ->
val_mem SEGS (arm W mem) (HA + 32) 8 off -> 0 <= pn < 2 ^ 32 -> 0 <= off < 2 ^ 64 ->
4096 <= SA -> SA + 56 <= alloc_ceiling ->
(forall o, 24 <= o < 32 -> writable_at SEGS (arm W mem) (SA + o)) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF SA 56 ->
val_mem SEGS (arm W mem) (SA + 16) 8 buf -> val_mem SEGS (arm W mem) (SA + 24) 8 used ->
0 <= used < 2 ^ 64 -> in_app SA 56 ->
4096 <= pv -> pv + 16 <= alloc_ceiling -> pv mod 8 = 0 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF pv 16 ->
val_mem SEGS (arm W mem) pv 8 v0s -> val_mem SEGS (arm W mem) (pv + 8) 8 v0n ->
0 <= v0s < 2 ^ 64 -> 0 <= v0n < 2 ^ 64 -> in_app pv 16 ->
4096 <= buf -> buf + 1 <= alloc_ceiling -> buf mod 8 = 0 ->
val_mem SEGS (arm W mem) (spZ regs + 32) 8 (HA + 24) ->
val_mem SEGS (arm W mem) (spZ regs + 40) 8 (shadow_addr (HA + 24)) ->
val_mem SEGS (arm W mem) (spZ regs + 48) 8 (SA + 24) ->
val_mem SEGS (arm W mem) (spZ regs + 56) 8 SA ->
val_mem SEGS (arm W mem) (spZ regs + 64) 8 (SA + 32) ->
val_mem SEGS (arm W mem) (spZ regs + 80) 8 (shadow_addr (HA + 16)) ->
val_mem SEGS (arm W mem) (spZ regs + 176) 8 (shadow_addr SA) ->
val_mem SEGS (arm W mem) (spZ regs + 192) 8 (shadow_addr (HA + 32)) ->
val_mem SEGS (arm W mem) (spZ regs + 200) 8 (SA + 16) ->
val_mem SEGS (arm W mem) (spZ regs + 208) 8 (SA + 8) ->
val_mem SEGS (arm W mem) (spZ regs + 216) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W mem) (spZ regs + 224) 8 (shadow_addr (SA + 24)) ->
(HA + 96 <= SA \/ SA + 56 <= HA) -> (HA + 96 <= pv \/ pv + 16 <= HA) ->
(SA + 56 <= pv \/ pv + 16 <= SA) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (dr_extra SA pv v0n pn off buf used v0s))) ss_drop
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_fed)) mem (seg_rom SEGS)))
/\ sh_ok SEGS BxD SHD (Eimg (Ereg regs (dr_extra SA pv v0n pn off buf used v0s))) (arm W mem) := drop_entry.


(* The write obligation of both runs: the five regions of ss_drop (and of the state at the test): the frame slot
   192(sp) is a byte of drain's own window, the two g_s windows are bytes of G_DR, s->used is a byte of the
   table block in the footprint, and the vector region has no window. *)
Ltac dk_awr Usp Hsp UHA USA HTB RQT HSAlo HSAhi HDS HDF HAb :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite Usp, Hsp in Hx;
    left; split; [left; clear - Hx HDS HDF; lia | clear - Hx; lia] |];
  apply awr_ok_x_cons_g;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite UHA in Hx;
    apply dk_inG; unfold ASRC; clear - Hx HAb; lia |];
  apply awr_ok_x_cons_g;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite UHA in Hx;
    apply dk_inG; unfold ASRC; clear - Hx HAb; lia |];
  apply awr_ok_x_cons;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USA in Hx;
    left; split; [|clear - Hx; lia]; right; left; split;
    [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; clear - Hx; lia
    | do 2 eexists; split; [exact HTB | rewrite RQT; clear - Hx HSAlo HSAhi; lia] ] |];
  apply awr_ok_x_cons; [|apply awr_ok_x_nil];
  intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; clear - Hx; lia.

Lemma drop_keep : forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DE B MT MMAX RG cx s1 D W1 c1 -> dwhole s1 = false ->
(forall W2 c2, DDM B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 c1 HB HDE Hwh Hddm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
(* ---- DE's witnesses ---- *)
destruct HDE as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hcfg & Hsp & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & HFR & M56 & M64 & M48 & M200 & M32 & M80 & M40 & M192 &
  Hn0 & Hjunk & HMEM & HnoNul & Hused & HSAME & Hcap & HU & Hskip & HKT & HKA & Heintr & Hpend & Hoff & Hstate &
  Hen & Hecap & HHIST & HRS & Hfut & HBUD).
pose proof HMEM as (HJ & _ & _ & _ & _ & Hgarr & Hawr & HOKX & Hsrc & _ & _ & _ & _ & Hperm).
pose proof HFR as (F208 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F224 & F216 & F176 & _).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & HBrest).
assert (Hjj : (dxj cx < 4)%nat) by exact (proj1 (proj2 (proj2 (proj2 HBrest)))). clear HBrest.
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
fold (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HJp : forall x, dsp0 cx - DRAIN_STK <= x < dsp0 cx -> apresent (w_H W1) m1 x).
{ pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJq & _).
  intros x Hx. apply HJq. clear - Hx. lia. }
assert (HSP1 : alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\
  spZ regs1 mod 16 = 0).
{ rewrite Hsp, HDF. rewrite HDS in Hslo. clear - Hceil Hslo Hshi H47 Hal16 C1.
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Zminus_mod, Hal16. reflexivity. }
(* ---- the relay's table block and the entry at SA ---- *)
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & _).
rewrite RQT in HGceil, HGia.
unfold ATABLE, AENT in HSAhi.
assert (HSAb : 4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling) by (clear - HSAlo HSAhi HG4096 HGceil; lia).
(* ---- g_s[j] ---- *)
pose proof HGSB as (HGS1 & HGS2 & HGS3). unfold ASRC in HGS2.
assert (HAb : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 384 /\ dHA RG cx mod 8 = 0).
{ unfold dHA. assert (Hj3 : Z.of_nat (dxj cx) <= 3) by (clear - Hjj; lia).
  split; [unfold ASRC; clear - Hj3; lia|]. split; [unfold ASRC; clear - Hj3; lia|].
  rewrite Z.add_mod, HGS3 by lia.
  replace (ASRC * Z.of_nat (dxj cx)) with ((12 * Z.of_nat (dxj cx)) * 8) by (unfold ASRC; ring).
  rewrite Z_mod_mult. reflexivity. }
pose proof Hsrc as (_ & _ & _ & _ & Aawr & _ & _ & _ & _ & Apend & Aoff & _ & _ & _ & Aoffr & _).
pose proof Apend as (L1 & L2 & _ & _ & L5 & L6 & _ & _ & L9).
pose proof HRS as (_ & _ & RS_gr & RS_wf & _ & _ & RS_pe).
(* ---- the pending list: its head record r0 ---- *)
assert (Erecs : exists r0 rs0, hl_recs (hs_pending h1) = r0 :: rs0).
{ destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:E0; [|exists r0, rs0; reflexivity].
  exfalso. apply RS_pe. rewrite <- Hpend. rewrite ?E0. reflexivity. }
destruct Erecs as (r0 & rs0 & Erecs).
assert (Hpn : hl_n (hs_pending h1) = Z.of_nat (S (length rs0))) by (unfold hl_n; rewrite Erecs; reflexivity).
assert (Hpcap : 0 < hl_cap (hs_pending h1)) by (clear - L5 Hpn; lia).
destruct L6 as [(Hc0 & _) | (_ & HVin & _ & HVg)]; [clear - Hc0 Hpcap; lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 _ _ HAR HVin) as (HV16 & HV4096 & HVceil & HVia & _).
assert (RQV : req_size (AREC * hl_cap (hs_pending h1)) = AREC * hl_cap (hs_pending h1))
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by (unfold AREC; clear - Hpcap; lia); reflexivity).
rewrite RQV in HVceil, HVia. unfold AREC in HVceil.
assert (HVg' := HVg). rewrite Erecs in HVg'.
destruct (dr_head_fields (arm W1 m1) _ r0 rs0 _ HVg') as (HV0 & HV8). clear HVg' HVg.
assert (L9' := L9). rewrite Erecs in L9'. apply Forall_inv in L9'. destruct L9' as (Hr0in & _).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 _ _ HAR Hr0in) as (_ & Hr04096 & Hr0ceil & _).
pose proof (req_size_pos (Z.of_nat (length (snd r0)) + 1) ltac:(lia)) as (_ & Hr0rq).
assert (Hr0b : 4096 <= fst r0 /\ fst r0 + Z.of_nat (length (snd r0)) + 1 <= alloc_ceiling)
  by (clear - Hr04096 Hr0ceil Hr0rq; lia).
rewrite unsigned_lit_small in HV0 by (clear - Hr0b C1; lia).
rewrite unsigned_lit_small in HV8 by (clear - Hr0b C1; lia).
assert (Hoffr : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
{ destruct Aoffr as [(Hx & _) | (r & rs & Hrr & Hx)]; [rewrite Erecs in Hx; discriminate|].
  rewrite Erecs in Hrr. injection Hrr as <- <-. exact Hx. }
clear Aoffr.
assert (Hdh : dhead s1 = bzs (snd r0)) by (unfold dhead; rewrite <- Hpend, Erecs; reflexivity).
assert (Hdhl : Z.of_nat (length (dhead s1)) = Z.of_nat (length (snd r0)))
  by (rewrite Hdh; unfold bzs; rewrite length_map; reflexivity).
assert (Hdn : dnum s1 <= Z.of_nat (length (dhead s1)) - drain_b_c.ds_off s1) by (unfold dnum; apply Z.le_min_l).
assert (Hkeep : drain_b_c.ds_off s1 + dnum s1 < Z.of_nat (length (snd r0))).
{ unfold dwhole in Hwh. apply Z.eqb_neq in Hwh. clear - Hwh Hdn Hdhl. lia. }
(* ---- the relay entry's buffer ---- *)
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _ & Hcapr & HUlen & Husedr & Hbufc & _).
assert (Hulen0 : 0 <= ulen s1) by (unfold ulen; lia).
assert (Hcapb : 4096 <= re_cap e1 <= 16384) by (clear - Hcapr Hcap RS_gr Hulen0; destruct Hcapr as [X|[X|X]]; lia).
clear Hcapr.
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & HJlen & Hbuf8)]; [clear - Hc0 Hcapb; lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 _ _ HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - Hcapb; lia); reflexivity).
rewrite RQC in HBceil, HBia.
destruct (dr_entry_fields (arm W1 m1) (dxSA cx) e1 Hpad1 Hgarr) as (MBUF & MUSED).
assert (HUb : 0 <= re_used e1 <= 16384) by (clear - HUlen Husedr Hcapb; lia).
rewrite unsigned_lit_small in MBUF by (clear - HB4096 HBceil Hcapb C1; lia).
rewrite unsigned_lit_small in MUSED by (clear - HUb; lia).
assert (Hnc : dnum s1 <= drain_b_c.ds_cap s1 - ulen s1) by (unfold dnum; apply Z.le_min_r).
assert (Hnb : 1 <= dnum s1 <= 16384) by (clear - Hn0 Hnc Hulen0 Hcap Hcapb; lia).
(* ---- the rest of DROPENTRY's premises ---- *)
assert (FW : forall o, 192 <= o < 200 -> writable_at SEGS (arm W1 m1) (spZ regs1 + o)).
{ intros o Ho. unfold arm. apply (apresent_writable SEGS). apply HJp. rewrite Hsp, HDF, HDS. clear - Ho; lia. }
assert (HAw : forall o, 16 <= o < 40 -> writable_at SEGS (arm W1 m1) (dHA RG cx + o))
  by (intros o Ho; apply Aawr; unfold ASRC; clear - Ho; lia).
assert (HSw : forall o, 24 <= o < 32 -> writable_at SEGS (arm W1 m1) (dxSA cx + o))
  by (intros o Ho; apply Hawr; unfold AENT; clear - Ho; lia).
assert (RAH : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (dHA RG cx) 96).
{ apply (azs_range_addressable B LAWS ly1 S1 W1 m1 md1); [exact HAR|].
  destruct HGSZ as (r & Hin & H8 & Hlo & Hhi). exists r. unfold ASRC in Hhi.
  split; [exact Hin|]. split; [exact H8|]. clear - Hlo Hhi HAb; split; lia. }
assert (RAS : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (dxSA cx) 56)
  by (apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE);
      [exact HAR | exact HTB | clear - HSAlo; lia | rewrite RQT; clear - HSAhi; lia]).
assert (RAV : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (hl_v (hs_pending h1)) 16)
  by (apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR HVin);
      [lia | rewrite RQV; unfold AREC; clear - Hpcap; lia]).
assert (IAS : in_app (dxSA cx) 56)
  by (apply (in_app_sub (dxG cx) 896); [exact HGia | clear - HSAlo; lia | lia | clear - HSAhi; lia]).
assert (IAV : in_app (hl_v (hs_pending h1)) 16)
  by (apply (in_app_sub (hl_v (hs_pending h1)) (AREC * hl_cap (hs_pending h1)));
      [exact HVia | lia | lia | unfold AREC; clear - Hpcap; lia]).
assert (HV8a : hl_v (hs_pending h1) mod 8 = 0) by (apply dk_mod8; exact HV16).
assert (HB8a : re_buf e1 mod 8 = 0) by (apply dk_mod8; exact HB16).
assert (L2' : val_mem SEGS (arm W1 m1) (dHA RG cx + 24) 4 (hl_n (hs_pending h1)))
  by (replace (dHA RG cx + 24) with (dHA RG cx + 16 + 8) by lia; exact L2).
assert (HHA1 : 0x10000 <= dHA RG cx) by (clear - HAb HGS1; lia).
assert (HHA2 : dHA RG cx + 96 <= 0x5fb000) by (clear - HAb HGS2; lia).
assert (HPN : 0 <= hl_n (hs_pending h1) < 2 ^ 32) by (clear - L5 Hpn; lia).
assert (HOFF : 0 <= hs_off h1 < 2 ^ 64) by (clear - Hoffr Hr0b C1; lia).
assert (HUSD : 0 <= re_used e1 < 2 ^ 64) by (clear - HUb; lia).
assert (HPV : hl_v (hs_pending h1) + 16 <= alloc_ceiling) by (clear - HVceil Hpcap; lia).
assert (HV0r : 0 <= fst r0 < 2 ^ 64) by (clear - Hr0b C1; lia).
assert (HV8r : 0 <= Z.of_nat (length (snd r0)) < 2 ^ 64) by (clear - Hr0b C1; lia).
assert (HBUF : re_buf e1 + 1 <= alloc_ceiling) by (clear - HBceil Hcapb; lia).
assert (FR : forall off v, val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + off) 8 v ->
  val_mem SEGS (arm W1 m1) (spZ regs1 + off) 8 v) by (intros off v Hv; rewrite Hsp; exact Hv).
(* ---- the three separations ---- *)
assert (DA1 : dHA RG cx + 96 <= dxSA cx \/ dxSA cx + 56 <= dHA RG cx).
{ apply dr_apart_of_disj; [lia | lia |]. intros x Hx1 Hx2.
  apply (dr_blk_noimg ly1 S1 W1 m1 md1 (dxG cx) ATABLE x HAR HTB); [rewrite RQT; clear - Hx2 HSAlo HSAhi; lia|].
  apply dk_gs_img. unfold ASRC. clear - Hx1 HAb; lia. }
assert (DA2 : dHA RG cx + 96 <= hl_v (hs_pending h1) \/ hl_v (hs_pending h1) + 16 <= dHA RG cx).
{ apply dr_apart_of_disj; [lia | lia |]. intros x Hx1 Hx2.
  apply (dr_blk_noimg ly1 S1 W1 m1 md1 _ _ x HAR HVin); [rewrite RQV; unfold AREC; clear - Hx2 Hpcap; lia|].
  apply dk_gs_img. unfold ASRC. clear - Hx1 HAb; lia. }
assert (HNE : (dxG cx, ATABLE) <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))).
{ intros Heq. pose proof (Permutation_NoDup Hperm (dk_ablocks_nodup _ _ _ _ _ HAR)) as HND.
  apply List.NoDup_cons_iff in HND as [HGnot _]. apply HGnot. rewrite Heq.
  apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left.
  unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0)) by (unfold AREC; clear - Hpcap; lia). left. reflexivity. }
assert (DA3 : dxSA cx + 56 <= hl_v (hs_pending h1) \/ hl_v (hs_pending h1) + 16 <= dxSA cx).
{ destruct (dk_blk_apart _ _ _ _ _ _ _ _ _ HAR HTB HVin HNE) as [X|X]; rewrite ?RQT, ?RQV in X;
  try unfold AREC in X; [left | right]; clear - X HSAlo HSAhi Hpcap; lia. }
destruct (DROPENTRY W1 regs1 m1 (dxSA cx) (dHA RG cx) (hl_v (hs_pending h1)) (Z.of_nat (length (snd r0)))
  (hl_n (hs_pending h1)) (hs_off h1) (re_buf e1) (re_used e1) (fst r0) (dnum s1)
  (proj1 HSP1) (proj1 (proj2 HSP1)) (proj1 (proj2 (proj2 HSP1))) (proj2 (proj2 (proj2 HSP1))) FW
  R21 R23 R19 Hnb HHA1 HHA2 (proj2 (proj2 HAb))
  HAw RAH L1 L2' Aoff HPN HOFF
  (proj1 HSAb) (proj2 HSAb) HSw RAS MBUF MUSED HUSD IAS
  HV4096 HPV HV8a RAV HV0 HV8 HV0r HV8r IAV
  HB4096 HBUF HB8a
  (FR _ _ M32) (FR _ _ M40) (FR _ _ M48) (FR _ _ M56) (FR _ _ M64) (FR _ _ M80)
  (FR _ _ F176) (FR _ _ M192) (FR _ _ M200) (FR _ _ F208) (FR _ _ F216) (FR _ _ F224)
  DA1 DA2 DA3) as [HS SHOK].
clear DA1 DA2 DA3 HNE FR.
(* ---- the symbolic run to the 0x83600 test ---- *)
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_fed)) with (Z_to_bv 64 (BASE + A_dr_fed)).
remember (Eimg (Ereg regs1 (dr_extra (dxSA cx) (hl_v (hs_pending h1)) (Z.of_nat (length (snd r0)))
  (hl_n (hs_pending h1)) (hs_off h1) (re_buf e1) (re_used e1) (fst r0)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_v (hs_pending h1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat (length (snd r0))))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (hl_n (hs_pending h1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (hs_off h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (fst r0))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (UHA : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (USA : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HS as HS0.
paj_run_tok RUN HS HJ SHOK DRspan. { dk_awr Usp Hsp UHA USA HTB RQT HSAlo HSAhi HDS HDF HAb. }
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ?x)) |- _ =>
  rename Hf into HFr1; rename x into msB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) _ |- _ => rename Hg into GR1 end.
match goal with Hf : frame_of _ _ m1 _ |- _ => clear Hf end.
assert (U19 : U E (SOff 19 0) = dnum s1)
  by (apply U_atom; [rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl), R19; reflexivity | clear - Hnb; lia]).
assert (U36 : U E (SOff 36 0) = hs_off h1) by (apply U_atom; [exact E36 | exact HOFF]).
assert (U34 : U E (SOff 34 0) = Z.of_nat (length (snd r0))) by (apply U_atom; [exact E34 | exact HV8r]).
assert (UADD : U E (SAlu ALU_ADD (SOff 19 0) (SOff 36 0)) = dnum s1 + hs_off h1)
  by (apply dk_U_add; [exact U19 | exact U36 | clear - Hnb HOFF Hkeep Hoff Hr0b C1; lia]).
psrr_branch_tok RUN BR HS SHOK DRspan.
2: { (* the test holds: off + n = v[0].n, i.e. dwhole s1 = true, refuted *)
  exfalso. rewrite branch_ne_U, UADD, U34 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  clear - Hc Hkeep Hoff. lia. }
(* the test fails: no drop; the fall-through to the join 0x83668 *)
paj_run_to_tok RUNTO HS HJ SHOK DRspan A_dr_join. { dk_awr Usp Hsp UHA USA HTB RQT HSAlo HSAhi HDS HDF HAb. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
  rename Hf into HFr2 end.
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) _ |- _ => rename Hg into GR2 end.
match goal with Hf : frame_of _ _ (ms_mem msB) _ |- _ => clear Hf end.
match type of HFr2 with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr2 end.
(* ---- the regions at the join: the frame, h->pending.n, the new h->pending_off and s->used ---- *)
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF0. cbn [ms_mem restrict] in RF0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF1. cbn [ms_mem restrict] in RF1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RF2. cbn [ms_mem restrict] in RF2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RF3. cbn [ms_mem restrict] in RF3.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS0 eq_refl) as RI0. cbn [ms_mem restrict mkst] in RI0.
set (e192 := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 32) (SLit 3)) (SOff 21 0)).
pose proof (slot_of_region E _ (spZ regs1) _ _ _ _ _ 192 e192 (U E e192) RF0 Usp ltac:(dk_in)
  (dk_den E e192) (dk_Urange E e192)) as VB192.
pose proof (slot_of_region E _ (spZ regs1) _ _ _ _ _ 192 e192 (U E e192) RI0 Usp ltac:(dk_in)
  (dk_den E e192) (dk_Urange E e192)) as VA192.
pose proof (field_of_region E _ 23 (dHA RG cx) _ _ _ _ _ 24 4%N (SOff 35 0) (hl_n (hs_pending h1)) RF1 UHA
  ltac:(dk_in) ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; clear - HPN; lia) ltac:(cbn; lia)) as VB24.
pose proof (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 24 8%N (SOff 38 0) (re_used e1) RF3 USA
  ltac:(dk_in) ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; clear - HUSD; lia) ltac:(cbn; lia)) as VBU.
pose proof (field_of_region E _ 23 (dHA RG cx) _ _ _ _ _ 32 8%N (SAlu ALU_ADD (SOff 19 0) (SOff 36 0))
  (drain_b_c.ds_off s1 + dnum s1) RF2 UHA ltac:(dk_in) ltac:(rewrite dk_den, UADD, Hoff, Z.add_comm; reflexivity)
  ltac:(cbn; clear - Hnb Hoff HOFF Hkeep Hr0b C1; lia) ltac:(cbn; lia)) as VO.
clear RF0 RF1 RF2 RF3 RI0.
(* ---- every byte off the new h->pending_off is the cut's ---- *)
assert (KEEPM : forall x, dk_out (dHA RG cx) x -> aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
{ intros x (Hx0 & Hxo).
  destruct (dk_in_dec (spZ regs1 + 192) 8 x) as [Hw | Hw].
  { exact (dk_aview_of_vm W1 m1 (ms_mem msF) (spZ regs1 + 192) 8 (U E e192) x VA192 VB192 Hw). }
  destruct (dk_in_dec (dHA RG cx + 24) 4 x) as [Hw2 | Hw2].
  { exact (dk_aview_of_vm W1 m1 (ms_mem msF) (dHA RG cx + 24) 4 (hl_n (hs_pending h1)) x L2' VB24 Hw2). }
  destruct (dk_in_dec (dxSA cx + 24) 8 x) as [Hw3 | Hw3].
  { exact (dk_aview_of_vm W1 m1 (ms_mem msF) (dxSA cx + 24) 8 (re_used e1) x MUSED VBU Hw3). }
  rewrite (aview_kept_out E _ (w_H W1) (ms_mem msB) (ms_mem msF) HFr2 x Hx0).
  2: { intros (r & Hin & Hr). cbn [In] in Hin.
       destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UHA, ?USA in Hr;
       clear - Hr Hw Hw2 Hw3 Hxo; lia. }
  apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msB) HFr1 x Hx0).
  intros (r & Hin & Hr). cbn [ss_mem ss_drop dr_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
  cbn [dr_r_frame dr_r_gsA dr_r_gsC dr_r_sa dr_r_vec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?Usp, ?UHA, ?USA in Hr; clear - Hr Hw Hw2 Hw3 Hxo; lia. }
assert (PRESM : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
  by (intros x Hp; exact (apresent_grows _ _ _ x GR2 (apresent_grows _ _ _ x GR1 Hp))).
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 (ms_mem msF) x).
{ intros x Hx. split.
  - apply KEEPM. rewrite HDF in Hx. rewrite HDS in Hslo.
    split; [clear - Hx Hshi H47 Hceil Hslo C1; lia | clear - Hx Hslo Hceil HAb HGS2 C1; lia].
  - unfold arm. apply writable_kept. exact (PRESM x). }
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
prreg HS (27%bv : bv 5) P27.
clear HS SHOK.
match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
(* ---- the round's future: list_drop asks nothing in this arm ---- *)
destruct Hfut as (tl2 & Hdl & Htl).
rewrite (dm_ddrop_keep s1 a Hwh) in Hdl, Htl.
change (RelayRunT.nret YO0i.sptr []) with 0%nat in Hdl. rewrite Nat.add_0_r in Hdl. rewrite Hwh in Hdl.
rewrite Htl, app_nil_l in HBUD.
set (o' := drain_b_c.ds_off s1 + dnum s1) in VO.
assert (Ho' : exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r)))
  by (exists r0, rs0; split; [exact Erecs | unfold o'; clear - Hkeep Hoff Hoffr Hnb; lia]).
(* ---- the history at p = 0 ---- *)
assert (HDH : DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D)
  (dk_setoff h1 o') LB1 (Z.of_nat (length (drl s1)))).
{ pose proof HHIST as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  assert (Hps : pstream s1 = ddata s1 ++ pstream (dnext (dlive cx) (dxmx cx) s1))
    by exact (dm_ps_split RG HGSB cx s1 RS_wf ltac:(clear - Hn0; lia)).
  pose proof (dm_chunk_le RG (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as Hcl.
  pose proof (dm_lines_le RG (drain_b_c.ds_ref s1) (ddata s1)) as Hll.
  unfold DHIST.
  change (pstream (dsv cx s1)) with (pstream (dnext (dlive cx) (dxmx cx) s1)).
  change (drain_b_c.ds_ref (dsv cx s1)) with (feed (drain_b_c.ds_ref s1) (ddata s1)).
  change (drain_b_c.ds_no (dsv cx s1)) with (drain_b_c.ds_no s1).
  change (drain_b_c.ds_H (dsv cx s1)) with (drain_b_c.ds_H s1).
  change (drain_b_c.ds_en (dsv cx s1)) with (drain_b_c.ds_en s1 + Z.of_nat (length (dref s1))).
  split; [rewrite D1, Hps, app_assoc; reflexivity|].
  split; [rewrite D2, feed_app; reflexivity|].
  split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
  split; [exact D8|]. split; [exact D9|].
  rewrite Hps, length_app in D10, D11. unfold drl, dchunk, dref.
  split; [clear - D10 Hcl; lia | clear - D11 Hll; lia]. }
(* ---- the memory core, across the store ---- *)
assert (HMEM2 : DMEM B RG cx ly1 S1 W1 (ms_mem msF) mdF k1 e1 (dk_setoff h1 o') (dsv cx s1) out1 ev1
  (lines (dSTR cx) D) LB1).
{ apply (dk_dmem_off cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 (ms_mem msF) mdF o');
    [ clear - Hceil Hslo HES HDF HDS; lia | clear - Hshi H47; lia | exact HSAlo | exact HSAhi | exact Hjj
    | reflexivity | reflexivity | exact HMEM | exact HJ | exact KEEPM | exact PRESM | exact VO | exact Ho' ]. }
(* ---- DDM ---- *)
assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> (k < 32)%nat ->
  Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
{ intros r k Hr Hk Hkr. rewrite Hr. apply EREG; assumption. }
assert (VF : forall off v, 0 <= off -> off + 8 <= 336 ->
  val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + off) 8 v ->
  val_mem SEGS (arm W1 (ms_mem msF)) (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply (akept_vm W1 m1); [|exact Hv].
  intros y Hy. apply KFR. rewrite HDF in Hy |- *. change (Z.of_nat 8) with 8 in Hy. clear - Hy Ho1 Ho2. lia. }
apply (Hddm W1). unfold DDM.
exists (ms_regs msF), ly1, S1, (ms_mem msF), mdF, k1, e1, (dk_setoff h1 o'), out1, ev1, LB1, spent, jb, a,
  (drain_b_c.da_out a), (drain_b_c.da_hp a), (drain_b_c.da_keys a), tl2.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ at 1; rewrite (RK _ 2%nat P2) by (first [lia | reflexivity]); exact Hsp|].
split; [rewrite (RK _ 3%nat P3) by (first [lia | reflexivity]); exact R3|].
split; [rewrite (RK _ 4%nat P4) by (first [lia | reflexivity]); exact R4|].
split; [rewrite (RK _ 18%nat P18) by (first [lia | reflexivity]); exact R18|].
split; [rewrite (RK _ 9%nat P9) by (first [lia | reflexivity]); exact R9|].
split; [rewrite (RK _ 8%nat P8) by (first [lia | reflexivity]); exact R8|].
split; [rewrite (RK _ 21%nat P21) by (first [lia | reflexivity]); exact R21|].
split; [rewrite (RK _ 23%nat P23) by (first [lia | reflexivity]); exact R23|].
split; [rewrite (RK _ 19%nat P19) by (first [lia | reflexivity]); exact R19|].
split; [rewrite P22, E32; reflexivity|].
split; [rewrite P25, USA; reflexivity|].
split; [rewrite P26, USA; reflexivity|].
split; [rewrite P27, USA; reflexivity|].
split; [exact (dk_frame_kept cx W1 m1 W1 (ms_mem msF) KFR HFR)|].
split; [apply VF; [lia | lia | exact M56]|].
split; [apply VF; [lia | lia | exact M64]|].
split; [apply VF; [lia | lia | exact M48]|].
split; [apply VF; [lia | lia | exact M200]|].
split; [exact Hn0|]. split; [clear - Hnb; lia|]. split; [exact Hjunk|].
split; [exact HMEM2|].
split; [exact HnoNul|]. split; [exact Hused|]. split; [exact HSAME|].
split; [exact Hcap|]. split; [exact HU|]. split; [exact Hskip|]. split; [exact HKT|]. split; [exact HKA|].
split; [exact Heintr|].
split; [unfold dnext; cbn [drain_b_c.ds_pend]; rewrite Hwh; exact Hpend|].
split; [unfold dnext; cbn [drain_b_c.ds_off]; rewrite Hwh; reflexivity|].
split; [exact Hstate|]. split; [exact Hen|]. split; [exact Hecap|].
split; [exact HDH|]. split; [exact HRS|]. split; [exact Hdl | exact HBUD].
Qed.

(* ================================================================================================
   The arm where the 0x83600 test HOLDS: the inlined list_drop(&h->pending, 0) - free(v[0].s) at
   0x83618 (afree_cf_rule over the walk journal, opened and closed), __asan_memmove(v, v + 16,
   16 (pending.n - 1)) at 0x83648 (amemmove_realizes through aj_gx_entry_at), h->pending.n -= 1 and
   h->pending_off = 0 - then the fall-through to the join 0x83668.  DROPENTRY is the Let above.
   ================================================================================================ *)


(* ---- byte helpers (W_drain_drop.v's dr_* copies, renamed) ---- *)
Lemma dw_nth_le_bytes : forall n z k, (k < n)%nat ->
nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma dw_le8_val : forall m a (w : word), garr8 SEGS m a (bzs (Mem.le8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hlen : (k < length (bzs (Mem.le8 w)))%nat) by (unfold bzs; rewrite length_map, Mem.length_le8; exact Hk).
rewrite (garr8_mbyte SEGS m a _ k H Hlen). f_equal.
assert (Hn : nth k (bzs (Mem.le8 w)) 0 = bz (nth k (Mem.le8 w) (Z_to_bv 8 0))).
{ unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by exact Hlen. apply List.map_nth. }
rewrite Hn.
unfold Mem.le8, word_to_le_bytes, bz. rewrite dw_nth_le_bytes by lia. rewrite Z_to_bv_bv_unsigned.
pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 8) with 64 by lia. rewrite (Z.mod_small (bv_unsigned w)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma dw_len_text_recs : forall l, length (concat (map text_rec l)) = (16 * length l)%nat.
Proof.
induction l as [|r l IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
Lemma dw_head_fields : forall m v (r0 : Z * list byte) rs0 junk,
garr8 SEGS m v (bzs (concat (map text_rec (r0 :: rs0)) ++ junk)) ->
val_mem SEGS m v 8 (bv_unsigned (Z_to_bv 64 (fst r0))) /\
val_mem SEGS m (v + 8) 8 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length (snd r0))))).
Proof.
intros m v r0 rs0 junk H.
cbn [map concat] in H. unfold text_rec at 1 in H. unfold bzs in H.
rewrite <- !app_assoc, map_app in H. apply garr8_app in H as [H1 H].
rewrite length_map, Mem.length_le8 in H. change (Z.of_nat 8) with 8 in H.
rewrite map_app in H. apply garr8_app in H as [H2 _].
split; [exact (dw_le8_val m v _ H1) | exact (dw_le8_val m (v + 8) _ H2)].
Qed.
Lemma dw_entry_fields : forall m SA e,
length (re_pad1 e) = 4%nat ->
garr8 SEGS m SA (bzs (entry_bytes e)) ->
val_mem SEGS m (SA + 16) 8 (bv_unsigned (Z_to_bv 64 (re_buf e))) /\
val_mem SEGS m (SA + 24) 8 (bv_unsigned (Z_to_bv 64 (re_used e))).
Proof.
intros m SA e Hp1 H. unfold entry_bytes, bzs in H.
rewrite map_app in H. apply garr8_app in H as [_ H].
rewrite length_map, Mem.length_le4 in H.
rewrite map_app in H. apply garr8_app in H as [_ H].
rewrite length_map, Mem.length_le4 in H.
rewrite map_app in H. apply garr8_app in H as [_ H].
rewrite length_map, Mem.length_le4 in H.
rewrite map_app in H. apply garr8_app in H as [_ H].
rewrite length_map, Hp1 in H.
replace (SA + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (SA + 16) in H by lia.
rewrite map_app in H. apply garr8_app in H as [H1 H].
rewrite length_map, Mem.length_le8 in H.
replace (SA + 16 + Z.of_nat 8) with (SA + 24) in H by lia.
rewrite map_app in H. apply garr8_app in H as [H2 _].
split; [exact (dw_le8_val m (SA + 16) _ H1) | exact (dw_le8_val m (SA + 24) _ H2)].
Qed.
Lemma dw_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & H1 & _ & H3). exists sg. split; [exact H1 | exact H3]. Qed.
Lemma dw_apart_of_disj : forall x nx y ny, 0 < nx -> 0 < ny ->
(forall a, x <= a < x + nx -> ~ (y <= a < y + ny)) -> x + nx <= y \/ y + ny <= x.
Proof.
intros x nx y ny Hx Hy H.
destruct (Z.le_gt_cases (x + nx) y) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases (y + ny) x) as [|H2]; [right; lia|].
exfalso. apply (H (Z.max x y)); lia.
Qed.

(* ---- two different live blocks are apart (W_drain_rest.v rs_pw_in2 / rs_blk_apart, renamed) ---- *)
Lemma dw_pw_in2 : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [In] in Hx, Hy. destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso; apply Hne; reflexivity.
- left. exact (HF y Hy).
- right. exact (HF x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.
Lemma dw_pw_nodup : forall l : list (Z * Z), (forall x, In x l -> 1 <= snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hpw; [apply List.NoDup_nil|].
destruct Hpw as [Hx Hl]. apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx. pose proof (Hx x Hin) as Z. pose proof (Hpos x (or_introl eq_refl)).
  unfold zdisjoint in Z. lia.
- apply IH; [intros y Hy; apply Hpos; right; exact Hy | exact Hl].
Qed.
Lemma dw_nodup_map_inj : forall {X Y} (f : X -> Y) (l : list X) x y,
List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z l IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|w ws Hz Hnd']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y Hnd' Hx Hy Hf)].
- exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
Qed.
Lemma dw_blk_apart : forall ly S (W : world SEGS) mem md p n q m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S W mem md p n q m HAR Hp Hq Hne.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof (dw_pw_nodup _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (dw_nodup_map_inj f _ _ _ Hnd Hp Hq E))).
destruct (dw_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold zdisjoint, f in X; cbn [fst snd] in X; lia.
Qed.
Lemma dw_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hp : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hp) as (_ & _ & _ & _ & _ & Hpw & _).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hk) as (_ & _ & _ & _ & _ & _ & Hk0).
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (dw_pw_nodup _ Hpos Hpw)).
Qed.
Lemma dw_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dw_req_pos : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dw_inG_gs : forall a, rg_s RG <= a < rg_s RG + 384 -> inG (G_DR B RG) a.
Proof. intros a Ha. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr, ASRC. cbn [fst snd]. lia. Qed.

(* a fact kept out of lia's sight (lia case-splits every disjunction in context) *)
Definition dw_hide (P : Prop) : Prop := P.
Lemma dw_hide_i : forall P : Prop, P -> dw_hide P.
Proof. intros P H. exact H. Qed.

Lemma dw_nodup_app_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
induction l1 as [|y l1 IH]; intros l2 x Hnd Hx Hx2; [destruct Hx|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hy Hnd].
destruct Hx as [<-|Hx]; [apply Hy; apply in_or_app; right; exact Hx2 | exact (IH l2 x Hnd Hx Hx2)].
Qed.
Lemma dw_nodup_app_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
induction l1 as [|y l1 IH]; intros l2 Hnd; [exact Hnd|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [_ Hnd]. exact (IH l2 Hnd).
Qed.

(* the trace owed after list_drop: every request asks a nonnegative size (W_drain_tr.v) *)
Lemma dw_dlfut_sizes : forall cx s1 ab jb o ha ks tl2,
  0 <= dxmx cx -> 0 <= drain_b_c.ds_cap s1 -> 0 <= drain_b_c.ds_ocap s1 -> 0 <= drain_b_c.ds_no s1 ->
  0 <= drain_b_c.ds_ka s1 ->
  0 <= drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
  0 <= pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
  dlfut cx (dnext (dlive cx) (dxmx cx) s1) ab (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
    (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl2 ->
  tr_sizes_ok tl2.
Proof.
intros cx s1 ab jb o ha ks tl2 Hmx Hc Ho Hn Hk He Hec HF.
apply (gs_dlfut_sizes cx (dnext (dlive cx) (dxmx cx) s1) ab (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1)
  (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl2 Hmx Ho); [| | | | | | exact HF].
- unfold dnext. cbn [drain_b_c.ds_cap]. exact Hc.
- unfold dnext, lrun. cbn [drain_b_c.ds_ocap].
  match goal with |- context [drain_b_c.lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
    exact (proj2 (sz_lines_run a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Ho)) end.
- unfold dnext. cbn [drain_b_c.ds_no]. lia.
- unfold dnext. cbn [drain_b_c.ds_en]. exact He.
- unfold dnext. cbn [drain_b_c.ds_ecap]. exact Hec.
- unfold dnext, lrun. cbn [drain_b_c.ds_ka].
  match goal with |- context [drain_b_c.lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
    exact (sz_lines_run_ka a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Hk) end.
Qed.

(* a region kept across a call that may change the world (W_frame.v region_kept_aview, two worlds) *)
Lemma dw_region_kept2 : forall E H H' (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H' m2) a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m2 n b lo hi wlo whi cs Hn Hav Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- apply Hw. exact Ha.
Qed.

(* an image byte stays writable when its presence is kept (W_lp_tail.v lpt_writable_img) *)
Lemma dw_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* errno lies in a writable segment (HERRW), so it is writable in every memory *)
Lemma dw_errno_writable : forall (W : world SEGS) (m : word -> option byte) i, 0 <= i < 4 ->
  writable_at SEGS (mrestrict (w_H W) m) (as_errno B + i).
Proof.
intros W m i Hi.
assert (Himg : in_img SEGS (as_errno B + i)).
{ assert (Hin : inG (G_DR B RG) (as_errno B + i)).
  { unfold inG, G_DR, G_SL. apply Exists_exists. exists (as_errno B, 4).
    split; [cbn [In]; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]. }
  exact (proj1 (HG _ Hin)). }
pose proof (HERRW i Hi) as Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 (as_errno B + i)) = as_errno B + i)
  by (apply unsigned_lit_small; pose proof (pa_segs_low _ Himg); unfold kLowMemEnd in *; lia).
assert (HH : w_H W (Z_to_bv 64 (as_errno B + i)) = false) by (apply hidden_not_img; rewrite Ha; exact Himg).
unfold writable_at, wview, mrestrict in *. rewrite HH.
destruct (m (Z_to_bv 64 (as_errno B + i))); [discriminate | exact Hw].
Qed.

Lemma dw_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn [length] in Hj; lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | cbn [length] in Hj; lia].
Qed.
Lemma dw_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn [length] in Hj; lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dw_zall; [exact H1 | cbn [length] in Hj; lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | cbn [length] in Hj; lia].
Qed.
(* g_s is apart from errno *)
Lemma dw_gs_errno : forall a, rg_s RG <= a < rg_s RG + 384 -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He. pose proof (dw_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D.
cbn [nth] in D. unfold zdisj in D. cbn [fst snd] in D. unfold ASRC in D. lia.
Qed.

(* the three shadow entries of the walk's state, in any AR state that has the table and the vector *)
Lemma dw_shok : forall E' ly S (W : world SEGS) mem md G SA HA pv cap,
  AR SEGS B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + 56 <= G + 896 ->
  In (pv, AREC * cap) (ablocks B ly S) -> 0 < cap ->
  rg_s RG <= HA -> HA + 96 <= rg_s RG + 384 ->
  ew E' 21 = Z_to_bv 64 SB -> ew E' 23 = Z_to_bv 64 HA -> ew E' 32 = Z_to_bv 64 SA -> ew E' 33 = Z_to_bv 64 pv ->
  sh_ok SEGS BxD SHD E' (mrestrict (w_H W) mem).
Proof.
intros E' ly S W mem md G SA HA pv cap HAR HGi H1 H2 HVi Hc HA1 HA2 X21 X23 X32 X33.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2.
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (RQV : req_size (AREC * cap) = 16 * cap) by (unfold AREC; apply dw_req_pos; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HGi) as (_ & HG4096 & HGceil & HGapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HVi) as (_ & HV4096 & HVceil & HVapp & _).
rewrite RQT in HGceil, HGapp. rewrite RQV in HVceil, HVapp.
assert (UB : U E' BxD = SHADOW_OFF) by (unfold BxD; rewrite (U_atom E' 21 SB X21) by (unfold SB; lia); reflexivity).
unfold sh_ok, SHD. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range SEGS (w_H W) mem E' BxD 32 SA 56 SA 0 56); [| exact UB | | lia | lia |].
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md G ATABLE); [exact HAR | exact HGi | lia | rewrite RQT; lia].
  + apply (U_atom E' 32 SA X32). lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem E' BxD 23 HA 96 HA 0 96); [| exact UB | | lia | lia |].
  + eapply range_addressable_sub; [exact (azs_range_addressable B LAWS ly S W mem md _ _ HAR HGSZ) | lia |].
    unfold ASRC. lia.
  + apply (U_atom E' 23 HA X23). lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem E' BxD 33 pv 16 pv 0 16); [| exact UB | | lia | lia |].
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md pv (AREC * cap)); [exact HAR | exact HVi | lia | rewrite RQV; lia].
  + apply (U_atom E' 33 pv X33). lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HVapp. unfold SHADOW_OFF. lia.
Qed.

(* list_drop's memmove length, 16 (pending.n - 1), as the walk computes it *)
Lemma dw_U_len : forall E' pn, ew E' 35 = Z_to_bv 64 pn -> 1 <= pn <= 2 ^ 27 ->
  U E' (SAlu ALU_SLL (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1))) (SLit 4)) = 16 * (pn - 1).
Proof.
intros E' pn H35 Hpn.
assert (UX : U E' (SExt true 32 (SOff 35 0)) = pn).
{ rewrite U_SExt, (U_atom E' 35 pn H35) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite (Z.mod_small pn) by lia. rewrite swrap32_id by lia. apply zcanon_id. unfold M64. lia. }
assert (UL : U E' (SLit (-1)) = 2 ^ 64 - 1) by (rewrite U_SLit; reflexivity).
assert (UW : U E' (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1))) = pn - 1).
{ rewrite U_of_S, S_SAluw, UX, UL. cbn [zalu_raw].
  rewrite (Z.mod_small pn) by lia.
  replace ((2 ^ 64 - 1) mod 2 ^ 32) with (2 ^ 32 - 1) by reflexivity.
  replace (pn + (2 ^ 32 - 1)) with ((pn - 1) + 1 * bv_modulus 32) by (change (bv_modulus 32) with (2 ^ 32); lia).
  rewrite swrap_add_mod, swrap32_id by lia.
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
rewrite U_SAlu, UW, U_lit by lia. cbn [zalu_raw]. change (Z.land 4 63) with 4.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* the pending texts are nonempty, so there are no more of them than pending bytes *)
Lemma dw_concat_len : forall (rs : list (Z * list byte)), Forall (fun r => (1 <= length (snd r))%nat) rs ->
  (length rs <= length (concat (map (fun r => bzs (snd r)) rs)))%nat.
Proof.
induction rs as [|r rs IH]; intros HF; [cbn; lia|].
pose proof (Forall_inv HF) as H1. cbv beta in H1. pose proof (IH (Forall_inv_tail HF)) as H2.
cbn [map concat length]. rewrite length_app.
assert (Hl : length (bzs (snd r)) = length (snd r)) by (unfold bzs; apply length_map).
rewrite Hl. lia.
Qed.

Lemma dw_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof.
intros [a b] [c d]. destruct (Z.eq_dec a c); destruct (Z.eq_dec b d);
  [left; congruence | right; congruence | right; congruence | right; congruence].
Qed.

Lemma dw_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

(* ================================================================================================
   The memory core at the join, after the free and the memmove (the DMEM of DDM).
   ================================================================================================ *)
(* h1 after list_drop (&h1->pending, 0): the records rs0 left, the array's bytes after them jk, the offset 0
   (plain drain_b.v hdrop) *)
Definition dw_hdrop (h1 : hsrc) (rs0 : list (Z * list byte)) (jk : list byte) : hsrc :=
  HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (HL (hl_v (hs_pending h1)) (hl_cap (hs_pending h1)) rs0 jk) 0
     (hs_partial h1) (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1).

Lemma dw_aview_of_vm2 : forall (W W' : world SEGS) m m' a (n : nat) v x,
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v -> a <= x < a + Z.of_nat n ->
aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x.
Proof.
intros W W' m m' a n v x H1 H2 Hx. unfold aview. replace x with (a + (x - a)) by lia.
unfold arm in H1, H2. rewrite (val_mem_agree SEGS _ _ a n v H1 H2 (x - a)) by lia. reflexivity.
Qed.

Lemma dw_abyte_trans : forall (W1 W2 W3 : world SEGS) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof.
intros W1 W2 W3 m1 m2 m3 a [A1 A2] [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw].
Qed.

(* drain's frame without the slot 192(sp) (dr_frame never reads it) *)
Lemma dw_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= a < dsp0 cx - DRAIN_FRAME + 200) ->
   abyte_kept W m W' m' a) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in HF |- *. cbv zeta in HF |- *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME -> (off + 8 <= 192 \/ 200 <= off) ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H3 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi).
replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | lia | exact HS].
Qed.

(* the bytes aentry_okx reads lie in the entry's blocks *)
Lemma dw_aentry_fp_blk : forall ly S (W : world SEGS) mem e,
aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
exists b n, In (b, n) (aentry_blks e) /\ b <= a < b + req_size n.
Proof.
intros ly S W mem e HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & HU8 & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
  exists (re_buf e), (re_cap e). split.
  + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). left. reflexivity.
  + pose proof (dw_req_ge (re_cap e)) as Hrq. clear - Ha Hj HU HU8 Hrq. lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. clear - Ha; lia.
    * unfold bzs in Ha. rewrite length_map, dw_key_ptrs_len in Ha.
      exists (re_hp e), (re_kh e). split.
      -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
         rewrite (proj2 (Z.eqb_neq _ 0) Hz). left. reflexivity.
      -- pose proof (dw_req_ge (re_kh e)) as Hrq. unfold re_nheld in Hk1. clear - Ha Hk1 Hrq. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split.
    * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * pose proof (dw_req_ge (Z.of_nat (length (key_text k)) + 1)) as Hrq. clear - Ha Hrq. lia.
Qed.

(* the bytes alist_at reads: the struct at LA, or its blocks *)
Lemma dw_alist_fp_blk : forall ly S (W : world SEGS) mem LA l lines,
alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
(LA <= a < LA + 16) \/ exists b n, In (b, n) (alist_blks l) /\ b <= a < b + req_size n.
Proof.
intros ly S W mem LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- left. cbn [fst snd] in Ha. exact Ha.
- right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dw_len_text_recs in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
    exists (hl_v l), (AREC * hl_cap l). split.
    * unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). left. reflexivity.
    * pose proof (dw_req_ge (AREC * hl_cap l)) as Hrq. unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    exists (fst q), (Z.of_nat (length (snd q)) + 1). split.
    * unfold alist_blks. apply in_or_app. right.
      apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
    * pose proof (dw_req_ge (Z.of_nat (length (snd q)) + 1)) as Hrq. clear - Ha Hrq. lia.
Qed.

(* the bytes aout_at reads: nine image cells off g_s and off the allocator's statics, or g_out's block *)
Lemma dw_aout_fp_cls : forall ly S (W : world SEGS) mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (rg_s RG <= a < rg_s RG + 384)) \/
exists b n, In (b, n) (aout_blks cap out) /\ b <= a < b + req_size n.
Proof.
intros ly S W mem c O mx no cap out HOUT r Hr a Ha.
pose proof (dw_zpw _ 2 3 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dw_zpw _ 2 4 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dw_zpw _ 2 5 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dw_zpw _ 2 6 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dw_zpw _ 2 7 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dw_zpw _ 2 8 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dw_zpw _ 2 9 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dw_zpw _ 2 10 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
pose proof (dw_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D11.
cbn [nth] in D3, D4, D5, D6, D7, D8, D9, D10, D11.
unfold zdisj in D3, D4, D5, D6, D7, D8, D9, D10, D11.
cbn [fst snd] in D3, D4, D5, D6, D7, D8, D9, D10, D11. unfold ASRC in *.
assert (GD : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros x l Hin Hx. destruct (HG a ltac:(unfold inG; apply Exists_exists; exists (x, l);
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia])) as (H1 & H2 & _). split; [exact H1 | exact H2]. }
assert (GO : forall x l, In (x, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] -> x <= a < x + l ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros x l Hin Hx. destruct (HGO a ltac:(unfold inG; apply Exists_exists; exists (x, l);
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia])) as (H1 & H2 & _). split; [exact H1 | exact H2]. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- left. destruct (GO (rg_send_max RG) 8 ltac:(cbn [In]; right; right; left; reflexivity) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D7; lia]].
- left. destruct (GD (rg_nout RG) 8 ltac:(unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D8; lia]].
- left. destruct (GD (rg_capout RG) 8 ltac:(unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D9; lia]].
- left. destruct (GD (rg_out RG) 8 ltac:(unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D10; lia]].
- left. destruct (GO (rg_client RG) 4 ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D3; lia]].
- left. destruct (GD (rg_client_broken RG) 1 ltac:(unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D4; lia]].
- left. destruct (GO (rg_send_dead RG) 1 ltac:(cbn [In]; right; left; reflexivity) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D6; lia]].
- left. destruct (GD (rg_send_eintr RG) 1 ltac:(unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D5; lia]].
- left. destruct (GD (as_errno B) 4 ltac:(unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as [Gi Gn]. split; [exact Gi | split; [exact Gn | clear - Ha D11; lia]].
- right. destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  exists out, cap. split; [unfold aout_blks; rewrite Hc0; left; reflexivity|].
  pose proof (dw_req_ge cap) as Hrq. clear - Ha Hrq. lia.
Qed.

(* W_drain_next.v dn_aentry_okx_kept *)
Lemma dw_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
aentry_okx B ly S W mem e ->
akept W mem W' mem' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

Lemma dw_nodup_neq : forall (A Bl : list (Z * Z)) x y, List.NoDup (A ++ x :: Bl) -> In y (A ++ Bl) -> y <> x.
Proof. intros A Bl x y Hnd Hy E. subst y. exact (List.NoDup_remove_2 _ _ _ Hnd Hy). Qed.

(* the harness source after list_drop (&h->pending, 0) *)
Lemma dw_asrc_drop : forall ly1 S1 (W1 : world SEGS) m1 ly2 S2 (W2 : world SEGS) m2 HA h1 r0 rs0 jk,
  asrc_at B ly1 S1 W1 m1 HA h1 -> rg_s RG <= HA -> HA + 96 <= rg_s RG + 384 ->
  hl_recs (hs_pending h1) = r0 :: rs0 ->
  (forall b, In b (asrc_blks (dw_hdrop h1 rs0 jk)) -> In b (ablocks B ly2 S2)) ->
  List.NoDup (asrc_blks (dw_hdrop h1 rs0 jk)) ->
  (forall b n x, In (b, n) (ablocks B ly2 S2) -> (b, n) <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) ->
     b <= x < b + req_size n -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W2 m2) x) ->
  val_mem SEGS (arm W2 m2) (HA + 24) 4 (Z.of_nat (length rs0)) -> val_mem SEGS (arm W2 m2) (HA + 32) 8 0 ->
  Z.of_nat (length jk) = AREC * (hl_cap (hs_pending h1) - Z.of_nat (length rs0)) ->
  garr8 SEGS (arm W2 m2) (hl_v (hs_pending h1)) (bzs (concat (map text_rec rs0) ++ jk)) ->
  asrc_at B ly2 S2 W2 m2 HA (dw_hdrop h1 rs0 jk).
Proof.
intros ly1 S1 W1 m1 ly2 S2 W2 m2 HA h1 r0 rs0 jk HSRC1 H1 H2 Hrecs INB HND KBL KIM KIMW V24 V32 Hjk Hgv.
pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2.
pose proof HSRC1 as (S1' & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18
  & S19 & S20 & S21 & S22 & S23 & S24).
apply dw_hide_i in S6. apply dw_hide_i in S7. apply dw_hide_i in S15. apply dw_hide_i in S17.
pose proof S10 as (Pv & Pn & Pc & Pawr & Pncap & Pvec & Pnd & Pnv & Pfa).
unfold hl_n in Pncap. rewrite Hrecs in Pncap, Pnd, Pnv, Pfa. cbn [length map] in Pncap.
destruct Pvec as [(Hc0 & _) | (Hcp & _ & _ & _)]; [lia|].
assert (GSI : forall x, HA <= x < HA + 96 -> in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
  by (intros x Hx; destruct (HG x (dw_inG_gs x ltac:(lia))) as (Gi1 & Gn1 & _); split; [exact Gi1 | exact Gn1]).
assert (Hvm : forall a n v, HA <= a -> (a + Z.of_nat n <= HA + 24 \/ HA + 40 <= a \/ (HA + 28 <= a /\ a + Z.of_nat n <= HA + 32)) ->
  a + Z.of_nat n <= HA + 96 -> val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v Ha Hn1 Hn2 Hv. apply (akept_vm W1 m1); [|exact Hv].
  intros x Hx. destruct (GSI x ltac:(lia)) as [Gi Gn]. apply KIM; [exact Gi | exact Gn | lia | lia]. }
set (f := fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)).
assert (Hh2b : asrc_blks (dw_hdrop h1 rs0 jk) =
  [(hs_partial h1, APARTIAL)] ++ (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) ::
  (map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1))).
{ unfold asrc_blks, alist_blks at 1, dw_hdrop. cbn [hs_partial hs_pending hs_expected hs_held hl_cap hl_v hl_recs].
  rewrite (proj2 (Z.eqb_neq (hl_cap (hs_pending h1)) 0)) by lia. reflexivity. }
assert (INB' : forall y, In y ([(hs_partial h1, APARTIAL)] ++ map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ->
  In y (ablocks B ly2 S2) /\ y <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))).
{ intros y Hy. rewrite Hh2b in HND. split; [|exact (dw_nodup_neq _ _ _ _ HND Hy)].
  apply INB. rewrite Hh2b. apply in_app_or in Hy. apply in_or_app. destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy]. }
assert (KB' : forall y x, In y ([(hs_partial h1, APARTIAL)] ++ map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ->
  fst y <= x < fst y + req_size (snd y) -> abyte_kept W1 m1 W2 m2 x).
{ intros [b n] x Hy Hx. destruct (INB' _ Hy) as [Hin Hne]. exact (KBL b n x Hin Hne Hx). }
assert (KL : forall LA l lines, alist_at B ly1 S1 W1 m1 LA l lines -> HA + 40 <= LA -> LA + 16 <= HA + 96 ->
  (forall b, In b (alist_blks l) -> In b ([(hs_partial h1, APARTIAL)] ++ map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1))) ->
  alist_at B ly2 S2 W2 m2 LA l lines).
{ intros LA l lines HL Hl1 Hl2 HBl.
  apply (alist_at_kept B ly1 S1 W1 m1); [exact HL | | intros b Hb; exact (proj1 (INB' b (HBl b Hb)))].
  intros r Hr x Hx. destruct (dw_alist_fp_blk _ _ _ _ _ _ _ HL r Hr x Hx) as [Hxl | (b & n & Hb & Hbx)].
  - destruct (GSI x ltac:(lia)) as [Gi Gn]. apply KIM; [exact Gi | exact Gn | lia | lia].
  - exact (KB' (b, n) x (HBl _ Hb) Hbx). }
assert (Hrs : (rs0 = [] /\ 0 = 0) \/ (exists r rs, rs0 = r :: rs /\ 0 <= 0 < Z.of_nat (length (snd r)))).
{ destruct rs0 as [|r1 rs1]; [left; split; reflexivity|]. right. exists r1, rs1. split; [reflexivity|].
  pose proof (Forall_inv (Forall_inv_tail Pfa)) as (_ & _ & _ & X). cbv beta in X. specialize (X eq_refl). lia. }
unfold asrc_at, dw_hdrop.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad hs_expected
  hs_held hl_v hl_cap hl_recs hl_junk].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S1']|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S2']|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S3]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S4]|].
split; [intros i Hi; destruct (GSI (HA + i) ltac:(unfold ASRC in Hi; lia)) as [Gi Gn]; apply KIMW; [exact Gi | exact Gn | exact (S5 i Hi)]|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|]. split; [exact S9|].
split.
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk].
  split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact Pv]|].
  split; [unfold hl_n; cbn [hl_recs]; replace (HA + 16 + 8) with (HA + 24) by lia; exact V24|].
  split; [apply Hvm; [lia | right; right; cbn; lia | cbn; lia | exact Pc]|].
  split; [intros i Hi; destruct (GSI (HA + 16 + i) ltac:(lia)) as [Gi Gn]; apply KIMW; [exact Gi | exact Gn | exact (Pawr i Hi)]|].
  split; [unfold hl_n; cbn [hl_recs]; lia|].
  split.
  { right. split; [exact Hcp|]. split.
    - apply INB. rewrite Hh2b. apply in_or_app. right. left. reflexivity.
    - split; [unfold hl_n; cbn [hl_recs]; exact Hjk | exact Hgv]. }
  split; [apply NoDup_ListNoDup; apply NoDup_ListNoDup in Pnd; cbn [map] in Pnd; apply List.NoDup_cons_iff in Pnd; exact (proj2 Pnd)|].
  split; [intros X; apply Pnv; cbn [map]; right; exact X|].
  rewrite Forall_forall in Pfa |- *. intros r Hr. destruct (Pfa r (or_intror Hr)) as (R1 & R2 & R3 & R4).
  assert (Hy : In (f r) ([(hs_partial h1, APARTIAL)] ++ map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)))
    by (apply in_or_app; right; apply in_or_app; left; apply in_map; exact Hr).
  split; [exact (proj1 (INB' _ Hy))|].
  split; [|split; [exact R3 | exact R4]].
  apply (akept_garr8 W1 m1); [|exact R2]. intros x Hx. apply (KB' (f r) x Hy).
  unfold f. cbn [fst snd]. unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
  pose proof (dw_req_ge (Z.of_nat (length (snd r)) + 1)). lia. }
split; [exact V32|].
split; [apply Hvm; [lia | right; left; lia | cbn; lia | exact S12]|].
split; [apply Hvm; [lia | right; left; lia | cbn; lia | exact S13]|].
split; [apply Hvm; [lia | right; left; lia | cbn; lia | exact S14]|].
split; [exact Hrs|].
split; [exact S16|]. split; [exact S17|].
split; [exact (proj1 (INB' (hs_partial h1, APARTIAL) ltac:(left; reflexivity)))|].
split; [exact S19|].
split.
{ apply (akept_garr8 W1 m1); [|exact S20]. intros x Hx. apply (KB' (hs_partial h1, APARTIAL) x ltac:(left; reflexivity)).
  cbn [fst snd]. unfold bzs in Hx. rewrite length_map, S19 in Hx. pose proof (dw_req_ge APARTIAL). lia. }
split; [exact S21|].
split; [apply KL; [exact S22 | lia | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb]|].
split; [apply KL; [exact S23 | lia | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]|].
(* NoDup of the blocks: the head text's block is gone *)
assert (E1 : hs_blocks h1 = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
  fst r0 :: (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
{ unfold hs_blocks, list_blocks at 1. rewrite Hrecs. cbn [map]. rewrite <- !app_assoc. reflexivity. }
assert (E2 : hs_blocks (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1)
    (HL (hl_v (hs_pending h1)) (hl_cap (hs_pending h1)) rs0 jk) 0 (hs_partial h1) (hs_pjunk h1) (hs_npartial h1)
    (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)) =
  (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
  (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
{ unfold hs_blocks, list_blocks at 1. cbn [hs_pending hs_partial hs_expected hs_held hl_v hl_cap hl_recs].
  rewrite <- !app_assoc. reflexivity. }
apply NoDup_ListNoDup in S24. apply NoDup_ListNoDup. rewrite E2. rewrite E1 in S24. exact (List.NoDup_remove_1 _ _ _ S24).
Qed.

Lemma dw_nodup_app_l : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
induction l1 as [|y l1 IH]; intros l2 Hnd; [apply List.NoDup_nil|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hy Hnd]. apply List.NoDup_cons.
- intros X. apply Hy. apply in_or_app. left. exact X.
- exact (IH l2 Hnd).
Qed.

(* the memory core at the join *)
Lemma dw_dmem : forall cx ly1 S1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 ly2 S2 W2 m2 md2 k2 r0 rs0 jk l1 l2,
  (dxj cx < 4)%nat -> dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE ->
  DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
  drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
  rom_view SEGS (dxW cx) (dxmem cx) ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 m2 md2 k2 ->
  frames S2 = frames S1 ->
  hl_recs (hs_pending h1) = r0 :: rs0 ->
  ablocks B ly1 S1 = l1 ++ (fst r0, Z.of_nat (length (snd r0)) + 1) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  (forall b n x, In (b, n) (ablocks B ly2 S2) -> (b, n) <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) ->
     b <= x < b + req_size n -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     ~ (dHA RG cx + 24 <= x < dHA RG cx + 28) -> ~ (dHA RG cx + 32 <= x < dHA RG cx + 40) -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W2 m2) x) ->
  (forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 200) ->
     abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x) ->
  val_mem SEGS (arm W2 m2) (dHA RG cx + 24) 4 (Z.of_nat (length rs0)) ->
  val_mem SEGS (arm W2 m2) (dHA RG cx + 32) 8 0 ->
  Z.of_nat (length jk) = AREC * (hl_cap (hs_pending h1) - Z.of_nat (length rs0)) ->
  garr8 SEGS (arm W2 m2) (hl_v (hs_pending h1)) (bzs (concat (map text_rec rs0) ++ jk)) ->
  DMEM B RG cx ly2 S2 W2 m2 md2 k2 e1 (dw_hdrop h1 rs0 jk) s' out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 ly2 S2 W2 m2 md2 k2 r0 rs0 jk l1 l2 Hj HG1 HG2
  HM Hno Hoc HROM0 HJ2 Hfr Hrecs Hbl1 Hbl2 KBL KIM KIMW KFR PIM V24 V32 Hjk Hgv.
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HAR2 : AR SEGS B ly2 S2 W2 m2 md2) by (eapply ajournal_gx_AR; exact HJ2).
pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2. unfold AENT, ATABLE in HG2.
assert (Hj3 : Z.of_nat (dxj cx) <= 3) by lia.
assert (HA1 : rg_s RG <= dHA RG cx) by (unfold dHA, ASRC; lia).
assert (HA2 : dHA RG cx + 96 <= rg_s RG + 384) by (unfold dHA, ASRC; lia).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Spend & _).
pose proof Spend as (_ & _ & _ & _ & Pncap & _).
unfold hl_n in Pncap. rewrite Hrecs in Pncap. cbn [length] in Pncap.
assert (Hcp : 0 < hl_cap (hs_pending h1)) by lia.
set (f := fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)).
set (vec := (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))).
set (Al := (dxG cx, ATABLE) :: aentry_blks e1 ++ [(hs_partial h1, APARTIAL); vec]).
set (Bl := map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx).
assert (EO : (dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx =
  Al ++ (fst r0, Z.of_nat (length (snd r0)) + 1) :: Bl).
{ unfold Al, Bl, vec, asrc_blks, alist_blks at 1. rewrite Hrecs.
  rewrite (proj2 (Z.eqb_neq (hl_cap (hs_pending h1)) 0)) by lia.
  cbn [map app]. rewrite <- !app_assoc. cbn [app]. reflexivity. }
assert (EN : (dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx = Al ++ Bl).
{ unfold Al, Bl, vec, asrc_blks, alist_blks at 1, dw_hdrop.
  cbn [hs_partial hs_pending hs_expected hs_held hl_cap hl_v hl_recs].
  rewrite (proj2 (Z.eqb_neq (hl_cap (hs_pending h1)) 0)) by lia.
  cbn [app]. rewrite <- !app_assoc. cbn [app]. reflexivity. }
assert (HPERM2 : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++ aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx)).
{ rewrite EN, Hbl2. apply (Permutation_app_inv l1 l2 Al Bl (fst r0, Z.of_nat (length (snd r0)) + 1)).
  rewrite <- Hbl1, <- EO. exact Hperm. }
assert (INB2 : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx) -> In b (ablocks B ly2 S2))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPERM2) Hb)).
assert (HND2 : List.NoDup ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx))
  by exact (Permutation_NoDup HPERM2 (dw_ablocks_nodup _ _ _ _ _ HAR2)).
assert (NV : forall y, In y ((dxG cx, ATABLE) :: aentry_blks e1 ++ aout_blks (drain_b_c.ds_ocap s) out1) -> y <> vec).
{ intros y Hy. rewrite EN in HND2.
  assert (E3 : Al ++ Bl = ((dxG cx, ATABLE) :: aentry_blks e1 ++ [(hs_partial h1, APARTIAL)]) ++ vec :: Bl).
  { unfold Al. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  rewrite E3 in HND2. apply (dw_nodup_neq _ _ _ _ HND2).
  destruct Hy as [<- | Hy]; [left; reflexivity|]. apply in_app_or in Hy. right. apply in_or_app.
  destruct Hy as [Hy|Hy]; [left; apply in_or_app; left; exact Hy | right].
  unfold Bl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hy. }
assert (KB2 : forall b n x, In (b, n) ((dxG cx, ATABLE) :: aentry_blks e1 ++ aout_blks (drain_b_c.ds_ocap s) out1) ->
  b <= x < b + req_size n -> abyte_kept W1 m1 W2 m2 x).
{ intros b n x Hb Hx. apply (KBL b n x); [| exact (NV _ Hb) | exact Hx]. apply INB2.
  destruct Hb as [<- | Hb]; [left; reflexivity|]. right. apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
assert (SAK : forall x, dxSA cx <= x < dxSA cx + 56 -> abyte_kept W1 m1 W2 m2 x)
  by (intros x Hx; apply (KB2 (dxG cx) ATABLE x (or_introl eq_refl)); rewrite RQT; lia).
assert (GSI : forall x, rg_s RG <= x < rg_s RG + 384 -> in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
  by (intros x Hx; destruct (HG x (dw_inG_gs x ltac:(lia))) as (Gi2 & Gn2 & _); split; [exact Gi2 | exact Gn2]).
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _).
unfold DMEM. rewrite Hno, Hoc.
split; [exact HJ2|].
split; [exact (ajournal_gx_rom_view SEGS B pa_segs_low (G_DR B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROMO HROM0)|].
split; [intros a Ha1 Ha2 Ha3 Hp; exact (PIM a Ha1 Ha2 Ha3 (Hpres a Ha1 Ha2 Ha3 Hp))|].
split; [rewrite Hfr; exact Hframes|].
split; [exact (dw_frame_kept cx W1 m1 W2 m2 KFR HFR)|].
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx. apply SAK.
  unfold bzs in Hx. rewrite length_map in Hx.
  assert (Hl : length (entry_bytes e1) = 56%nat).
  { unfold entry_bytes. rewrite !length_app, Hpad1, Hpad2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite Hl in Hx. cbn in Hx. lia. }
split; [apply (akept_awr W1 m1); [intros x Hx; apply SAK; unfold AENT in Hx; lia | exact Hawr]|].
split.
{ apply (dw_aentry_okx_kept ly1 S1 W1 m1); [exact HOKX | |].
  - intros r Hr x Hx. destruct (dw_aentry_fp_blk _ _ _ _ _ HOKX r Hr x Hx) as (b & n & Hb & Hbx).
    apply (KB2 b n x); [right; apply in_or_app; left; exact Hb | exact Hbx].
  - intros b Hb. apply INB2. right. apply in_or_app. left. exact Hb. }
split.
{ apply (dw_asrc_drop ly1 S1 W1 m1 ly2 S2 W2 m2 (dHA RG cx) h1 r0 rs0 jk Hsrc HA1 HA2 Hrecs).
  - intros b Hb. apply INB2. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - apply List.NoDup_cons_iff in HND2. pose proof (dw_nodup_app_r _ _ (proj2 HND2)) as X. exact (dw_nodup_app_l _ _ X).
  - exact KBL.
  - exact KIM.
  - exact KIMW.
  - exact V24.
  - exact V32.
  - exact Hjk.
  - exact Hgv. }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (fd & o & V1 & V2 & Ho'). exists fd, o.
  assert (Hij' : Z.of_nat i <> Z.of_nat (dxj cx)) by lia.
  assert (Hi3 : Z.of_nat i <= 3) by lia.
  split; [|split; [|exact Ho']]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx;
  (destruct (GSI x ltac:(unfold ASRC in Hx; cbn in Hx; lia)) as [Gi Gn]; apply KIM; [exact Gi | exact Gn | | ]);
  unfold dHA; unfold ASRC in Hx |- *; cbn in Hx; lia. }
split.
{ intros x Hx Hn. apply (dw_abyte_trans _ _ _ _ _ _ _ (Hgsk x Hx Hn)).
  unfold ASRC in Hx, Hn. destruct (GSI x ltac:(lia)) as [Gi Gn]. apply KIM; [exact Gi | exact Gn | lia | lia]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1); [exact Hout | |].
  - intros r Hr x Hx. destruct (dw_aout_fp_cls _ _ _ _ _ _ _ _ _ _ Hout r Hr x Hx) as [(Gi & Gn & Gs) | (b & n & Hb & Hbx)].
    + apply KIM; [exact Gi | exact Gn | lia | lia].
    + apply (KB2 b n x); [right; apply in_or_app; right; exact Hb | exact Hbx].
  - intros b Hb. apply INB2. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split; [exact Hlivout|].
exact HPERM2.
Qed.

(* a byte array whose bytes moved: the view at b + j is the old view at a + j (W_lp_tail.v lpt_garr8_moved) *)
Lemma dw_garr8_moved : forall H H' (m m' : word -> option byte) a b l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (b + j) = aview SEGS H m (a + j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') b l.
Proof.
intros H H' m m' a b l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (b + Z.of_nat j) 1); [|exact Hv].
intros k Hk. rewrite <- !Z.add_assoc. apply HK. lia.
Qed.

(* the record array after memmove (v, v + 16, 16 |rs0|): the records rs0, then the old bytes from 16 |rs0| on
   (plain drain_b.v rtd_mm) *)
Lemma dw_vec_after : forall (H H' : word -> bool) (m m' : word -> option byte) v (r0 : Z * list byte) rs0 junk,
  garr8 SEGS (mrestrict H m) v (bzs (concat (map text_rec (r0 :: rs0)) ++ junk)) ->
  (forall j, 0 <= j < 16 * Z.of_nat (length rs0) -> aview SEGS H' m' (v + j) = aview SEGS H m (v + 16 + j)) ->
  (forall x, v + 16 * Z.of_nat (length rs0) <= x < v + Z.of_nat (length (concat (map text_rec (r0 :: rs0)) ++ junk)) ->
     aview SEGS H' m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H' m') v
    (bzs (concat (map text_rec rs0) ++ skipn (16 * length rs0) (concat (map text_rec (r0 :: rs0)) ++ junk))).
Proof.
intros H H' m m' v r0 rs0 junk Hg HMV HKV.
assert (LC : length (concat (map text_rec rs0)) = (16 * length rs0)%nat) by apply dw_len_text_recs.
assert (LT : length (text_rec r0) = 16%nat) by (unfold text_rec; rewrite length_app, !Mem.length_le8; reflexivity).
unfold bzs. rewrite map_app. apply garr8_app. split.
- fold (bzs (concat (map text_rec rs0))).
  pose proof Hg as Hg1. cbn [map concat] in Hg1. unfold bzs in Hg1. rewrite <- app_assoc, map_app in Hg1.
  apply garr8_app in Hg1 as [_ Hg1]. rewrite length_map, LT in Hg1. rewrite map_app in Hg1.
  apply garr8_app in Hg1 as [Hg1 _]. fold (bzs (concat (map text_rec rs0))) in Hg1.
  apply (dw_garr8_moved H H' m m' (v + Z.of_nat 16) v); [|exact Hg1].
  intros j Hj. unfold bzs in Hj. rewrite length_map, LC in Hj. rewrite HMV by lia. f_equal; lia.
- rewrite length_map, LC.
  set (L := concat (map text_rec (r0 :: rs0)) ++ junk) in *.
  assert (Hg2 : garr8 SEGS (mrestrict H m) (v + Z.of_nat (16 * length rs0)) (map bz (skipn (16 * length rs0) L))).
  { rewrite <- (firstn_skipn (16 * length rs0) L) in Hg. unfold bzs in Hg. rewrite map_app in Hg.
    apply garr8_app in Hg as [_ Hg]. rewrite length_map, length_firstn in Hg.
    assert (HlL : (16 * length rs0 <= length L)%nat).
    { unfold L. rewrite length_app. cbn [map concat]. rewrite length_app, LT, LC. lia. }
    replace (Init.Nat.min (16 * length rs0) (length L)) with (16 * length rs0)%nat in Hg by lia. exact Hg. }
  apply (dw_garr8_moved H H' m m' (v + Z.of_nat (16 * length rs0)) (v + Z.of_nat (16 * length rs0))); [|exact Hg2].
  intros j Hj. rewrite length_map, length_skipn in Hj. apply HKV. lia.
Qed.

Lemma dw_U_pn1 : forall E' pn, ew E' 35 = Z_to_bv 64 pn -> 1 <= pn <= 2 ^ 27 ->
  U E' (SAlu ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1))) = pn - 1.
Proof.
intros E' pn H35 Hpn.
assert (UX : U E' (SExt true 32 (SOff 35 0)) = pn).
{ rewrite U_SExt, (U_atom E' 35 pn H35) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite (Z.mod_small pn) by lia. rewrite swrap32_id by lia. apply zcanon_id. unfold M64. lia. }
assert (UL : U E' (SLit (-1)) = 2 ^ 64 - 1) by (rewrite U_SLit; reflexivity).
rewrite U_SAlu, UX, UL. cbn [zalu_raw]. unfold zcanon, M64.
replace (pn + (2 ^ 64 - 1)) with ((pn - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.


Lemma drop_whole : forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DE B MT MMAX RG cx s1 D W1 c1 -> dwhole s1 = true ->
(forall W2 c2, DDM B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Proof.
intros cx s1 D W1 c1 HB HDE Hw HK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HGSB as (Hg1 & Hg2 & Hg3). unfold ASRC in Hg2.
unfold DE in HDE.
destruct HDE as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & Hsp & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & HFR & S56 & S64 & S48 & S200 & S32 & S80 & S40 & S192 &
  Hn0 & Hdata & HMEM & Hnonul & Hused & HSAME & Hcap & HU & Hskip & HH & Hka & Hei & Hpend & Hoff & Hst & Hen & Hecap &
  HHIST & HRST & Hfut & HBUD).
pose proof HFR as HFR'. unfold dr_frame in HFR'. cbv zeta in HFR'.
destruct HFR' as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
pose proof HMEM as (HJ & HROM & HPRES & HFRAMES & _ & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & _ & HPERM).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
unfold AENT, ATABLE in HSAG.
assert (HSTKb : alloc_ceiling + ASTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 HDS HES HDF HAS; lia).
assert (Hspal : spZ regs1 mod 16 = 0) by (rewrite Hsp, Zminus_mod, Hal16; reflexivity).
pose proof HJ as (_ & _ & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSPres & _).
rewrite !Z.add_0_r in HSPres. clear memS0 HJi0.
(* ---- the relay's table block and the relay entry ---- *)
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _ & _).
rewrite RQT in HGceil, HGapp, HGpres.
set (SA := dxSA cx) in *.
set (HA := dHA RG cx) in *.
assert (HHA : rg_s RG <= HA /\ HA + ASRC <= rg_s RG + 4 * ASRC).
{ unfold HA, dHA, ASRC. lia. }
assert (HAm : HA mod 8 = 0).
{ unfold HA, dHA, ASRC. pose proof (Z_div_mod_eq_full (rg_s RG) 8) as Hd. rewrite Hg3 in Hd.
  replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with ((rg_s RG / 8 + 12 * Z.of_nat (dxj cx)) * 8) by lia.
  apply Z_mod_mult. }
unfold ASRC in HHA.
(* ---- the harness source and its pending list ---- *)
pose proof HSRC as (_ & _ & _ & _ & Sawr & _ & _ & _ & _ & Spend & Soff & _ & _ & _
  & Srecs & _ & _ & _ & _ & _ & _ & _ & _ & _).
apply dw_hide_i in Srecs.
pose proof Spend as (Pv & Pn & Pc & Pawr & Pncap & Pvec & Pnd & Pnv & Pfa).
pose proof HRST as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:Erecs.
{ exfalso. apply RS_pe. rewrite <- Hpend. reflexivity. }
assert (Hhead : dhead s1 = bzs (snd r0)) by (unfold dhead; rewrite <- Hpend; reflexivity).
assert (Hwh : drain_b_c.ds_off s1 + dnum s1 = Z.of_nat (length (snd r0))).
{ unfold dwhole in Hw. apply Z.eqb_eq in Hw. rewrite Hw, Hhead. unfold bzs. rewrite length_map. reflexivity. }
assert (Hnb : 1 <= dnum s1 <= 16384).
{ assert (Hcapv : re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384)
    by (destruct HOKX as (_ & _ & _ & _ & _ & X & _); exact X).
  pose proof (Z.le_min_r (Z.of_nat (length (dhead s1)) - drain_b_c.ds_off s1) (drain_b_c.ds_cap s1 - ulen s1)) as X.
  fold (dnum s1) in X. unfold ulen in X. rewrite <- Hcap in X. lia. }
assert (Hpn : hl_n (hs_pending h1) = Z.of_nat (S (length rs0))) by (unfold hl_n; rewrite Erecs; reflexivity).
assert (Hcap0 : 0 < hl_cap (hs_pending h1)) by lia.
destruct Pvec as [(Hc0 & _) | (_ & Hvin & Hjl & Hvg)]; [lia|].
assert (RQV : req_size (AREC * hl_cap (hs_pending h1)) = 16 * hl_cap (hs_pending h1))
  by (unfold AREC; apply dw_req_pos; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hvin) as (HV16 & HV4096 & HVceil & HVapp & HVpres & _ & _).
rewrite RQV in HVceil, HVapp, HVpres.
set (pv := hl_v (hs_pending h1)) in *.
set (cap := hl_cap (hs_pending h1)) in *.
pose proof (Forall_inv Pfa) as (R0in & R0g & _ & R0len).
assert (R0l : (1 <= length (snd r0))%nat) by exact (R0len eq_refl). clear R0len.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR R0in) as (_ & HT4096 & HTceil & HTapp & HTpres & _ & _).
rewrite dw_req_pos in HTceil, HTapp, HTpres by lia.
pose proof (dw_head_fields _ _ _ _ _ Hvg) as (MV0 & MV8).
rewrite unsigned_lit_small in MV0, MV8 by lia.
(* ---- the relay's buffer ---- *)
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _ & _ & HUlen & Husedr & Hbufc & _).
assert (Hcappos : 0 < re_cap e1).
{ pose proof (Z.le_min_r (Z.of_nat (length (dhead s1)) - drain_b_c.ds_off s1) (drain_b_c.ds_cap s1 - ulen s1)) as X.
  fold (dnum s1) in X. unfold ulen in X. rewrite <- Hcap in X. lia. }
destruct Hbufc as [(Hc0 & _) | (_ & Hbin & Hjunk & Hbuf8)]; [lia|].
assert (RQB : req_size (re_cap e1) = re_cap e1) by (apply dw_req_pos; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (HB16 & HB4096 & HBceil & _ & _ & _ & _).
rewrite RQB in HBceil.
pose proof (dw_entry_fields _ _ _ Hpad1 HENT) as (MBUF & MUSED).
rewrite unsigned_lit_small in MBUF, MUSED by lia.
(* ---- the three separations ---- *)
assert (DHS : HA + 96 <= SA \/ SA + 56 <= HA).
{ apply dw_apart_of_disj; [lia | lia |]. intros x Hx Hy.
  apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR HGin1); [rewrite RQT; lia|].
  exact (proj1 (HG x (dw_inG_gs x ltac:(lia)))). }
apply dw_hide_i in DHS.
assert (DHV : HA + 96 <= pv \/ pv + 16 <= HA).
{ apply dw_apart_of_disj; [lia | lia |]. intros x Hx Hy.
  apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR Hvin); [rewrite RQV; lia|].
  exact (proj1 (HG x (dw_inG_gs x ltac:(lia)))). }
apply dw_hide_i in DHV.
pose proof (Permutation_NoDup HPERM (dw_ablocks_nodup _ _ _ _ _ HAR)) as HND.
apply List.NoDup_cons_iff in HND as [HGnot HND].
assert (Hvsrc : In (pv, AREC * cap) (asrc_blks h1)).
{ unfold asrc_blks, alist_blks. fold cap. right. apply in_or_app. left. apply in_or_app. left.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
assert (DSV : SA + 56 <= pv \/ pv + 16 <= SA).
{ assert (Hne : (dxG cx, ATABLE) <> (pv, AREC * cap)).
  { intros E. apply HGnot. rewrite E. apply in_or_app. right. apply in_or_app. left. exact Hvsrc. }
  pose proof (dw_blk_apart _ _ _ _ _ _ _ _ _ HAR HGin1 Hvin Hne) as X. rewrite RQT, RQV in X.
  lia. }
apply dw_hide_i in DSV.
(* ---- the entry state ---- *)
assert (X5 : forall o, 192 <= o < 200 -> writable_at SEGS (arm W1 m1) (spZ regs1 + o)).
{ intros o Ho. unfold arm. apply (apresent_writable SEGS). apply HSPres. lia. }
assert (X13 : forall o, 16 <= o < 40 -> writable_at SEGS (arm W1 m1) (HA + o)).
{ intros o Ho. apply Sawr. unfold ASRC. lia. }
assert (X14 : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF HA 96).
{ eapply range_addressable_sub; [exact (azs_range_addressable B LAWS ly1 S1 W1 m1 md1 _ _ HAR HGSZ) | lia |].
  unfold ASRC in *. lia. }
assert (X22 : forall o, 24 <= o < 32 -> writable_at SEGS (arm W1 m1) (SA + o)).
{ intros o Ho. apply HAWR. unfold AENT. lia. }
assert (X23 : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56).
{ apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE); [exact HAR | exact HGin1 | lia |].
  rewrite RQT. lia. }
assert (X27 : in_app SA 56) by (eapply in_app_sub; [exact HGapp | lia | lia | lia]).
assert (X30 : pv mod 8 = 0).
{ pose proof (Z_div_mod_eq_full pv 16) as Hd. rewrite HV16 in Hd.
  replace pv with ((pv / 16 * 2) * 8) by lia. apply Z_mod_mult. }
assert (X31 : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF pv 16).
{ apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 pv (AREC * cap)); [exact HAR | exact Hvin | lia |].
  rewrite RQV. lia. }
assert (X36 : in_app pv 16) by (eapply in_app_sub; [exact HVapp | lia | lia | lia]).
assert (X39 : re_buf e1 mod 8 = 0).
{ pose proof (Z_div_mod_eq_full (re_buf e1) 16) as Hd. rewrite HB16 in Hd.
  replace (re_buf e1) with ((re_buf e1 / 16 * 2) * 8) by lia. apply Z_mod_mult. }
assert (Hoffr : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
{ unfold dw_hide in Srecs. destruct Srecs as [(X & _) | (r & rs & X & Y)]; [discriminate X|]. injection X as <- <-. exact Y. }
assert (Hpnr : 0 <= hl_n (hs_pending h1) < 2 ^ 32) by lia.
pose proof (DROPENTRY W1 regs1 m1 SA HA pv (Z.of_nat (length (snd r0))) (hl_n (hs_pending h1)) (hs_off h1)
  (re_buf e1) (re_used e1) (fst r0) (dnum s1)
  ltac:(lia) ltac:(lia) ltac:(lia) Hspal X5 R21 R23 R19 Hnb ltac:(lia) ltac:(lia) HAm X13 X14 Pv ltac:(replace (HA + 24) with (HA + 16 + 8) by lia; exact Pn) Soff
  Hpnr ltac:(lia) ltac:(lia) ltac:(lia) X22 X23 MBUF MUSED ltac:(lia) X27 ltac:(lia) ltac:(lia) X30 X31
  MV0 MV8 ltac:(lia) ltac:(lia) X36 ltac:(lia) ltac:(lia) X39
  ltac:(rewrite Hsp; exact S32) ltac:(rewrite Hsp; exact S40) ltac:(rewrite Hsp; exact S48)
  ltac:(rewrite Hsp; exact S56) ltac:(rewrite Hsp; exact S64) ltac:(rewrite Hsp; exact S80)
  ltac:(rewrite Hsp; exact F176) ltac:(rewrite Hsp; exact S192) ltac:(rewrite Hsp; exact S200)
  ltac:(rewrite Hsp; exact F208) ltac:(rewrite Hsp; exact F216) ltac:(rewrite Hsp; exact F224)
  DHS DHV DSV) as [HS SHOK].

subst c1. unfold cfg_at. change (w64 (BASE + A_dr_fed)) with (Z_to_bv 64 (BASE + A_dr_fed)).
remember (Eimg (Ereg regs1 (dr_extra SA pv (Z.of_nat (length (snd r0))) (hl_n (hs_pending h1)) (hs_off h1)
  (re_buf e1) (re_used e1) (fst r0)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (dr_extra SA pv (Z.of_nat (length (snd r0))) (hl_n (hs_pending h1)) (hs_off h1)
  (re_buf e1) (re_used e1) (fst r0))) E)
  by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat (length (snd r0))))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (hl_n (hs_pending h1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (hs_off h1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_buf e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (re_used e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (fst r0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (U23 : bv_unsigned (ew E 23) = HA) by (rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = pv) by (rewrite E33; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ SHOK DRspan.
{ cbn [ss_mem ss_drop dr_regions].
  apply awr_ok_x_cons.
  { intros x Hx. cbn [dr_r_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [dr_r_gsA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [dr_r_gsC YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons.
  { intros x Hx. cbn [dr_r_sa YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32 in Hx.
    left. split; [|lia]. right. left. split.
    - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1 | rewrite RQT; lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [dr_r_vec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
psrr_branch_tok RUN BR HS SHOK DRspan.
{ (* the taken edge `n + off <> v[0].n` is refuted: the head text is used up *)
  exfalso. rewrite branch_ne_U in Hc.
  assert (UA : U E (SAlu ALU_ADD (SOff 19 0) (SOff 36 0)) = Z.of_nat (length (snd r0))).
  { rewrite U_SAlu. rewrite (U_atom E 19 (dnum s1) (eq_trans (EREG 19%nat 19%bv ltac:(lia) eq_refl) R19)) by lia.
    rewrite (U_atom E 36 (hs_off h1) E36) by lia. cbn [zalu_raw]. rewrite zcanon_id by (try unfold M64; lia).
    rewrite Hoff. lia. }
  rewrite UA, (U_atom E 34 _ E34) in Hc by lia. rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
rename HFr into HFrA. lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGRA end. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msA end.
assert (KA : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem msA) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msA) HFrA x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_drop dr_regions In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [dr_r_frame dr_r_gsA dr_r_gsC dr_r_sa dr_r_vec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp, ?U23, ?U32, ?U33 in Hr; lia. }
clear HFrA.
(* ---- run 2: to free(v[0].s) ---- *)
paj_run_tok RUN HS HJ SHOK DRspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32 in Hx.
    left. split; [|lia]. right. left. split.
    - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1 | rewrite RQT; lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msB end.
rename HFr into HFrB. lazymatch goal with H : mem_grows _ (mrestrict _ (ms_mem msB)) |- _ => rename H into HGRB end.
clear HF.
assert (KB : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) (ms_mem msA) x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out E _ (w_H W1) (ms_mem msA) (ms_mem msB) HFrB x Hx).
  intros (r & Hin & Hr).
  match type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp, ?U23, ?U32, ?U33 in Hr; lia. }
clear HFrB.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
assert (Usp1 : spZ (ms_regs msB) = dsp0 cx + - DRAIN_FRAME).
{ unfold spZ at 1. rewrite Q2, Usp, Hsp. lia. }
assert (R10f : getr (ms_regs msB) 10 = w64 (fst r0)) by (rewrite Q10, E39; reflexivity).
assert (G3 : getr (ms_regs msB) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs msB) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (HCH : chain_pre ly1 (aview SEGS (w_H W1) (ms_mem msB)) (ms_regs msB) []).
{ assert (Hd8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  apply (achain_chain_pre ly1 _ (spZ (ms_regs msB)) ((rg_s RG + 4) / 8) [] (ms_regs msB)).
  - apply achain_low. lia.
  - lia.
  - unfold s0Z. rewrite Q8, (EREG 8%nat 8%bv ltac:(lia) eq_refl), R8. unfold w64. apply unsigned_lit_small. lia.
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia. }
(* the text block is in the journal's footprint when it is one of the entry's blocks *)
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HROM0 & HPERM0 & _ & _ & _ & _ & _ & Hmok0).
assert (Htsrc : In (fst r0, Z.of_nat (length (snd r0)) + 1) (asrc_blks h1)).
{ unfold asrc_blks, alist_blks. right. apply in_or_app. left. apply in_or_app. right. rewrite Erecs. left. reflexivity. }
assert (HFP : In (fst r0, Z.of_nat (length (snd r0)) + 1) (ablocks B (dxly cx) (dxS cx)) ->
  forall i, 0 <= i < req_size (Z.of_nat (length (snd r0)) + 1) -> inFP (dFP cx) (fst r0 + i)).
{ intros Hin0 i Hi. apply (Permutation_in _ HPERM0) in Hin0. destruct Hin0 as [X | Hin0].
  { exfalso. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Htsrc. }
  assert (HnR : ~ In (fst r0, Z.of_nat (length (snd r0)) + 1) (dxrest cx)).
  { intros X. pose proof (dw_nodup_app_r _ _ HND) as HND2.
    apply (dw_nodup_app_disj _ _ _ HND2 Htsrc). apply in_or_app. right. exact X. }
  unfold dFP, dr_fp. apply inFP_cons. right.
  exists (fst r0, fst r0 + req_size (Z.of_nat (length (snd r0)) + 1)). split; [|cbn [fst snd]; lia].
  unfold ablocks_fp. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r0, Z.of_nat (length (snd r0)) + 1)).
  apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
  apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
  apply in_app_or in Hin0. destruct Hin0 as [X|X]; [apply in_or_app; right; apply in_or_app; right; exact X | contradiction]. }
(* the budget for the free *)
pose proof HBUD as (HMLE & Hsp0 & Hcost & Hbb & Hmaxt).
destruct Hfut as (tl2 & Hlf & Htl).
assert (Hdrop : ddrop s1 a = [RelayRunT.RFree (Z.of_nat (length (dhead s1)) + 1) (nth 0 (drain_b_c.da_pend a) RelayRunF.adr0)])
  by exact (dm_ddrop_whole s1 a Hw).
assert (Hctl : tr_cost MT tl = mo_free MT + tr_cost MT tl2).
{ rewrite Htl, (dm_tr_cost_app MT RG), (dm_cost_ddrop MT RG), Hw. reflexivity. }
assert (HSZ : tr_sizes_ok tl2).
{ pose proof HOUT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & Hmx0 & Hlo0 & _).
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & Hob1).
  pose proof HHIST as (_ & _ & _ & _ & _ & Hno & _).
  pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhp & _).
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Sexp & _ & _).
  pose proof Sexp as (_ & _ & _ & _ & Encap & _).
  eapply (dw_dlfut_sizes cx s1); [lia | lia | | | | | | exact Hlf].
  - destruct Hob1 as [(X & _)|(X & _)]; lia.
  - rewrite Hno. lia.
  - rewrite <- Hka. unfold drain_b_c.ent_ka. destruct (Z.eqb_spec (re_hp e1) 0); [lia|].
    destruct Hhp as [(X & _)|(_ & _ & _ & X & _)]; lia.
  - rewrite <- Hen. unfold hl_n. lia.
  - rewrite <- Hecap. unfold hl_n in Encap. lia. }
assert (HMOf : mo_ok MT S1 (mo_free MT)).
{ pose proof (gs_tr_cost_nonneg MT MTL tl2 HSZ) as Hc2. pose proof (mo_free_nonneg MT MTL) as Hf.
  exact (mok_station MT (dxS cx) S1 (dcost MT cx) spent (mo_free MT) MTL Hmok0 HMLE Hf ltac:(lia)). }
rewrite (pal_free B TL).
eapply SRr_bind.
{ exact (AFREE W1 (ms_regs msB) (ms_mem msB) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS (dxmd cx) [] ly1 S1 _ k1
    (fst r0) (Z.of_nat (length (snd r0)) + 1) (- DRAIN_FRAME) (getr (ms_regs msB) 1) []
    HJi R0in R10f Usp1 eq_refl ltac:(lia) ltac:(lia) G3 G4 eq_refl
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HFP HMOf). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (l1 & l2 & Hbl1 & Hbl2) & Hfr2 & Hkept2
  & Hmle2 & Herr2 & Hpres2).
rewrite Q1.
pose proof (proj1 HJ2i) as HAR2.
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSPres2 & _).
assert (HJ2 : @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1)).
{ apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
    (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1) memS); [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG |].
  intros x Hx. exfalso. lia. }
clear HJ2i.
assert (Hne_t : (dxG cx, ATABLE) <> (fst r0, Z.of_nat (length (snd r0)) + 1)).
{ intros X. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Htsrc. }
assert (Hne_v : (pv, AREC * cap) <> (fst r0, Z.of_nat (length (snd r0)) + 1)).
{ intros X. injection X as X1 _. apply Pnv. rewrite X1. left. reflexivity. }
assert (KEEPBLK : forall b, In b (ablocks B ly1 S1) -> b <> (fst r0, Z.of_nat (length (snd r0)) + 1) ->
  In b (ablocks B ly2 S2)).
{ intros b Hb Hne. rewrite Hbl2. rewrite Hbl1 in Hb. apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb|[Hb|Hb]]; [left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | right; exact Hb]. }
assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)) by exact (KEEPBLK _ HGin1 Hne_t).
assert (Hvin2 : In (pv, AREC * cap) (ablocks B ly2 S2)) by exact (KEEPBLK _ Hvin Hne_v).
assert (DTF : dxG cx + 896 <= fst r0 \/ fst r0 + (Z.of_nat (length (snd r0)) + 1) <= dxG cx).
{ pose proof (dw_blk_apart _ _ _ _ _ _ _ _ _ HAR HGin1 R0in Hne_t) as X.
  rewrite RQT, dw_req_pos in X by lia. exact X. }
apply dw_hide_i in DTF.
assert (DVF : pv + 16 * cap <= fst r0 \/ fst r0 + (Z.of_nat (length (snd r0)) + 1) <= pv).
{ pose proof (dw_blk_apart _ _ _ _ _ _ _ _ _ HAR Hvin R0in Hne_v) as X.
  rewrite RQV, dw_req_pos in X by lia. exact X. }
apply dw_hide_i in DVF.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 HGin2) as (_ & _ & _ & _ & HGpres2 & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hvin2) as (_ & _ & _ & _ & HVpres2 & _ & _).
rewrite RQT in HGpres2. rewrite RQV in HVpres2.
destruct Hkept2 as (KF1 & KF2 & KF3 & _ & KF5 & _).
assert (NOWN : forall (ly : alayout) S (W : world SEGS) m md a, AR SEGS B ly S W m md -> rg_s RG <= a < rg_s RG + 384 ->
  ~ aowned B ly S a).
{ intros ly S W m md x HA0 Hx Ho. pose proof (HG x (dw_inG_gs x Hx)) as (Hi & Hno & _).
  exact (Hno (proj1 (al_owned_image _ _ LAWS ly S W m md x HA0 Hi) Ho)). }
assert (GSV : forall x, rg_s RG <= x < rg_s RG + 384 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) (ms_mem msB) x).
{ intros x Hx. pose proof (HG x (dw_inG_gs x Hx)) as (Hi & Hno & _). apply KF3; [exact Hi | exact Hno | exact (dw_gs_errno x Hx)]. }
assert (GSW : forall x, rg_s RG <= x < rg_s RG + 384 ->
  writable_at SEGS (mrestrict (w_H W1) (ms_mem msB)) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x).
{ intros x Hx. pose proof (HG x (dw_inG_gs x Hx)) as (Hi & Hno & _). apply dw_writable_img; [exact Hi|].
  apply Hpres2; [exact Hi | exact (NOWN _ _ _ _ _ x HAR Hx) | exact (NOWN _ _ _ _ _ x HAR2 Hx) | exact (dw_gs_errno x Hx) |].
  intros Hb. apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR R0in Hb Hi). }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 2 (spZ regs1)); [exact Usp | |].
    + intros x Hx. apply KF1; lia.
    + intros x Hx _. apply (apresent_writable SEGS). apply HSPres2. lia.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 23 HA); [exact U23 | |].
    + intros x Hx. apply GSV. lia.
    + intros x Hx. apply GSW. lia.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 23 HA); [exact U23 | |].
    + intros x Hx. apply GSV. lia.
    + intros x Hx. apply GSW. lia.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 32 SA); [exact U32 | |].
    + intros x Hx. replace x with (dxG cx + (x - dxG cx)) by lia.
      apply (KF2 _ _ _ HGin1); [rewrite RQT; lia|]. cbv beta. rewrite dw_req_pos by lia. unfold dw_hide in DTF. lia.
    + intros x Hx _. apply (apresent_writable SEGS). exact (proj1 (HGpres2 x ltac:(lia))).
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 33 pv); [exact U33 | |].
    + intros x Hx. replace x with (pv + (x - pv)) by lia.
      apply (KF2 _ _ _ Hvin); [rewrite RQV; lia|]. cbv beta. rewrite dw_req_pos by lia. unfold dw_hide in DVF. lia.
    + intros x Hx. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (Usp2 : bv_unsigned (ew Ea 2) = spZ regs1) by (rewrite OLDa by lia; exact Usp).
assert (U23a : bv_unsigned (ew Ea 23) = HA) by (rewrite OLDa by lia; exact U23).
assert (U32a : bv_unsigned (ew Ea 32) = SA) by (rewrite OLDa by lia; exact U32).
assert (U33a : bv_unsigned (ew Ea 33) = pv) by (rewrite OLDa by lia; exact U33).
assert (SHOK2 : sh_ok SEGS BxD SHD Ea (mrestrict (w_H W2) mem2)).
{ apply (dw_shok Ea ly2 S2 W2 mem2 md2 (dxG cx) SA HA pv cap HAR2 HGin2 ltac:(lia) ltac:(lia) Hvin2 ltac:(lia)
    ltac:(lia) ltac:(lia)).
  - rewrite OLDa by lia. rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl), R21. reflexivity.
  - rewrite OLDa by lia. rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23. reflexivity.
  - rewrite OLDa by lia. exact E32.
  - rewrite OLDa by lia. exact E33. }
paj_run_tok RUN HS HJ2 SHOK2 DRspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp2, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23a in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23a in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32a in Hx.
    left. split; [|lia]. right. left. split.
    - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2 | rewrite RQT; lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msC end.
rename HFr into HFrC. lazymatch goal with H : mem_grows _ (mrestrict _ (ms_mem msC)) |- _ => rename H into HGRC end.
clear HF.
assert (KC : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W2) (ms_mem msC) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msC) HFrC x Hx).
  intros (r & Hin & Hr).
  match type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp2, ?U23a, ?U32a, ?U33a in Hr; lia. }
clear HFrC.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* the pending count: |rs0| < 2 ^ 26 (each pending text is nonempty, DHIST bounds the pending bytes) *)
assert (Hrs0 : Z.of_nat (length rs0) < 2 ^ 26).
{ pose proof HHIST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
  assert (Hps : pstream s1 = skipn (Z.to_nat (drain_b_c.ds_off s1)) (bzs (snd r0)) ++
    concat (map (fun r => bzs (snd r)) rs0)).
  { unfold pstream, prest. rewrite <- Hpend. reflexivity. }
  assert (HF1 : Forall (fun r => (1 <= length (snd r))%nat) rs0).
  { eapply Forall_impl; [|exact (Forall_inv_tail Pfa)]. intros r (_ & _ & _ & X). exact (X eq_refl). }
  pose proof (dw_concat_len rs0 HF1) as X. rewrite Hps, length_app in D10. lia. }
set (NV := 16 * Z.of_nat (length rs0)) in *.
assert (HNV : 0 <= NV /\ NV + 16 <= 16 * cap) by (unfold NV; lia).
assert (Usp3 : spZ (ms_regs msC) = dsp0 cx + - DRAIN_FRAME).
{ unfold spZ at 1. rewrite P2, Usp2, Hsp. lia. }
assert (G10 : getr (ms_regs msC) 10 = w64 pv) by (rewrite P10, OLDa by lia; exact E33).
assert (G11 : getr (ms_regs msC) 11 = w64 (pv + 16)) by (rewrite P11, U33a; reflexivity).
assert (G12 : getr (ms_regs msC) 12 = w64 NV).
{ rewrite P12.
  transitivity (sv_denot Ea (SAlu ALU_SLL (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1))) (SLit 4))).
  { cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite (dw_U_len Ea (hl_n (hs_pending h1))); [unfold NV; lia | rewrite OLDa by lia; exact E35 | lia]. }
assert (DTV : dxG cx + 896 <= pv \/ pv + 16 * cap <= dxG cx).
{ assert (Hne : (dxG cx, ATABLE) <> (pv, AREC * cap)).
  { intros X. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Hvsrc. }
  pose proof (dw_blk_apart _ _ _ _ _ _ _ _ _ HAR HGin1 Hvin Hne) as X. rewrite RQT, RQV in X. exact X. }
apply dw_hide_i in DTV.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARC.
assert (ROMC : rom_view SEGS W2 (ms_mem msC))
  by (exact (ajournal_gx_rom_view SEGS B pa_segs_low (G_DR B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROMO HROM0)).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARC Hvin2) as (_ & _ & _ & _ & HVpresC & _ & _). rewrite RQV in HVpresC.
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_asan_memmove)
    (fun x => pv <= x < pv + NV)
    (fun regs' mem' => getr regs' 10 = w64 pv /\
       forall i, 0 <= i < NV -> aview SEGS (w_H W2) mem' (pv + i) = aview SEGS (w_H W2) (ms_mem msC) (pv + 16 + i))
    W2 (ms_regs msC) (ms_mem msC) DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly2 S2 _ (k1 + 1) (- DRAIN_FRAME) _ HG eq_refl HJ2).
  - exact Usp3.
  - unfold DRAIN_FRAME. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite P3, OLDa, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3 by lia. exact Hgp.
  - rewrite P4, OLDa, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4 by lia. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros x. destruct (Z_le_gt_dec pv x); destruct (Z_lt_ge_dec x (pv + NV));
      [left; lia | right; lia | right; lia | right; lia].
  - intros x Hx Hg. exfalso. apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia|].
    exact (proj1 (HG x Hg)).
  - intros x Hx Hng. split; [|lia].
    destruct (in_dec dw_pair_dec (pv, AREC * cap) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
    + right. left. split.
      * apply (Permutation_in _ HPERM0) in Hin0. destruct Hin0 as [X | Hin0].
        { exfalso. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Hvsrc. }
        assert (HnR : ~ In (pv, AREC * cap) (dxrest cx)).
        { intros X. apply (dw_nodup_app_disj _ _ _ (dw_nodup_app_r _ _ HND) Hvsrc). apply in_or_app. right. exact X. }
        unfold dFP, dr_fp. apply inFP_cons. right.
        exists (pv, pv + req_size (AREC * cap)). split; [|cbn [fst snd]; rewrite RQV; lia].
        unfold ablocks_fp. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (pv, AREC * cap)).
        apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
        apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
        apply in_app_or in Hin0. destruct Hin0 as [X|X];
          [apply in_or_app; right; apply in_or_app; right; exact X | contradiction].
      * exists pv, (AREC * cap). split; [exact Hvin2 | rewrite RQV; lia].
    + right. right. left. exists pv, (AREC * cap). split; [exact Hvin2|]. split; [exact Hnot0 | rewrite RQV; lia].
  - intros HPRE HSC.
    apply (AMEMMOVE ly2 S2 W2 (ms_regs msC) (ms_mem msC) _ pv (pv + 16) NV HPRE G10 G11 G12).
    + lia.
    + lia.
    + lia.
    + intros x Hx. destruct (HVpresC x ltac:(lia)) as [HPx HPo].
      split; [exact (apresent_writable SEGS _ _ _ HPx)|]. split; [exact HPo|]. rewrite Usp3. lia.
    + eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + intros Hn. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia | exact Hn].
    + lia.
    + lia.
    + intros x Hx. destruct (HVpresC x ltac:(lia)) as [HPx _].
      split; [exact (aview_some_of_apresent SEGS _ _ _ HPx)|]. rewrite Usp3. lia.
    + eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + intros Hn. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia | exact Hn].
    + exact ROMC.
    + intros Hn. split.
      * eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; unfold NV in Hn; lia].
      * eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; unfold NV in Hn; lia].
    + intros x Hx Hr. apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia | exact Hr]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (HR10 & HMV) & Hfr3 & Hpres3).
assert (Usp3a : bv_unsigned (ew Ea 2) = dsp0 cx + - DRAIN_FRAME) by (rewrite Usp2, Hsp; lia).
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 2 (spZ regs1)); [exact Usp2 | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | lia | lia].
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 23 HA); [exact U23a | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | | lia]. intros Hwr.
    apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia|].
    exact (proj1 (HG x (dw_inG_gs x ltac:(lia)))).
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 23 HA); [exact U23a | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | | lia]. intros Hwr.
    apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia|].
    exact (proj1 (HG x (dw_inG_gs x ltac:(lia)))).
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 32 SA); [exact U32a | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | | lia]. unfold dw_hide in DTV. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 64 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 64)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
assert (Usp4 : bv_unsigned (ew Eb 2) = spZ regs1) by (rewrite OLDb by lia; exact Usp2).
assert (U23b : bv_unsigned (ew Eb 23) = HA) by (rewrite OLDb by lia; exact U23a).
assert (U32b : bv_unsigned (ew Eb 32) = SA) by (rewrite OLDb by lia; exact U32a).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (SHOK3 : sh_ok SEGS BxD SHD Eb (mrestrict (w_H W2) mem3)).
{ apply (dw_shok Eb ly2 S2 W2 mem3 md3 (dxG cx) SA HA pv cap HAR3 HGin2 ltac:(lia) ltac:(lia) Hvin2 ltac:(lia)
    ltac:(lia) ltac:(lia)).
  - rewrite OLDb, OLDa by lia. rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl), R21. reflexivity.
  - rewrite OLDb, OLDa by lia. rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23. reflexivity.
  - rewrite OLDb, OLDa by lia. exact E32.
  - rewrite OLDb, OLDa by lia. exact E33. }
paj_run_to_tok RUNTO HS HJ3 SHOK3 DRspan A_dr_join.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp4, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23b in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23b in Hx. apply dw_inG_gs. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32b in Hx.
  left. split; [|lia]. right. left. split.
  - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
  - exists (dxG cx), ATABLE. split; [exact HGin2 | rewrite RQT; lia]. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
rename HFr into HFrD. lazymatch goal with H : mem_grows (mrestrict _ mem3) _ |- _ => rename H into HGRD end.
clear HF.
assert (KD : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W2) mem3 x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out Eb _ (w_H W2) mem3 (ms_mem msF) HFrD x Hx).
  intros (r & Hin & Hr).
  match type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp4, ?U23b, ?U32b in Hr; lia. }
clear HFrD.
(* ---- the regions at the join ---- *)
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF1. cbn [ms_mem restrict] in RF1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RF2. cbn [ms_mem restrict] in RF2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RF3. cbn [ms_mem restrict] in RF3.
assert (E35b : ew Eb 35 = Z_to_bv 64 (hl_n (hs_pending h1))) by (rewrite OLDb, OLDa by lia; exact E35).
pose proof (field_of_region Eb _ 23 HA _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1)))
  (Z.of_nat (length rs0)) RF1 U23b ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite denot_lit_U, (dw_U_pn1 Eb (hl_n (hs_pending h1)) E35b) by lia; f_equal; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V24.
pose proof (field_of_region Eb _ 23 HA _ _ _ _ _ 32 8%N (SLit 0) 0 RF2 U23b
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V32.
pose proof (field_of_region Eb _ 32 SA _ _ _ _ _ 24 8%N (SOff 38 0) (re_used e1) RF3 U32b
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite OLDb, OLDa by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VBU.
change (N.to_nat 4) with 4%nat in V24. change (N.to_nat 8) with 8%nat in V32, VBU.
clear RF1 RF2 RF3.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (21%bv : bv 5) F21.
prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
prreg HS (27%bv : bv 5) F27.
clear HS SHOK3.
match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARF.
pose proof HJ3 as (_ & _ & (memSF & HJiF & _) & _).
pose proof HJiF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSPresF & _).
rewrite !Z.add_0_r in HSPresF. clear memSF HJiF.
(* ---- what the free left ---- *)
assert (FREEV : forall x, (alloc_ceiling <= x < 2 ^ 64 /\ ~ (dsp0 cx + - DRAIN_FRAME - ASTACK <= x < dsp0 cx + - DRAIN_FRAME)) \/
  (exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= x < b + req_size n /\
     ~ (fst r0 <= x < fst r0 + req_size (Z.of_nat (length (snd r0)) + 1))) \/
  (in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B)) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) (ms_mem msB) x).
{ intros x [[Hx1 Hx2] | [(b & n & Hb & Hbx & Hnf) | (Hi & Hno)]].
  - apply KF1; [exact Hx1 | exact Hx2].
  - replace x with (b + (x - b)) by lia. apply (KF2 b n (x - b) Hb); [lia | cbv beta; lia].
  - destruct (Z_le_gt_dec (as_errno B) x); destruct (Z_lt_ge_dec x (as_errno B + 4)).
    + replace x with (as_errno B + (x - as_errno B)) by lia. apply Herr2. lia.
    + apply KF3; [exact Hi | exact Hno | lia].
    + apply KF3; [exact Hi | exact Hno | lia].
    + apply KF3; [exact Hi | exact Hno | lia]. }
(* ---- every byte the cut reads, from the DE memory to the join's ---- *)
assert (VALL : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  ~ (pv <= x < pv + NV) -> ~ (dsp0 cx + - DRAIN_FRAME - ASTACK <= x < dsp0 cx + - DRAIN_FRAME) ->
  ((alloc_ceiling <= x < 2 ^ 64) \/
   (exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= x < b + req_size n /\
      ~ (fst r0 <= x < fst r0 + req_size (Z.of_nat (length (snd r0)) + 1))) \/
   (in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))) ->
  aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2 N3 N4 N5 N6 HC.
  rewrite (KD x Hx N1 N2 N3 N4).
  rewrite (Hfr3 x Hx N5) by lia.
  rewrite (KC x Hx N1 N2 N3 N4).
  rewrite FREEV by (destruct HC as [H1 | [H2 | H3]]; [left; split; [exact H1 | exact N6] | right; left; exact H2 | right; right; exact H3]).
  rewrite (KB x Hx N1 N2 N3 N4). exact (KA x Hx N1 N2 N3 N4). }
assert (VSAW : forall x, SA + 24 <= x < SA + 32 -> aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; exact (dw_aview_of_vm2 W1 W2 m1 (ms_mem msF) (SA + 24) 8 (re_used e1) x MUSED VBU ltac:(cbn; lia))).
assert (PIMG : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
  apresent (w_H W1) m1 x -> apresent (w_H W2) (ms_mem msF) x).
{ intros x Hi Hno He Hp.
  assert (NO : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md -> ~ aowned B ly S x)
    by (intros ly S W m md HA0 Ho; apply Hno; exact (proj1 (al_owned_image _ _ LAWS ly S W m md x HA0 Hi) Ho)).
  apply (apresent_grows _ _ _ x HGRD). apply Hpres3. apply (apresent_grows _ _ _ x HGRC).
  apply (Hpres2 x Hi (NO _ _ _ _ _ HAR) (NO _ _ _ _ _ HAR2) He).
  - intros Hb. exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR R0in Hb Hi).
  - apply (apresent_grows _ _ _ x HGRB). apply (apresent_grows _ _ _ x HGRA). exact Hp. }
assert (WIMG : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W2 (ms_mem msF)) x).
{ intros x Hi Hno Hwr. destruct (Z_le_gt_dec (as_errno B) x); destruct (Z_lt_ge_dec x (as_errno B + 4)).
  - replace x with (as_errno B + (x - as_errno B)) by lia. unfold arm. apply dw_errno_writable. lia.
  - unfold arm in *. apply (dw_writable_img W1 W2 m1 (ms_mem msF) x Hi); [|exact Hwr].
    intros Hp. apply PIMG; [exact Hi | exact Hno | lia | exact Hp].
  - unfold arm in *. apply (dw_writable_img W1 W2 m1 (ms_mem msF) x Hi); [|exact Hwr].
    intros Hp. apply PIMG; [exact Hi | exact Hno | lia | exact Hp].
  - unfold arm in *. apply (dw_writable_img W1 W2 m1 (ms_mem msF) x Hi); [|exact Hwr].
    intros Hp. apply PIMG; [exact Hi | exact Hno | lia | exact Hp]. }
assert (KIM : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> abyte_kept W1 m1 W2 (ms_mem msF) x).
{ intros x Hi Hno N2 N3. pose proof (pa_img_range x Hi) as Hxr. split; [|exact (WIMG x Hi Hno)].
  apply VALL; [lia | lia | exact N2 | exact N3 | | | lia | right; right; split; [exact Hi | exact Hno]].
  - intros Hs. apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR HGin1); [rewrite RQT; lia | exact Hi].
  - intros Hv. apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR Hvin); [rewrite RQV; lia | exact Hi]. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx ->
  ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W2 (ms_mem msF) x).
{ intros x Hx Hn. split.
  - apply VALL; [lia | rewrite Hsp; lia | lia | lia | lia | lia | lia | left; lia].
  - intros _. unfold arm. apply (apresent_writable SEGS). apply HSPresF. lia. }
assert (KBL : forall b n x, In (b, n) (ablocks B ly2 S2) -> (b, n) <> (pv, AREC * cap) -> b <= x < b + req_size n ->
  abyte_kept W1 m1 W2 (ms_mem msF) x).
{ intros b n x Hb Hne Hx.
  assert (Hb1 : In (b, n) (ablocks B ly1 S1)).
  { rewrite Hbl2 in Hb. rewrite Hbl1. apply in_app_or in Hb. apply in_or_app.
    destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
  assert (Hnf : (b, n) <> (fst r0, Z.of_nat (length (snd r0)) + 1)).
  { apply (dw_nodup_neq l1 l2); [rewrite <- Hbl1; exact (dw_ablocks_nodup _ _ _ _ _ HAR) | rewrite <- Hbl2; exact Hb]. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb1) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARF Hb) as (_ & _ & _ & _ & HbpresF & _ & _).
  pose proof (dw_blk_apart _ _ _ _ _ _ _ _ _ HAR Hb1 R0in Hnf) as DF.
  rewrite (dw_req_pos (Z.of_nat (length (snd r0)) + 1)) in DF by lia.
  pose proof (dw_blk_apart _ _ _ _ _ _ _ _ _ HAR2 Hb Hvin2 Hne) as DVb. rewrite RQV in DVb.
  assert (Hnimg : ~ in_img SEGS x) by exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR Hb1 Hx).
  split; [|intros _; unfold arm; apply (apresent_writable SEGS); exact (proj1 (HbpresF x Hx))].
  destruct (Z_le_gt_dec (SA + 24) x); destruct (Z_lt_ge_dec x (SA + 32)); [apply VSAW; lia | | |];
  (apply VALL; [lia | lia | | | lia | lia | lia |]);
  try (intros Hw0; apply Hnimg; exact (proj1 (HG x (dw_inG_gs x ltac:(lia)))));
  right; left; exists b, n; (split; [exact Hb1|]); (split; [exact Hx|]); rewrite dw_req_pos by lia; lia. }
(* ---- the record array after the memmove ---- *)
set (JK := skipn (16 * length rs0) (concat (map text_rec (r0 :: rs0)) ++ hl_junk (hs_pending h1))).
assert (Hold : Z.of_nat (length (concat (map text_rec (r0 :: rs0)) ++ hl_junk (hs_pending h1))) = 16 * cap).
{ rewrite length_app, Nat2Z.inj_add, dw_len_text_recs, Hjl, Hpn. unfold AREC. cbn [length]. lia. }
assert (Hjk : Z.of_nat (length JK) = AREC * (cap - Z.of_nat (length rs0))).
{ unfold JK. rewrite length_skipn. unfold AREC. lia. }
assert (VEX : forall x, pv <= x < pv + 16 * cap -> 0 <= x < 2 ^ 64 /\ ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) /\
  ~ (HA + 24 <= x < HA + 28) /\ ~ (HA + 32 <= x < HA + 40) /\ ~ (SA + 24 <= x < SA + 32) /\
  ~ (dsp0 cx + - DRAIN_FRAME - ASTACK <= x < dsp0 cx + - DRAIN_FRAME)).
{ intros x Hx. unfold dw_hide in DTV.
  assert (Hni : ~ in_img SEGS x) by (apply (blk_img SEGS B LAWS _ _ _ _ _ _ _ x HAR Hvin); rewrite RQV; lia).
  split; [lia|]. split; [lia|].
  split; [intros Hw0; apply Hni; exact (proj1 (HG x (dw_inG_gs x ltac:(lia))))|].
  split; [intros Hw0; apply Hni; exact (proj1 (HG x (dw_inG_gs x ltac:(lia))))|].
  split; lia. }
assert (GV : garr8 SEGS (arm W2 (ms_mem msF)) pv (bzs (concat (map text_rec rs0) ++ JK))).
{ unfold arm, JK. apply (dw_vec_after (w_H W1) (w_H W2) m1 (ms_mem msF) pv r0 rs0 (hl_junk (hs_pending h1)) Hvg).
  - intros j Hj. destruct (VEX (pv + j) ltac:(lia)) as (Vq0 & Vq1 & Vq2 & Vq3 & Vq4 & Vq5).
    destruct (VEX (pv + 16 + j) ltac:(lia)) as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5).
    rewrite (KD (pv + j) Vq0 Vq1 Vq2 Vq3 Vq4). rewrite (HMV j) by (unfold NV; lia).
    rewrite (KC (pv + 16 + j) Y0 Y1 Y2 Y3 Y4).
    rewrite FREEV by (right; left; exists pv, (AREC * cap); split; [exact Hvin|]; split; [rewrite RQV; lia|];
      rewrite dw_req_pos by lia; unfold dw_hide in DVF; lia).
    rewrite (KB (pv + 16 + j) Y0 Y1 Y2 Y3 Y4). exact (KA (pv + 16 + j) Y0 Y1 Y2 Y3 Y4).
  - intros x Hx. rewrite Hold in Hx. destruct (VEX x ltac:(lia)) as (Vq0 & Vq1 & Vq2 & Vq3 & Vq4 & Vq5).
    apply VALL; [exact Vq0 | exact Vq1 | exact Vq2 | exact Vq3 | exact Vq4 | unfold NV; lia | exact Vq5 |].
    right. left. exists pv, (AREC * cap). split; [exact Hvin|]. split; [rewrite RQV; lia|].
    rewrite dw_req_pos by lia. unfold dw_hide in DVF. lia. }
(* ---- the memory core ---- *)
assert (HMEM2 : DMEM B RG cx ly2 S2 W2 (ms_mem msF) mdF (k1 + 1) e1 (dw_hdrop h1 rs0 JK) (dsv cx s1) out1 ev1
  (lines (dSTR cx) D) LB1).
{ apply (dw_dmem cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 ly2 S2 W2 (ms_mem msF) mdF
    (k1 + 1) r0 rs0 JK l1 l2 Hj4 HGSA ltac:(unfold AENT, ATABLE; lia) HMEM eq_refl eq_refl HROM0 HJ3 Hfr2 Erecs Hbl1 Hbl2
    KBL KIM WIMG KFR PIMG V24 V32 Hjk GV). }
(* ---- the history at p = 0 ---- *)
assert (HDH : DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D)
  (dw_hdrop h1 rs0 JK) LB1 (Z.of_nat (length (drl s1)))).
{ pose proof HHIST as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  assert (Hps : pstream s1 = ddata s1 ++ pstream (dnext (dlive cx) (dxmx cx) s1))
    by exact (dm_ps_split RG HGSB cx s1 RS_wf ltac:(lia)).
  pose proof (dm_chunk_le RG (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as Hcl.
  pose proof (dm_lines_le RG (drain_b_c.ds_ref s1) (ddata s1)) as Hll.
  unfold DHIST.
  change (pstream (dsv cx s1)) with (pstream (dnext (dlive cx) (dxmx cx) s1)).
  change (drain_b_c.ds_ref (dsv cx s1)) with (feed (drain_b_c.ds_ref s1) (ddata s1)).
  change (drain_b_c.ds_no (dsv cx s1)) with (drain_b_c.ds_no s1).
  change (drain_b_c.ds_H (dsv cx s1)) with (drain_b_c.ds_H s1).
  change (drain_b_c.ds_en (dsv cx s1)) with (drain_b_c.ds_en s1 + Z.of_nat (length (dref s1))).
  split; [rewrite D1, Hps, app_assoc; reflexivity|].
  split; [rewrite D2, feed_app; reflexivity|].
  split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
  split; [exact D8|]. split; [exact D9|].
  rewrite Hps, length_app in D10, D11. unfold drl, dchunk, dref.
  split; [clear - D10 Hcl; lia | clear - D11 Hll; lia]. }
(* ---- the meter ---- *)
assert (HBUD2 : dbud MT MMAX cx S2 (spent + mo_free MT) tl2).
{ pose proof (mo_free_nonneg MT MTL) as Hf. unfold dbud.
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ HMLE Hmle2)|].
  split; [lia|]. split; [lia|].
  split.
  - assert (Hbs : blocks_bytes S2 + (Z.of_nat (length (snd r0)) + 1) = blocks_bytes S1).
    { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1), Hbl1, Hbl2, !bsum_app, bsum_cons.
      cbn [snd]. lia. }
    (* C3: the free of the head record (ddrop's one request, RFree (|head| + 1)) lowers the live bytes by exactly
       its size, so the peak of the rest stays in room (W_tr_peak.v tr_peak_free) *)
    assert (HdlC3 : Z.of_nat (length (dhead s1)) = Z.of_nat (length (snd r0)))
      by (rewrite Hhead; unfold bzs; rewrite length_map; reflexivity).
    assert (HpkC3 : tr_peak tl2 - (Z.of_nat (length (snd r0)) + 1) <= tr_peak tl)
      by (rewrite Htl, Hdrop; cbn [app]; rewrite W_tr_peak.tr_peak_free, HdlC3; lia).
    lia.
  - assert (Htm : tr_max tl = Z.max 0 (tr_max tl2)) by (rewrite Htl, (dm_tr_max_app RG HGSB), dm_max_ddrop; reflexivity).
    lia. }
assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> (k < 32)%nat ->
  Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
{ intros r k Hr Hk Hkr. rewrite Hr, OLDb, OLDa by lia. apply EREG; assumption. }
apply (HK W2). unfold DDM.
match type of Hlf with dlfut _ _ ?a0 _ _ _ _ _ ?jb0 ?o0 ?ha0 ?ks0 _ =>
  exists (ms_regs msF), ly2, S2, (ms_mem msF), mdF, (k1 + 1), e1, (dw_hdrop h1 rs0 JK), out1, ev1, LB1,
    (spent + mo_free MT), jb0, a0, o0, ha0, ks0, tl2 end.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ at 1; rewrite (RK _ 2%nat F2) by (first [lia | reflexivity]); exact Hsp|].
split; [rewrite (RK _ 3%nat F3) by (first [lia | reflexivity]); exact R3|].
split; [rewrite (RK _ 4%nat F4) by (first [lia | reflexivity]); exact R4|].
split; [rewrite (RK _ 18%nat F18) by (first [lia | reflexivity]); exact R18|].
split; [rewrite (RK _ 9%nat F9) by (first [lia | reflexivity]); exact R9|].
split; [rewrite (RK _ 8%nat F8) by (first [lia | reflexivity]); exact R8|].
split; [rewrite (RK _ 21%nat F21) by (first [lia | reflexivity]); exact R21|].
split; [rewrite (RK _ 23%nat F23) by (first [lia | reflexivity]); exact R23|].
split; [rewrite (RK _ 19%nat F19) by (first [lia | reflexivity]); exact R19|].
split; [rewrite F22, OLDb, OLDa by lia; exact E32|].
split; [rewrite F25, U32b; reflexivity|].
split; [rewrite F26, U32b; reflexivity|].
split; [rewrite F27, U32b; reflexivity|].
split; [exact (dw_frame_kept cx W1 m1 W2 (ms_mem msF) KFR HFR)|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S56]|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S64]|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S48]|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S200]|].
split; [exact Hn0|]. split; [lia|]. split; [exact Hdata|].
split; [exact HMEM2|].
split; [exact Hnonul|]. split; [exact Hused|]. split; [exact HSAME|].
split; [exact Hcap|]. split; [exact HU|]. split; [exact Hskip|]. split; [exact HH|]. split; [exact Hka|].
split; [exact Hei|].
split; [unfold dnext; cbn [drain_b_c.ds_pend]; rewrite Hw; unfold dtail; rewrite <- Hpend; reflexivity|].
split; [unfold dnext; cbn [drain_b_c.ds_off]; rewrite Hw; reflexivity|].
split; [exact Hst|]. split; [exact Hen|]. split; [exact Hecap|].
split; [exact HDH|]. split; [exact HRST|]. split; [exact Hlf | exact HBUD2].
Qed.

Definition drop_keep_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DE B MT MMAX RG cx s1 D W1 c1 -> dwhole s1 = false ->
(forall W2 c2, DDM B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Lemma drop_keep_ok : drop_keep_stmt.
Proof. exact drop_keep. Qed.

Definition drop_whole_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DE B MT MMAX RG cx s1 D W1 c1 -> dwhole s1 = true ->
(forall W2 c2, DDM B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Lemma drop_whole_ok : drop_whole_stmt.
Proof. exact drop_whole. Qed.

Theorem dr_drop_split : drop_keep_stmt -> drop_whole_stmt -> dr_dropb_stmt B MT MMAX RG ->
dr_drop_stmt B MT MMAX RG.
Proof.
intros KEEP WHOLE DROPB cx s1 D W1 c1 HB HDE Hdll Hdlr.
destruct (dwhole s1) eqn:Hw.
- apply (WHOLE cx s1 D W1 c1 HB HDE Hw). intros W2 c2 HQ. exact (DROPB cx s1 D W2 c2 HB HQ Hdll Hdlr).
- apply (KEEP cx s1 D W1 c1 HB HDE Hw). intros W2 c2 HQ. exact (DROPB cx s1 D W2 c2 HB HQ Hdll Hdlr).
Qed.

(* The first half with its no-drop arm discharged: what is left is the drop arm and the second half. *)
Theorem dr_drop_of_whole : drop_whole_stmt -> dr_dropb_stmt B MT MMAX RG -> dr_drop_stmt B MT MMAX RG.
Proof. intros WHOLE DROPB. exact (dr_drop_split drop_keep_ok WHOLE DROPB). Qed.

(* ---- DROP's first half: DE 0x835ac -> DDM 0x83668, both arms proved; the second half
   (DDM -> DLL 0 q / DLR 0, W_drain_dropb_cx.v dr_dropb_stmt) is the one premise left. ---- *)
Theorem dr_drop_of : dr_dropb_stmt B MT MMAX RG -> dr_drop_stmt B MT MMAX RG.
Proof. exact (dr_drop_of_whole drop_whole_ok). Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice B, 2026-10-30): dr_drop_x proves W_drain_cx_x.v's dr_drop_stmt_x, the
   DROP segment over W_drain_cx_x.v's Section variables (B PST ARx MT RP MMAX RG), at DRAIN_STK_x: the keep arm
   drop_keep_x (the 0x83600 test fails: h->pending_off += n) and the whole arm drop_whole_x (the inlined list_drop:
   free #1 at 0x83618 through AFREE in its caller-context form afree_cf_rule_c_x, its return address 0x8361c in CTX_F
   by HCTX_fr1; __asan_memmove at 0x83648 through AMEMMOVE; h->pending.n -= 1, h->pending_off = 0), both to
   W_drain_dropb_cx.v's cut DDM_x; dr_drop_of_x joins the two arms and W_drain_dropb.v's dr_dropb_x is the second half.
   The entry's ghost list Hp and budget kr are carried; the cut's own ghost list Hp1 is kept (after the free, the rule
   post's).  The room round at free #1: the cut's dbud_x owes ddrop's RFree first; W_drain_room_x.v's gs_rm_take gives
   the rule's room and its post the room of the rest, gs_cnt_call the count premise and gs_cnt_free the counts after
   the call.  The lemmas that read AR have twins dk_NAME_x / dw_NAME_x over ARx (a block's size is nonnegative by BLKN,
   the block shadow facts are W_journal_x.v's hp0 lemmas by HP0); the AR-free lemmas and drop_entry are cited with the
   Section arguments they abstract; the AR file's Section-local Ltacs are restated with _x.
   Everything above this line is unchanged; the twin only adds names (the AR name with _x).
   ============================================================================================================ *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_drain_room_x W_drain_dropb.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the generic-relation / placement facts the walks read (a Theorem Labs lane's texts, 2026-10-30) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
(* W_drain_cx_x.v Section c's hypotheses (its text), the allocator rules in their caller-context forms *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis HCTX_fr1 : In [BASE + AF_fr_drain + 0x540] CTX_F.   (* free #1 returns to 0x8361c *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* ALLOC_TAIL is no hypothesis: W_drain_cx_x.alloc_tail_x SEGS B ARx LAWS *)

(* ================================================================================================
   THE KEEP ARM over ARx (drop_keep above, the 0x83600 test fails: h->pending_off += n, no drop).
   The AR lemmas it cites that read AR get a dk_*_x twin; the AR-free ones are cited with the Section
   variables and hypotheses they abstract.  W_drain_drop.v's Ltacs of Section c end with it: dk_in_x /
   dk_awr_x are their texts.
   ================================================================================================ *)
Ltac dk_in_x := repeat (first [left; reflexivity | right]).

(* two different live blocks are apart, and the live blocks are distinct (dk_blk_apart / dk_ablocks_nodup over ARx;
   the positive request sizes from BLKN, ARx's blocks law having no size conjunct) *)
Lemma dk_blk_apart_x : forall ly S Hp (W : world SEGS) mem md p n q m,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S Hp W mem md p n q m HAR Hpn Hq Hne.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hpn) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hk) as Hk0.
  exact (proj1 (req_size_pos k ltac:(lia))). }
pose proof (dk_pw_nodup RG _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (dk_nodup_map_inj f _ _ _ Hnd Hpn Hq E))).
destruct (dk_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hpn) (in_map f _ _ Hq) Hf) as [X|X];
  unfold zdisjoint, f in X; cbn [fst snd] in X; lia.
Qed.
Lemma dk_ablocks_nodup_x : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hpn : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hpn) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hk) as Hk0.
  exact (proj1 (req_size_pos k ltac:(lia))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (dk_pw_nodup RG _ Hpos Hpw)).
Qed.

(* a live block lies off the image (dr_blk_noimg over ARx, from the law alx_client_img) *)
Lemma dk_blk_noimg_x : forall ly S Hp (W : world SEGS) mem md q m a,
ARx ly S Hp W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S Hp W mem md q m a HAR Hin Ha.
exact (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR (or_introl (ex_intro _ q (ex_intro _ m (conj Hin Ha)))))).
Qed.

Lemma dk_blk_out_x : forall ly S Hp (W : world SEGS) mem md q n a HA,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a < q + req_size n ->
rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC -> dk_out HA a.
Proof.
intros ly S Hp W mem md q n a HA HAR Hin Ha H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
split; [clear - H4096 Hceil Ha C1; lia|]. intros Hx.
apply (dk_blk_noimg_x ly S Hp W mem md q n a HAR Hin Ha). apply (dk_gs_img B RG HG). clear - Hx H1 H2; lia.
Qed.

Lemma dk_aentry_fp_out_x : forall ly S Hp (W : world SEGS) mem md e HA,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e -> rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> dk_out HA a.
Proof.
intros ly S Hp W mem md e HA HAR HE H1 H2 r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & HU8 & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
  apply (dk_blk_out_x ly S Hp W mem md (re_buf e) (re_cap e) a HA HAR Hin); [|exact H1 | exact H2].
  pose proof (dk_req_ge RG (re_cap e)) as Hrq. clear - Ha Hj HU HU8 Hrq. lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. clear - Ha; lia.
    * unfold bzs in Ha. rewrite length_map, (dk_key_ptrs_len RG) in Ha.
      apply (dk_blk_out_x ly S Hp W mem md (re_hp e) (re_kh e) a HA HAR Hin); [|exact H1 | exact H2].
      pose proof (dk_req_ge RG (re_kh e)) as Hrq. unfold re_nheld in Hk1. clear - Ha Hk1 Hrq. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (dk_blk_out_x ly S Hp W mem md _ _ a HA HAR Hin); [|exact H1 | exact H2].
    pose proof (dk_req_ge RG (Z.of_nat (length (key_text k)) + 1)) as Hrq. clear - Ha Hrq. lia.
Qed.

Lemma dk_alist_fp_out_x : forall ly S Hp (W : world SEGS) mem md LA l lines HA,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
(forall a, LA <= a < LA + 16 -> dk_out HA a) ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> dk_out HA a.
Proof.
intros ly S Hp W mem md LA l lines HA HAR HL H1 H2 HLA r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. exact (HLA a Ha).
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, (dk_recs_len RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
    apply (dk_blk_out_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HA HAR Hin); [|exact H1 | exact H2].
    pose proof (dk_req_ge RG (AREC * hl_cap l)) as Hrq.
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (dk_blk_out_x ly S Hp W mem md _ _ a HA HAR Hin); [|exact H1 | exact H2].
    pose proof (dk_req_ge RG (Z.of_nat (length (snd q)) + 1)) as Hrq. clear - Ha Hrq. lia.
Qed.

Lemma dk_aout_fp_out_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out HA,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> dk_out HA a.
Proof.
intros ly S Hp W mem md c O mx no cap out HA HAR HOUT H1 H2 r Hr a Ha.
pose proof (dk_zpw RG _ 2 3 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dk_zpw RG _ 2 4 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dk_zpw RG _ 2 5 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dk_zpw RG _ 2 6 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dk_zpw RG _ 2 7 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dk_zpw RG _ 2 8 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dk_zpw RG _ 2 9 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dk_zpw RG _ 2 10 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
pose proof (dk_zpw RG _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D11.
cbn [nth] in D3, D4, D5, D6, D7, D8, D9, D10, D11.
unfold zdisj in D3, D4, D5, D6, D7, D8, D9, D10, D11.
cbn [fst snd] in D3, D4, D5, D6, D7, D8, D9, D10, D11.
assert (GLB : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> 0 <= a < 2 ^ 64).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI) as HL. unfold kLowMemEnd in HL. clear - HL. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). split; [clear - Ha Hs1 Hs2; lia | clear - Ha D7 H1 H2; lia].
- split; [apply (GLB (rg_nout RG) 8); [unfold G_DR, G_SL; dk_in_x | exact Ha] | clear - Ha D8 H1 H2; lia].
- split; [apply (GLB (rg_capout RG) 8); [unfold G_DR, G_SL; dk_in_x | exact Ha] | clear - Ha D9 H1 H2; lia].
- split; [apply (GLB (rg_out RG) 8); [unfold G_DR, G_SL; dk_in_x | exact Ha] | clear - Ha D10 H1 H2; lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  split; [clear - Ha H9; lia | clear - Ha D3 H1 H2; lia].
- split; [apply (GLB (rg_client_broken RG) 1); [unfold G_DR, G_SL; dk_in_x | exact Ha] | clear - Ha D4 H1 H2; lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  split; [clear - Ha H12; lia | clear - Ha D6 H1 H2; lia].
- split; [apply (GLB (rg_send_eintr RG) 1); [unfold G_DR, G_SL; dk_in_x | exact Ha] | clear - Ha D5 H1 H2; lia].
- split; [apply (GLB (as_errno B) 4); [unfold G_DR, G_SL; dk_in_x | exact Ha] | clear - Ha D11 H1 H2; lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; clear - Hc Hc0; lia|].
  apply (dk_blk_out_x ly S Hp W mem md out cap a HA HAR Hin); [|exact H1 | exact H2].
  pose proof (dk_req_ge RG cap) as Hrq. clear - Ha Hrq. lia.
Qed.

(* asrc_at with the pending offset set to o' (dk_asrc_off over ARx) *)
Lemma dk_asrc_off_x : forall ly S Hp (W : world SEGS) m m' md HA h o',
ARx ly S Hp W m md -> asrc_at B ly S W m HA h ->
(forall b, In b (asrc_blks h) -> In b (ablocks B ly S)) ->
rg_s RG <= HA -> HA + 96 <= rg_s RG + 4 * ASRC ->
(forall a, dk_out HA a -> abyte_kept W m W m' a) ->
(forall a, writable_at SEGS (arm W m) a -> writable_at SEGS (arm W m') a) ->
val_mem SEGS (arm W m') (HA + 32) 8 o' ->
(exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r))) ->
asrc_at B ly S W m' HA (dk_setoff h o').
Proof.
intros ly S Hp W m m' md HA h o' HAR HS HBL H1 H2 KO KW Vo Ho.
pose proof asan_consts as (C1 & _).
pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2, H2.
pose proof HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18
  & S19 & S20 & S21 & S22 & S23 & S24).
assert (Hvm : forall a n v, HA <= a -> (a + Z.of_nat n <= HA + 32 \/ HA + 40 <= a) -> a + Z.of_nat n <= HA + 96 ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v).
{ intros a n v Ha Hn1 Hn2 Hv. apply (akept_vm W m); [|exact Hv].
  intros x Hx. apply KO. split; [clear - Hx Ha Hn2 Hg1 Hg2 H1 H2; lia | clear - Hx Hn1; lia]. }
assert (KL : forall LA l lines, alist_at B ly S W m LA l lines ->
  (HA + 40 <= LA \/ LA + 16 <= HA + 32) -> HA <= LA -> LA + 16 <= HA + 96 ->
  (forall b, In b (alist_blks l) -> In b (ablocks B ly S)) -> alist_at B ly S W m' LA l lines).
{ intros LA l lines HL Hl1 Hl2 Hl3 HBl.
  apply (alist_at_kept B ly S W m); [exact HL | | exact HBl].
  intros r Hr x Hx. apply KO.
  refine (dk_alist_fp_out_x ly S Hp W m md LA l lines HA HAR HL H1 _ _ r Hr x Hx); [unfold ASRC; exact H2|].
  intros y Hy. split; [clear - Hy Hl2 Hl3 Hg1 Hg2 H1 H2; lia | clear - Hy Hl1; lia]. }
unfold dk_setoff, asrc_at.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad hs_expected
  hs_held].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S1]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S2]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S3]|].
split; [apply Hvm; [lia | left; cbn; lia | cbn; lia | exact S4]|].
split; [intros i Hi; apply KW; exact (S5 i Hi)|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|]. split; [exact S9|].
split; [apply KL; [exact S10 | right; lia | lia | lia |
  intros b Hb; apply HBL; right; apply in_or_app; left; exact Hb]|].
split; [exact Vo|].
split; [apply Hvm; [lia | right; lia | cbn; lia | exact S12]|].
split; [apply Hvm; [lia | right; lia | cbn; lia | exact S13]|].
split; [apply Hvm; [lia | right; lia | cbn; lia | exact S14]|].
split; [right; exact Ho|].
split; [exact S16|]. split; [exact S17|]. split; [exact S18|]. split; [exact S19|].
split.
{ apply (akept_garr8 W m); [|exact S20]. intros x Hx. apply KO.
  unfold bzs in Hx. rewrite length_map, S19 in Hx.
  apply (dk_blk_out_x ly S Hp W m md (hs_partial h) APARTIAL x HA HAR S18); [|exact H1 | unfold ASRC; exact H2].
  pose proof (dk_req_ge RG APARTIAL) as Hrq. clear - Hx Hrq. lia. }
split; [exact S21|].
split; [apply KL; [exact S22 | left; lia | lia | lia |
  intros b Hb; apply HBL; right; apply in_or_app; right; apply in_or_app; left; exact Hb]|].
split; [apply KL; [exact S23 | left; lia | lia | lia |
  intros b Hb; apply HBL; right; apply in_or_app; right; apply in_or_app; right; exact Hb]|].
exact S24.
Qed.

(* W_drain_drop.v's dk_awr (Section c's Ltac), its text: the write obligation of both runs *)
Ltac dk_awr_x Usp Hsp UHA USA HTB RQT HSAlo HSAhi HDS HDF HAb :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite Usp, Hsp in Hx;
    left; split; [left; clear - Hx HDS HDF; lia | clear - Hx; lia] |];
  apply awr_ok_x_cons_g;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite UHA in Hx;
    apply dk_inG; unfold ASRC; clear - Hx HAb; lia |];
  apply awr_ok_x_cons_g;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite UHA in Hx;
    apply dk_inG; unfold ASRC; clear - Hx HAb; lia |];
  apply awr_ok_x_cons;
  [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USA in Hx;
    left; split; [|clear - Hx; lia]; right; left; split;
    [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; clear - Hx; lia
    | do 2 eexists; split; [exact HTB | rewrite RQT; clear - Hx HSAlo HSAhi; lia] ] |];
  apply awr_ok_x_cons; [|apply awr_ok_x_nil];
  intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; clear - Hx; lia.


(* ---- DROP's whole arm over ARx (drop_whole_x below): W_drain_drop.v's dw_* lemmas that read AR, each as dw_NAME_x
   over ARx (Hp after S); its AR-free dw_* lemmas, dw_hdrop / dw_hide and drop_entry are cited with their Section
   arguments. ---- *)
(* W_drain_drop.v dw_blk_apart: two different live blocks are apart (a block's size is nonnegative: BLKN) *)
Lemma dw_blk_apart_x : forall ly S Hp (W : world SEGS) mem md p n q m,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S Hp W mem md p n q m HAR Hpi Hq Hne.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hpi) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  exact (proj1 (req_size_pos k (BLKN _ _ _ _ _ _ _ _ HAR Hk))). }
pose proof (dw_pw_nodup RG _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (dw_nodup_map_inj f _ _ _ Hnd Hpi Hq E))).
destruct (dw_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hpi) (in_map f _ _ Hq) Hf) as [X|X];
  unfold zdisjoint, f in X; cbn [fst snd] in X; lia.
Qed.
(* W_drain_drop.v dw_ablocks_nodup *)
Lemma dw_ablocks_nodup_x : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
destruct (ablocks B ly S) as [|[p n] l] eqn:Eb; [apply List.NoDup_nil|].
assert (Hpi : In (p, n) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hpi) as (_ & _ & _ & _ & _ & Hpw).
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hpos : forall x, In x (map f (ablocks B ly S)) -> 1 <= snd x).
{ intros x Hx. apply in_map_iff in Hx as ([r k] & <- & Hk).
  exact (proj1 (req_size_pos k (BLKN _ _ _ _ _ _ _ _ HAR Hk))). }
rewrite <- Eb. exact (NoDup_map_inv f _ (dw_pw_nodup RG _ Hpos Hpw)).
Qed.
(* W_drain_drop.v dw_shok: the three shadow entries of the walk's state, in any ARx state that has the table and the
   vector (the heap blocks' shadow facts from HP0) *)
Lemma dw_shok_x : forall E' ly S Hp (W : world SEGS) mem md G SA HA pv cap,
  ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + 56 <= G + 896 ->
  In (pv, AREC * cap) (ablocks B ly S) -> 0 < cap ->
  rg_s RG <= HA -> HA + 96 <= rg_s RG + 384 ->
  ew E' 21 = Z_to_bv 64 SB -> ew E' 23 = Z_to_bv 64 HA -> ew E' 32 = Z_to_bv 64 SA -> ew E' 33 = Z_to_bv 64 pv ->
  sh_ok SEGS BxD SHD E' (mrestrict (w_H W) mem).
Proof.
intros E' ly S Hp W mem md G SA HA pv cap HAR HGi H1 H2 HVi Hc HA1 HA2 X21 X23 X32 X33.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2.
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (RQV : req_size (AREC * cap) = 16 * cap) by (unfold AREC; apply (dw_req_pos RG); lia).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HGi) as (_ & HG4096 & HGceil & HGapp & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HVi) as (_ & HV4096 & HVceil & HVapp & _).
rewrite RQT in HGceil, HGapp. rewrite RQV in HVceil, HVapp.
assert (UB : U E' BxD = SHADOW_OFF) by (unfold BxD; rewrite (U_atom E' 21 SB X21) by (unfold SB; lia); reflexivity).
unfold sh_ok, SHD. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range SEGS (w_H W) mem E' BxD 32 SA 56 SA 0 56); [| exact UB | | lia | lia |].
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md G ATABLE);
      [exact HAR | exact HGi | lia | rewrite RQT; lia].
  + apply (U_atom E' 32 SA X32). lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem E' BxD 23 HA 96 HA 0 96); [| exact UB | | lia | lia |].
  + eapply range_addressable_sub; [exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md _ _ HAR HGSZ) | lia |].
    unfold ASRC. lia.
  + apply (U_atom E' 23 HA X23). lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem E' BxD 33 pv 16 pv 0 16); [| exact UB | | lia | lia |].
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md pv (AREC * cap));
      [exact HAR | exact HVi | lia | rewrite RQV; lia].
  + apply (U_atom E' 33 pv X33). lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HVapp. unfold SHADOW_OFF. lia.
Qed.


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp W mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREER : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_F R.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* DMEM_x across the store: the memory m2 keeps every byte off [HA + 32, HA + 40), which holds o' (dk_dmem_off over
   ARx; the journal at the entry's Hp and the cut's Hp1) *)
Lemma dk_dmem_off_xR : forall cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 m2 md2 o',
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
(forall a, dk_out (dHA RG cx) a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
val_mem SEGS (arm W1 m2) (dHA RG cx + 32) 8 o' ->
(exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r))) ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m2 md2 k1 e1 (dk_setoff h1 o') s' out1 ev1 sent LB1.
Proof.
intros cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 m2 md2 o' Hst Htop HG1 HG2 Hj Hno Hoc HM HJ2 KV KP
  Vo Ho.
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof asan_consts as (C1 & _).
assert (Hj3 : Z.of_nat (dxj cx) <= 3) by (clear - Hj; lia).
assert (HAb : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 4 * ASRC)
  by (unfold dHA, ASRC; clear - Hj3; lia).
destruct HAb as (HA1 & HA2).
assert (KB : forall a, dk_out (dHA RG cx) a -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha. split; [exact (KV a Ha)|]. unfold arm. apply writable_kept. exact (KP a). }
assert (KW : forall a, writable_at SEGS (arm W1 m1) a -> writable_at SEGS (arm W1 m2) a)
  by (intros a; unfold arm; apply writable_kept; exact (KP a)).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (INB : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx) -> In b (ablocks B ly1 S1))
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (SAO : forall x, dxSA cx <= x < dxSA cx + AENT -> dk_out (dHA RG cx) x).
{ intros x Hx. apply (dk_blk_out_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE x _ HAR HTB); [|exact HA1 | exact HA2].
  rewrite RQT. unfold ATABLE, AENT in Hx, HG2 |- *. clear - Hx HG1 HG2. lia. }
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _).
unfold DMEM_xR. rewrite Hno, Hoc.
split; [exact HJ2|].
split.
{ intros a Ha. pose proof (pa_img_range a (dr_rom_img a Ha)) as Hai.
  rewrite KV; [exact (Hrom a Ha)|]. split; [clear - Hai; lia|]. intros Hx. apply (HGR a); [|exact Ha].
  apply dk_inG. clear - Hx HA1 HA2; lia. }
split; [intros a Ha1 Ha2 Ha3 Hp'; apply KP; exact (Hpres a Ha1 Ha2 Ha3 Hp')|].
split; [exact Hframes|].
split.
{ apply (dk_frame_kept RG HGSB cx W1 m1 W1 m2); [|exact HFR]. intros a Ha. apply KB.
  unfold ESTACK in Hst. split; [clear - Ha Hst Htop C1; lia | clear - Ha Hst HA2 Hg2 C1; lia]. }
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx. apply KB. apply SAO.
  rewrite (dk_entry_len e1 Hpad1 Hpad2) in Hx. unfold AENT. clear - Hx; lia. }
split; [apply (akept_awr W1 m1); [intros x Hx; apply KB; apply SAO; exact Hx | exact Hawr]|].
split.
{ apply (dk_aentry_okx_kept B RG ly1 S1 W1 m1); [exact HOKX | |
    intros b Hb; apply INB; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KB. exact (dk_aentry_fp_out_x ly1 S1 Hp1 W1 m1 md1 e1 _ HAR HOKX HA1 HA2 r Hr x Hx). }
split.
{ apply (dk_asrc_off_x ly1 S1 Hp1 W1 m1 m2 md1); [exact HAR | exact Hsrc | | exact HA1 | exact HA2 | exact KB
    | exact KW | exact Vo | exact Ho].
  intros b Hb. apply INB. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Ho'). exists f, o.
  assert (Hij' : Z.of_nat i <> Z.of_nat (dxj cx)) by (clear - Hij; lia).
  assert (Hi3 : Z.of_nat i <= 3) by (clear - Hi; lia).
  split; [|split; [|exact Ho']]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx; apply KB;
  unfold dk_out, dHA; unfold ASRC in Hx, Hg2 |- *; cbn in Hx;
  (split; [clear - Hx Hg1 Hg2 Hi3; lia | clear - Hx Hij' Hj3 Hi3; lia]). }
split.
{ intros x Hx Hn. destruct (Hgsk x Hx Hn) as [A1 A2].
  assert (Hxo : dk_out (dHA RG cx) x)
    by (unfold dk_out; unfold ASRC in Hx, Hg2, Hn; split; [clear - Hx Hg1 Hg2; lia | clear - Hn; lia]).
  destruct (KB x Hxo) as [B1 B2]. split; [rewrite B1; exact A1 | intros Hw; apply B2; apply A2; exact Hw]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1); [exact Hout | |
    intros b Hb; apply INB; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
  intros r Hr x Hx. apply KB. exact (dk_aout_fp_out_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ _ HAR Hout HA1 HA2 r Hr x Hx). }
split; [exact Hlivout | exact Hperm].
Qed.
Lemma drop_keep_xR : forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W1 c1 -> dwhole s1 = false ->
(forall W2 c2, DDM_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hp kr s1 D W1 c1 HB HDE Hwh Hddm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
(* ---- DE_x's witnesses ---- *)
destruct HDE as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hcfg & Hsp & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & HFR & M56 & M64 & M48 & M200 & M32 & M80 & M40 & M192 &
  Hn0 & Hjunk & HMEM & HnoNul & Hused & HSAME & Hcap & HU & Hskip & HKT & HKA & Heintr & Hpend & Hoff & Hstate &
  Hen & Hecap & HHIST & HRS & Hfut & HBUD).
pose proof HMEM as (HJ & _ & _ & _ & _ & Hgarr & Hawr & HOKX & Hsrc & _ & _ & _ & _ & Hperm).
pose proof HFR as (F208 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F224 & F216 & F176 & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & HBrest).
assert (Hjj : (dxj cx < 4)%nat) by exact (proj1 (proj2 (proj2 (proj2 HBrest)))). clear HBrest.
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
fold (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HJp : forall x, dsp0 cx - DRAIN_STK_x <= x < dsp0 cx -> apresent (w_H W1) m1 x).
{ pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJq & _).
  intros x Hx. apply HJq. clear - Hx. lia. }
assert (HSP1 : alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\
  spZ regs1 mod 16 = 0).
{ rewrite Hsp, HDF. rewrite HDS in Hslo. clear - Hceil Hslo Hshi H47 Hal16 C1.
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Zminus_mod, Hal16. reflexivity. }
(* ---- the relay's table block and the entry at SA ---- *)
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & _).
rewrite RQT in HGceil, HGia.
unfold ATABLE, AENT in HSAhi.
assert (HSAb : 4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling) by (clear - HSAlo HSAhi HG4096 HGceil; lia).
(* ---- g_s[j] ---- *)
pose proof HGSB as (HGS1 & HGS2 & HGS3). unfold ASRC in HGS2.
assert (HAb : rg_s RG <= dHA RG cx /\ dHA RG cx + 96 <= rg_s RG + 384 /\ dHA RG cx mod 8 = 0).
{ unfold dHA. assert (Hj3 : Z.of_nat (dxj cx) <= 3) by (clear - Hjj; lia).
  split; [unfold ASRC; clear - Hj3; lia|]. split; [unfold ASRC; clear - Hj3; lia|].
  rewrite Z.add_mod, HGS3 by lia.
  replace (ASRC * Z.of_nat (dxj cx)) with ((12 * Z.of_nat (dxj cx)) * 8) by (unfold ASRC; ring).
  rewrite Z_mod_mult. reflexivity. }
pose proof Hsrc as (_ & _ & _ & _ & Aawr & _ & _ & _ & _ & Apend & Aoff & _ & _ & _ & Aoffr & _).
pose proof Apend as (L1 & L2 & _ & _ & L5 & L6 & _ & _ & L9).
pose proof HRS as (_ & _ & RS_gr & RS_wf & _ & _ & RS_pe).
(* ---- the pending list: its head record r0 ---- *)
assert (Erecs : exists r0 rs0, hl_recs (hs_pending h1) = r0 :: rs0).
{ destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:E0; [|exists r0, rs0; reflexivity].
  exfalso. apply RS_pe. rewrite <- Hpend. rewrite ?E0. reflexivity. }
destruct Erecs as (r0 & rs0 & Erecs).
assert (Hpn : hl_n (hs_pending h1) = Z.of_nat (S (length rs0))) by (unfold hl_n; rewrite Erecs; reflexivity).
assert (Hpcap : 0 < hl_cap (hs_pending h1)) by (clear - L5 Hpn; lia).
destruct L6 as [(Hc0 & _) | (_ & HVin & _ & HVg)]; [clear - Hc0 Hpcap; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR HVin) as (HV16 & HV4096 & HVceil & HVia & _).
assert (RQV : req_size (AREC * hl_cap (hs_pending h1)) = AREC * hl_cap (hs_pending h1))
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by (unfold AREC; clear - Hpcap; lia); reflexivity).
rewrite RQV in HVceil, HVia. unfold AREC in HVceil.
assert (HVg' := HVg). rewrite Erecs in HVg'.
destruct (dr_head_fields RG HGSB (arm W1 m1) _ r0 rs0 _ HVg') as (HV0 & HV8). clear HVg' HVg.
assert (L9' := L9). rewrite Erecs in L9'. apply Forall_inv in L9'. destruct L9' as (Hr0in & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hr0in) as (_ & Hr04096 & Hr0ceil & _).
pose proof (req_size_pos (Z.of_nat (length (snd r0)) + 1) ltac:(lia)) as (_ & Hr0rq).
assert (Hr0b : 4096 <= fst r0 /\ fst r0 + Z.of_nat (length (snd r0)) + 1 <= alloc_ceiling)
  by (clear - Hr04096 Hr0ceil Hr0rq; lia).
rewrite unsigned_lit_small in HV0 by (clear - Hr0b C1; lia).
rewrite unsigned_lit_small in HV8 by (clear - Hr0b C1; lia).
assert (Hoffr : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
{ destruct Aoffr as [(Hx & _) | (r & rs & Hrr & Hx)]; [rewrite Erecs in Hx; discriminate|].
  rewrite Erecs in Hrr. injection Hrr as <- <-. exact Hx. }
clear Aoffr.
assert (Hdh : dhead s1 = bzs (snd r0)) by (unfold dhead; rewrite <- Hpend, Erecs; reflexivity).
assert (Hdhl : Z.of_nat (length (dhead s1)) = Z.of_nat (length (snd r0)))
  by (rewrite Hdh; unfold bzs; rewrite length_map; reflexivity).
assert (Hdn : dnum s1 <= Z.of_nat (length (dhead s1)) - drain_b_c.ds_off s1) by (unfold dnum; apply Z.le_min_l).
assert (Hkeep : drain_b_c.ds_off s1 + dnum s1 < Z.of_nat (length (snd r0))).
{ unfold dwhole in Hwh. apply Z.eqb_neq in Hwh. clear - Hwh Hdn Hdhl. lia. }
(* ---- the relay entry's buffer ---- *)
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _ & Hcapr & HUlen & Husedr & Hbufc & _).
assert (Hulen0 : 0 <= ulen s1) by (unfold ulen; lia).
assert (Hcapb : 4096 <= re_cap e1 <= 16384) by (clear - Hcapr Hcap RS_gr Hulen0; destruct Hcapr as [X|[X|X]]; lia).
clear Hcapr.
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & HJlen & Hbuf8)]; [clear - Hc0 Hcapb; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - Hcapb; lia); reflexivity).
rewrite RQC in HBceil, HBia.
destruct (dr_entry_fields RG HGSB (arm W1 m1) (dxSA cx) e1 Hpad1 Hgarr) as (MBUF & MUSED).
assert (HUb : 0 <= re_used e1 <= 16384) by (clear - HUlen Husedr Hcapb; lia).
rewrite unsigned_lit_small in MBUF by (clear - HB4096 HBceil Hcapb C1; lia).
rewrite unsigned_lit_small in MUSED by (clear - HUb; lia).
assert (Hnc : dnum s1 <= drain_b_c.ds_cap s1 - ulen s1) by (unfold dnum; apply Z.le_min_r).
assert (Hnb : 1 <= dnum s1 <= 16384) by (clear - Hn0 Hnc Hulen0 Hcap Hcapb; lia).
(* ---- the rest of drop_entry's premises ---- *)
assert (FW : forall o, 192 <= o < 200 -> writable_at SEGS (arm W1 m1) (spZ regs1 + o)).
{ intros o Ho. unfold arm. apply (apresent_writable SEGS). apply HJp. rewrite Hsp, HDF, HDS. clear - Ho; lia. }
assert (HAw : forall o, 16 <= o < 40 -> writable_at SEGS (arm W1 m1) (dHA RG cx + o))
  by (intros o Ho; apply Aawr; unfold ASRC; clear - Ho; lia).
assert (HSw : forall o, 24 <= o < 32 -> writable_at SEGS (arm W1 m1) (dxSA cx + o))
  by (intros o Ho; apply Hawr; unfold AENT; clear - Ho; lia).
assert (RAH : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (dHA RG cx) 96).
{ apply (azs_range_addressable_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1); [exact HAR|].
  destruct HGSZ as (r & Hin & H8 & Hlo & Hhi). exists r. unfold ASRC in Hhi.
  split; [exact Hin|]. split; [exact H8|]. clear - Hlo Hhi HAb; split; lia. }
assert (RAS : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (dxSA cx) 56)
  by (apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE);
      [exact HAR | exact HTB | clear - HSAlo; lia | rewrite RQT; clear - HSAhi; lia]).
assert (RAV : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (hl_v (hs_pending h1)) 16)
  by (apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR HVin);
      [lia | rewrite RQV; unfold AREC; clear - Hpcap; lia]).
assert (IAS : in_app (dxSA cx) 56)
  by (apply (in_app_sub (dxG cx) 896); [exact HGia | clear - HSAlo; lia | lia | clear - HSAhi; lia]).
assert (IAV : in_app (hl_v (hs_pending h1)) 16)
  by (apply (in_app_sub (hl_v (hs_pending h1)) (AREC * hl_cap (hs_pending h1)));
      [exact HVia | lia | lia | unfold AREC; clear - Hpcap; lia]).
assert (HV8a : hl_v (hs_pending h1) mod 8 = 0) by (apply (dk_mod8 RG); exact HV16).
assert (HB8a : re_buf e1 mod 8 = 0) by (apply (dk_mod8 RG); exact HB16).
assert (L2' : val_mem SEGS (arm W1 m1) (dHA RG cx + 24) 4 (hl_n (hs_pending h1)))
  by (replace (dHA RG cx + 24) with (dHA RG cx + 16 + 8) by lia; exact L2).
assert (HHA1 : 0x10000 <= dHA RG cx) by (clear - HAb HGS1; lia).
assert (HHA2 : dHA RG cx + 96 <= 0x5fb000) by (clear - HAb HGS2; lia).
assert (HPN : 0 <= hl_n (hs_pending h1) < 2 ^ 32) by (clear - L5 Hpn; lia).
assert (HOFF : 0 <= hs_off h1 < 2 ^ 64) by (clear - Hoffr Hr0b C1; lia).
assert (HUSD : 0 <= re_used e1 < 2 ^ 64) by (clear - HUb; lia).
assert (HPV : hl_v (hs_pending h1) + 16 <= alloc_ceiling) by (clear - HVceil Hpcap; lia).
assert (HV0r : 0 <= fst r0 < 2 ^ 64) by (clear - Hr0b C1; lia).
assert (HV8r : 0 <= Z.of_nat (length (snd r0)) < 2 ^ 64) by (clear - Hr0b C1; lia).
assert (HBUF : re_buf e1 + 1 <= alloc_ceiling) by (clear - HBceil Hcapb; lia).
assert (FR : forall off v, val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + off) 8 v ->
  val_mem SEGS (arm W1 m1) (spZ regs1 + off) 8 v) by (intros off v Hv; rewrite Hsp; exact Hv).
(* ---- the three separations ---- *)
assert (DA1 : dHA RG cx + 96 <= dxSA cx \/ dxSA cx + 56 <= dHA RG cx).
{ apply (dr_apart_of_disj RG HGSB); [lia | lia |]. intros x Hx1 Hx2.
  apply (dk_blk_noimg_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE x HAR HTB);
    [rewrite RQT; clear - Hx2 HSAlo HSAhi; lia|].
  apply (dk_gs_img B RG HG). unfold ASRC. clear - Hx1 HAb; lia. }
assert (DA2 : dHA RG cx + 96 <= hl_v (hs_pending h1) \/ hl_v (hs_pending h1) + 16 <= dHA RG cx).
{ apply (dr_apart_of_disj RG HGSB); [lia | lia |]. intros x Hx1 Hx2.
  apply (dk_blk_noimg_x ly1 S1 Hp1 W1 m1 md1 _ _ x HAR HVin); [rewrite RQV; unfold AREC; clear - Hx2 Hpcap; lia|].
  apply (dk_gs_img B RG HG). unfold ASRC. clear - Hx1 HAb; lia. }
assert (HNE : (dxG cx, ATABLE) <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))).
{ intros Heq. pose proof (Permutation_NoDup Hperm (dk_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HND.
  apply List.NoDup_cons_iff in HND as [HGnot _]. apply HGnot. rewrite Heq.
  apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left.
  unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0)) by (unfold AREC; clear - Hpcap; lia). left. reflexivity. }
assert (DA3 : dxSA cx + 56 <= hl_v (hs_pending h1) \/ hl_v (hs_pending h1) + 16 <= dxSA cx).
{ destruct (dk_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR HTB HVin HNE) as [X|X]; rewrite ?RQT, ?RQV in X;
  try unfold AREC in X; [left | right]; clear - X HSAlo HSAhi Hpcap; lia. }
destruct (drop_entry RG HGSB W1 regs1 m1 (dxSA cx) (dHA RG cx) (hl_v (hs_pending h1)) (Z.of_nat (length (snd r0)))
  (hl_n (hs_pending h1)) (hs_off h1) (re_buf e1) (re_used e1) (fst r0) (dnum s1)
  (proj1 HSP1) (proj1 (proj2 HSP1)) (proj1 (proj2 (proj2 HSP1))) (proj2 (proj2 (proj2 HSP1))) FW
  R21 R23 R19 Hnb HHA1 HHA2 (proj2 (proj2 HAb))
  HAw RAH L1 L2' Aoff HPN HOFF
  (proj1 HSAb) (proj2 HSAb) HSw RAS MBUF MUSED HUSD IAS
  HV4096 HPV HV8a RAV HV0 HV8 HV0r HV8r IAV
  HB4096 HBUF HB8a
  (FR _ _ M32) (FR _ _ M40) (FR _ _ M48) (FR _ _ M56) (FR _ _ M64) (FR _ _ M80)
  (FR _ _ F176) (FR _ _ M192) (FR _ _ M200) (FR _ _ F208) (FR _ _ F216) (FR _ _ F224)
  DA1 DA2 DA3) as [HS SHOK].
clear DA1 DA2 DA3 HNE FR.
(* ---- the symbolic run to the 0x83600 test ---- *)
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_fed)) with (Z_to_bv 64 (BASE + A_dr_fed)).
remember (Eimg (Ereg regs1 (dr_extra (dxSA cx) (hl_v (hs_pending h1)) (Z.of_nat (length (snd r0)))
  (hl_n (hs_pending h1)) (hs_off h1) (re_buf e1) (re_used e1) (fst r0)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_v (hs_pending h1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat (length (snd r0))))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (hl_n (hs_pending h1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (hs_off h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (fst r0))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (UHA : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (USA : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HS as HS0.
paj_run_tok_xR RUNR HS HJ SHOK DRspan. { dk_awr_x Usp Hsp UHA USA HTB RQT HSAlo HSAhi HDS HDF HAb. }
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ?x)) |- _ =>
  rename Hf into HFr1; rename x into msB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) _ |- _ => rename Hg into GR1 end.
match goal with Hf : frame_of _ _ m1 _ |- _ => clear Hf end.
assert (U19 : U E (SOff 19 0) = dnum s1)
  by (apply U_atom; [rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl), R19; reflexivity | clear - Hnb; lia]).
assert (U36 : U E (SOff 36 0) = hs_off h1) by (apply U_atom; [exact E36 | exact HOFF]).
assert (U34 : U E (SOff 34 0) = Z.of_nat (length (snd r0))) by (apply U_atom; [exact E34 | exact HV8r]).
assert (UADD : U E (SAlu ALU_ADD (SOff 19 0) (SOff 36 0)) = dnum s1 + hs_off h1)
  by (apply (dk_U_add RG); [exact U19 | exact U36 | clear - Hnb HOFF Hkeep Hoff Hr0b C1; lia]).
psrr_branch_tok RUNR BRR HS SHOK DRspan.
2: { (* the test holds: off + n = v[0].n, i.e. dwhole s1 = true, refuted *)
  exfalso. rewrite branch_ne_U, UADD, U34 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  clear - Hc Hkeep Hoff. lia. }
(* the test fails: no drop; the fall-through to the join 0x83668 *)
paj_run_to_tok_xR RUNTOR HS HJ SHOK DRspan A_dr_join. { dk_awr_x Usp Hsp UHA USA HTB RQT HSAlo HSAhi HDS HDF HAb. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ =>
  rename Hf into HFr2 end.
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) _ |- _ => rename Hg into GR2 end.
match goal with Hf : frame_of _ _ (ms_mem msB) _ |- _ => clear Hf end.
match type of HFr2 with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr2 end.
(* ---- the regions at the join: the frame, h->pending.n, the new h->pending_off and s->used ---- *)
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF0. cbn [ms_mem restrict] in RF0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF1. cbn [ms_mem restrict] in RF1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RF2. cbn [ms_mem restrict] in RF2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RF3. cbn [ms_mem restrict] in RF3.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS0 eq_refl) as RI0. cbn [ms_mem restrict mkst] in RI0.
set (e192 := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 32) (SLit 3)) (SOff 21 0)).
pose proof (slot_of_region E _ (spZ regs1) _ _ _ _ _ 192 e192 (U E e192) RF0 Usp ltac:(dk_in_x)
  (dk_den E e192) (dk_Urange E e192)) as VB192.
pose proof (slot_of_region E _ (spZ regs1) _ _ _ _ _ 192 e192 (U E e192) RI0 Usp ltac:(dk_in_x)
  (dk_den E e192) (dk_Urange E e192)) as VA192.
pose proof (field_of_region E _ 23 (dHA RG cx) _ _ _ _ _ 24 4%N (SOff 35 0) (hl_n (hs_pending h1)) RF1 UHA
  ltac:(dk_in_x) ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; clear - HPN; lia) ltac:(cbn; lia)) as VB24.
pose proof (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 24 8%N (SOff 38 0) (re_used e1) RF3 USA
  ltac:(dk_in_x) ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; clear - HUSD; lia) ltac:(cbn; lia)) as VBU.
pose proof (field_of_region E _ 23 (dHA RG cx) _ _ _ _ _ 32 8%N (SAlu ALU_ADD (SOff 19 0) (SOff 36 0))
  (drain_b_c.ds_off s1 + dnum s1) RF2 UHA ltac:(dk_in_x) ltac:(rewrite dk_den, UADD, Hoff, Z.add_comm; reflexivity)
  ltac:(cbn; clear - Hnb Hoff HOFF Hkeep Hr0b C1; lia) ltac:(cbn; lia)) as VO.
clear RF0 RF1 RF2 RF3 RI0.
(* ---- every byte off the new h->pending_off is the cut's ---- *)
assert (KEEPM : forall x, dk_out (dHA RG cx) x -> aview SEGS (w_H W1) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
{ intros x (Hx0 & Hxo).
  destruct (dk_in_dec RG (spZ regs1 + 192) 8 x) as [Hw | Hw].
  { exact (dk_aview_of_vm RG W1 m1 (ms_mem msF) (spZ regs1 + 192) 8 (U E e192) x VA192 VB192 Hw). }
  destruct (dk_in_dec RG (dHA RG cx + 24) 4 x) as [Hw2 | Hw2].
  { exact (dk_aview_of_vm RG W1 m1 (ms_mem msF) (dHA RG cx + 24) 4 (hl_n (hs_pending h1)) x L2' VB24 Hw2). }
  destruct (dk_in_dec RG (dxSA cx + 24) 8 x) as [Hw3 | Hw3].
  { exact (dk_aview_of_vm RG W1 m1 (ms_mem msF) (dxSA cx + 24) 8 (re_used e1) x MUSED VBU Hw3). }
  rewrite (aview_kept_out E _ (w_H W1) (ms_mem msB) (ms_mem msF) HFr2 x Hx0).
  2: { intros (r & Hin & Hr). cbn [In] in Hin.
       destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UHA, ?USA in Hr;
       clear - Hr Hw Hw2 Hw3 Hxo; lia. }
  apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msB) HFr1 x Hx0).
  intros (r & Hin & Hr). cbn [ss_mem ss_drop dr_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
  cbn [dr_r_frame dr_r_gsA dr_r_gsC dr_r_sa dr_r_vec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?Usp, ?UHA, ?USA in Hr; clear - Hr Hw Hw2 Hw3 Hxo; lia. }
assert (PRESM : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msF) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ x GR2 (apresent_grows _ _ _ x GR1 Hpx))).
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 (ms_mem msF) x).
{ intros x Hx. split.
  - apply KEEPM. rewrite HDF in Hx. rewrite HDS in Hslo.
    split; [clear - Hx Hshi H47 Hceil Hslo C1; lia | clear - Hx Hslo Hceil HAb HGS2 C1; lia].
  - unfold arm. apply writable_kept. exact (PRESM x). }
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
prreg HS (27%bv : bv 5) P27.
clear HS SHOK.
match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
(* ---- the round's future: list_drop asks nothing in this arm ---- *)
destruct Hfut as (tl2 & Hdl & Htl).
rewrite (dm_ddrop_keep s1 a Hwh) in Hdl, Htl.
change (RelayRunT.nret YO0i.sptr []) with 0%nat in Hdl. rewrite Nat.add_0_r in Hdl. rewrite Hwh in Hdl.
rewrite Htl, app_nil_l in HBUD.
set (o' := drain_b_c.ds_off s1 + dnum s1) in VO.
assert (Ho' : exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r)))
  by (exists r0, rs0; split; [exact Erecs | unfold o'; clear - Hkeep Hoff Hoffr Hnb; lia]).
(* ---- the history at p = 0 ---- *)
assert (HDH : DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D)
  (dk_setoff h1 o') LB1 (Z.of_nat (length (drl s1)))).
{ pose proof HHIST as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  assert (Hps : pstream s1 = ddata s1 ++ pstream (dnext (dlive cx) (dxmx cx) s1))
    by exact (dm_ps_split RG HGSB cx s1 RS_wf ltac:(clear - Hn0; lia)).
  pose proof (dm_chunk_le RG (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as Hcl.
  pose proof (dm_lines_le RG (drain_b_c.ds_ref s1) (ddata s1)) as Hll.
  unfold DHIST.
  change (pstream (dsv cx s1)) with (pstream (dnext (dlive cx) (dxmx cx) s1)).
  change (drain_b_c.ds_ref (dsv cx s1)) with (feed (drain_b_c.ds_ref s1) (ddata s1)).
  change (drain_b_c.ds_no (dsv cx s1)) with (drain_b_c.ds_no s1).
  change (drain_b_c.ds_H (dsv cx s1)) with (drain_b_c.ds_H s1).
  change (drain_b_c.ds_en (dsv cx s1)) with (drain_b_c.ds_en s1 + Z.of_nat (length (dref s1))).
  split; [rewrite D1, Hps, app_assoc; reflexivity|].
  split; [rewrite D2, feed_app; reflexivity|].
  split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
  split; [exact D8|]. split; [exact D9|].
  rewrite Hps, length_app in D10, D11. unfold drl, dchunk, dref.
  split; [clear - D10 Hcl; lia | clear - D11 Hll; lia]. }
(* ---- the memory core, across the store ---- *)
assert (HMEM2 : DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 (ms_mem msF) mdF k1 e1 (dk_setoff h1 o') (dsv cx s1) out1 ev1
  (lines (dSTR cx) D) LB1).
{ apply (dk_dmem_off_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1
    (ms_mem msF) mdF o');
    [ clear - Hceil Hslo HES HDF HDS; lia | clear - Hshi H47; lia | exact HSAlo | exact HSAhi | exact Hjj
    | reflexivity | reflexivity | exact HMEM | exact HJ | exact KEEPM | exact PRESM | exact VO | exact Ho' ]. }
(* ---- DDM_x ---- *)
assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> (k < 32)%nat ->
  Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
{ intros r k Hr Hk Hkr. rewrite Hr. apply EREG; assumption. }
assert (VF : forall off v, 0 <= off -> off + 8 <= 336 ->
  val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + off) 8 v ->
  val_mem SEGS (arm W1 (ms_mem msF)) (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply (akept_vm W1 m1); [|exact Hv].
  intros y Hy. apply KFR. rewrite HDF in Hy |- *. change (Z.of_nat 8) with 8 in Hy. clear - Hy Ho1 Ho2. lia. }
apply (Hddm W1). unfold DDM_xR.
exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF), mdF, k1, e1, (dk_setoff h1 o'), out1, ev1, LB1, spent, jb, a,
  (drain_b_c.da_out a), (drain_b_c.da_hp a), (drain_b_c.da_keys a), tl2.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ at 1; rewrite (RK _ 2%nat P2) by (first [lia | reflexivity]); exact Hsp|].
split; [rewrite (RK _ 3%nat P3) by (first [lia | reflexivity]); exact R3|].
split; [rewrite (RK _ 4%nat P4) by (first [lia | reflexivity]); exact R4|].
split; [rewrite (RK _ 18%nat P18) by (first [lia | reflexivity]); exact R18|].
split; [rewrite (RK _ 9%nat P9) by (first [lia | reflexivity]); exact R9|].
split; [rewrite (RK _ 8%nat P8) by (first [lia | reflexivity]); exact R8|].
split; [rewrite (RK _ 21%nat P21) by (first [lia | reflexivity]); exact R21|].
split; [rewrite (RK _ 23%nat P23) by (first [lia | reflexivity]); exact R23|].
split; [rewrite (RK _ 19%nat P19) by (first [lia | reflexivity]); exact R19|].
split; [rewrite P22, E32; reflexivity|].
split; [rewrite P25, USA; reflexivity|].
split; [rewrite P26, USA; reflexivity|].
split; [rewrite P27, USA; reflexivity|].
split; [exact (dk_frame_kept RG HGSB cx W1 m1 W1 (ms_mem msF) KFR HFR)|].
split; [apply VF; [lia | lia | exact M56]|].
split; [apply VF; [lia | lia | exact M64]|].
split; [apply VF; [lia | lia | exact M48]|].
split; [apply VF; [lia | lia | exact M200]|].
split; [exact Hn0|]. split; [clear - Hnb; lia|]. split; [exact Hjunk|].
split; [exact HMEM2|].
split; [exact HnoNul|]. split; [exact Hused|]. split; [exact HSAME|].
split; [exact Hcap|]. split; [exact HU|]. split; [exact Hskip|]. split; [exact HKT|]. split; [exact HKA|].
split; [exact Heintr|].
split; [unfold dnext; cbn [drain_b_c.ds_pend]; rewrite Hwh; exact Hpend|].
split; [unfold dnext; cbn [drain_b_c.ds_off]; rewrite Hwh; reflexivity|].
split; [exact Hstate|]. split; [exact Hen|]. split; [exact Hecap|].
split; [exact HDH|]. split; [exact HRS|]. split; [exact Hdl | exact HBUD].
Qed.
(* W_drain_drop.v dw_dmem: the memory core at the join, over ARx *)
Lemma dw_dmem_xR : forall cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 ly2 S2 Hp2 W2 m2 md2 k2 r0 rs0 jk l1 l2,
  (dxj cx < 4)%nat -> dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE ->
  DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
  drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
  rom_view SEGS (dxW cx) (dxmem cx) ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
  frames S2 = frames S1 ->
  hl_recs (hs_pending h1) = r0 :: rs0 ->
  ablocks B ly1 S1 = l1 ++ (fst r0, Z.of_nat (length (snd r0)) + 1) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  (forall b n x, In (b, n) (ablocks B ly2 S2) -> (b, n) <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) ->
     b <= x < b + req_size n -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     ~ (dHA RG cx + 24 <= x < dHA RG cx + 28) -> ~ (dHA RG cx + 32 <= x < dHA RG cx + 40) -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W2 m2) x) ->
  (forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 200) ->
     abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x) ->
  val_mem SEGS (arm W2 m2) (dHA RG cx + 24) 4 (Z.of_nat (length rs0)) ->
  val_mem SEGS (arm W2 m2) (dHA RG cx + 32) 8 0 ->
  Z.of_nat (length jk) = AREC * (hl_cap (hs_pending h1) - Z.of_nat (length rs0)) ->
  garr8 SEGS (arm W2 m2) (hl_v (hs_pending h1)) (bzs (concat (map text_rec rs0) ++ jk)) ->
  DMEM_xR B PST ARx RG R cx Hp ly2 S2 Hp2 W2 m2 md2 k2 e1 (dw_hdrop h1 rs0 jk) s' out1 ev1 sent LB1.
Proof.
intros cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 ly2 S2 Hp2 W2 m2 md2 k2 r0 rs0 jk l1 l2 Hj HG1 HG2
  HM Hno Hoc HROM0 HJ2 Hfr Hrecs Hbl1 Hbl2 KBL KIM KIMW KFR PIM V24 V32 Hjk Hgv.
destruct HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
pose proof HGSB as (Hg1 & Hg2 & _). unfold ASRC in Hg2. unfold AENT, ATABLE in HG2.
assert (Hj3 : Z.of_nat (dxj cx) <= 3) by lia.
assert (HA1 : rg_s RG <= dHA RG cx) by (unfold dHA, ASRC; lia).
assert (HA2 : dHA RG cx + 96 <= rg_s RG + 384) by (unfold dHA, ASRC; lia).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Spend & _).
pose proof Spend as (_ & _ & _ & _ & Pncap & _).
unfold hl_n in Pncap. rewrite Hrecs in Pncap. cbn [length] in Pncap.
assert (Hcp : 0 < hl_cap (hs_pending h1)) by lia.
set (f := fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)).
set (vec := (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))).
set (Al := (dxG cx, ATABLE) :: aentry_blks e1 ++ [(hs_partial h1, APARTIAL); vec]).
set (Bl := map f rs0 ++ alist_blks (hs_expected h1) ++ alist_blks (hs_held h1) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx).
assert (EO : (dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx =
  Al ++ (fst r0, Z.of_nat (length (snd r0)) + 1) :: Bl).
{ unfold Al, Bl, vec, asrc_blks, alist_blks at 1. rewrite Hrecs.
  rewrite (proj2 (Z.eqb_neq (hl_cap (hs_pending h1)) 0)) by lia.
  cbn [map app]. rewrite <- !app_assoc. cbn [app]. reflexivity. }
assert (EN : (dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx = Al ++ Bl).
{ unfold Al, Bl, vec, asrc_blks, alist_blks at 1, dw_hdrop.
  cbn [hs_partial hs_pending hs_expected hs_held hl_cap hl_v hl_recs].
  rewrite (proj2 (Z.eqb_neq (hl_cap (hs_pending h1)) 0)) by lia.
  cbn [app]. rewrite <- !app_assoc. cbn [app]. reflexivity. }
assert (HPERM2 : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++ aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx)).
{ rewrite EN, Hbl2. apply (Permutation_app_inv l1 l2 Al Bl (fst r0, Z.of_nat (length (snd r0)) + 1)).
  rewrite <- Hbl1, <- EO. exact Hperm. }
assert (INB2 : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx) -> In b (ablocks B ly2 S2))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPERM2) Hb)).
assert (HND2 : List.NoDup ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dw_hdrop h1 rs0 jk) ++
  aout_blks (drain_b_c.ds_ocap s) out1 ++ dxrest cx))
  by exact (Permutation_NoDup HPERM2 (dw_ablocks_nodup_x _ _ _ _ _ _ HAR2)).
assert (NV : forall y, In y ((dxG cx, ATABLE) :: aentry_blks e1 ++ aout_blks (drain_b_c.ds_ocap s) out1) -> y <> vec).
{ intros y Hy. rewrite EN in HND2.
  assert (E3 : Al ++ Bl = ((dxG cx, ATABLE) :: aentry_blks e1 ++ [(hs_partial h1, APARTIAL)]) ++ vec :: Bl).
  { unfold Al. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  rewrite E3 in HND2. apply (dw_nodup_neq _ _ _ _ HND2).
  destruct Hy as [<- | Hy]; [left; reflexivity|]. apply in_app_or in Hy. right. apply in_or_app.
  destruct Hy as [Hy|Hy]; [left; apply in_or_app; left; exact Hy | right].
  unfold Bl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hy. }
assert (KB2 : forall b n x, In (b, n) ((dxG cx, ATABLE) :: aentry_blks e1 ++ aout_blks (drain_b_c.ds_ocap s) out1) ->
  b <= x < b + req_size n -> abyte_kept W1 m1 W2 m2 x).
{ intros b n x Hb Hx. apply (KBL b n x); [| exact (NV _ Hb) | exact Hx]. apply INB2.
  destruct Hb as [<- | Hb]; [left; reflexivity|]. right. apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
assert (SAK : forall x, dxSA cx <= x < dxSA cx + 56 -> abyte_kept W1 m1 W2 m2 x)
  by (intros x Hx; apply (KB2 (dxG cx) ATABLE x (or_introl eq_refl)); rewrite RQT; lia).
assert (GSI : forall x, rg_s RG <= x < rg_s RG + 384 -> in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
  by (intros x Hx; destruct (HG x ((dw_inG_gs B RG) x ltac:(lia))) as (Gi3 & Gn3 & _); split; [exact Gi3 | exact Gn3]).
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _).
unfold DMEM_xR. rewrite Hno, Hoc.
split; [exact HJ2|].
split; [exact (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low (G_DR B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROMO PSTR HROM0)|].
split; [intros a Ha1 Ha2 Ha3 Hp; exact (PIM a Ha1 Ha2 Ha3 (Hpres a Ha1 Ha2 Ha3 Hp))|].
split; [rewrite Hfr; exact Hframes|].
split; [exact ((dw_frame_kept RG HGSB) cx W1 m1 W2 m2 KFR HFR)|].
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx. apply SAK.
  unfold bzs in Hx. rewrite length_map in Hx.
  assert (Hl : length (entry_bytes e1) = 56%nat).
  { unfold entry_bytes. rewrite !length_app, Hpad1, Hpad2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite Hl in Hx. cbn in Hx. lia. }
split; [apply (akept_awr W1 m1); [intros x Hx; apply SAK; unfold AENT in Hx; lia | exact Hawr]|].
split.
{ apply ((dw_aentry_okx_kept B RG) ly1 S1 W1 m1); [exact HOKX | |].
  - intros r Hr x Hx. destruct ((dw_aentry_fp_blk B RG) _ _ _ _ _ HOKX r Hr x Hx) as (b & n & Hb & Hbx).
    apply (KB2 b n x); [right; apply in_or_app; left; exact Hb | exact Hbx].
  - intros b Hb. apply INB2. right. apply in_or_app. left. exact Hb. }
split.
{ apply ((dw_asrc_drop B RG HG HGSB) ly1 S1 W1 m1 ly2 S2 W2 m2 (dHA RG cx) h1 r0 rs0 jk Hsrc HA1 HA2 Hrecs).
  - intros b Hb. apply INB2. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - apply List.NoDup_cons_iff in HND2. pose proof (dw_nodup_app_r _ _ (proj2 HND2)) as X. exact (dw_nodup_app_l _ _ X).
  - exact KBL.
  - exact KIM.
  - exact KIMW.
  - exact V24.
  - exact V32.
  - exact Hjk.
  - exact Hgv. }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (fd & o & V1 & V2 & Ho'). exists fd, o.
  assert (Hij' : Z.of_nat i <> Z.of_nat (dxj cx)) by lia.
  assert (Hi3 : Z.of_nat i <= 3) by lia.
  split; [|split; [|exact Ho']]; (apply (akept_vm W1 m1); [|assumption]); intros x Hx;
  (destruct (GSI x ltac:(unfold ASRC in Hx; cbn in Hx; lia)) as [Gi Gn]; apply KIM; [exact Gi | exact Gn | | ]);
  unfold dHA; unfold ASRC in Hx |- *; cbn in Hx; lia. }
split.
{ intros x Hx Hn. apply (dw_abyte_trans _ _ _ _ _ _ _ (Hgsk x Hx Hn)).
  unfold ASRC in Hx, Hn. destruct (GSI x ltac:(lia)) as [Gi Gn]. apply KIM; [exact Gi | exact Gn | lia | lia]. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1); [exact Hout | |].
  - intros r Hr x Hx. destruct ((dw_aout_fp_cls B RG HG HGO HRGD) _ _ _ _ _ _ _ _ _ _ Hout r Hr x Hx) as [(Gi & Gn & Gs) | (b & n & Hb & Hbx)].
    + apply KIM; [exact Gi | exact Gn | lia | lia].
    + apply (KB2 b n x); [right; apply in_or_app; right; exact Hb | exact Hbx].
  - intros b Hb. apply INB2. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split; [exact Hlivout|].
exact HPERM2.
Qed.
(* W_drain_drop.v drop_whole: DE 0x835ac -> free #1 (0x83618, AFREE at HCTX_fr1) -> __asan_memmove (0x83648,
   AMEMMOVE) -> DDM 0x83668, over ARx *)
Lemma drop_whole_xR : forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W1 c1 -> dwhole s1 = true ->
(forall W2 c2, DDM_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hpe kr s1 D W1 c1 HB HDE Hw HK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HGSB as (Hg1 & Hg2 & Hg3). unfold ASRC in Hg2.
unfold DE_xR in HDE.
destruct HDE as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & Hsp & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & HFR & S56 & S64 & S48 & S200 & S32 & S80 & S40 & S192 &
  Hn0 & Hdata & HMEM & Hnonul & Hused & HSAME & Hcap & HU & Hskip & HH & Hka & Hei & Hpend & Hoff & Hst & Hen & Hecap &
  HHIST & HRST & Hfut & HBUD).
pose proof HFR as HFR'. unfold dr_frame in HFR'. cbv zeta in HFR'.
destruct HFR' as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
pose proof HMEM as (HJ & HROM & HPRES & HFRAMES & _ & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & _ & HPERM).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & _ & HGSA & HSAG & _ & _ & _ & Hj4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
unfold AENT, ATABLE in HSAG.
assert (HSTKb : alloc_ceiling + ASTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 HDS HES HDF HAS; lia).
assert (Hspal : spZ regs1 mod 16 = 0) by (rewrite Hsp, Zminus_mod, Hal16; reflexivity).
pose proof HJ as (_ & _ & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSPres & _).
rewrite !Z.add_0_r in HSPres. clear memS0 HJi0.
(* ---- the relay's table block and the relay entry ---- *)
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
rewrite RQT in HGceil, HGapp, HGpres.
set (SA := dxSA cx) in *.
set (HA := dHA RG cx) in *.
assert (HHA : rg_s RG <= HA /\ HA + ASRC <= rg_s RG + 4 * ASRC).
{ unfold HA, dHA, ASRC. lia. }
assert (HAm : HA mod 8 = 0).
{ unfold HA, dHA, ASRC. pose proof (Z_div_mod_eq_full (rg_s RG) 8) as Hd. rewrite Hg3 in Hd.
  replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with ((rg_s RG / 8 + 12 * Z.of_nat (dxj cx)) * 8) by lia.
  apply Z_mod_mult. }
unfold ASRC in HHA.
(* ---- the harness source and its pending list ---- *)
pose proof HSRC as (_ & _ & _ & _ & Sawr & _ & _ & _ & _ & Spend & Soff & _ & _ & _
  & Srecs & _ & _ & _ & _ & _ & _ & _ & _ & _).
apply dw_hide_i in Srecs.
pose proof Spend as (Pv & Pn & Pc & Pawr & Pncap & Pvec & Pnd & Pnv & Pfa).
pose proof HRST as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:Erecs.
{ exfalso. apply RS_pe. rewrite <- Hpend. reflexivity. }
assert (Hhead : dhead s1 = bzs (snd r0)) by (unfold dhead; rewrite <- Hpend; reflexivity).
assert (Hwh : drain_b_c.ds_off s1 + dnum s1 = Z.of_nat (length (snd r0))).
{ unfold dwhole in Hw. apply Z.eqb_eq in Hw. rewrite Hw, Hhead. unfold bzs. rewrite length_map. reflexivity. }
assert (Hnb : 1 <= dnum s1 <= 16384).
{ assert (Hcapv : re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384)
    by (destruct HOKX as (_ & _ & _ & _ & _ & X & _); exact X).
  pose proof (Z.le_min_r (Z.of_nat (length (dhead s1)) - drain_b_c.ds_off s1) (drain_b_c.ds_cap s1 - ulen s1)) as X.
  fold (dnum s1) in X. unfold ulen in X. rewrite <- Hcap in X. lia. }
assert (Hpn : hl_n (hs_pending h1) = Z.of_nat (S (length rs0))) by (unfold hl_n; rewrite Erecs; reflexivity).
assert (Hcap0 : 0 < hl_cap (hs_pending h1)) by lia.
destruct Pvec as [(Hc0 & _) | (_ & Hvin & Hjl & Hvg)]; [lia|].
assert (RQV : req_size (AREC * hl_cap (hs_pending h1)) = 16 * hl_cap (hs_pending h1))
  by (unfold AREC; apply (dw_req_pos RG); lia).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hvin) as (HV16 & HV4096 & HVceil & HVapp & HVpres & _).
rewrite RQV in HVceil, HVapp, HVpres.
set (pv := hl_v (hs_pending h1)) in *.
set (cap := hl_cap (hs_pending h1)) in *.
pose proof (Forall_inv Pfa) as (R0in & R0g & _ & R0len).
assert (R0l : (1 <= length (snd r0))%nat) by exact (R0len eq_refl). clear R0len.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR R0in) as (_ & HT4096 & HTceil & HTapp & HTpres & _).
rewrite (dw_req_pos RG) in HTceil, HTapp, HTpres by lia.
pose proof ((dw_head_fields RG HGSB) _ _ _ _ _ Hvg) as (MV0 & MV8).
rewrite unsigned_lit_small in MV0, MV8 by lia.
(* ---- the relay's buffer ---- *)
pose proof HOKX as (_ & _ & Hpad1 & Hpad2 & _ & _ & HUlen & Husedr & Hbufc & _).
assert (Hcappos : 0 < re_cap e1).
{ pose proof (Z.le_min_r (Z.of_nat (length (dhead s1)) - drain_b_c.ds_off s1) (drain_b_c.ds_cap s1 - ulen s1)) as X.
  fold (dnum s1) in X. unfold ulen in X. rewrite <- Hcap in X. lia. }
destruct Hbufc as [(Hc0 & _) | (_ & Hbin & Hjunk & Hbuf8)]; [lia|].
assert (RQB : req_size (re_cap e1) = re_cap e1) by (apply (dw_req_pos RG); lia).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (HB16 & HB4096 & HBceil & _ & _ & _).
rewrite RQB in HBceil.
pose proof ((dw_entry_fields RG HGSB) _ _ _ Hpad1 HENT) as (MBUF & MUSED).
rewrite unsigned_lit_small in MBUF, MUSED by lia.
(* ---- the three separations ---- *)
assert (DHS : HA + 96 <= SA \/ SA + 56 <= HA).
{ apply (dw_apart_of_disj RG HGSB); [lia | lia |]. intros x Hx Hy.
  apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR HGin1); [rewrite RQT; lia|].
  exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia)))). }
apply dw_hide_i in DHS.
assert (DHV : HA + 96 <= pv \/ pv + 16 <= HA).
{ apply (dw_apart_of_disj RG HGSB); [lia | lia |]. intros x Hx Hy.
  apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR Hvin); [rewrite RQV; lia|].
  exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia)))). }
apply dw_hide_i in DHV.
pose proof (Permutation_NoDup HPERM (dw_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HND.
apply List.NoDup_cons_iff in HND as [HGnot HND].
assert (Hvsrc : In (pv, AREC * cap) (asrc_blks h1)).
{ unfold asrc_blks, alist_blks. fold cap. right. apply in_or_app. left. apply in_or_app. left.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
assert (DSV : SA + 56 <= pv \/ pv + 16 <= SA).
{ assert (Hne : (dxG cx, ATABLE) <> (pv, AREC * cap)).
  { intros E. apply HGnot. rewrite E. apply in_or_app. right. apply in_or_app. left. exact Hvsrc. }
  pose proof (dw_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR HGin1 Hvin Hne) as X. rewrite RQT, RQV in X.
  lia. }
apply dw_hide_i in DSV.
(* ---- the entry state ---- *)
assert (X5 : forall o, 192 <= o < 200 -> writable_at SEGS (arm W1 m1) (spZ regs1 + o)).
{ intros o Ho. unfold arm. apply (apresent_writable SEGS). apply HSPres. lia. }
assert (X13 : forall o, 16 <= o < 40 -> writable_at SEGS (arm W1 m1) (HA + o)).
{ intros o Ho. apply Sawr. unfold ASRC. lia. }
assert (X14 : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF HA 96).
{ eapply range_addressable_sub; [exact (azs_range_addressable_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR HGSZ) | lia |].
  unfold ASRC in *. lia. }
assert (X22 : forall o, 24 <= o < 32 -> writable_at SEGS (arm W1 m1) (SA + o)).
{ intros o Ho. apply HAWR. unfold AENT. lia. }
assert (X23 : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE); [exact HAR | exact HGin1 | lia |].
  rewrite RQT. lia. }
assert (X27 : in_app SA 56) by (eapply in_app_sub; [exact HGapp | lia | lia | lia]).
assert (X30 : pv mod 8 = 0).
{ pose proof (Z_div_mod_eq_full pv 16) as Hd. rewrite HV16 in Hd.
  replace pv with ((pv / 16 * 2) * 8) by lia. apply Z_mod_mult. }
assert (X31 : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF pv 16).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 pv (AREC * cap)); [exact HAR | exact Hvin | lia |].
  rewrite RQV. lia. }
assert (X36 : in_app pv 16) by (eapply in_app_sub; [exact HVapp | lia | lia | lia]).
assert (X39 : re_buf e1 mod 8 = 0).
{ pose proof (Z_div_mod_eq_full (re_buf e1) 16) as Hd. rewrite HB16 in Hd.
  replace (re_buf e1) with ((re_buf e1 / 16 * 2) * 8) by lia. apply Z_mod_mult. }
assert (Hoffr : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
{ unfold dw_hide in Srecs. destruct Srecs as [(X & _) | (r & rs & X & Y)]; [discriminate X|]. injection X as <- <-. exact Y. }
assert (Hpnr : 0 <= hl_n (hs_pending h1) < 2 ^ 32) by lia.
pose proof (drop_entry RG HGSB W1 regs1 m1 SA HA pv (Z.of_nat (length (snd r0))) (hl_n (hs_pending h1)) (hs_off h1)
  (re_buf e1) (re_used e1) (fst r0) (dnum s1)
  ltac:(lia) ltac:(lia) ltac:(lia) Hspal X5 R21 R23 R19 Hnb ltac:(lia) ltac:(lia) HAm X13 X14 Pv ltac:(replace (HA + 24) with (HA + 16 + 8) by lia; exact Pn) Soff
  Hpnr ltac:(lia) ltac:(lia) ltac:(lia) X22 X23 MBUF MUSED ltac:(lia) X27 ltac:(lia) ltac:(lia) X30 X31
  MV0 MV8 ltac:(lia) ltac:(lia) X36 ltac:(lia) ltac:(lia) X39
  ltac:(rewrite Hsp; exact S32) ltac:(rewrite Hsp; exact S40) ltac:(rewrite Hsp; exact S48)
  ltac:(rewrite Hsp; exact S56) ltac:(rewrite Hsp; exact S64) ltac:(rewrite Hsp; exact S80)
  ltac:(rewrite Hsp; exact F176) ltac:(rewrite Hsp; exact S192) ltac:(rewrite Hsp; exact S200)
  ltac:(rewrite Hsp; exact F208) ltac:(rewrite Hsp; exact F216) ltac:(rewrite Hsp; exact F224)
  DHS DHV DSV) as [HS SHOK].

subst c1. unfold cfg_at. change (w64 (BASE + A_dr_fed)) with (Z_to_bv 64 (BASE + A_dr_fed)).
remember (Eimg (Ereg regs1 (dr_extra SA pv (Z.of_nat (length (snd r0))) (hl_n (hs_pending h1)) (hs_off h1)
  (re_buf e1) (re_used e1) (fst r0)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (dr_extra SA pv (Z.of_nat (length (snd r0))) (hl_n (hs_pending h1)) (hs_off h1)
  (re_buf e1) (re_used e1) (fst r0))) E)
  by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat (length (snd r0))))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (hl_n (hs_pending h1)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (hs_off h1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_buf e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (re_used e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (fst r0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (U23 : bv_unsigned (ew E 23) = HA) by (rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = pv) by (rewrite E33; apply unsigned_lit_small; lia).
paj_run_tok_xR RUNR HS HJ SHOK DRspan.
{ cbn [ss_mem ss_drop dr_regions].
  apply awr_ok_x_cons.
  { intros x Hx. cbn [dr_r_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [dr_r_gsA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [dr_r_gsC YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons.
  { intros x Hx. cbn [dr_r_sa YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32 in Hx.
    left. split; [|lia]. right. left. split.
    - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1 | rewrite RQT; lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [dr_r_vec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
psrr_branch_tok RUNR BRR HS SHOK DRspan.
{ (* the taken edge `n + off <> v[0].n` is refuted: the head text is used up *)
  exfalso. rewrite branch_ne_U in Hc.
  assert (UA : U E (SAlu ALU_ADD (SOff 19 0) (SOff 36 0)) = Z.of_nat (length (snd r0))).
  { rewrite U_SAlu. rewrite (U_atom E 19 (dnum s1) (eq_trans (EREG 19%nat 19%bv ltac:(lia) eq_refl) R19)) by lia.
    rewrite (U_atom E 36 (hs_off h1) E36) by lia. cbn [zalu_raw]. rewrite zcanon_id by (try unfold M64; lia).
    rewrite Hoff. lia. }
  rewrite UA, (U_atom E 34 _ E34) in Hc by lia. rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
rename HFr into HFrA. lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGRA end. clear HF.
lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into msA end.
assert (KA : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem msA) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msA) HFrA x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_drop dr_regions In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [dr_r_frame dr_r_gsA dr_r_gsC dr_r_sa dr_r_vec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp, ?U23, ?U32, ?U33 in Hr; lia. }
clear HFrA.
(* ---- run 2: to free(v[0].s) ---- *)
paj_run_tok_xR RUNR HS HJ SHOK DRspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23 in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32 in Hx.
    left. split; [|lia]. right. left. split.
    - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1 | rewrite RQT; lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into msB end.
rename HFr into HFrB. lazymatch goal with H : mem_grows _ (mrestrict _ (ms_mem msB)) |- _ => rename H into HGRB end.
clear HF.
assert (KB : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) (ms_mem msA) x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out E _ (w_H W1) (ms_mem msA) (ms_mem msB) HFrB x Hx).
  intros (r & Hin & Hr).
  match type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp, ?U23, ?U32, ?U33 in Hr; lia. }
clear HFrB.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
assert (Usp1 : spZ (ms_regs msB) = dsp0 cx + - DRAIN_FRAME).
{ unfold spZ at 1. rewrite Q2, Usp, Hsp. lia. }
assert (R10f : getr (ms_regs msB) 10 = w64 (fst r0)) by (rewrite Q10, E39; reflexivity).
assert (G3 : getr (ms_regs msB) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs msB) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (HCH : chain_pre ly1 (aview SEGS (w_H W1) (ms_mem msB)) (ms_regs msB) []).
{ assert (Hd8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  apply (achain_chain_pre ly1 _ (spZ (ms_regs msB)) ((rg_s RG + 4) / 8) [] (ms_regs msB)).
  - apply achain_low. lia.
  - lia.
  - unfold s0Z. rewrite Q8, (EREG 8%nat 8%bv ltac:(lia) eq_refl), R8. unfold w64. apply unsigned_lit_small. lia.
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia. }
(* the text block is in the journal's footprint when it is one of the entry's blocks *)
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HROM0 & HPERM0 & _ & _ & _ & _ & _ & Hmok0 & _ & _).
assert (Htsrc : In (fst r0, Z.of_nat (length (snd r0)) + 1) (asrc_blks h1)).
{ unfold asrc_blks, alist_blks. right. apply in_or_app. left. apply in_or_app. right. rewrite Erecs. left. reflexivity. }
assert (HFP : In (fst r0, Z.of_nat (length (snd r0)) + 1) (ablocks B (dxly cx) (dxS cx)) ->
  forall i, 0 <= i < req_size (Z.of_nat (length (snd r0)) + 1) -> inFP (dFP cx) (fst r0 + i)).
{ intros Hin0 i Hi. apply (Permutation_in _ HPERM0) in Hin0. destruct Hin0 as [X | Hin0].
  { exfalso. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Htsrc. }
  assert (HnR : ~ In (fst r0, Z.of_nat (length (snd r0)) + 1) (dxrest cx)).
  { intros X. pose proof (dw_nodup_app_r _ _ HND) as HND2.
    apply (dw_nodup_app_disj _ _ _ HND2 Htsrc). apply in_or_app. right. exact X. }
  unfold dFP, dr_fp. apply inFP_cons. right.
  exists (fst r0, fst r0 + req_size (Z.of_nat (length (snd r0)) + 1)). split; [|cbn [fst snd]; lia].
  unfold ablocks_fp. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (fst r0, Z.of_nat (length (snd r0)) + 1)).
  apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
  apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
  apply in_app_or in Hin0. destruct Hin0 as [X|X]; [apply in_or_app; right; apply in_or_app; right; exact X | contradiction]. }
(* the budget for the free *)
pose proof HBUD as ((HMLE & Hsp0 & Hcost & Hbb & Hmaxt) & HRMc & HCNTc).
destruct Hfut as (tl2 & Hlf & Htl).
assert (Hdrop : ddrop s1 a = [RelayRunT.RFree (Z.of_nat (length (dhead s1)) + 1) (nth 0 (drain_b_c.da_pend a) RelayRunF.adr0)])
  by exact (dm_ddrop_whole s1 a Hw).
assert (Hctl : tr_cost MT tl = mo_free MT + tr_cost MT tl2).
{ rewrite Htl, (dm_tr_cost_app MT RG), (dm_cost_ddrop MT RG), Hw. reflexivity. }
assert (HSZ : tr_sizes_ok tl2).
{ pose proof HOUT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & Hmx0 & Hlo0 & _).
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & Hob1).
  pose proof HHIST as (_ & _ & _ & _ & _ & Hno & _).
  pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhp & _).
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Sexp & _ & _).
  pose proof Sexp as (_ & _ & _ & _ & Encap & _).
  eapply ((dw_dlfut_sizes RG HGSB) cx s1); [lia | lia | | | | | | exact Hlf].
  - destruct Hob1 as [(X & _)|(X & _)]; lia.
  - rewrite Hno. lia.
  - rewrite <- Hka. unfold drain_b_c.ent_ka. destruct (Z.eqb_spec (re_hp e1) 0); [lia|].
    destruct Hhp as [(X & _)|(_ & _ & _ & X & _)]; lia.
  - rewrite <- Hen. unfold hl_n. lia.
  - rewrite <- Hecap. unfold hl_n in Encap. lia. }
assert (HMOf : mo_ok MT S1 (mo_free MT)).
{ pose proof (gs_tr_cost_nonneg MT MTL tl2 HSZ) as Hc2. pose proof (mo_free_nonneg MT MTL) as Hf.
  exact (mok_station MT (dxS cx) S1 (dcost MT cx) spent (mo_free MT) MTL Hmok0 HMLE Hf ltac:(lia)). }
(* the room round at free #1 (W_drain_room_x's Section rk): ddrop's RFree (|head| + 1) is the trace's head; the
   rule's room is 1 + (MT_rk's charge of the rest + kr), its count premise the live counts *)
assert (HdlC : Z.of_nat (length (dhead s1)) = Z.of_nat (length (snd r0)))
  by (rewrite Hhead; unfold bzs; rewrite length_map; reflexivity).
assert (Etl : tl = [RelayRunT.RFree (Z.of_nat (length (snd r0)) + 1) (nth 0 (drain_b_c.da_pend a) RelayRunF.adr0)] ++ tl2)
  by (rewrite Htl, Hdrop, HdlC; reflexivity).
assert (HRMF : rp_RM RP S1 (1 + (Z.to_nat (tr_cost MT_rk tl2) + kr))).
{ rewrite Etl in HRMc.
  refine (W_drain_room_x.gs_rm_take RP S1
    [RelayRunT.RFree (Z.of_nat (length (snd r0)) + 1) (nth 0 (drain_b_c.da_pend a) RelayRunF.adr0)] tl2 kr 1 _ HRMc).
  unfold tr_cost. cbn. lia. }
assert (HCNTF : cnt_ok RP (ablocks B ly1 S1)) by exact (W_drain_room_x.gs_cnt_call RP tl _ HCNTc).
rewrite (pal_free B TL).
eapply (SRrG_bind SEGS R R_trans).
{ exact (AFREER W1 (ms_regs msB) (ms_mem msB) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) memS (dxmd cx) []
    ly1 S1 Hp1 _ k1 (fst r0) (Z.of_nat (length (snd r0)) + 1) (- DRAIN_FRAME) (getr (ms_regs msB) 1) []
    (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat
    HJi R0in R10f Usp1 eq_refl ltac:(lia) ltac:(lia)
    (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (- DRAIN_FRAME) _ HJi Usp1 ltac:(lia))
    G3 G4 eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH (RO_ARx _ _ _ _ _ _ (proj1 HJi))
    ltac:(unfold raZ; cbn [spine map]; rewrite Q1; rewrite unsigned_lit_small by lia;
          match goal with |- In [?x] _ =>
            replace x with (BASE + AF_fr_drain + 0x540) by (try unfold AF_fr_drain; try unfold BASE; ring) end;
          exact HCTX_fr1)
    HRMF HCNTF HFP HMOf). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (l1 & l2 & Hbl1 & Hbl2) & Hfr2
  & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
rewrite Q1.
pose proof (proj1 HJ2i) as HAR2.
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSPres2 & _).
assert (HJ2 : @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx)
    (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1) memS); [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG |].
  intros x Hx. exfalso. lia. }
clear HJ2i.
assert (Hne_t : (dxG cx, ATABLE) <> (fst r0, Z.of_nat (length (snd r0)) + 1)).
{ intros X. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Htsrc. }
assert (Hne_v : (pv, AREC * cap) <> (fst r0, Z.of_nat (length (snd r0)) + 1)).
{ intros X. injection X as X1 _. apply Pnv. rewrite X1. left. reflexivity. }
assert (KEEPBLK : forall b, In b (ablocks B ly1 S1) -> b <> (fst r0, Z.of_nat (length (snd r0)) + 1) ->
  In b (ablocks B ly2 S2)).
{ intros b Hb Hne. rewrite Hbl2. rewrite Hbl1 in Hb. apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb|[Hb|Hb]]; [left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | right; exact Hb]. }
assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)) by exact (KEEPBLK _ HGin1 Hne_t).
assert (Hvin2 : In (pv, AREC * cap) (ablocks B ly2 S2)) by exact (KEEPBLK _ Hvin Hne_v).
assert (DTF : dxG cx + 896 <= fst r0 \/ fst r0 + (Z.of_nat (length (snd r0)) + 1) <= dxG cx).
{ pose proof (dw_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR HGin1 R0in Hne_t) as X.
  rewrite RQT, (dw_req_pos RG) in X by lia. exact X. }
apply dw_hide_i in DTF.
assert (DVF : pv + 16 * cap <= fst r0 \/ fst r0 + (Z.of_nat (length (snd r0)) + 1) <= pv).
{ pose proof (dw_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hvin R0in Hne_v) as X.
  rewrite RQV, (dw_req_pos RG) in X by lia. exact X. }
apply dw_hide_i in DVF.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 HGin2) as (_ & _ & _ & _ & HGpres2 & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hvin2) as (_ & _ & _ & _ & HVpres2 & _).
rewrite RQT in HGpres2. rewrite RQV in HVpres2.
destruct Hkept2 as (KF1 & KF2 & KF3 & _ & KF5 & _).
assert (NOWN : forall (ly : alayout) S Hq (W : world SEGS) m md a, ARx ly S Hq W m md -> rg_s RG <= a < rg_s RG + 384 ->
  ~ aowned B ly S a).
{ intros ly S Hq W m md x HA0 Hx Ho. pose proof (HG x ((dw_inG_gs B RG) x Hx)) as (Hi & Hno & _).
  exact (Hno (proj1 (alx_owned_image _ _ _ LAWS ly S Hq W m md x HA0 Hi) Ho)). }
assert (GSV : forall x, rg_s RG <= x < rg_s RG + 384 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) (ms_mem msB) x).
{ intros x Hx. pose proof (HG x ((dw_inG_gs B RG) x Hx)) as (Hi & Hno & _). apply KF3; [exact Hi | exact Hno | exact ((dw_gs_errno B RG HRGD HGSB) x Hx)]. }
assert (GSW : forall x, rg_s RG <= x < rg_s RG + 384 ->
  writable_at SEGS (mrestrict (w_H W1) (ms_mem msB)) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x).
{ intros x Hx. pose proof (HG x ((dw_inG_gs B RG) x Hx)) as (Hi & Hno & _). apply (dw_writable_img RG); [exact Hi|].
  apply Hpres2; [exact Hi | exact (NOWN _ _ _ _ _ _ x HAR Hx) | exact (NOWN _ _ _ _ _ _ x HAR2 Hx) | exact ((dw_gs_errno B RG HRGD HGSB) x Hx) |].
  intros Hb. apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR R0in Hb Hi). }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 2 (spZ regs1)); [exact Usp | |].
    + intros x Hx. apply KF1; lia.
    + intros x Hx _. apply (apresent_writable SEGS). apply HSPres2. lia.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 23 HA); [exact U23 | |].
    + intros x Hx. apply GSV. lia.
    + intros x Hx. apply GSW. lia.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 23 HA); [exact U23 | |].
    + intros x Hx. apply GSV. lia.
    + intros x Hx. apply GSW. lia.
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 32 SA); [exact U32 | |].
    + intros x Hx. replace x with (dxG cx + (x - dxG cx)) by lia.
      apply (KF2 _ _ _ HGin1); [rewrite RQT; lia|]. cbv beta. rewrite (dw_req_pos RG) by lia. unfold dw_hide in DTF. lia.
    + intros x Hx _. apply (apresent_writable SEGS). exact (proj1 (HGpres2 x ltac:(lia))).
  - apply (dw_region_kept2 E (w_H W1) (w_H W2) (ms_mem msB) mem2 33 pv); [exact U33 | |].
    + intros x Hx. replace x with (pv + (x - pv)) by lia.
      apply (KF2 _ _ _ Hvin); [rewrite RQV; lia|]. cbv beta. rewrite (dw_req_pos RG) by lia. unfold dw_hide in DVF. lia.
    + intros x Hx. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (Usp2 : bv_unsigned (ew Ea 2) = spZ regs1) by (rewrite OLDa by lia; exact Usp).
assert (U23a : bv_unsigned (ew Ea 23) = HA) by (rewrite OLDa by lia; exact U23).
assert (U32a : bv_unsigned (ew Ea 32) = SA) by (rewrite OLDa by lia; exact U32).
assert (U33a : bv_unsigned (ew Ea 33) = pv) by (rewrite OLDa by lia; exact U33).
assert (SHOK2 : sh_ok SEGS BxD SHD Ea (mrestrict (w_H W2) mem2)).
{ apply (dw_shok_x Ea ly2 S2 Hp2 W2 mem2 md2 (dxG cx) SA HA pv cap HAR2 HGin2 ltac:(lia) ltac:(lia) Hvin2 ltac:(lia)
    ltac:(lia) ltac:(lia)).
  - rewrite OLDa by lia. rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl), R21. reflexivity.
  - rewrite OLDa by lia. rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23. reflexivity.
  - rewrite OLDa by lia. exact E32.
  - rewrite OLDa by lia. exact E33. }
paj_run_tok_xR RUNR HS HJ2 SHOK2 DRspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp2, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23a in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23a in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32a in Hx.
    left. split; [|lia]. right. left. split.
    - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2 | rewrite RQT; lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into msC end.
rename HFr into HFrC. lazymatch goal with H : mem_grows _ (mrestrict _ (ms_mem msC)) |- _ => rename H into HGRC end.
clear HF.
assert (KC : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W2) (ms_mem msC) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msC) HFrC x Hx).
  intros (r & Hin & Hr).
  match type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp2, ?U23a, ?U32a, ?U33a in Hr; lia. }
clear HFrC.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* the pending count: |rs0| < 2 ^ 26 (each pending text is nonempty, DHIST bounds the pending bytes) *)
assert (Hrs0 : Z.of_nat (length rs0) < 2 ^ 26).
{ pose proof HHIST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
  assert (Hps : pstream s1 = skipn (Z.to_nat (drain_b_c.ds_off s1)) (bzs (snd r0)) ++
    concat (map (fun r => bzs (snd r)) rs0)).
  { unfold pstream, prest. rewrite <- Hpend. reflexivity. }
  assert (HF1 : Forall (fun r => (1 <= length (snd r))%nat) rs0).
  { eapply Forall_impl; [|exact (Forall_inv_tail Pfa)]. intros r (_ & _ & _ & X). exact (X eq_refl). }
  pose proof ((dw_concat_len RG HGSB) rs0 HF1) as X. rewrite Hps, length_app in D10. lia. }
set (NV := 16 * Z.of_nat (length rs0)) in *.
assert (HNV : 0 <= NV /\ NV + 16 <= 16 * cap) by (unfold NV; lia).
assert (Usp3 : spZ (ms_regs msC) = dsp0 cx + - DRAIN_FRAME).
{ unfold spZ at 1. rewrite P2, Usp2, Hsp. lia. }
assert (G10 : getr (ms_regs msC) 10 = w64 pv) by (rewrite P10, OLDa by lia; exact E33).
assert (G11 : getr (ms_regs msC) 11 = w64 (pv + 16)) by (rewrite P11, U33a; reflexivity).
assert (G12 : getr (ms_regs msC) 12 = w64 NV).
{ rewrite P12.
  transitivity (sv_denot Ea (SAlu ALU_SLL (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1))) (SLit 4))).
  { cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite ((dw_U_len RG HGSB) Ea (hl_n (hs_pending h1))); [unfold NV; lia | rewrite OLDa by lia; exact E35 | lia]. }
assert (DTV : dxG cx + 896 <= pv \/ pv + 16 * cap <= dxG cx).
{ assert (Hne : (dxG cx, ATABLE) <> (pv, AREC * cap)).
  { intros X. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Hvsrc. }
  pose proof (dw_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR HGin1 Hvin Hne) as X. rewrite RQT, RQV in X. exact X. }
apply dw_hide_i in DTV.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARC.
assert (ROMC : rom_view SEGS W2 (ms_mem msC))
  by (exact (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low (G_DR B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROMO PSTR HROM0)).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARC Hvin2) as (_ & _ & _ & _ & HVpresC & _). rewrite RQV in HVpresC.
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_asan_memmove)
    (fun x => pv <= x < pv + NV)
    (fun regs' mem' => getr regs' 10 = w64 pv /\
       forall i, 0 <= i < NV -> aview SEGS (w_H W2) mem' (pv + i) = aview SEGS (w_H W2) (ms_mem msC) (pv + 16 + i))
    W2 (ms_regs msC) (ms_mem msC) DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly2 S2 Hp2 _ (k1 + 1) (- DRAIN_FRAME) _ HG eq_refl
    HJ2).
  - exact Usp3.
  - unfold DRAIN_FRAME. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite P3, OLDa, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3 by lia. exact Hgp.
  - rewrite P4, OLDa, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4 by lia. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros x. destruct (Z_le_gt_dec pv x); destruct (Z_lt_ge_dec x (pv + NV));
      [left; lia | right; lia | right; lia | right; lia].
  - intros x Hx Hg. exfalso. apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia|].
    exact (proj1 (HG x Hg)).
  - intros x Hx Hng. split; [|lia].
    destruct (in_dec dw_pair_dec (pv, AREC * cap) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
    + right. left. split.
      * apply (Permutation_in _ HPERM0) in Hin0. destruct Hin0 as [X | Hin0].
        { exfalso. apply HGnot. rewrite X. apply in_or_app. right. apply in_or_app. left. exact Hvsrc. }
        assert (HnR : ~ In (pv, AREC * cap) (dxrest cx)).
        { intros X. apply (dw_nodup_app_disj _ _ _ (dw_nodup_app_r _ _ HND) Hvsrc). apply in_or_app. right. exact X. }
        unfold dFP, dr_fp. apply inFP_cons. right.
        exists (pv, pv + req_size (AREC * cap)). split; [|cbn [fst snd]; rewrite RQV; lia].
        unfold ablocks_fp. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (pv, AREC * cap)).
        apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
        apply in_app_or in Hin0. destruct Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
        apply in_app_or in Hin0. destruct Hin0 as [X|X];
          [apply in_or_app; right; apply in_or_app; right; exact X | contradiction].
      * exists pv, (AREC * cap). split; [exact Hvin2 | rewrite RQV; lia].
    + right. right. left. exists pv, (AREC * cap). split; [exact Hvin2|]. split; [exact Hnot0 | rewrite RQV; lia].
  - intros HPRE HSC.
    apply (AMEMMOVE ly2 S2 Hp2 W2 (ms_regs msC) (ms_mem msC) _ pv (pv + 16) NV HPRE G10 G11 G12).
    + lia.
    + lia.
    + lia.
    + intros x Hx. destruct (HVpresC x ltac:(lia)) as [HPx HPo].
      split; [exact (apresent_writable SEGS _ _ _ HPx)|]. split; [exact HPo|]. rewrite Usp3. lia.
    + eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + intros Hn. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia | exact Hn].
    + lia.
    + lia.
    + intros x Hx. destruct (HVpresC x ltac:(lia)) as [HPx _].
      split; [exact (aview_some_of_apresent SEGS _ _ _ HPx)|]. rewrite Usp3. lia.
    + eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia].
    + intros Hn. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; lia | exact Hn].
    + exact ROMC.
    + intros Hn. split.
      * eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; unfold NV in Hn; lia].
      * eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARC Hvin2); [lia | rewrite RQV; unfold NV in Hn; lia].
    + intros x Hx Hr. apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia | exact Hr]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (HR10 & HMV) & Hfr3 & Hpres3).
assert (Usp3a : bv_unsigned (ew Ea 2) = dsp0 cx + - DRAIN_FRAME) by (rewrite Usp2, Hsp; lia).
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 2 (spZ regs1)); [exact Usp2 | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | lia | lia].
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 23 HA); [exact U23a | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | | lia]. intros Hwr.
    apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia|].
    exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia)))).
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 23 HA); [exact U23a | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | | lia]. intros Hwr.
    apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR2 Hvin2); [rewrite RQV; lia|].
    exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia)))).
  - apply (region_kept_aview Ea (w_H W2) (ms_mem msC) mem3 32 SA); [exact U32a | | exact Hpres3].
    intros x Hx. apply Hfr3; [lia | | lia]. unfold dw_hide in DTV. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 64 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 64)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
assert (Usp4 : bv_unsigned (ew Eb 2) = spZ regs1) by (rewrite OLDb by lia; exact Usp2).
assert (U23b : bv_unsigned (ew Eb 23) = HA) by (rewrite OLDb by lia; exact U23a).
assert (U32b : bv_unsigned (ew Eb 32) = SA) by (rewrite OLDb by lia; exact U32a).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (SHOK3 : sh_ok SEGS BxD SHD Eb (mrestrict (w_H W2) mem3)).
{ apply (dw_shok_x Eb ly2 S2 Hp2 W2 mem3 md3 (dxG cx) SA HA pv cap HAR3 HGin2 ltac:(lia) ltac:(lia) Hvin2 ltac:(lia)
    ltac:(lia) ltac:(lia)).
  - rewrite OLDb, OLDa by lia. rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl), R21. reflexivity.
  - rewrite OLDb, OLDa by lia. rewrite (EREG 23%nat 23%bv ltac:(lia) eq_refl), R23. reflexivity.
  - rewrite OLDb, OLDa by lia. exact E32.
  - rewrite OLDb, OLDa by lia. exact E33. }
paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 DRspan A_dr_join.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Usp4, Hsp in Hx.
    left. split; [left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23b in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons_g.
  { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U23b in Hx. apply (dw_inG_gs B RG). lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U32b in Hx.
  left. split; [|lia]. right. left. split.
  - unfold dFP, dr_fp. apply inFP_cons. left. change (dxSA cx) with SA. unfold AENT. lia.
  - exists (dxG cx), ATABLE. split; [exact HGin2 | rewrite RQT; lia]. }
match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
rename HFr into HFrD. lazymatch goal with H : mem_grows (mrestrict _ mem3) _ |- _ => rename H into HGRD end.
clear HF.
assert (KD : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W2) mem3 x).
{ intros x Hx N1 N2 N3 N4. apply (aview_kept_out Eb _ (w_H W2) mem3 (ms_mem msF) HFrD x Hx).
  intros (r & Hin & Hr).
  match type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp4, ?U23b, ?U32b in Hr; lia. }
clear HFrD.
(* ---- the regions at the join ---- *)
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF1. cbn [ms_mem restrict] in RF1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RF2. cbn [ms_mem restrict] in RF2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RF3. cbn [ms_mem restrict] in RF3.
assert (E35b : ew Eb 35 = Z_to_bv 64 (hl_n (hs_pending h1))) by (rewrite OLDb, OLDa by lia; exact E35).
pose proof (field_of_region Eb _ 23 HA _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1)))
  (Z.of_nat (length rs0)) RF1 U23b ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite denot_lit_U, ((dw_U_pn1 RG) Eb (hl_n (hs_pending h1)) E35b) by lia; f_equal; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V24.
pose proof (field_of_region Eb _ 23 HA _ _ _ _ _ 32 8%N (SLit 0) 0 RF2 U23b
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V32.
pose proof (field_of_region Eb _ 32 SA _ _ _ _ _ 24 8%N (SOff 38 0) (re_used e1) RF3 U32b
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite OLDb, OLDa by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VBU.
change (N.to_nat 4) with 4%nat in V24. change (N.to_nat 8) with 8%nat in V32, VBU.
clear RF1 RF2 RF3.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (21%bv : bv 5) F21.
prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
prreg HS (27%bv : bv 5) F27.
clear HS SHOK3.
match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) end.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARF.
pose proof HJ3 as (_ & _ & (memSF & HJiF & _) & _).
pose proof HJiF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSPresF & _).
rewrite !Z.add_0_r in HSPresF. clear memSF HJiF.
(* ---- what the free left ---- *)
assert (FREEV : forall x, (alloc_ceiling <= x < 2 ^ 64 /\ ~ (dsp0 cx + - DRAIN_FRAME - ASTACK <= x < dsp0 cx + - DRAIN_FRAME)) \/
  (exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= x < b + req_size n /\
     ~ (fst r0 <= x < fst r0 + req_size (Z.of_nat (length (snd r0)) + 1))) \/
  (in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B)) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) (ms_mem msB) x).
{ intros x [[Hx1 Hx2] | [(b & n & Hb & Hbx & Hnf) | (Hi & Hno)]].
  - apply KF1; [exact Hx1 | exact Hx2].
  - replace x with (b + (x - b)) by lia. apply (KF2 b n (x - b) Hb); [lia | cbv beta; lia].
  - destruct (Z_le_gt_dec (as_errno B) x); destruct (Z_lt_ge_dec x (as_errno B + 4)).
    + replace x with (as_errno B + (x - as_errno B)) by lia. apply Herr2. lia.
    + apply KF3; [exact Hi | exact Hno | lia].
    + apply KF3; [exact Hi | exact Hno | lia].
    + apply KF3; [exact Hi | exact Hno | lia]. }
(* ---- every byte the cut reads, from the DE memory to the join's ---- *)
assert (VALL : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> ~ (SA + 24 <= x < SA + 32) ->
  ~ (pv <= x < pv + NV) -> ~ (dsp0 cx + - DRAIN_FRAME - ASTACK <= x < dsp0 cx + - DRAIN_FRAME) ->
  ((alloc_ceiling <= x < 2 ^ 64) \/
   (exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= x < b + req_size n /\
      ~ (fst r0 <= x < fst r0 + req_size (Z.of_nat (length (snd r0)) + 1))) \/
   (in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))) ->
  aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2 N3 N4 N5 N6 HC.
  rewrite (KD x Hx N1 N2 N3 N4).
  rewrite (Hfr3 x Hx N5) by lia.
  rewrite (KC x Hx N1 N2 N3 N4).
  rewrite FREEV by (destruct HC as [H1 | [H2 | H3]]; [left; split; [exact H1 | exact N6] | right; left; exact H2 | right; right; exact H3]).
  rewrite (KB x Hx N1 N2 N3 N4). exact (KA x Hx N1 N2 N3 N4). }
assert (VSAW : forall x, SA + 24 <= x < SA + 32 -> aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; exact ((dw_aview_of_vm2 RG) W1 W2 m1 (ms_mem msF) (SA + 24) 8 (re_used e1) x MUSED VBU ltac:(cbn; lia))).
assert (PIMG : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
  apresent (w_H W1) m1 x -> apresent (w_H W2) (ms_mem msF) x).
{ intros x Hi Hno He Hpx.
  assert (NO : forall ly S Hq (W : world SEGS) m md, ARx ly S Hq W m md -> ~ aowned B ly S x)
    by (intros ly S Hq W m md HA0 Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hq W m md x HA0 Hi) Ho)).
  apply (apresent_grows _ _ _ x HGRD). apply Hpres3. apply (apresent_grows _ _ _ x HGRC).
  apply (Hpres2 x Hi (NO _ _ _ _ _ _ HAR) (NO _ _ _ _ _ _ HAR2) He).
  - intros Hb. exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR R0in Hb Hi).
  - apply (apresent_grows _ _ _ x HGRB). apply (apresent_grows _ _ _ x HGRA). exact Hpx. }
assert (WIMG : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W2 (ms_mem msF)) x).
{ intros x Hi Hno Hwr. destruct (Z_le_gt_dec (as_errno B) x); destruct (Z_lt_ge_dec x (as_errno B + 4)).
  - replace x with (as_errno B + (x - as_errno B)) by lia. unfold arm. apply (dw_errno_writable B RG HG HERRW). lia.
  - unfold arm in *. apply ((dw_writable_img RG) W1 W2 m1 (ms_mem msF) x Hi); [|exact Hwr].
    intros Hpx. apply PIMG; [exact Hi | exact Hno | lia | exact Hpx].
  - unfold arm in *. apply ((dw_writable_img RG) W1 W2 m1 (ms_mem msF) x Hi); [|exact Hwr].
    intros Hpx. apply PIMG; [exact Hi | exact Hno | lia | exact Hpx].
  - unfold arm in *. apply ((dw_writable_img RG) W1 W2 m1 (ms_mem msF) x Hi); [|exact Hwr].
    intros Hpx. apply PIMG; [exact Hi | exact Hno | lia | exact Hpx]. }
assert (KIM : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (HA + 24 <= x < HA + 28) -> ~ (HA + 32 <= x < HA + 40) -> abyte_kept W1 m1 W2 (ms_mem msF) x).
{ intros x Hi Hno N2 N3. pose proof (pa_img_range x Hi) as Hxr. split; [|exact (WIMG x Hi Hno)].
  apply VALL; [lia | lia | exact N2 | exact N3 | | | lia | right; right; split; [exact Hi | exact Hno]].
  - intros Hs. apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR HGin1); [rewrite RQT; lia | exact Hi].
  - intros Hv. apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR Hvin); [rewrite RQV; lia | exact Hi]. }
assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx ->
  ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 200) -> abyte_kept W1 m1 W2 (ms_mem msF) x).
{ intros x Hx Hn. split.
  - apply VALL; [lia | rewrite Hsp; lia | lia | lia | lia | lia | lia | left; lia].
  - intros _. unfold arm. apply (apresent_writable SEGS). apply HSPresF. lia. }
assert (KBL : forall b n x, In (b, n) (ablocks B ly2 S2) -> (b, n) <> (pv, AREC * cap) -> b <= x < b + req_size n ->
  abyte_kept W1 m1 W2 (ms_mem msF) x).
{ intros b n x Hb Hne Hx.
  assert (Hb1 : In (b, n) (ablocks B ly1 S1)).
  { rewrite Hbl2 in Hb. rewrite Hbl1. apply in_app_or in Hb. apply in_or_app.
    destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
  assert (Hnf : (b, n) <> (fst r0, Z.of_nat (length (snd r0)) + 1)).
  { apply (dw_nodup_neq l1 l2); [rewrite <- Hbl1; exact (dw_ablocks_nodup_x _ _ _ _ _ _ HAR) | rewrite <- Hbl2; exact Hb]. }
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb1) as (_ & Hb4096 & Hbceil & _ & _ & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARF Hb) as (_ & _ & _ & _ & HbpresF & _).
  pose proof (dw_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hb1 R0in Hnf) as DF.
  rewrite ((dw_req_pos RG) (Z.of_nat (length (snd r0)) + 1)) in DF by lia.
  pose proof (dw_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR2 Hb Hvin2 Hne) as DVb. rewrite RQV in DVb.
  assert (Hnimg : ~ in_img SEGS x) by exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR Hb1 Hx).
  split; [|intros _; unfold arm; apply (apresent_writable SEGS); exact (proj1 (HbpresF x Hx))].
  destruct (Z_le_gt_dec (SA + 24) x); destruct (Z_lt_ge_dec x (SA + 32)); [apply VSAW; lia | | |];
  (apply VALL; [lia | lia | | | lia | lia | lia |]);
  try (intros Hw0; apply Hnimg; exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia)))));
  right; left; exists b, n; (split; [exact Hb1|]); (split; [exact Hx|]); rewrite (dw_req_pos RG) by lia; lia. }
(* ---- the record array after the memmove ---- *)
set (JK := skipn (16 * length rs0) (concat (map text_rec (r0 :: rs0)) ++ hl_junk (hs_pending h1))).
assert (Hold : Z.of_nat (length (concat (map text_rec (r0 :: rs0)) ++ hl_junk (hs_pending h1))) = 16 * cap).
{ rewrite length_app, Nat2Z.inj_add, (dw_len_text_recs RG), Hjl, Hpn. unfold AREC. cbn [length]. lia. }
assert (Hjk : Z.of_nat (length JK) = AREC * (cap - Z.of_nat (length rs0))).
{ unfold JK. rewrite length_skipn. unfold AREC. lia. }
assert (VEX : forall x, pv <= x < pv + 16 * cap -> 0 <= x < 2 ^ 64 /\ ~ (spZ regs1 + 192 <= x < spZ regs1 + 200) /\
  ~ (HA + 24 <= x < HA + 28) /\ ~ (HA + 32 <= x < HA + 40) /\ ~ (SA + 24 <= x < SA + 32) /\
  ~ (dsp0 cx + - DRAIN_FRAME - ASTACK <= x < dsp0 cx + - DRAIN_FRAME)).
{ intros x Hx. unfold dw_hide in DTV.
  assert (Hni : ~ in_img SEGS x) by (apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR Hvin); rewrite RQV; lia).
  split; [lia|]. split; [lia|].
  split; [intros Hw0; apply Hni; exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia))))|].
  split; [intros Hw0; apply Hni; exact (proj1 (HG x ((dw_inG_gs B RG) x ltac:(lia))))|].
  split; lia. }
assert (GV : garr8 SEGS (arm W2 (ms_mem msF)) pv (bzs (concat (map text_rec rs0) ++ JK))).
{ unfold arm, JK. apply ((dw_vec_after RG HGSB) (w_H W1) (w_H W2) m1 (ms_mem msF) pv r0 rs0 (hl_junk (hs_pending h1)) Hvg).
  - intros j Hj. destruct (VEX (pv + j) ltac:(lia)) as (Vq0 & Vq1 & Vq2 & Vq3 & Vq4 & Vq5).
    destruct (VEX (pv + 16 + j) ltac:(lia)) as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5).
    rewrite (KD (pv + j) Vq0 Vq1 Vq2 Vq3 Vq4). rewrite (HMV j) by (unfold NV; lia).
    rewrite (KC (pv + 16 + j) Y0 Y1 Y2 Y3 Y4).
    rewrite FREEV by (right; left; exists pv, (AREC * cap); split; [exact Hvin|]; split; [rewrite RQV; lia|];
      rewrite (dw_req_pos RG) by lia; unfold dw_hide in DVF; lia).
    rewrite (KB (pv + 16 + j) Y0 Y1 Y2 Y3 Y4). exact (KA (pv + 16 + j) Y0 Y1 Y2 Y3 Y4).
  - intros x Hx. rewrite Hold in Hx. destruct (VEX x ltac:(lia)) as (Vq0 & Vq1 & Vq2 & Vq3 & Vq4 & Vq5).
    apply VALL; [exact Vq0 | exact Vq1 | exact Vq2 | exact Vq3 | exact Vq4 | unfold NV; lia | exact Vq5 |].
    right. left. exists pv, (AREC * cap). split; [exact Hvin|]. split; [rewrite RQV; lia|].
    rewrite (dw_req_pos RG) by lia. unfold dw_hide in DVF. lia. }
(* ---- the memory core ---- *)
assert (HMEM2 : DMEM_xR B PST ARx RG R cx Hpe ly2 S2 Hp2 W2 (ms_mem msF) mdF (k1 + 1) e1 (dw_hdrop h1 rs0 JK) (dsv cx s1)
  out1 ev1 (lines (dSTR cx) D) LB1).
{ apply (dw_dmem_xR cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 ly2 S2 Hp2 W2
    (ms_mem msF) mdF (k1 + 1) r0 rs0 JK l1 l2 Hj4 HGSA ltac:(unfold AENT, ATABLE; lia) HMEM eq_refl eq_refl HROM0 HJ3 Hfr2 Erecs Hbl1 Hbl2
    KBL KIM WIMG KFR PIMG V24 V32 Hjk GV). }
(* ---- the history at p = 0 ---- *)
assert (HDH : DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D)
  (dw_hdrop h1 rs0 JK) LB1 (Z.of_nat (length (drl s1)))).
{ pose proof HHIST as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  assert (Hps : pstream s1 = ddata s1 ++ pstream (dnext (dlive cx) (dxmx cx) s1))
    by exact (dm_ps_split RG HGSB cx s1 RS_wf ltac:(lia)).
  pose proof (dm_chunk_le RG (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as Hcl.
  pose proof (dm_lines_le RG (drain_b_c.ds_ref s1) (ddata s1)) as Hll.
  unfold DHIST.
  change (pstream (dsv cx s1)) with (pstream (dnext (dlive cx) (dxmx cx) s1)).
  change (drain_b_c.ds_ref (dsv cx s1)) with (feed (drain_b_c.ds_ref s1) (ddata s1)).
  change (drain_b_c.ds_no (dsv cx s1)) with (drain_b_c.ds_no s1).
  change (drain_b_c.ds_H (dsv cx s1)) with (drain_b_c.ds_H s1).
  change (drain_b_c.ds_en (dsv cx s1)) with (drain_b_c.ds_en s1 + Z.of_nat (length (dref s1))).
  split; [rewrite D1, Hps, app_assoc; reflexivity|].
  split; [rewrite D2, feed_app; reflexivity|].
  split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
  split; [exact D8|]. split; [exact D9|].
  rewrite Hps, length_app in D10, D11. unfold drl, dchunk, dref.
  split; [clear - D10 Hcl; lia | clear - D11 Hll; lia]. }
(* ---- the meter ---- *)
assert (HBUD2 : dbud MT MMAX cx S2 (spent + mo_free MT) tl2).
{ pose proof (mo_free_nonneg MT MTL) as Hf. unfold dbud.
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ HMLE Hmle2)|].
  split; [lia|]. split; [lia|].
  split.
  - assert (Hbs : blocks_bytes S2 + (Z.of_nat (length (snd r0)) + 1) = blocks_bytes S1).
    { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1), Hbl1, Hbl2, !bsum_app, bsum_cons.
      cbn [snd]. lia. }
    (* C3: the free of the head record (ddrop's one request, RFree (|head| + 1)) lowers the live bytes by exactly
       its size, so the peak of the rest stays in room (W_tr_peak.v tr_peak_free) *)
    assert (HdlC3 : Z.of_nat (length (dhead s1)) = Z.of_nat (length (snd r0)))
      by (rewrite Hhead; unfold bzs; rewrite length_map; reflexivity).
    assert (HpkC3 : tr_peak tl2 - (Z.of_nat (length (snd r0)) + 1) <= tr_peak tl)
      by (rewrite Htl, Hdrop; cbn [app]; rewrite W_tr_peak.tr_peak_free, HdlC3; lia).
    lia.
  - assert (Htm : tr_max tl = Z.max 0 (tr_max tl2)) by (rewrite Htl, (dm_tr_max_app RG HGSB), dm_max_ddrop; reflexivity).
    lia. }
(* the room round after the call: the rule post's room of the rest, and the counts with the freed block out of the
   post's split (W_drain_room_x.gs_cnt_free) *)
assert (HCNT2 : cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P tl2) + 2)%nat) (ablocks B ly2 S2)).
{ rewrite Etl, Hbl1 in HCNTc. cbn [app] in HCNTc. rewrite Hbl2.
  exact (W_drain_room_x.gs_cnt_free RP _ _ tl2 l1 l2 _ HCNTc). }
assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> (k < 32)%nat ->
  Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
{ intros r k Hr Hk Hkr. rewrite Hr, OLDb, OLDa by lia. apply EREG; assumption. }
apply (HK W2). unfold DDM_xR.
match type of Hlf with dlfut _ _ ?a0 _ _ _ _ _ ?jb0 ?o0 ?ha0 ?ks0 _ =>
  exists (ms_regs msF), ly2, S2, Hp2, (ms_mem msF), mdF, (k1 + 1), e1, (dw_hdrop h1 rs0 JK), out1, ev1, LB1,
    (spent + mo_free MT), jb0, a0, o0, ha0, ks0, tl2 end.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ at 1; rewrite (RK _ 2%nat F2) by (first [lia | reflexivity]); exact Hsp|].
split; [rewrite (RK _ 3%nat F3) by (first [lia | reflexivity]); exact R3|].
split; [rewrite (RK _ 4%nat F4) by (first [lia | reflexivity]); exact R4|].
split; [rewrite (RK _ 18%nat F18) by (first [lia | reflexivity]); exact R18|].
split; [rewrite (RK _ 9%nat F9) by (first [lia | reflexivity]); exact R9|].
split; [rewrite (RK _ 8%nat F8) by (first [lia | reflexivity]); exact R8|].
split; [rewrite (RK _ 21%nat F21) by (first [lia | reflexivity]); exact R21|].
split; [rewrite (RK _ 23%nat F23) by (first [lia | reflexivity]); exact R23|].
split; [rewrite (RK _ 19%nat F19) by (first [lia | reflexivity]); exact R19|].
split; [rewrite F22, OLDb, OLDa by lia; exact E32|].
split; [rewrite F25, U32b; reflexivity|].
split; [rewrite F26, U32b; reflexivity|].
split; [rewrite F27, U32b; reflexivity|].
split; [exact ((dw_frame_kept RG HGSB) cx W1 m1 W2 (ms_mem msF) KFR HFR)|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S56]|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S64]|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S48]|].
split; [apply (akept_vm W1 m1); [intros y Hy; apply KFR; cbn in Hy; lia | exact S200]|].
split; [exact Hn0|]. split; [lia|]. split; [exact Hdata|].
split; [exact HMEM2|].
split; [exact Hnonul|]. split; [exact Hused|]. split; [exact HSAME|].
split; [exact Hcap|]. split; [exact HU|]. split; [exact Hskip|]. split; [exact HH|]. split; [exact Hka|].
split; [exact Hei|].
split; [unfold dnext; cbn [drain_b_c.ds_pend]; rewrite Hw; unfold dtail; rewrite <- Hpend; reflexivity|].
split; [unfold dnext; cbn [drain_b_c.ds_off]; rewrite Hw; reflexivity|].
split; [exact Hst|]. split; [exact Hen|]. split; [exact Hecap|].
split; [exact HDH|]. split; [exact HRST|]. split; [exact Hlf | exact (conj HBUD2 (conj HRM2 HCNT2))].
Qed.
(* ---- DROP over ARx: the two arms join at DDM_x (dr_drop_split's text), then the second half, W_drain_dropb.v's
   dr_dropb_x. ---- *)
Theorem dr_drop_of_xR : dr_dropb_stmt_xR B PST ARx MT RP MMAX RG R -> dr_drop_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros DROPB cx Hp kr s1 D W1 c1 HB HDE Hdll Hdlr.
destruct (dwhole s1) eqn:Hw.
- apply (drop_whole_xR cx Hp kr s1 D W1 c1 HB HDE Hw). intros W2 c2 HQ. exact (DROPB cx Hp kr s1 D W2 c2 HB HQ Hdll Hdlr).
- apply (drop_keep_xR cx Hp kr s1 D W1 c1 HB HDE Hw). intros W2 c2 HQ. exact (DROPB cx Hp kr s1 D W2 c2 HB HQ Hdll Hdlr).
Qed.
(* DROP over ARx: W_drain_cx_x.v's dr_drop_stmt_x *)
Theorem dr_drop_xR : dr_drop_stmt_xR B PST ARx MT RP MMAX RG R.
Proof. apply dr_drop_of_xR. eapply W_drain_dropb.dr_dropb_xR; eassumption. Qed.
End wR.


(* DMEM_x across the store: the memory m2 keeps every byte off [HA + 32, HA + 40), which holds o' (dk_dmem_off over
   ARx; the journal at the entry's Hp and the cut's Hp1) *)
Lemma dk_dmem_off_x : forall cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 m2 md2 o',
alloc_ceiling + ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 ->
dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE -> (dxj cx < 4)%nat ->
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
(forall a, dk_out (dHA RG cx) a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
val_mem SEGS (arm W1 m2) (dHA RG cx + 32) 8 o' ->
(exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= o' < Z.of_nat (length (snd r))) ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m2 md2 k1 e1 (dk_setoff h1 o') s' out1 ev1 sent LB1.
Proof. eapply (dk_dmem_off_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


Lemma drop_keep_x : forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W1 c1 -> dwhole s1 = false ->
(forall W2 c2, DDM_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (drop_keep_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* W_drain_drop.v dw_dmem: the memory core at the join, over ARx *)
Lemma dw_dmem_x : forall cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s s' out1 ev1 sent LB1 ly2 S2 Hp2 W2 m2 md2 k2 r0 rs0 jk l1 l2,
  (dxj cx < 4)%nat -> dxG cx <= dxSA cx -> dxSA cx + AENT <= dxG cx + ATABLE ->
  DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
  drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
  rom_view SEGS (dxW cx) (dxmem cx) ->
  @ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
  frames S2 = frames S1 ->
  hl_recs (hs_pending h1) = r0 :: rs0 ->
  ablocks B ly1 S1 = l1 ++ (fst r0, Z.of_nat (length (snd r0)) + 1) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  (forall b n x, In (b, n) (ablocks B ly2 S2) -> (b, n) <> (hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1)) ->
     b <= x < b + req_size n -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     ~ (dHA RG cx + 24 <= x < dHA RG cx + 28) -> ~ (dHA RG cx + 32 <= x < dHA RG cx + 40) -> abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
     writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W2 m2) x) ->
  (forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> ~ (dsp0 cx - DRAIN_FRAME + 192 <= x < dsp0 cx - DRAIN_FRAME + 200) ->
     abyte_kept W1 m1 W2 m2 x) ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x) ->
  val_mem SEGS (arm W2 m2) (dHA RG cx + 24) 4 (Z.of_nat (length rs0)) ->
  val_mem SEGS (arm W2 m2) (dHA RG cx + 32) 8 0 ->
  Z.of_nat (length jk) = AREC * (hl_cap (hs_pending h1) - Z.of_nat (length rs0)) ->
  garr8 SEGS (arm W2 m2) (hl_v (hs_pending h1)) (bzs (concat (map text_rec rs0) ++ jk)) ->
  DMEM_x B PST ARx RG cx Hp ly2 S2 Hp2 W2 m2 md2 k2 e1 (dw_hdrop h1 rs0 jk) s' out1 ev1 sent LB1.
Proof. eapply (dw_dmem_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* W_drain_drop.v drop_whole: DE 0x835ac -> free #1 (0x83618, AFREE at HCTX_fr1) -> __asan_memmove (0x83648,
   AMEMMOVE) -> DDM 0x83668, over ARx *)
Lemma drop_whole_x : forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W1 c1 -> dwhole s1 = true ->
(forall W2 c2, DDM_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (drop_whole_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | (apply afree_cf_rule_c_xR_of_x; assumption) | (apply arealloc_cf_rule_c_xR_of_x; assumption) | (intros; exact I) | assumption]. Qed.


(* ---- DROP over ARx: the two arms join at DDM_x (dr_drop_split's text), then the second half, W_drain_dropb.v's
   dr_dropb_x. ---- *)
Theorem dr_drop_of_x : dr_dropb_stmt_x B PST ARx MT RP MMAX RG -> dr_drop_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_drop_of_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | (apply afree_cf_rule_c_xR_of_x; assumption) | (apply arealloc_cf_rule_c_xR_of_x; assumption) | (intros; exact I) | assumption]. Qed.


(* DROP over ARx: W_drain_cx_x.v's dr_drop_stmt_x *)
Theorem dr_drop_x : dr_drop_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_drop_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | (apply afree_cf_rule_c_xR_of_x; assumption) | (apply arealloc_cf_rule_c_xR_of_x; assumption) | (intros; exact I) | assumption]. Qed.

End cx.
End bx.
End ax.
