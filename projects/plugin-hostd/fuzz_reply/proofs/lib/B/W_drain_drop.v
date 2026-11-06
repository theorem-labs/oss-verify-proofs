(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_drop.v, the DROP stage of the image-B (fuzz_reply.asan-ubsan) walk
   of fuzz_reply's drain.  Proves no function (kind: segment lemma): dr_drop : dr_drop_stmt B MT MMAX RG, the statement
   of lib/B/W_drain_cx.v (a working branch; that file is not edited).
   The walk, from fuzz_reply.asan-ubsan's objdump, from DE 0x838a0 (s7 = HA = &g_s[j], a5 = n = dnum s1):
     0x838a0  ld a0,168(sp); lbu; ld s4,128(sp); ld s11,176(sp); li s10,384; bnez -> report
                                                   shadow check of h->pending_off (HA + 32), NOT TAKEN
     0x838b8  ld a1,32(s7); add a1,a1,a5; sd a1,32(s7)              h->pending_off += n
     0x838c4  ld a0,112(sp); lbu; ld s5,144(sp); ld s6,136(sp); ld a4,96(sp); bnez -> report
                                                   shadow check of h->pending (HA + 16), NOT TAKEN
     0x838dc  ld a0,0(a4); beqz a0 -> unimp (NONNULL); andi a2,a0,7; bnez a2 -> unimp (ALIGN8)
                                                   v = h->pending.v, decided by v's atom facts (trap kit R1)
     0x838ec  shadow check of v + 8, NOT TAKEN; ld a0,8(v)                v[0].n, the head text's length
     0x83908  bne a1,a0 -> 0x8392c                                        off + n <> v[0].n: not dwhole s1
       fall through (dwhole s1): mv a0,a4; li a1,0; jal list_drop (0x83914 -> 0x85b50)   list_drop (&h->pending, 0)
         0x83918  shadow check of HA + 32, NOT TAKEN; sd zero,32(s7); ld a5,192(sp)       h->pending_off = 0
     0x8392c  bltz a5 -> 0x83ed8; beqz a5 -> 0x83fa8      both refuted: 0 < n (DE), n's atom fact
     0x83934  shadow check of s->used (SA + 24), NOT TAKEN; ld a0,0(s6); add a0,a0,a5; sd a0,0(s6)   s->used += n
     0x8394c  shadow check of s->buf (SA + 16), NOT TAKEN; ld s8,0(s4)    s8 = s->buf
   -> DJ 0x8395c at p = 0 (lib/B/W_drain_join.v), then dr_memchr_join.
   The call takes lib/B/W_list_drop.v pb_list_drop_ro_c (Qed; the _c free rule AFREE and HCTX_ld, list_drop's free
   returning to 0x85bec) at G1 = [(HA + 16, 16)] (not at G_DR: gx_rt excludes errno's bytes), lifted into drain's
   journal by lib/B/W_drain_feed.v df_gx_call (ajournal_gx_G_mono).
   The memory and model bookkeeping is lib/B/W_drain_dropk.v (dd_arm_close, dd_DJ).
   STRUCTURE PORTED FROM a working branch 1c09e330abe lib/B/Prog/drain_p_read_drop_free.v (the
   drop arm and its list_drop call), drain_p_read_tail_drop.v and drain_p_read_tail_keep.v (the two tails); nothing
   is copied, the vocabulary (SRr over AR, journal ajournal_gx, symbolic seats) is this framework's. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_dnrk W_drain_join
  W_drain_rest W_drain_feed W_drain_dropk W_list_drop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH), the R specs (W_contract_xR.v, W_contract_xR_g3.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_room_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* ------------------------------------------------------------------ small facts *)
Lemma ddw_apart : forall a1 n1 a2 n2, 0 < n1 -> 0 < n2 ->
(forall x, a1 <= x < a1 + n1 -> a2 <= x < a2 + n2 -> False) -> a1 + n1 <= a2 \/ a2 + n2 <= a1.
Proof.
intros a1 n1 a2 n2 H1 H2 H. destruct (Z_le_gt_dec (a1 + n1) a2) as [E|E]; [left; exact E|].
destruct (Z_le_gt_dec (a2 + n2) a1) as [F|F]; [right; exact F|].
exfalso. apply (H (Z.max a1 a2)); lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the head record's length field, v[0].n, the second word of the vector *)
Lemma ddw_v0n : forall (m : word -> option byte) v (r : Z * list byte) rest,
garr8 SEGS m v (bzs (text_rec r ++ rest)) -> Z.of_nat (length (snd r)) < 2 ^ 64 ->
val_mem SEGS m (v + 8) 8 (Z.of_nat (length (snd r))).
Proof.
intros m v r rest Hg Hl. unfold text_rec in Hg. rewrite <- app_assoc in Hg. unfold bzs in Hg. rewrite !map_app in Hg.
apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg as [_ Hg].
rewrite length_map, Mem.length_le8 in Hg. change (Z.of_nat 8) with 8 in Hg.
apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg as [Hg _].
rewrite dnk_le8_bytes in Hg by lia. apply (dnk_garr8_le m (v + 8) 8 _ Hg). cbn. lia.
Qed.

(* the shadow address of atom m + c in the frame-slot shape the runner's tok_load reads *)
Definition ddw_shg (m : nat) (c : Z) : cval := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 33 0)).

Lemma ddw_den_sh : forall E (m : nat) v c, ew E m = Z_to_bv 64 v -> ew E 33 = Z_to_bv 64 SHADOW_OFF ->
  0 <= v -> v + c < 2 ^ 60 -> 0 <= c ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 33 0)) = Z_to_bv 64 (shadow_addr (v + c)).
Proof.
intros E m v c Hm H33 H0 H1 Hc.
assert (H8 : 0 <= (v + c) / 8 <= v + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E m v c Hm ltac:(lia) ltac:(lia)), U_SLit, (zcanon_id 3) by (unfold M64; lia).
rewrite (U_atom E 33 SHADOW_OFF H33 ltac:(unfold SHADOW_OFF; lia)).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* 0x83908 `bne a1,a0`: a1 = n + off (atoms 15 and 35), a0 = v[0].n (atom 36) *)
Lemma ddw_bne : forall E x y z, ew E 15 = Z_to_bv 64 x -> ew E 35 = Z_to_bv 64 y -> ew E 36 = Z_to_bv 64 z ->
  0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_ADD (SOff 15 0) (SOff 35 0))) (sv_denot E (SOff 36 0)) = negb (x + y =? z).
Proof.
intros E x y z H15 H35 H36 Hx Hy Hz. rewrite branch_ne_U. f_equal. f_equal.
- rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 15 x H15 ltac:(lia)), (U_atom E 35 y H35 ltac:(lia)).
  apply zcanon_id. unfold M64. lia.
- exact (U_atom E 36 z H36 Hz).
Qed.

(* the value a store of `atom m + atom k` leaves *)
Lemma ddw_den_add : forall E (m k : nat) x y, ew E m = Z_to_bv 64 x -> ew E k = Z_to_bv 64 y ->
  0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SOff m 0) (SOff k 0)) = Z_to_bv 64 (x + y).
Proof.
intros E m k x y Hm Hk Hx Hy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E m x Hm ltac:(lia)), (U_atom E k y Hk ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

(* a run's write permission: each region's window is empty, in g_s[j] (G_DR) or in the source_t (drain's FP) *)
Ltac ddw_awr B2 B23 B32 GSW FPE :=
  lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end;
  repeat first [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [ let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2, ?B23, ?B32 in Hy;
        first [ exfalso; clear - Hy; lia
              | right; left; apply GSW; clear - Hy; lia
              | left; split; [right; left; apply FPE; clear - Hy; lia | clear; lia] ] | ] ].

(* ------------------------------------------------------------------ the symbolic state at 0x838a0 *)
(* Atoms 0..31: the registers (s7 = HA, a5 = n); 32 = SA, 33 = SHADOW_OFF, 34 = v = h->pending.v,
   35 = h->pending_off, 36 = v[0].n, 37 = s->buf, 38 = s->used.  Regions: drain's frame (the slots the walk reads),
   h->pending_off (written), h->pending.v, v[0].n, s->buf / s->used (s->used written).  Shadow entries: g_s[j]
   (HGSZ), v[0] (the vector block) and the source_t (the table block). *)
Definition ddw_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 96 248 96 96
    [YP09.mkChunk 96 (CVal 8 (SOff 23 16)); YP09.mkChunk 112 (ddw_shg 23 16); YP09.mkChunk 128 (CVal 8 (SOff 32 16));
     YP09.mkChunk 136 (CVal 8 (SOff 32 24)); YP09.mkChunk 144 (CVal 8 (SOff 32 0)); YP09.mkChunk 168 (ddw_shg 23 32);
     YP09.mkChunk 176 (CVal 8 (SOff 32 32)); YP09.mkChunk 192 (CVal 8 (SOff 15 0)); YP09.mkChunk 224 (ddw_shg 32 16);
     YP09.mkChunk 232 (ddw_shg 32 24); YP09.mkChunk 240 (CVal 8 (SOff 33 0))].
Definition ddw_off : YP09.region := YP09.mkRegion (Some 23%nat) 32 40 32 40 [YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition ddw_hv : YP09.region := YP09.mkRegion (Some 23%nat) 16 24 16 16 [YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition ddw_vec : YP09.region := YP09.mkRegion (Some 34%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 36 0))].
Definition ddw_ent : YP09.region :=
  YP09.mkRegion (Some 32%nat) 16 32 24 32 [YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0))].
Definition ddw_PTRF : afact := mkAF 4096 140737479966720 3.
Definition ddw_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (15%nat, mkAF 1 16384 0); (23%nat, mkAF 0x10000 IMG_TOP 3);
            (32%nat, ddw_PTRF); (33%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (34%nat, ddw_PTRF);
            (35%nat, mkAF 0 (2 ^ 30) 0); (36%nat, mkAF 1 (2 ^ 30) 0); (37%nat, ddw_PTRF); (38%nat, mkAF 0 16384 0) ]
          [] [].
Definition ddw_ss : sstate := mkSS A_dr_fed sr_atoms [ddw_frame; ddw_off; ddw_hv; ddw_vec; ddw_ent] None ddw_facts.
Definition ddw_SH : list shent := [mkSHE 23 0 96; mkSHE 34 0 16; mkSHE 32 0 56].
Definition ddw_extra (SA v off v0n buf used : Z) : list word :=
  map (Z_to_bv 64) [SA; SHADOW_OFF; v; off; v0n; buf; used].

Lemma ddw_seat : forall (W1 : world SEGS) regs1 m1 sp HA n SA v off v0n buf used,
spZ regs1 = sp -> 2 ^ 46 <= sp -> alloc_ceiling <= sp -> sp + 352 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 23 = w64 HA -> getr regs1 15 = w64 n ->
val_mem SEGS (arm W1 m1) (sp + 96) 8 (HA + 16) ->
val_mem SEGS (arm W1 m1) (sp + 112) 8 (shadow_addr (HA + 16)) ->
val_mem SEGS (arm W1 m1) (sp + 128) 8 (SA + 16) ->
val_mem SEGS (arm W1 m1) (sp + 136) 8 (SA + 24) ->
val_mem SEGS (arm W1 m1) (sp + 144) 8 SA ->
val_mem SEGS (arm W1 m1) (sp + 168) 8 (shadow_addr (HA + 32)) ->
val_mem SEGS (arm W1 m1) (sp + 176) 8 (SA + 32) ->
val_mem SEGS (arm W1 m1) (sp + 192) 8 n ->
val_mem SEGS (arm W1 m1) (sp + 224) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W1 m1) (sp + 232) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W1 m1) (sp + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (HA + 32) 8 off -> val_mem SEGS (arm W1 m1) (HA + 16) 8 v ->
val_mem SEGS (arm W1 m1) (v + 8) 8 v0n ->
val_mem SEGS (arm W1 m1) (SA + 16) 8 buf -> val_mem SEGS (arm W1 m1) (SA + 24) 8 used ->
awr W1 m1 HA ASRC -> awr W1 m1 SA AENT ->
0x10000 <= HA -> HA + 96 <= IMG_TOP -> HA mod 8 = 0 ->
1 <= n <= 16384 ->
4096 <= SA -> SA + 56 <= alloc_ceiling -> SA mod 8 = 0 ->
4096 <= v <= 140737479966720 -> v + 16 <= alloc_ceiling -> v mod 8 = 0 ->
0 <= off <= 2 ^ 30 -> 1 <= v0n <= 2 ^ 30 ->
4096 <= buf <= 140737479966720 -> buf mod 8 = 0 -> 0 <= used <= 16384 ->
(v + 16 <= HA + 16 \/ HA + 40 <= v + 8) -> (SA + 32 <= HA + 16 \/ HA + 40 <= SA + 16) ->
(v + 16 <= SA + 16 \/ SA + 32 <= v + 8) ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF HA 96 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF v 16 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56 ->
(forall y, v <= y < v + 16 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) ->
(forall y, SA <= y < SA + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (ddw_extra SA v off v0n buf used))) ddw_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_fed)) m1 (seg_rom SEGS))) /\
sh_ok SEGS dj_Bx ddw_SH (Eimg (Ereg regs1 (ddw_extra SA v off v0n buf used))) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 sp HA n SA v off v0n buf used Hsp Hs1 Hs0 Hs2 Hs16 R23 R15 F96 F112 F128 F136 F144 F168 F176
  F192 F224 F232 F240 Voff Vv Vn Vbuf Vused HAW HSW HA1 HA2 HA8 Hn SA1 SA2 SA8 Hv1 Hv2 Hv8 Hoff Hv0n Hb1 Hb8 Hu
  D1 D2 D3 RAH RAV RAS HAPV HAPS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold IMG_TOP in HA2.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (ddw_extra SA v off v0n buf used))).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (EX : forall i, (i < 7)%nat ->
  ew E (32 + i) = nth i (ddw_extra SA v off v0n buf used) (Z_to_bv 64 0)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  do 7 (destruct i as [|i]; [exact (ew_Ereg_extra regs1 _ _)|]). lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SA) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 off) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 v0n) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 buf) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 used) by exact (EX 6%nat ltac:(lia)).
assert (E23 : ew E 23 = Z_to_bv 64 HA) by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); exact R23).
assert (E15 : ew E 15 = Z_to_bv 64 n) by (rewrite (EREG 15%nat 15%bv) by (first [lia | reflexivity]); exact R15).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (U23 : bv_unsigned (ew E 23) = HA) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = n) by (rewrite E15; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = off) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = v0n) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = buf) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = used) by (rewrite E38; apply unsigned_lit_small; lia).
assert (SHR : forall c, 0 <= c -> forall x, 0 <= x -> x + c < 2 ^ 60 ->
  0 <= shadow_addr (x + c) < 2 ^ 64).
{ intros c Hc x Hx Hxc. unfold shadow_addr, SHADOW_OFF.
  split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
  assert ((x + c) / 8 <= x + c) by (apply Z.div_le_upper_bound; lia). lia. }
split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ddw_frame, ddw_off, ddw_hv, ddw_vec, ddw_ent.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp 96 8 (SOff 23 16) (HA + 16));
           [exact (den_atom E 23 HA 16 E23 ltac:(lia) ltac:(lia)) | zside | zside | exact F96].
      -- apply (chunk_ok_val SEGS E _ sp 112 8 _ (shadow_addr (HA + 16)));
           [exact (ddw_den_sh E 23 HA 16 E23 E33 ltac:(lia) ltac:(lia) ltac:(lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply SHR; lia | zside | exact F112].
      -- apply (chunk_ok_val SEGS E _ sp 128 8 (SOff 32 16) (SA + 16));
           [exact (den_atom E 32 SA 16 E32 ltac:(lia) ltac:(lia)) | zside | zside | exact F128].
      -- apply (chunk_ok_val SEGS E _ sp 136 8 (SOff 32 24) (SA + 24));
           [exact (den_atom E 32 SA 24 E32 ltac:(lia) ltac:(lia)) | zside | zside | exact F136].
      -- apply (chunk_ok_val SEGS E _ sp 144 8 (SOff 32 0) SA);
           [exact (den_atom0 E 32 SA E32 ltac:(lia)) | zside | zside | exact F144].
      -- apply (chunk_ok_val SEGS E _ sp 168 8 _ (shadow_addr (HA + 32)));
           [exact (ddw_den_sh E 23 HA 32 E23 E33 ltac:(lia) ltac:(lia) ltac:(lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply SHR; lia | zside | exact F168].
      -- apply (chunk_ok_val SEGS E _ sp 176 8 (SOff 32 32) (SA + 32));
           [exact (den_atom E 32 SA 32 E32 ltac:(lia) ltac:(lia)) | zside | zside | exact F176].
      -- apply (chunk_ok_val SEGS E _ sp 192 8 (SOff 15 0) n);
           [exact (den_atom0 E 15 n E15 ltac:(lia)) | zside | zside | exact F192].
      -- apply (chunk_ok_val SEGS E _ sp 224 8 _ (shadow_addr (SA + 16)));
           [exact (ddw_den_sh E 32 SA 16 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply SHR; lia | zside | exact F224].
      -- apply (chunk_ok_val SEGS E _ sp 232 8 _ (shadow_addr (SA + 24)));
           [exact (ddw_den_sh E 32 SA 24 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply SHR; lia | zside | exact F232].
      -- apply (chunk_ok_val SEGS E _ sp 240 8 (SOff 33 0) SHADOW_OFF);
           [exact (den_atom0 E 33 SHADOW_OFF E33 ltac:(unfold SHADOW_OFF; lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | zside | exact F240].
    * rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (HAW o); unfold ASRC; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ HA 32 8 (SOff 35 0) off);
        [exact (den_atom0 E 35 off E35 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside
        | exact Voff].
    * rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ HA 16 8 (SOff 34 0) v);
        [exact (den_atom0 E 34 v E34 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside
        | exact Vv].
    * rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ v 8 8 (SOff 36 0) v0n);
        [exact (den_atom0 E 36 v0n E36 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside
        | exact Vn].
    * rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (HSW o); unfold AENT; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 37 0) buf);
           [exact (den_atom0 E 37 buf E37 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside
           | exact Vbuf].
      -- apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 38 0) used);
           [exact (den_atom0 E 38 used E38 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside
           | exact Vused].
  + apply pairwise_disjoint_of_extents.
    unfold ddw_frame, ddw_off, ddw_hv, ddw_vec, ddw_ent, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U2, U23, U32, U34.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    change (2 ^ 47) with 140737488355328 in *.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold ddw_facts, ddw_PTRF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U15, U23, U32, U33, U34, U35, U36, U37, U38.
    assert (M16 : sp mod 2 ^ 4 = 0) by (change (2 ^ 4) with 16; exact Hs16).
    assert (M8a : SA mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact SA8).
    assert (M8b : v mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Hv8).
    assert (M8c : buf mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Hb8).
    assert (M8d : HA mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact HA8).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold IMG_TOP.
    repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
      unfold SHADOW_OFF in *; lia.
- unfold sh_ok, ddw_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 23 HA 96 HA 0 96 RAH).
    * unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
    * apply (U_atom E 23 HA E23). lia.
    * lia.
    * lia.
    * intros y Hy. change (Z.min 0 96) with 0 in Hy. change (Z.max 0 96) with 96 in Hy.
      unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 34 v 16 v 0 16 RAV).
    * unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
    * apply (U_atom E 34 v E34). lia.
    * lia.
    * lia.
    * intros y Hy. change (Z.min 0 16) with 0 in Hy. change (Z.max 0 16) with 16 in Hy. apply HAPV. lia.
  + apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 32 SA 56 SA 0 56 RAS).
    * unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
    * apply (U_atom E 32 SA E32). lia.
    * lia.
    * lia.
    * intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPS. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
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
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let JOIN := dr_memchr_join B MT MMAX RG LAWS HG AMEMCHR HCROM HRGD HGSB HMMAX HV9 HSD HSM.
(* The one callee fact of the DROP walk: list_drop's contract at any G with gx_ok, gx_rt and rom_out
   (lib/B/W_list_drop.v pb_list_drop_ro_c, Qed, with the _c free rule AFREE and HCTX_ld).  Only ddw_ld_call uses it,
   at G1 = [(&h->pending, 16)]. *)
Let LDG : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G -> ldrop_spec B MT G (BASE + AF_fr_list_drop) :=
  pb_list_drop_ro_c B MT LAWS TL CTX_F AFREE HCTX_ld AMEMMOVE.

(* ------------------------------------------------------------------ the list_drop call at 0x83914 *)
(* a list's blocks are live blocks (lib/B/W_drain_dnrk.v:558 dnk_alist_blks_in, at this section's B) *)
Lemma ddw_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
- destruct Hb as [<- | Hb].
  + destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
Qed.

(* one live block per address *)
Lemma ddw_blk_uniq : forall ly S (W : world SEGS) m md p q q', AR SEGS B ly S W m md ->
  In (p, q) (ablocks B ly S) -> In (p, q') (ablocks B ly S) -> q = q'.
Proof.
intros ly S W m md p q q' HAR H1 H2.
pose proof (df_pu_nd B LAWS ly S W m md (ablocks B ly S) [] [] HAR ltac:(rewrite app_nil_r; reflexivity)) as ND.
destruct (in_split _ _ H1) as (l1 & l2 & El). rewrite El in ND, H2. rewrite map_app in ND. cbn [map fst] in ND.
apply List.NoDup_remove_2 in ND.
apply in_app_or in H2 as [H2 | [H2 | H2]].
- exfalso. apply ND. apply in_or_app. left. exact (in_map fst _ _ H2).
- apply (f_equal snd) in H2. exact H2.
- exfalso. apply ND. apply in_or_app. right. exact (in_map fst _ _ H2).
Qed.

Lemma ddw_frames_of : forall G1 STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
ajournal_gx SEGS B G1 0 [] STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 -> frames S2 = frames Sc.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
Qed.

(* list_drop's footprint: the vector and the head record's text *)
Definition ddw_FP (l : hlist) : list (Z * Z) :=
[(hl_v l, hl_v l + AREC * hl_cap l);
 (fst (nth 0 (hl_recs l) (0, [])),
  fst (nth 0 (hl_recs l) (0, [])) + req_size (Z.of_nat (length (snd (nth 0 (hl_recs l) (0, [])))) + 1))].

(* a block of the source at the call: one of drain's entry blocks (in dFP) or a block new in the round *)
Lemma ddw_src_awr : forall cx ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 b nb a,
DBASE B MT MMAX RG cx -> DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
In (b, nb) (asrc_blks h1) -> b <= a < b + req_size nb ->
(inFP (dFP cx) a /\ exists b' nb', In (b', nb') (ablocks B ly1 S1) /\ b' <= a < b' + req_size nb') \/
in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 b nb a HB HM HinS Ha.
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPerm0 & _).
assert (Hinv : In (b, nb) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). right. apply in_or_app. right. apply in_or_app. left. exact HinS. }
destruct (in_dec df_pair_dec (b, nb) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnin0].
- left. split; [|exists b, nb; split; [exact Hinv | exact Ha]].
  pose proof (df_pu_ne_in B LAWS ly1 S1 W1 m1 md1 (dxG cx, ATABLE) _ _ HAR1 Hperm
    (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl HinS))))) as HNE.
  cbn [fst] in HNE.
  assert (ND : List.NoDup (map fst (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx))).
  { apply (df_pu_nd B LAWS ly1 S1 W1 m1 md1 _ ((dxG cx, ATABLE) :: aentry_blks e1) [] HAR1).
    rewrite app_nil_r. exact Hperm. }
  pose proof (df_nd_fst _ _ _ ND HinS) as NR.
  pose proof (Permutation_in _ HPerm0 Hin0) as Hin1.
  assert (HinF : In (b, nb) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
  { destruct Hin1 as [Eq|Hin1]; [injection Eq as E1 E2; exfalso; exact (HNE E1)|].
    apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; left; exact Q|].
    apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; right; apply in_or_app; left; exact Q|].
    apply in_app_or in Hin1 as [Q|Q]; [apply in_or_app; right; apply in_or_app; right; exact Q|].
    exfalso. apply NR. apply in_or_app. right. exact Q. }
  exists (b, b + req_size nb). split; [|cbn [fst snd]; lia].
  unfold dFP, dr_fp. right. unfold ablocks_fp.
  exact (in_map (fun b0 : Z * Z => (fst b0, fst b0 + req_size (snd b0))) _ _ HinF).
- right. exists b, nb. split; [exact Hinv|]. split; [exact Hnin0 | exact Ha].
Qed.

(* the call itself, through LDG (pb_list_drop_ro_c) at G1 = [(&h->pending, 16)], composed into drain's journal; the
   continuation gets the call's effect on memory *)
Lemma ddw_ld_call : forall cx ly1 S1 k1 (W : world SEGS) mc mdc regsc raw (l : hlist) Q,
DBASE B MT MMAX RG cx ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W mc mdc k1 ->
spZ regsc = dsp0 cx - DRAIN_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 (dHA RG cx + 16) -> getr regsc 11 = w64 (Z.of_nat 0) ->
alist_at B ly1 S1 W mc (dHA RG cx + 16) l false ->
(0 < length (hl_recs l))%nat ->
mo_ok MT S1 (mo_free MT) ->
rom_view SEGS W mc ->
(forall a, inFP (ddw_FP l) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) ->
(forall W2 ly2 S2 kk regs2 m2 md2,
  ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
    (dxmd cx) [] ly2 S2 W2 m2 md2 kk ->
  aregs_preserved regsc regs2 ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> (forall i', 0 <= i' < req_size n -> ~ inFP (ddw_FP l) (p + i')) ->
     0 <= i < req_size n -> abyte_kept W mc W2 m2 (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dHA RG cx + 16 <= a < dHA RG cx + 32) -> abyte_kept W mc W2 m2 a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mc W2 m2 a) ->
  (forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W mc W2 m2 a) ->
  rom_view SEGS W2 m2 -> apres_kept B W mc W2 m2 -> frames S2 = frames S1 ->
  alist_at B ly2 S2 W2 m2 (dHA RG cx + 16) (ldrop_list l 0%nat) false ->
  (exists b1 b2, ablocks B ly1 S1 = b1 ++ (fst (nth 0 (hl_recs l) (0, [])),
     Z.of_nat (length (snd (nth 0 (hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) ->
  mo_le MT S1 S2 (mo_free MT) ->
  SRr SEGS W2 (mkCfg (mkst regs2 raw m2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_list_drop)) mc (seg_rom SEGS)) mdc) Q.
Proof.
intros cx ly1 S1 k1 W mc mdc regsc raw l Q HB HJ Hsp Hgp Htp Hra Hraw Hra4 Hs0 H10 H11 HL Hi Hmo Hrom HFP HK.
pose proof HB as ((_ & _ & _ & _ & _ & Hstk0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _ & _ & _ & _ & _ & _ & Hrv0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HspR : alloc_ceiling + DRAIN_STK <= dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
clear Hstk0 Hceil Hslo Hshi H47.
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; clear - Hj; lia).
pose proof HGSB as (HGlo & HGhi & HGal). unfold IMG_TOP in HGhi.
assert (Hsub : forall a, inG [(dHA RG cx + 16, 16)] a -> inG (G_DR B RG) a).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  exact (proj1 (df_pu_gs B RG HRGD a ltac:(clear - Ha HAr; unfold ASRC in *; lia))). }
assert (HG1 : gx_ok SEGS B [(dHA RG cx + 16, 16)]) by exact (gx_ok_sub SEGS B _ _ Hsub HG).
assert (HR1 : gx_rt B [(dHA RG cx + 16, 16)]).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  pose proof (df_pu_zpw B RG _ 0%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D0.
  pose proof (df_pu_zpw B RG _ 1%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D1.
  pose proof (df_pu_zpw B RG _ 2%nat 11%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D2.
  cbn [nth] in D0, D1, D2. unfold zdisj in D0, D1, D2. cbn [fst snd] in D0, D1, D2.
  clear - D0 D1 D2 Ha HAr. unfold ASRC in *. repeat split; lia. }
assert (HRO1 : rom_out SEGS B [(dHA RG cx + 16, 16)]).
{ intros a Ha. destruct (HROMO a Ha) as (R1 & R2 & R3 & R4).
  split; [intros Hc; exact (R1 (Hsub a Hc)) | split; [exact R2 | split; [exact R3 | exact R4]]]. }
assert (HZ1 : azs B (dHA RG cx + 16) 16).
{ apply (df_azs_sub B RG HGSB (rg_s RG) (4 * ASRC));
  [exact HGSZ | clear - HAr; unfold ASRC in *; lia | clear - HAr; unfold ASRC in *; lia]. }
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (C16 : (- DRAIN_FRAME) mod 16 = 0) by reflexivity.
assert (Cneg : - DRAIN_FRAME <= 0) by (apply Z.leb_le; reflexivity).
assert (CLD : 0 <= LDROP_STK) by (apply Z.leb_le; reflexivity).
assert (CBUD : LDROP_STK - - DRAIN_FRAME <= DRAIN_STK) by (apply Z.leb_le; reflexivity).
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HLD : LDROP_STK = 16448) by reflexivity.
assert (HLA8 : (dHA RG cx + 16) mod 8 = 0).
{ unfold dHA, ASRC. replace (rg_s RG + 96 * Z.of_nat (dxj cx) + 16) with (rg_s RG + (12 * Z.of_nat (dxj cx) + 2) * 8)
    by lia.
  rewrite Z.mod_add by lia. exact HGal. }
pose proof HL as (_ & _ & _ & _ & HLnc & HLvb & _).
assert (Hmv : AREC * (hl_n l - 1 - Z.of_nat 0) < 2 ^ 32).
{ destruct HLvb as [(Hc0 & _) | (Hcp & Hin & _)].
  - exfalso. clear - HLnc Hc0 Hi. unfold hl_n in *. lia.
  - destruct (al_blocks SEGS B LAWS ly1 S1 W mc mdc _ _ HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    clear - Hn HLnc Hcp. unfold MALLOC_MAX, AREC, hl_n in *. lia. }
assert (HLAg : forall a, dHA RG cx + 16 <= a < dHA RG cx + 16 + 16 ->
  inG [(dHA RG cx + 16, 16)] a /\ ~ (spZ regsc - LDROP_STK <= a < spZ regsc)).
{ intros a Ha. split; [exact (proj2 (df_G1_in _ a) Ha)|]. rewrite Hsp.
  clear - Ha HAr HGhi HspR C1 ACL HDS HDF HLD. unfold ASRC in *. lia. }
assert (HVg : forall a, hl_v l <= a < hl_v l + AREC * hl_cap l -> ~ (spZ regsc - LDROP_STK <= a < spZ regsc)).
{ intros a Ha. rewrite Hsp. destruct HLvb as [(Hc0 & Hv0) | (Hcp & Hin & _)].
  - exfalso. rewrite Hc0 in Ha. clear - Ha. unfold AREC in Ha. lia.
  - destruct (al_blocks SEGS B LAWS ly1 S1 W mc mdc _ _ HARc Hin) as (_ & _ & Hc & _).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(clear - Hcp; unfold AREC; lia)) as (_ & Hrq).
    clear - Ha Hc Hrq HspR HDS HDF HLD C1 ACL. lia. }
assert (HFPp : ~ YI16.sink_open_fp (ddw_FP l)).
{ apply sink_closed_pos. unfold ddw_FP.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & HLF).
  destruct (hl_recs l) as [|r0 rs0] eqn:Er; [cbn in Hi; lia|].
  apply Forall_inv in HLF. destruct HLF as (Hr0in & _).
  destruct (al_blocks SEGS B LAWS ly1 S1 W mc mdc _ _ HARc Hr0in) as (_ & Hr04096 & _).
  destruct HLvb as [(Hc0 & Hv0) | (Hcp & Hin & _)].
  - exfalso. clear - HLnc Hc0 Hi Er. unfold hl_n in *. rewrite Er in HLnc. cbn [length] in HLnc. lia.
  - destruct (al_blocks SEGS B LAWS ly1 S1 W mc mdc _ _ HARc Hin) as (_ & Hv4096 & _).
    constructor; [cbn [fst]; clear - Hv4096; lia | constructor; [cbn [fst nth]; clear - Hr04096; lia | constructor]]. }
eapply SRr_bind.
{ eapply (df_gx_call B RG LAWS HG [(dHA RG cx + 16, 16)] W regsc mc (BASE + AF_fr_list_drop) DRAIN_STK (dsp0 cx)
    (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) ly1 S1 mdc k1 LDROP_STK (ddw_FP l) (- DRAIN_FRAME) raw []
    (fun ly2 S2 W2 regs2 mem2 md2 kk =>
       alist_at B ly2 S2 W2 mem2 (dHA RG cx + 16) (ldrop_list l 0%nat) false /\
       (exists b1 b2, ablocks B ly1 S1 = b1 ++ (fst (nth 0 (hl_recs l) (0, [])),
          Z.of_nat (length (snd (nth 0 (hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
       apres_kept B W mc W2 mem2 /\
       (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) mc (as_errno B + i)) /\
       mo_le MT S1 S2 (mo_free MT))
    Hsub HJ Hsp C16 Cneg CLD CBUD Hgp Htp Hra Hraw Hra4 (achain_low _ _ _ _ Hs0)).
  - intros HPRE1. eapply SRr_mono.
    { exact (LDG [(dHA RG cx + 16, 16)] HG1 HR1 HRO1 W ly1 S1 regsc mc mdc []
        (dHA RG cx + 16) l false 0%nat HPRE1 H10 H11 HL Hi HLA8 ltac:(clear - HAr HGlo; lia) Hmv HZ1 HLAg HVg Hmo Hrom). }
    cbv beta. unfold ldrop_post.
    intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPK & Herr & HAL & HBS & HMLE).
    exists ly2, S2, regs2, mem2, md2, 1.
    split; [rewrite Hra; reflexivity|]. split; [rewrite Hsp in HJ2; exact HJ2|]. split; [exact HP2|].
    split; [exact HAL|]. split; [exact HBS|]. split; [exact HPK|]. split; [exact Herr | exact HMLE].
  - exact HFP. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & kk & -> & HJa & HJb & HP & (HAL & HBS & HPK & Herr & HMLE)).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb) as HAR2.
apply (HK W2 ly2 S2 (k1 + kk) regs2 mem2 md2).
- exact HJa.
- exact HP.
- (* a live block off the call's footprint: the callee's block clause keeps it, and it is alive *)
  intros p n i Hin Hno Hi'.
  destruct (df_keep_blk B RG LAWS HG [(dHA RG cx + 16, 16)] LDROP_STK (dsp0 cx + - DRAIN_FRAME) (ddw_FP l) ly1 S1 W mc mdc
    ly2 S2 W2 mem2 md2 kk p n Hsub HARc HJb Hin Hno) as [Hin2 Hv].
  split; [exact (Hv i Hi') | intros _; exact (df_blk_wr B LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin2 i Hi')].
- (* an image byte off h->pending: the callee's image clause, its presence by apres_kept *)
  intros a Hia Ho He Hn. split.
  + apply (df_keep_img B [(dHA RG cx + 16, 16)] LDROP_STK (dsp0 cx + - DRAIN_FRAME) (ddw_FP l) ly1 S1 W mc mdc
      ly2 S2 W2 mem2 md2 kk).
    * exact HFPp.
    * exact HJb.
    * exact Hia.
    * exact Ho.
    * exact He.
    * intros Hc. apply Hn. apply (proj1 (df_G1_in _ a)) in Hc. clear - Hc. lia.
  + exact (df_wr_img W W2 mc mem2 a Hia (HPK a Hia Ho He)).
- (* errno: ldrop_post's view, and a writable segment's byte *)
  intros a Ha.
  assert (Hv : aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mc a).
  { replace a with (as_errno B + (a - as_errno B)) by ring. apply Herr. clear - Ha. lia. }
  assert (HeG : inG (G_DR B RG) a).
  { unfold G_DR, G_SL, inG. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha. lia. }
  split; [exact Hv|]. intros Hw.
  apply (df_err_wr W W2 mc mem2 a (proj1 (HG a HeG))); [|exact Hv|exact Hw].
  intros Hr. exact (proj1 (proj2 (proj2 (HROMO a Hr))) Ha).
- (* drain's frame: above the callee's window, kept by its stack clause; present by drain's journal *)
  intros a Ha. split.
  + apply (df_keep_hi B RG HG [(dHA RG cx + 16, 16)] LDROP_STK (dsp0 cx + - DRAIN_FRAME) (ddw_FP l) ly1 S1 W mc mdc
      ly2 S2 W2 mem2 md2 kk Hsub HJb a).
    * clear - HspR Ha HDS HDF C1. lia.
    * clear - Ha HLD. lia.
  + intros _. apply (apresent_writable SEGS).
    apply (df_gx_pres B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa).
    clear - Ha HDS HDF. lia.
- exact (ajournal_gx_rom_view SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa HROMO Hrv0).
- exact HPK.
- exact (ddw_frames_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb).
- exact HAL.
- exact HBS.
- exact HMLE.
Qed.

(* the meter over a trace's parts (W_drain_feed.v:2010-2033, here at this section's MT) *)
Lemma ddw_tr_cost_app : forall (t1 t2 : dtrace), tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma ddw_tr_alloc_app : forall (t1 t2 : dtrace), tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma ddw_tr_max_nonneg : forall (t : dtrace), 0 <= tr_max t.
Proof.
intros t. unfold tr_max. induction t as [|ev t IH]; [cbn [fold_right]; lia|].
cbn [fold_right]. destruct ev; lia.
Qed.
Lemma ddw_tr_max_app : forall (t1 t2 : dtrace), tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (ddw_tr_max_nonneg t2) as H2. unfold tr_max in *.
induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

(* the budget after list_drop: spent grows by one free, the trace loses list_drop's request.  C3: the free of the head
   record (list_drop_tra's one request, RFree (n + 1)) lowers the live bytes by its size, so the peak of the rest stays
   in room (W_tr_peak.v tr_peak_free) *)
Lemma ddw_bud : forall cx S1 S2 spent (ad : dadrF) n tl2,
dbud MT MMAX cx S1 spent (ListTr.list_drop_tra ad n ++ tl2) ->
mo_le MT S1 S2 (mo_free MT) -> blocks_bytes S2 + (n + 1) <= blocks_bytes S1 ->
dbud MT MMAX cx S2 (spent + mo_free MT) tl2.
Proof.
intros cx S1 S2 spent ad n tl2 (B1 & B2 & B3 & B4 & B5) Hmle Hbb.
pose proof (mo_free_nonneg MT MTL) as F0.
rewrite ddw_tr_cost_app in B3.
rewrite ddw_tr_max_app in B5.
change (tr_cost MT (ListTr.list_drop_tra ad n)) with (mo_free MT + 0) in B3.
unfold ListTr.list_drop_tra in B4. cbn [app] in B4. rewrite W_tr_peak.tr_peak_free in B4.
change (tr_max (ListTr.list_drop_tra ad n)) with 0 in B5.
pose proof (ddw_tr_max_nonneg tl2) as M0.
split; [exact (mo_le_trans MT MTL _ _ _ _ _ B1 Hmle)|].
split; [lia|]. split; [lia|]. split; lia.
Qed.

Theorem dr_drop : dr_drop_stmt B MT MMAX RG.
Proof.
unfold dr_drop_stmt. intros cx s1 D W1 c1 HB HDE Kll Klr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
destruct HDE as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & Hsp & R3 & R4 & R8 & R9 & R18 & R23 & R15 & HFR & F96 & F112 & F168 & F192 & Hn0 & Hjunk & HM & HnzU &
  Hused & HDB & HSAME & Hcap & HU & Hsk & HHk & Hka & Hei & Hpend & Hoff & Hst & Hen & Hec & HH & HRS & HFUT & HBUD).
subst c1.
pose proof HM as (HJ & Hrom & Hpres & Hframes & HFRm & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof HB as (Hafn & _ & HGB & HSAlo & HSAhi & HSA8 & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (HG16 & HG4 & HGc & HGapp & _).
change (req_size ATABLE) with 896 in HGc, HGapp.
pose proof HRS as (Href & HJ1 & H4096 & Hdwf & Hstrict & Hei1 & Hpne).
pose proof HJ1 as (_ & _ & _ & HNZ).
pose proof HEOK as (Heof & Hskp & Hp1 & Hp2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & _).
assert (HULEN : ulen s1 = re_used e1) by (unfold ulen; rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcap16 : re_cap e1 <= 16384) by (destruct Hcapr as [X|[X|X]]; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & HBin & Hjunkl & Hbgarr)]; [exfalso; lia|].
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
(* the source: h->pending's head record r0, its vector v *)
pose proof Hsrc as (A1 & A2 & A3 & A4 & AW & A6 & A7 & A8 & A9 & AL & AOFF & A40 & A48 & A56 & AOR & A16 & A17 &
  A18 & A19 & A20 & A21 & A22 & A23 & A24).
pose proof AL as (LV & LN & LC & LW & LNC & LBLK & LND & LNI & LF).
assert (Erecs : exists r0 rs0, hl_recs (hs_pending h1) = r0 :: rs0).
{ destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:E; [|exists r0, rs0; reflexivity].
  exfalso. try rewrite E in Hpend. cbn [map] in Hpend. exact (Hpne (eq_sym Hpend)). }
destruct Erecs as (r0 & rs0 & Erecs).
assert (Ehead : dhead s1 = bzs (snd r0) /\ dtail s1 = map (fun r => bzs (snd r)) rs0).
{ unfold dhead, dtail. rewrite <- Hpend, Erecs. cbn [map]. split; reflexivity. }
assert (Hn1 : 1 <= hl_n (hs_pending h1)) by (unfold hl_n; rewrite Erecs; cbn [length]; lia).
destruct LBLK as [(Hcv0 & _) | (Hcvp & Hvin & Hvjl & Hvg)]; [lia|].
set (v := hl_v (hs_pending h1)) in *.
set (vcap := hl_cap (hs_pending h1)) in *.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 v (AREC * vcap) HAR Hvin) as (Hv16 & Hv4096 & Hvc & Hvapp & _ & _ & Hvn).
pose proof (req_size_pos (AREC * vcap) ltac:(unfold AREC; lia)) as (_ & Hvrq).
pose proof LF as LF0. rewrite Erecs in LF0. apply Forall_inv in LF0. destruct LF0 as (Hr0in & Hr0g & _ & Hr0l).
specialize (Hr0l eq_refl).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR Hr0in) as (_ & Hr04096 & Hr0c & _ & _ & _ & Hr0n).
unfold MALLOC_MAX in Hvn, Hr0n.
assert (Hv0n : val_mem SEGS (arm W1 m1) (v + 8) 8 (Z.of_nat (length (snd r0)))).
{ rewrite Erecs in Hvg. cbn [map concat] in Hvg. rewrite <- app_assoc in Hvg. exact (ddw_v0n _ v r0 _ Hvg ltac:(lia)). }
destruct AOR as [(Hnil & _) | (r0' & rs0' & Er0 & Hoffr)]; [rewrite Erecs in Hnil; discriminate|].
rewrite Erecs in Er0. injection Er0 as <- <-.
assert (Hdn : dnum s1 = Z.min (Z.of_nat (length (snd r0)) - hs_off h1) (re_cap e1 - re_used e1)).
{ unfold dnum. rewrite (proj1 Ehead), Hoff, Hcap, HULEN. unfold bzs. rewrite length_map. reflexivity. }
(* the source slot HA = &g_s[j] *)
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
pose proof HGSB as (HGlo & HGhi & HGal). unfold IMG_TOP in HGhi.
assert (HAr : 0x10000 <= dHA RG cx /\ dHA RG cx + 96 <= 0x5fc000 /\ rg_s RG <= dHA RG cx /\
  dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; lia).
assert (HA8 : dHA RG cx mod 8 = 0).
{ rewrite HAe. unfold ASRC. replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with (rg_s RG + (12 * Z.of_nat (dxj cx)) * 8) by lia.
  rewrite Z.mod_add by lia. exact HGal. }
assert (GSI : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B)).
{ intros x Hx. destruct (HG x (proj1 (df_pu_gs B RG HRGD x Hx))) as (Gi & Gn & _). exact (conj Gi Gn). }
(* the regions are apart *)
assert (HvG : v <> dxG cx).
{ intros E. apply (df_pu_ne_in B LAWS ly1 S1 W1 m1 md1 (dxG cx, ATABLE) (v, AREC * vcap) _ HAR Hperm);
    [| cbn [fst]; exact (eq_sym E)].
  apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left.
  unfold alist_blks. fold v vcap. rewrite (proj2 (Z.eqb_neq vcap 0) ltac:(lia)). left. reflexivity. }
assert (D1 : v + 16 <= dHA RG cx + 16 \/ dHA RG cx + 40 <= v + 8).
{ assert (X : forall x, v + 8 <= x < v + 8 + 8 -> dHA RG cx + 16 <= x < dHA RG cx + 16 + 24 -> False).
  { intros x Hx1 Hx2. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR Hvin); [unfold AREC in *; lia|].
    exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))). }
  destruct (ddw_apart (v + 8) 8 (dHA RG cx + 16) 24 ltac:(lia) ltac:(lia) X); [left | right]; lia. }
assert (D2 : dxSA cx + 32 <= dHA RG cx + 16 \/ dHA RG cx + 40 <= dxSA cx + 16).
{ assert (X : forall x, dxSA cx + 16 <= x < dxSA cx + 16 + 16 -> dHA RG cx + 16 <= x < dHA RG cx + 16 + 24 -> False).
  { intros x Hx1 Hx2. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
    exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))). }
  destruct (ddw_apart (dxSA cx + 16) 16 (dHA RG cx + 16) 24 ltac:(lia) ltac:(lia) X); [left | right]; lia. }
assert (D3 : v + 16 <= dxSA cx + 16 \/ dxSA cx + 32 <= v + 8).
{ assert (X : forall x, v + 8 <= x < v + 8 + 8 -> dxSA cx + 16 <= x < dxSA cx + 16 + 16 -> False).
  { intros x Hx1 Hx2. apply (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 v (AREC * vcap) (dxG cx) ATABLE x HAR Hvin GT HvG);
      [unfold AREC in *; lia | change (req_size ATABLE) with 896; lia]. }
  destruct (ddw_apart (v + 8) 8 (dxSA cx + 16) 16 ltac:(lia) ltac:(lia) X); [left | right]; lia. }
(* the frame slots *)
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 & F176 &
  F184 & F200 & F208 & F216 & F224 & F232 & F240 & FS).
assert (Hsp0 : 2 ^ 46 <= dsp0 cx - DRAIN_FRAME /\ alloc_ceiling <= dsp0 cx - DRAIN_FRAME /\
  dsp0 cx - DRAIN_FRAME + 352 <= 2 ^ 47 /\ (dsp0 cx - DRAIN_FRAME) mod 16 = 0).
{ rewrite HDF. split; [lia|]. split; [lia|]. split; [lia|]. rewrite Zminus_mod, Hal16. reflexivity. }
pose proof (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR GT
  HSAlo ltac:(change (req_size ATABLE) with 896; lia)) as RAS.
pose proof (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 v (AREC * vcap) v 16 HAR Hvin
  ltac:(lia) ltac:(unfold AREC in *; lia)) as RAV.
pose proof (azs_range_addressable B LAWS ly1 S1 W1 m1 md1 (dHA RG cx) 96 HAR
  (df_azs_sub B RG HGSB (rg_s RG) (4 * ASRC) (dHA RG cx) 96 HGSZ ltac:(lia) ltac:(unfold ASRC in *; lia))) as RAH.
assert (Hv16b : 16 <= req_size (AREC * vcap) /\ v + 16 <= alloc_ceiling)
  by (clear - Hvc Hvrq Hcvp; unfold AREC in *; lia).
assert (HAPS : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. clear - Hy HSAlo HSAhi HGapp C1 C2 C3 C4 C5.
  unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (HAPV : forall y, v <= y < v + 16 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. clear - Hy Hvapp Hv16b C1 C2 C3 C4 C5.
  unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
pose proof (dnk_entry_buf (arm W1 m1) (dxSA cx) e1 Hgarr Hp1 ltac:(lia)) as V16.
pose proof (dnk_entry_used (arm W1 m1) (dxSA cx) e1 Hgarr Hp1 ltac:(lia)) as V24.
destruct (ddw_seat W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dHA RG cx) (dnum s1) (dxSA cx) v (hs_off h1)
  (Z.of_nat (length (snd r0))) (re_buf e1) (re_used e1) Hsp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R23 R15
  F96 F112 F128 F136 F144 F168 F176 F192 F224 F232 F240 AOFF LV Hv0n V16 V24 AW Hawr
  ltac:(lia) ltac:(unfold IMG_TOP; lia) HA8 ltac:(lia) ltac:(lia) ltac:(lia) HSA8 ltac:(lia) (proj2 Hv16b)
  ltac:(rewrite Zmod_divides in Hv16 |- * by lia; destruct Hv16 as (c & Hc); exists (2 * c); lia)
  ltac:(lia) ltac:(lia) ltac:(lia) Hdb3 ltac:(lia) D1 D2 D3 RAH RAV RAS HAPV HAPS) as [HS SHOK].
remember (Eimg (Ereg regs1 (ddw_extra (dxSA cx) v (hs_off h1) (Z.of_nat (length (snd r0))) (re_buf e1) (re_used e1))))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (EX : forall i, (i < 7)%nat -> ew E (32 + i) =
  nth i (ddw_extra (dxSA cx) v (hs_off h1) (Z.of_nat (length (snd r0))) (re_buf e1) (re_used e1)) (Z_to_bv 64 0)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  do 7 (destruct i as [|i]; [exact (ew_Ereg_extra regs1 _ _)|]). lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (hs_off h1)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (Z.of_nat (length (snd r0)))) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_buf e1)) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 (re_used e1)) by exact (EX 6%nat ltac:(lia)).
clear HE EX.
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact Hsp).
assert (B23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); rewrite R23;
      apply unsigned_lit_small; lia).
assert (B32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (B34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (FPE : forall y, dxSA cx <= y < dxSA cx + 56 ->
  inFP (dFP cx) y /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= y < b + req_size nb).
{ intros y Hy. split.
  - exists (dxSA cx, dxSA cx + AENT). split; [unfold dFP, dr_fp; left; reflexivity | cbn [fst snd]; unfold AENT; lia].
  - exists (dxG cx), ATABLE. split; [exact GT | change (req_size ATABLE) with 896; lia]. }
assert (GSW : forall y, dHA RG cx + 16 <= y < dHA RG cx + 40 -> inG (G_DR B RG) y)
  by (intros y Hy; exact (proj1 (df_pu_gs B RG HRGD y ltac:(unfold ASRC in *; lia)))).
unfold cfg_at. change (w64 (BASE + A_dr_fed)) with (Z_to_bv 64 (BASE + A_dr_fed)).
assert (E15 : ew E 15 = Z_to_bv 64 (dnum s1))
  by (rewrite (EREG 15%nat 15%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R15).
pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR GT) as HoffG. red in HoffG.
change (req_size ATABLE) with 896 in HoffG.
assert (Hlen0 : Z.of_nat (length (snd r0)) < 2 ^ 28) by lia.
(* the list's bytes are off both windows *)
assert (HPB : forall p q x, In (p, q) (alist_blks (hs_pending h1)) -> p <= x < p + req_size q ->
  0 <= x < 2 ^ 64 /\ ~ (dHA RG cx + 32 <= x < dHA RG cx + 40) /\ ~ (dxSA cx + 24 <= x < dxSA cx + 32)).
{ intros p q x Hpq Hx.
  assert (Hpq1 : In (p, q) (ablocks B ly1 S1)) by exact (ddw_alist_blks_in ly1 S1 W1 m1 _ _ _ AL _ Hpq).
  assert (HpG : p <> dxG cx).
  { intros E0. apply (df_pu_ne_in B LAWS ly1 S1 W1 m1 md1 (dxG cx, ATABLE) (p, q) _ HAR Hperm);
      [| cbn [fst]; exact (eq_sym E0)].
    apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left. exact Hpq. }
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 p q HAR Hpq1) as (_ & Hp4 & Hpc & _).
  split; [lia|]. split.
  - intros Hg. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 p q x HAR Hpq1 Hx).
    exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
  - intros Hs. apply (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 p q (dxG cx) ATABLE x HAR Hpq1 GT HpG Hx).
    change (req_size ATABLE) with 896. lia. }
paj_run_tok RUN HS HJ SHOK dj_Bspan.
{ ddw_awr B2 B23 B32 GSW FPE. }
lazymatch type of HS with context [restrict _ ?y] => rename y into msA end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
psrr_branch_tok RUN BR HS SHOK dj_Bspan.
- (* 0x83908 taken: off + n <> v[0].n, the head text stays (not dwhole s1) *)
  rewrite (ddw_bne E (dnum s1) (hs_off h1) (Z.of_nat (length (snd r0))) E15 E35 E36 ltac:(lia) ltac:(lia) ltac:(lia))
    in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hwh : dwhole s1 = false).
  { unfold dwhole. rewrite (proj1 Ehead), <- Hoff. unfold bzs. rewrite length_map. apply Z.eqb_neq. clear - Hc. lia. }
  assert (Hlt : hs_off h1 + dnum s1 < Z.of_nat (length (snd r0))) by (clear - Hdn Hc; lia).
  paj_run_to_tok RUNTO HS HJ SHOK dj_Bspan A_dr_join.
  { ddw_awr B2 B23 B32 GSW FPE. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR2; rename HG0 into GR2; clear HF.
  (* the two runs wrote h->pending_off and s->used only *)
  assert (KL2 : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hy1 Hy2. etransitivity.
    - apply (aview_eq_of SEGS); apply FR2; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin.
    - apply (aview_eq_of SEGS); apply FR1; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin. }
  assert (KP2 : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hy))).
  assert (KK : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hy1 Hy2. split; [exact (KL2 y Hy Hy1 Hy2)|].
    unfold arm. exact (writable_kept (w_H W1) m1 (ms_mem msF) y (KP2 y)). }
  assert (Hromc : rom_view SEGS W1 (ms_mem msF)).
  { intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
    rewrite KL2; [exact (Hrom y Hy) | clear - Hyi; lia | intros Hg; exact (HGR y (GSW y ltac:(lia)) Hy)
      | clear - HoffG HSAlo HSAhi Hyi; lia]. }
  assert (AL2 : alist_at B ly1 S1 W1 (ms_mem msF) (dHA RG cx + 16) (hs_pending h1) false).
  { apply (alist_at_kept B ly1 S1 W1 m1 ly1 S1 W1 (ms_mem msF) _ _ _ AL).
    - apply (df_pu_alist_kept B RG ly1 S1 W1 W1 m1 (ms_mem msF) _ _ _ AL).
      + intros x Hx. apply KK; [lia | lia |]. intros Hs.
        apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
        exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
      + intros p q x Hpq Hx. destruct (HPB p q x Hpq Hx) as (X1 & X2 & X3). exact (KK x X1 X2 X3).
    - intros bb Hbb. exact (ddw_alist_blks_in ly1 S1 W1 m1 _ _ _ AL bb Hbb). }
  (* the two stores: h->pending_off = off + n, s->used = used + n *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 4 _ HS eq_refl) as RG4
  end.
  cbn [ms_mem restrict] in RG1, RG4.
  assert (Voff : val_mem SEGS (arm W1 (ms_mem msF)) (dHA RG cx + 32) 8 (hs_off h1 + dnum s1)).
  { first [ unfold arm; eapply (field_of_region _ _ 23%nat (dHA RG cx) _ _ _ _ _ 32 8%N _ (hs_off h1 + dnum s1) RG1 B23);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | first [ rewrite (ddw_den_add _ 15 35 (dnum s1) (hs_off h1) E15 E35 ltac:(lia) ltac:(lia))
                    | rewrite (ddw_den_add _ 35 15 (hs_off h1) (dnum s1) E35 E15 ltac:(lia) ltac:(lia)) ]; f_equal; lia
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  assert (Vu : val_mem SEGS (arm W1 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + dnum s1)).
  { first [ unfold arm; eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 24 8%N _ (re_used e1 + dnum s1) RG4 B32);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | first [ rewrite (ddw_den_add _ 38 15 (re_used e1) (dnum s1) E38 E15 ltac:(lia) ltac:(lia))
                    | rewrite (ddw_den_add _ 15 38 (dnum s1) (re_used e1) E15 E38 ltac:(lia) ltac:(lia)) ]; f_equal; lia
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  assert (KX : forall y, 0 <= y < 2 ^ 64 -> ~ ddX RG cx (dsp0 cx - DRAIN_FRAME) (fun _ => False) y ->
    abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hx. unfold ddX in Hx.
    apply KK; [exact Hy | intros Hc'; apply Hx; left; clear - Hc'; lia | intros Hc'; apply Hx; right; left; exact Hc']. }
  assert (Hoff2 : (hl_recs (hs_pending h1) = [] /\ hs_off h1 + dnum s1 = 0) \/
    (exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= hs_off h1 + dnum s1 < Z.of_nat (length (snd r))))
    by (right; exists r0, rs0; split; [exact Erecs | clear - Hoffr Hn0 Hlt; lia]).
  pose proof (dd_arm_close B MT MMAX RG LAWS HG HGO HRGD HGSB cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 ly1 S1 W1 (ms_mem msF) _ _ (dsp0 cx - DRAIN_FRAME) (fun _ => False) (hs_pending h1)
    (hs_off h1 + dnum s1) [] (dnum s1) HB HM HJ Hromc (fun y _ _ _ Hp => KP2 y Hp) eq_refl
    ltac:(clear - Hsp0; lia) (fun y Hy => False_ind _ Hy) (fun y Hy Hx _ => KX y Hy Hx)
    AL2 eq_refl eq_refl eq_refl (Permutation_refl _) Voff
    Hoff2
    Vu ltac:(clear - Hn0; lia) ltac:(clear - Hjunkl Hdn; lia) ltac:(clear - Hcpos; lia)) as HM2.
  pose proof HM2 as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  destruct HFUT as (tl2 & HLF & Htl).
  unfold ddrop in Htl. rewrite Hwh in Htl. cbn [app] in Htl. subst tl.
  rewrite Hwh in HLF.
  apply (JOIN cx s1 D 0%nat W1 _ HB); [|exact Kll | exact Klr].
  eapply (dd_DJ B MT MMAX RG HGSB cx s1 D (ms_regs msF) ly1 S1 W1 (ms_mem msF) _ _ e1 h1 (hs_pending h1)
    (hs_off h1 + dnum s1) out1 ev1 LB1 spent (jb + dnret (ddrop s1 a))%nat a (drain_b_c.da_out a) (drain_b_c.da_hp a)
    (drain_b_c.da_keys a) tl2).
  + unfold dregs_line.
    split; [unfold spZ; rewrite X2, (EREG 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]);
      exact Hsp|].
    split; [rewrite X3, (EREG 3%nat 3%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R3|].
    split; [rewrite X4, (EREG 4%nat 4%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R4|].
    split; [rewrite X21, E32; reflexivity|].
    split; [rewrite X20, E32, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, E32, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X8, (EREG 8%nat 8%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R8|].
    split; [rewrite X9, (EREG 9%nat 9%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R9|].
    split; [rewrite X18, (EREG 18%nat 18%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R18|].
    exact HFRF.
  + rewrite X26. reflexivity.
  + rewrite X24, E37. reflexivity.
  + exact HDB.
  + exact HM2.
  + exact Hjunk.
  + exact HSAME.
  + exact Hcap.
  + exact HU.
  + exact Hsk.
  + exact HHk.
  + exact Hka.
  + exact Hei.
  + exact Hst.
  + exact Hen.
  + exact Hec.
  + exact HH.
  + exact HRS.
  + reflexivity.
  + reflexivity.
  + rewrite Hwh. exact Hpend.
  + rewrite Hwh, Hoff. reflexivity.
  + exact HLF.
  + exact HBUD.
- (* 0x83908 not taken: off + n = v[0].n, the head text is used up (dwhole s1): list_drop (&h->pending, 0) *)
  rewrite (ddw_bne E (dnum s1) (hs_off h1) (Z.of_nat (length (snd r0))) E15 E35 E36 ltac:(lia) ltac:(lia) ltac:(lia))
    in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hwh : dwhole s1 = true).
  { unfold dwhole. rewrite (proj1 Ehead), <- Hoff. unfold bzs. rewrite length_map. apply Z.eqb_eq. clear - Hc. lia. }
  (* the budget: list_drop's free is the first request of the round's rest *)
  assert (HCP : 0 <= drain_b_c.ds_cap s1) by (clear - H4096 HULEN HUlen; unfold ulen in *; lia).
  assert (HOC : 0 <= drain_b_c.ds_ocap s1).
  { destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & Hoc).
    clear - Hoc. destruct Hoc as [(E0 & _) | (P0 & _)]; lia. }
  assert (HEC : 0 <= drain_b_c.ds_ecap s1).
  { destruct (Z_lt_le_dec (drain_b_c.ds_ecap s1) 0) as [Hlt0|Hge]; [|exact Hge].
    pose proof (df_pcapm_neg B RG HGSB (dref s1) (drain_b_c.ds_en s1) _ Hlt0) as X.
    pose proof A22 as (_ & _ & _ & _ & Hnc22 & _). unfold hl_n in Hnc22.
    rewrite <- Hec in X. clear - X Hnc22. lia. }
  pose proof (df_tnn_drfut B RG HGSB cx s1 jb a tl HCP HEC HOC HFUT) as TNN.
  destruct HFUT as (tl2 & HLF & Htl).
  unfold ddrop in Htl. rewrite Hwh in Htl. rewrite Hwh in HLF. subst tl.
  apply Forall_app in TNN as [_ TN2].
  pose proof (df_tnn_cost B MT RG MTL HGSB tl2 TN2) as TC2.
  pose proof (mo_free_nonneg MT MTL) as F0.
  assert (HMO1 : mo_ok MT S1 (mo_free MT)).
  { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMok).
    pose proof HBUD as (Bl & _ & Bc & _ & _).
    rewrite ddw_tr_cost_app in Bc.
    lazymatch type of Bc with context [tr_cost MT (ListTr.list_drop_tra ?x ?y)] =>
      change (tr_cost MT (ListTr.list_drop_tra x y)) with (mo_free MT + 0) in Bc end.
    apply (mok_station MT (dxS cx) S1 _ spent _ MTL HMok Bl); [exact F0|]. clear - Bc TC2. lia. }
  assert (Hr0G : fst r0 <> dxG cx).
  { intros E0. apply (df_pu_ne_in B LAWS ly1 S1 W1 m1 md1 (dxG cx, ATABLE) (fst r0, Z.of_nat (length (snd r0)) + 1) _
      HAR Hperm); [| cbn [fst]; exact (eq_sym E0)].
    apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left.
    unfold alist_blks. apply in_or_app. right. rewrite Erecs. left. reflexivity. }
  (* to the call: no store on this stretch *)
  paj_run_to_tok RUNTO HS HJ SHOK dj_Bspan AF_fr_list_drop.
  { ddw_awr B2 B23 B32 GSW FPE. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msC end.
  rename HFr into FR2; rename HG0 into GR2; clear HF.
  assert (KLC : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W1) (ms_mem msC) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hy1 Hy2. etransitivity.
    - apply (aview_eq_of SEGS); apply FR2; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin.
    - apply (aview_eq_of SEGS); apply FR1; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin. }
  assert (KPC : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msC) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hy))).
  assert (KKC : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> abyte_kept W1 m1 W1 (ms_mem msC) y).
  { intros y Hy Hy1 Hy2. split; [exact (KLC y Hy Hy1 Hy2)|].
    unfold arm. exact (writable_kept (w_H W1) m1 (ms_mem msC) y (KPC y)). }
  assert (HromC : rom_view SEGS W1 (ms_mem msC)).
  { intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
    rewrite KLC; [exact (Hrom y Hy) | clear - Hyi; lia | intros Hg; exact (HGR y (GSW y ltac:(lia)) Hy)
      | clear - HoffG HSAlo HSAhi Hyi; lia]. }
  assert (ALC : alist_at B ly1 S1 W1 (ms_mem msC) (dHA RG cx + 16) (hs_pending h1) false).
  { apply (alist_at_kept B ly1 S1 W1 m1 ly1 S1 W1 (ms_mem msC) _ _ _ AL).
    - apply (df_pu_alist_kept B RG ly1 S1 W1 W1 m1 (ms_mem msC) _ _ _ AL).
      + intros x Hx. apply KKC; [lia | lia |]. intros Hs.
        apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
        exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
      + intros p q x Hpq Hx. destruct (HPB p q x Hpq Hx) as (X1 & X2 & X3). exact (KKC x X1 X2 X3).
    - intros bb Hbb. exact (ddw_alist_blks_in ly1 S1 W1 m1 _ _ _ AL bb Hbb). }
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?ms0) _ (ms_mem ?ms0) _; cfg_model := ?md0 |} _ =>
    set (rc0 := ms_regs ms0) in *; set (mc := ms_mem ms0) in *; set (mdc := md0) in * end.
  refine (ddw_ld_call cx ly1 S1 _ W1 mc mdc rc0 (getr rc0 1) (hs_pending h1) _ HB HJ _ _ _ eq_refl _ _ _ _ _ ALC
    ltac:(rewrite Erecs; cbn [length]; lia) HMO1 HromC _ _).
  { unfold spZ. rewrite Q2, (EREG 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). exact Hsp. }
  { rewrite Q3, (EREG 3%nat 3%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). rewrite R3. exact Hgp. }
  { rewrite Q4, (EREG 4%nat 4%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). rewrite R4. exact Htp. }
  { rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { rewrite T1, unsigned_lit_small by (clear - HBASE; lia). clear - HBASE. lia. }
  { unfold s0Z. rewrite Q8, (EREG 8%nat 8%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). rewrite R8.
    unfold w64. rewrite unsigned_lit_small by (clear - HGlo HGhi; unfold ASRC in *; lia).
    clear - HGlo HGhi C1. unfold ASRC in *. lia. }
  { rewrite Q10, B23; reflexivity. }
  { rewrite Q11; reflexivity. }
  { (* the footprint: the vector and r0's text are source blocks, in dFP or new in the round *)
    intros y (r & Hr & Hry). cbn [ddw_FP In] in Hr. rewrite Erecs in Hr. cbn [nth] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hry.
    - apply (ddw_src_awr cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 _ LB1 v (AREC * vcap) y HB HM); [|lia].
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks. fold v vcap.
      rewrite (proj2 (Z.eqb_neq vcap 0) ltac:(lia)). left. reflexivity.
    - apply (ddw_src_awr cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 _ LB1 (fst r0) (Z.of_nat (length (snd r0)) + 1) y HB
        HM); [|lia].
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks. apply in_or_app. right. rewrite Erecs. left.
      reflexivity. }
  intros W2 ly2 S2 kk regs2 m2 md2 HJ2 HAP KB KI KE KF HROM2 HPK2 HFR2 HL2 HBS HMO.
  (* ---- back at 0x83918 ---- *)
  rewrite Erecs in HBS. cbn [nth fst snd] in HBS. destruct HBS as (b1 & b2 & EB1 & EB2).
  assert (KB' : forall p q i, In (p, q) (ablocks B ly1 S1) -> p <> v -> p <> fst r0 -> 0 <= i < req_size q ->
    abyte_kept W1 mc W2 m2 (p + i)).
  { intros p q i Hpq Hpv Hpr Hi. apply (KB p q i Hpq); [|exact Hi].
    intros i' Hi' (r & Hr & Hra). cbn [ddw_FP In] in Hr. rewrite Erecs in Hr. cbn [nth] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra.
    - apply (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 p q v (AREC * vcap) (p + i') HAR Hpq Hvin Hpv); lia.
    - apply (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 p q (fst r0) _ (p + i') HAR Hpq Hr0in Hpr); lia. }
  assert (GT2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)).
  { pose proof GT as GT0. rewrite EB2. rewrite EB1 in GT0. apply in_app_or in GT0 as [X | [X | X]]; apply in_or_app;
      [left; exact X | exfalso; injection X as X _; exact (Hr0G X) | right; exact X]. }
  rewrite T1.
  jafter_call_keep_pi HS 39%nat regs2 (mrestrict (w_H W2) m2) HAP [0; 1; 4]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B2; intros y Hy.
      + apply (mbyte_of_aview SEGS). apply (proj1 (KF y ltac:(clear - Hy HDF; lia))).
      + exfalso. clear - Hy. lia.
    - assert (KG : forall y, dHA RG cx + 32 <= y < dHA RG cx + 40 -> abyte_kept W1 mc W2 m2 y).
      { intros y Hy. destruct (df_pu_gs B RG HRGD y ltac:(unfold ASRC in *; lia)) as (HgG & Hne).
        destruct (HG y HgG) as (Hi & Ho & _). apply (KI y Hi Ho Hne). clear - Hy. lia. }
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B23; intros y Hy.
      + apply (mbyte_of_aview SEGS). exact (proj1 (KG y Hy)).
      + intros Hw. exact (proj2 (KG y ltac:(clear - Hy; lia)) Hw).
    - assert (KT : forall y, dxSA cx + 16 <= y < dxSA cx + 32 -> abyte_kept W1 mc W2 m2 y).
      { intros y Hy. replace y with (dxG cx + (y - dxG cx)) by lia.
        apply (KB' (dxG cx) ATABLE (y - dxG cx) GT (not_eq_sym HvG) (not_eq_sym Hr0G)).
        change (req_size ATABLE) with 896. lia. }
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B32; intros y Hy.
      + apply (mbyte_of_aview SEGS). exact (proj1 (KT y Hy)).
      + intros Hw. exact (proj2 (KT y ltac:(clear - Hy; lia)) Hw). }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex 39 ?lc) _ _ =>
    assert (OLDc : forall n, (n < 39)%nat -> ew (havoc Ex 39 lc) n = ew Ex n)
      by (intros n Hn; apply YN3v.ew_havoc_old; exact Hn);
    assert (HEIc : img_env VAL A_LIM (havoc Ex 39 lc)) by (apply img_env_havoc; [assumption | cbv; lia]);
    remember (havoc Ex 39 lc) as Ec eqn:HEc in HS, OLDc, HEIc
  end.
  clear HEc.
  assert (EREGc : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ec nn = getr regs1 r)
    by (intros nn r Hnn Hr; rewrite OLDc by lia; exact (EREG nn r Hnn Hr)).
  assert (B2c : bv_unsigned (ew Ec 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDc by lia; exact B2).
  assert (B23c : bv_unsigned (ew Ec 23) = dHA RG cx) by (rewrite OLDc by lia; exact B23).
  assert (B32c : bv_unsigned (ew Ec 32) = dxSA cx) by (rewrite OLDc by lia; exact B32).
  assert (E32c : ew Ec 32 = Z_to_bv 64 (dxSA cx)) by (rewrite OLDc by lia; exact E32).
  assert (E33c : ew Ec 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDc by lia; exact E33).
  assert (E15c : ew Ec 15 = Z_to_bv 64 (dnum s1)) by (rewrite OLDc by lia; exact E15).
  assert (E37c : ew Ec 37 = Z_to_bv 64 (re_buf e1)) by (rewrite OLDc by lia; exact E37).
  assert (E38c : ew Ec 38 = Z_to_bv 64 (re_used e1)) by (rewrite OLDc by lia; exact E38).
  assert (E23c : ew Ec 23 = Z_to_bv 64 (dHA RG cx)).
  { rewrite OLDc by lia. rewrite (EREG 23%nat 23%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]).
    exact R23. }
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (SHOK2 : sh_ok SEGS dj_Bx [mkSHE 23 0 96; mkSHE 32 0 56] Ec (mrestrict (w_H W2) m2)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (shent_ok_of_range SEGS (w_H W2) m2 Ec dj_Bx 23 (dHA RG cx) 96 (dHA RG cx) 0 96
        (azs_range_addressable B LAWS ly2 S2 W2 m2 md2 (dHA RG cx) 96 HAR2
          (df_azs_sub B RG HGSB (rg_s RG) (4 * ASRC) (dHA RG cx) 96 HGSZ ltac:(lia) ltac:(unfold ASRC in *; lia)))).
      + unfold dj_Bx. apply (U_atom Ec 33 SHADOW_OFF E33c). unfold SHADOW_OFF; lia.
      + apply (U_atom Ec 23 (dHA RG cx) E23c). lia.
      + lia.
      + lia.
      + intros y Hy. change (Z.min 0 96) with 0 in Hy. change (Z.max 0 96) with 96 in Hy.
        unfold SHADOW_OFF. clear - Hy HAr. lia.
    - apply (shent_ok_of_range SEGS (w_H W2) m2 Ec dj_Bx 32 (dxSA cx) 56 (dxSA cx) 0 56
        (range_addressable_of_block SEGS B LAWS ly2 S2 W2 m2 md2 (dxG cx) ATABLE (dxSA cx) 56 HAR2 GT2
          HSAlo ltac:(change (req_size ATABLE) with 896; lia))).
      + unfold dj_Bx. apply (U_atom Ec 33 SHADOW_OFF E33c). unfold SHADOW_OFF; lia.
      + apply (U_atom Ec 32 (dxSA cx) E32c). lia.
      + lia.
      + lia.
      + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPS. lia. }
  assert (FPE2 : forall y, dxSA cx <= y < dxSA cx + 56 ->
    inFP (dFP cx) y /\ exists b nb, In (b, nb) (ablocks B ly2 S2) /\ b <= y < b + req_size nb).
  { intros y Hy. split; [exact (proj1 (FPE y Hy))|].
    exists (dxG cx), ATABLE. split; [exact GT2 | change (req_size ATABLE) with 896; lia]. }
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dj_Bspan A_dr_join.
  { ddw_awr B2c B23c B32c GSW FPE2. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  assert (KL3 : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W2) (ms_mem msF) y = aview SEGS (w_H W2) m2 y).
  { intros y Hy Hy1 Hy2.
    apply (aview_eq_of SEGS); apply FR3; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2c, ?B23c, ?B32c in Hr;
         clear - Hr Hy1 Hy2; lia |]); destruct Hin. }
  assert (KP3 : forall y, apresent (w_H W2) m2 y -> apresent (w_H W2) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 Hy)).
  assert (KK3 : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> abyte_kept W2 m2 W2 (ms_mem msF) y).
  { intros y Hy Hy1 Hy2. split; [exact (KL3 y Hy Hy1 Hy2)|].
    unfold arm. exact (writable_kept (w_H W2) m2 (ms_mem msF) y (KP3 y)). }
  assert (Hrom3 : rom_view SEGS W2 (ms_mem msF)).
  { intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
    rewrite KL3; [exact (HROM2 y Hy) | clear - Hyi; lia | intros Hg; exact (HGR y (GSW y ltac:(lia)) Hy)
      | clear - HoffG HSAlo HSAhi Hyi; lia]. }
  (* the list after list_drop, kept by the last run *)
  assert (HLB : forall b, In b (alist_blks (ldrop_list (hs_pending h1) 0%nat)) -> In b (alist_blks (hs_pending h1))).
  { intros bb Hbb. unfold alist_blks, ldrop_list in Hbb |- *. cbn [hl_cap hl_v hl_recs] in Hbb |- *.
    rewrite Erecs in Hbb |- *.
    cbn [firstn skipn app map] in Hbb |- *. apply in_app_or in Hbb as [X | X]; apply in_or_app; [left; exact X|].
    right. right. exact X. }
  assert (AL3 : alist_at B ly2 S2 W2 (ms_mem msF) (dHA RG cx + 16) (ldrop_list (hs_pending h1) 0%nat) false).
  { apply (alist_at_kept B ly2 S2 W2 m2 ly2 S2 W2 (ms_mem msF) _ _ _ HL2).
    - apply (df_pu_alist_kept B RG ly2 S2 W2 W2 m2 (ms_mem msF) _ _ _ HL2).
      + intros x Hx. apply KK3; [lia | lia |]. intros Hs.
        apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
        exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
      + intros p q x Hpq Hx. destruct (HPB p q x (HLB _ Hpq) Hx) as (X1 & X2 & X3). exact (KK3 x X1 X2 X3).
    - intros bb Hbb. exact (ddw_alist_blks_in ly2 S2 W2 m2 _ _ _ HL2 bb Hbb). }
  (* the two stores: h->pending_off = 0, s->used = used + n *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG4
  end.
  cbn [ms_mem restrict] in RG1, RG4.
  assert (Voff : val_mem SEGS (arm W2 (ms_mem msF)) (dHA RG cx + 32) 8 0).
  { first [ unfold arm; eapply (field_of_region _ _ 23%nat (dHA RG cx) _ _ _ _ _ 32 8%N _ 0 RG1 B23c);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | reflexivity
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  assert (Vu : val_mem SEGS (arm W2 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + dnum s1)).
  { first [ unfold arm; eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 24 8%N _ (re_used e1 + dnum s1) RG4 B32c);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | first [ rewrite (ddw_den_add _ 38 15 (re_used e1) (dnum s1) E38c E15c ltac:(lia) ltac:(lia))
                    | rewrite (ddw_den_add _ 15 38 (dnum s1) (re_used e1) E15c E38c ltac:(lia) ltac:(lia)) ]; f_equal; lia
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  (* every byte DMEM reads off DROP's writes is kept: the first two runs, the call, the last run *)
  set (XB := fun y => exists p q, In (p, q) (alist_blks (hs_pending h1)) /\ p <= y < p + req_size q).
  assert (KX : forall y, 0 <= y < 2 ^ 64 -> ~ ddX RG cx (dsp0 cx - DRAIN_FRAME - LDROP_STK) XB y ->
    (exists p q, In (p, q) (ablocks B ly1 S1) /\ p <= y < p + req_size q) \/
    (in_img SEGS y /\ ~ Exists (in_zr y) (as_owned_static B)) \/ (dsp0 cx - DRAIN_FRAME <= y < dsp0 cx) ->
    abyte_kept W1 m1 W2 (ms_mem msF) y).
  { intros y Hy Hx HK. unfold ddX in Hx.
    assert (Hy1 : ~ (dHA RG cx + 32 <= y < dHA RG cx + 40)) by (intros Hc'; apply Hx; left; clear - Hc'; lia).
    assert (Hy2 : ~ (dxSA cx + 24 <= y < dxSA cx + 32)) by (intros Hc'; apply Hx; right; left; exact Hc').
    apply (df_bk_trans _ _ _ _ _ _ y (KKC y Hy Hy1 Hy2)).
    apply (df_bk_trans W1 W2 W2 mc m2 (ms_mem msF) y); [|exact (KK3 y Hy Hy1 Hy2)].
    destruct HK as [(p & q & Hpq & Hyq) | [(Hi & Ho) | Hfr]].
    - assert (Hpv : p <> v).
      { intros E0. subst p. apply Hx. right. right. left. unfold XB. exists v, (AREC * vcap).
        split; [|rewrite (ddw_blk_uniq ly1 S1 W1 m1 md1 v (AREC * vcap) q HAR Hvin Hpq); exact Hyq].
        unfold alist_blks. fold v vcap. rewrite (proj2 (Z.eqb_neq vcap 0) ltac:(lia)). left. reflexivity. }
      assert (Hpr : p <> fst r0).
      { intros E0. subst p. apply Hx. right. right. left. unfold XB. exists (fst r0), (Z.of_nat (length (snd r0)) + 1).
        split; [|rewrite (ddw_blk_uniq ly1 S1 W1 m1 md1 (fst r0) _ q HAR Hr0in Hpq); exact Hyq].
        unfold alist_blks. apply in_or_app. right. rewrite Erecs. left. reflexivity. }
      replace y with (p + (y - p)) by lia. apply (KB' p q (y - p) Hpq Hpv Hpr). lia.
    - destruct (Z_le_gt_dec (as_errno B) y) as [He1|He1]; [destruct (Z_lt_ge_dec y (as_errno B + 4)) as [He2|He2]|].
      + exact (KE y (conj He1 He2)).
      + apply (KI y Hi Ho); [clear - He2; lia | intros Hc'; apply Hx; left; clear - Hc'; lia].
      + apply (KI y Hi Ho); [clear - He1; lia | intros Hc'; apply Hx; left; clear - Hc'; lia].
    - exact (KF y Hfr). }
  (* C3: list_drop frees the head record, |dhead s1| + 1 bytes (ddrop's one request) *)
  assert (Hbb : blocks_bytes S2 + (Z.of_nat (length (dhead s1)) + 1) <= blocks_bytes S1).
  { rewrite (proj1 Ehead). unfold bzs. rewrite length_map.
    rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), EB1, EB2, !bsum_app, bsum_cons. cbn [snd].
    clear. lia. }
  pose proof (dd_arm_close B MT MMAX RG LAWS HG HGO HRGD HGSB cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 ly2 S2 W2 (ms_mem msF) _ _ (dsp0 cx - DRAIN_FRAME - LDROP_STK) XB
    (ldrop_list (hs_pending h1) 0%nat) 0 [r0] (dnum s1) HB HM HJ2 Hrom3
    (fun y Hi Ho He Hp => KP3 y (HPK2 y Hi Ho He (KPC y Hp))) ltac:(rewrite HFR2; reflexivity)
    ltac:(clear - Hcl Hslo HDS HDF; unfold LDROP_STK, LDROP_FRAME, ASTACK in *; lia) (fun y Hy => Hy) KX AL3 eq_refl eq_refl
    ltac:(cbn [ldrop_list hl_recs]; rewrite Erecs; reflexivity)
    ltac:(rewrite EB1, EB2; cbn [map app]; apply Permutation_sym, Permutation_middle) Voff
    ltac:(cbn [ldrop_list hl_recs]; rewrite Erecs; cbn [firstn skipn app];
          destruct rs0 as [|r1 rs1]; [left; split; reflexivity|];
          right; exists r1, rs1; split; [reflexivity|];
          pose proof LF as LF1; rewrite Erecs in LF1; apply Forall_inv_tail, Forall_inv in LF1;
          destruct LF1 as (_ & _ & _ & L1); specialize (L1 eq_refl); lia)
    Vu ltac:(clear - Hn0; lia) ltac:(clear - Hjunkl Hdn; lia) ltac:(clear - Hcpos; lia)) as HM2.
  pose proof HM2 as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  apply (JOIN cx s1 D 0%nat W2 _ HB); [|exact Kll | exact Klr].
  eapply (dd_DJ B MT MMAX RG HGSB cx s1 D (ms_regs msF) ly2 S2 W2 (ms_mem msF) _ _ e1 h1 (ldrop_list (hs_pending h1) 0%nat)
    0 out1 ev1 LB1 (spent + mo_free MT) (jb + dnret (ddrop s1 a))%nat
    (drain_b_c.DA (drain_b_c.da_out a) (drain_b_c.da_buf a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)
       (skipn 1 (drain_b_c.da_pend a)) (drain_b_c.da_ev a) (drain_b_c.da_erecs a))
    (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a) tl2).
  + unfold dregs_line.
    split; [unfold spZ; rewrite X2, (EREGc 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]);
      exact Hsp|].
    split; [rewrite X3, (EREGc 3%nat 3%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R3|].
    split; [rewrite X4, (EREGc 4%nat 4%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R4|].
    split; [rewrite X21, E32c; reflexivity|].
    split; [rewrite X20, E32c, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32c, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, E32c, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X8, (EREGc 8%nat 8%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R8|].
    split; [rewrite X9, (EREGc 9%nat 9%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R9|].
    split; [rewrite X18, (EREGc 18%nat 18%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R18|].
    exact HFRF.
  + rewrite X26. reflexivity.
  + rewrite X24, E37c. reflexivity.
  + exact HDB.
  + exact HM2.
  + exact Hjunk.
  + exact HSAME.
  + exact Hcap.
  + exact HU.
  + exact Hsk.
  + exact HHk.
  + exact Hka.
  + exact Hei.
  + exact Hst.
  + exact Hen.
  + exact Hec.
  + exact HH.
  + exact HRS.
  + reflexivity.
  + reflexivity.
  + rewrite Hwh. cbn [ldrop_list hl_recs]. rewrite Erecs. cbn [firstn skipn app]. exact (eq_sym (proj2 Ehead)).
  + rewrite Hwh. reflexivity.
  + exact HLF.
  + exact (ddw_bud cx S1 S2 spent _ _ tl2 HBUD HMO Hbb).
Qed.


End c.

(* ---- THE GENERIC WALK (an internal work row, slice B): DROP over any allocator relation ARx with its laws, at the room texts
   (the room record RP, the entry's budget kr).  The Section's variables are W_drain_cx_x.v's Section c's, B PST ARx
   MT RP MMAX RG in that order; its hypotheses are the ones the walk reads, in the order and with the names of
   lib/A/W_drain_drop.v Section cx (a Theorem Labs lane's A drop over ARx), each W_drain_cx_x.v hypothesis at that file's text,
   the free rule in its caller-context form with B's one free site on this stretch, list_drop's (HCTX_ld, in A's
   HCTX_fr1 slot).  After LAWS come the generic-relation facts, at the texts shared across the slices:
     HP0 (no hidden head in any ARx state: list_drop's contract, the table's and the vector's shadow facts),
     BLKN / BLKM (a live block's size is in [0, 2^30): AR's al_blocks carries 0 <= n < MALLOC_MAX, ARx_blocks_law
     neither; the head text's length and pending_off fit the walk's atom facts, the vector's move fits memmove),
     PSTR / PSTG / PSTO (ROM, g_s and aout_at's cells lie off the placement PST: list_drop's journal keeps an image byte
     only off PST, YCbqG.ajournal_x's image clause).
   The AR walk (Section c) is unchanged.  Its Definitions and its AR-free lemmas are cited; each lemma that reads AR,
   DBASE, DMEM or ajournal_gx is restated here with an _x suffix, the block facts and the call kit over ARx it reads are
   lib/B/W_drain_feed.v Section cx's (df_pu_nd_x, df_pu_ne_in_x, df_lp_rq_out_x, df_blk_wr_x, df_keep_hi_x,
   df_keep_img_x, df_keep_blk_x, df_gx_call_x, df_gx_pres_x), cited, and lib/B/W_drain_dropk.v Section cx's lemmas are
   cited.  The join is a12's dr_memchr_join_x (lib/B/W_drain_join.v Section cx); list_drop's contract is
   lib/B/W_list_drop.v pb_list_drop_ro_x at G1 = [(&h->pending, 16)], its room and count premises from the cut's
   dbud_x and its post's rp_RM the next cut's room (lib/B/W_drain_room_x.v gs_rm_take / gs_cnt_call / gs_cnt_free: the
   trace's head request is list_drop's free). ---- *)
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
(* the generic-relation / placement facts the walk reads (the texts shared across the slices) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis BLKM : forall ly S Hp (W : world SEGS) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  n < 2 ^ 30.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ Exists (in_zr a) PST.
Hypothesis PSTO : forall a, inG (G_SL B RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
  ~ Exists (in_zr a) PST.
(* W_drain_cx_x.v Section c's hypotheses (its text), the allocator rule in its caller-context form *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Variable CTX_F : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
(* B's one allocator site on this stretch is list_drop's free (0x85be8 returns to 0x85bec) *)
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.

Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let JOIN := dr_memchr_join_x B PST ARx MT RP MMAX RG LAWS HP0 HG HGO AMEMCHR HCROM HRGD HGSB HMMAX HSD HSM.
(* The one callee fact of the walk: list_drop's contract at any G with gx_ok, gx_rt and rom_out (lib/B/W_list_drop.v
   pb_list_drop_ro_x, Qed, with the _c free rule AFREE and HCTX_ld).  Only ddw_ld_call_x uses it, at
   G1 = [(&h->pending, 16)]. *)
Let LDG : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop) :=
  pb_list_drop_ro_x B PST ARx LAWS HP0 MT RP TL CTX_F AFREE HCTX_ld AMEMMOVE.

(* a lemma of lib/B/W_drain_dropk.v Section cx at this Section's B PST ARx MT RP MMAX RG: its Section hypotheses (the
   leading non-dependent Prop premises) are this Section's, each taken by assumption *)
Local Ltac ddw_sec H := repeat lazymatch type of H with
  | ?P -> ?Q => lazymatch type of P with Prop => specialize (H ltac:(eassumption)) end
  end.

(* ------------------------------------------------------------------ block facts over ARx *)
(* one live block per address (ddw_blk_uniq over ARx) *)
Lemma ddw_blk_uniq_x : forall ly S Hpl (W : world SEGS) m md p q q', ARx ly S Hpl W m md ->
  In (p, q) (ablocks B ly S) -> In (p, q') (ablocks B ly S) -> q = q'.
Proof.
intros ly S Hpl W m md p q q' HAR H1 H2.
pose proof (df_pu_nd_x B ARx LAWS BLKN ly S Hpl W m md (ablocks B ly S) [] [] HAR
  ltac:(rewrite app_nil_r; reflexivity)) as ND.
destruct (in_split _ _ H1) as (l1 & l2 & El). rewrite El in ND, H2. rewrite map_app in ND. cbn [map fst] in ND.
apply List.NoDup_remove_2 in ND.
apply in_app_or in H2 as [H2 | [H2 | H2]].
- exfalso. apply ND. apply in_or_app. left. exact (in_map fst _ _ H2).
- apply (f_equal snd) in H2. exact H2.
- exfalso. apply ND. apply in_or_app. right. exact (in_map fst _ _ H2).
Qed.


(* a block of the source at the call: one of drain's entry blocks (in dFP) or a block new in the round *)

(* ------------------------------------------------------------------ the list_drop call at 0x83914 *)
(* the call itself, through LDG (pb_list_drop_ro_x) at G1 = [(&h->pending, 16)], composed into drain's journal; the
   continuation gets the call's effect on memory.  The room: the call's rp_RM at its charge plus the budget kr' left
   after it, its count premise at ldrop_pk; the continuation gets the post's rp_RM at kr'. *)

(* ---- the room and the counts across the call (lib/B/W_drain_room_x.v): the request trace's head is list_drop's free
   RFree (n + 1), its room charge MT_rk's 1 (gs_rm_take), its count step the freed head record (gs_cnt_free) ---- *)
(* the budget after list_drop (ddw_bud, Section c) with the room and the counts: the post's rp_RM is the rest's room,
   and the freed head record (one block of the free's size) pays for the free's count step *)
Lemma ddw_bud_x : forall cx kr ly1 S1 ly2 S2 spent (ad : dadrF) n (tl2 : dtrace) p b1 b2,
dbud_x B MT RP MMAX cx kr ly1 S1 spent (ListTr.list_drop_tra ad n ++ tl2) ->
mo_le MT S1 S2 (mo_free MT) -> blocks_bytes S2 + (n + 1) <= blocks_bytes S1 ->
ablocks B ly1 S1 = b1 ++ (p, n + 1) :: b2 -> ablocks B ly2 S2 = b1 ++ b2 ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tl2) + kr) ->
dbud_x B MT RP MMAX cx kr ly2 S2 (spent + mo_free MT) tl2.
Proof.
intros cx kr ly1 S1 ly2 S2 spent ad n tl2 p b1 b2 (Hb & _ & Hc) Hmle Hbb E1 E2 HRM2.
split; [exact (ddw_bud B MT MMAX RG MTL HGSB HMMAX cx S1 S2 spent ad n tl2 Hb Hmle Hbb)|].
split; [exact HRM2|].
rewrite E2. rewrite E1 in Hc. exact (gs_cnt_free RP (n + 1) ad tl2 b1 b2 p Hc).
Qed.

(* ---- DROP: DE 0x838a0 -> (list_drop when the head text is used up) -> DJ 0x8395c at p = 0 -> the join. ---- *)


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of each relation-dependent lemma above.  Each
   twin is its strict text with the journal and the step relation at R: ajournal_gx_x -> ajournal_gx_xR .. R,
   SRr SEGS -> SRrG SEGS R, the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG, W_kit.v paj_branch_xR), each carrier X_x -> its twin X_xR (R last), the journal lemmas their _xR
   forms, and each lemma name L -> LR; the relation-free helpers above are cited as they are.  The strict text is
   untouched. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_F R.
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* the join at R (lib/B/W_drain_join.v dr_memchr_join_xR) *)
Let JOINR := dr_memchr_join_xR B PST ARx MT RP MMAX RG LAWS HP0 HG HGO AMEMCHR HCROM HRGD HGSB HMMAX HSD HSM R R_trans WLE_R.
(* list_drop's contract at R (lib/B/W_list_drop.v pb_list_drop_ro_xR; the spec W_contract_xR_g3.v ldrop_spec_xR) *)
Let LDGR : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec_xR B PST ARx R MT RP G (BASE + AF_fr_list_drop).
Proof. intros G HG' GRT HRO'. eapply pb_list_drop_ro_xR with (R := R) (RO := RO); eassumption. Qed.

Lemma ddw_frames_of_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
frames S2 = frames Sc.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
Qed.

Lemma ddw_src_awr_xR : forall cx Hpe kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 b nb a,
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
DMEM_xR B PST ARx RG R cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
In (b, nb) (asrc_blks h1) -> b <= a < b + req_size nb ->
(inFP (dFP cx) a /\ exists b' nb', In (b', nb') (ablocks B ly1 S1) /\ b' <= a < b' + req_size nb') \/
in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a.
Proof.
intros cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 b nb a HB HM HinS Ha.
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPerm0 & _).
assert (Hinv : In (b, nb) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). right. apply in_or_app. right. apply in_or_app. left. exact HinS. }
destruct (in_dec df_pair_dec (b, nb) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnin0].
- left. split; [|exists b, nb; split; [exact Hinv | exact Ha]].
  pose proof (df_pu_ne_in_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 (dxG cx, ATABLE) _ _ HAR1 Hperm
    (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl HinS))))) as HNE.
  cbn [fst] in HNE.
  assert (ND : List.NoDup (map fst (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx))).
  { apply (df_pu_nd_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 _ ((dxG cx, ATABLE) :: aentry_blks e1) [] HAR1).
    rewrite app_nil_r. exact Hperm. }
  pose proof (df_nd_fst _ _ _ ND HinS) as NR.
  pose proof (Permutation_in _ HPerm0 Hin0) as Hin1.
  assert (HinF : In (b, nb) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
  { destruct Hin1 as [Eq|Hin1]; [injection Eq as E1 E2; exfalso; exact (HNE E1)|].
    apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; left; exact Q|].
    apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; right; apply in_or_app; left; exact Q|].
    apply in_app_or in Hin1 as [Q|Q]; [apply in_or_app; right; apply in_or_app; right; exact Q|].
    exfalso. apply NR. apply in_or_app. right. exact Q. }
  exists (b, b + req_size nb). split; [|cbn [fst snd]; lia].
  unfold dFP, dr_fp. right. unfold ablocks_fp.
  exact (in_map (fun b0 : Z * Z => (fst b0, fst b0 + req_size (snd b0))) _ _ HinF).
- right. exists b, nb. split; [exact Hinv|]. split; [exact Hnin0 | exact Ha].
Qed.

Lemma ddw_ld_call_xR : forall cx Hpe kr ly1 S1 Hp1 k1 (W : world SEGS) mc mdc regsc raw (l : hlist) (kr' : nat) Q,
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W mc mdc k1 ->
spZ regsc = dsp0 cx - DRAIN_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 (dHA RG cx + 16) -> getr regsc 11 = w64 (Z.of_nat 0) ->
alist_at B ly1 S1 W mc (dHA RG cx + 16) l false ->
(0 < length (hl_recs l))%nat ->
mo_ok MT S1 (mo_free MT) ->
rp_RM RP S1 (Z.to_nat (mo_free MT_rk) + kr') ->
cnt_ok_pk RP ldrop_pk (ablocks B ly1 S1) ->
rom_view SEGS W mc ->
(forall a, inFP (ddw_FP l) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) ->
(forall W2 ly2 S2 Hp2 kk regs2 m2 md2,
  ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx)
    (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 kk ->
  aregs_preserved regsc regs2 ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> (forall i', 0 <= i' < req_size n -> ~ inFP (ddw_FP l) (p + i')) ->
     0 <= i < req_size n -> abyte_kept W mc W2 m2 (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ (dHA RG cx + 16 <= a < dHA RG cx + 32) -> abyte_kept W mc W2 m2 a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mc W2 m2 a) ->
  (forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W mc W2 m2 a) ->
  rom_view SEGS W2 m2 -> apres_kept B W mc W2 m2 -> frames S2 = frames S1 ->
  alist_at B ly2 S2 W2 m2 (dHA RG cx + 16) (ldrop_list l 0%nat) false ->
  (exists b1 b2, ablocks B ly1 S1 = b1 ++ (fst (nth 0 (hl_recs l) (0, [])),
     Z.of_nat (length (snd (nth 0 (hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) ->
  mo_le MT S1 S2 (mo_free MT) -> rp_RM RP S2 kr' ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 raw m2 (seg_rom SEGS)) md2) Q) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_list_drop)) mc (seg_rom SEGS)) mdc) Q.
Proof.
intros cx Hpe kr ly1 S1 Hp1 k1 W mc mdc regsc raw l kr' Q HB HJ Hsp Hgp Htp Hra Hraw Hra4 Hs0 H10 H11 HL Hi Hmo HRM
  HCNT Hrom HFP HK.
pose proof HB as ((_ & _ & _ & _ & _ & Hstk0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _ & _ & _ & _ & _ & _ & Hrv0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HspR : alloc_ceiling + DRAIN_STK_x <= dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
clear Hstk0 Hceil Hslo Hshi H47.
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; clear - Hj; lia).
pose proof HGSB as (HGlo & HGhi & HGal). unfold IMG_TOP in HGhi.
assert (Hsub : forall a, inG [(dHA RG cx + 16, 16)] a -> inG (G_DR B RG) a).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  exact (proj1 (df_pu_gs B RG HRGD a ltac:(clear - Ha HAr; unfold ASRC in *; lia))). }
assert (HG1 : gx_ok SEGS B [(dHA RG cx + 16, 16)]) by exact (gx_ok_sub SEGS B _ _ Hsub HG).
assert (HR1 : gx_rt B [(dHA RG cx + 16, 16)]).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  pose proof (df_pu_zpw B RG _ 0%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D0.
  pose proof (df_pu_zpw B RG _ 1%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D1.
  pose proof (df_pu_zpw B RG _ 2%nat 11%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D2.
  cbn [nth] in D0, D1, D2. unfold zdisj in D0, D1, D2. cbn [fst snd] in D0, D1, D2.
  clear - D0 D1 D2 Ha HAr. unfold ASRC in *. repeat split; lia. }
assert (HRO1 : rom_out SEGS B [(dHA RG cx + 16, 16)]).
{ intros a Ha. destruct (HROMO a Ha) as (R1 & R2 & R3 & R4).
  split; [intros Hc; exact (R1 (Hsub a Hc)) | split; [exact R2 | split; [exact R3 | exact R4]]]. }
assert (HZ1 : azs B (dHA RG cx + 16) 16).
{ apply (df_azs_sub B RG HGSB (rg_s RG) (4 * ASRC));
  [exact HGSZ | clear - HAr; unfold ASRC in *; lia | clear - HAr; unfold ASRC in *; lia]. }
assert (HARc : ARx ly1 S1 Hp1 W mc mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (C16 : (- DRAIN_FRAME) mod 16 = 0) by reflexivity.
assert (Cneg : - DRAIN_FRAME <= 0) by (apply Z.leb_le; reflexivity).
assert (CLD : 0 <= LDROP_STK) by (apply Z.leb_le; reflexivity).
assert (CBUD : LDROP_STK - - DRAIN_FRAME <= DRAIN_STK_x) by (apply Z.leb_le; reflexivity).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HLD : LDROP_STK = 16448) by reflexivity.
assert (HLA8 : (dHA RG cx + 16) mod 8 = 0).
{ unfold dHA, ASRC. replace (rg_s RG + 96 * Z.of_nat (dxj cx) + 16) with (rg_s RG + (12 * Z.of_nat (dxj cx) + 2) * 8)
    by lia.
  rewrite Z.mod_add by lia. exact HGal. }
pose proof HL as (_ & _ & _ & _ & HLnc & HLvb & _).
assert (Hmv : AREC * (hl_n l - 1 - Z.of_nat 0) < 2 ^ 32).
{ destruct HLvb as [(Hc0 & _) | (Hcp & Hin & _)].
  - exfalso. clear - HLnc Hc0 Hi. unfold hl_n in *. lia.
  - pose proof (BLKM ly1 S1 Hp1 W mc mdc _ _ HARc Hin) as Hn.
    clear - Hn HLnc Hcp. unfold AREC, hl_n in *. lia. }
assert (HLAg : forall a, dHA RG cx + 16 <= a < dHA RG cx + 16 + 16 ->
  inG [(dHA RG cx + 16, 16)] a /\ ~ (spZ regsc - LDROP_STK <= a < spZ regsc)).
{ intros a Ha. split; [exact (proj2 (df_G1_in _ a) Ha)|]. rewrite Hsp.
  clear - Ha HAr HGhi HspR C1 ACL HDS HDF HLD. unfold ASRC in *. lia. }
assert (HVg : forall a, hl_v l <= a < hl_v l + AREC * hl_cap l -> ~ (spZ regsc - LDROP_STK <= a < spZ regsc)).
{ intros a Ha. rewrite Hsp. destruct HLvb as [(Hc0 & Hv0) | (Hcp & Hin & _)].
  - exfalso. rewrite Hc0 in Ha. clear - Ha. unfold AREC in Ha. lia.
  - destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W mc mdc _ _ HARc Hin) as (_ & _ & Hc & _).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(clear - Hcp; unfold AREC; lia)) as (_ & Hrq).
    clear - Ha Hc Hrq HspR HDS HDF HLD C1 ACL. lia. }
assert (HFPp : ~ YI16.sink_open_fp (ddw_FP l)).
{ apply sink_closed_pos. unfold ddw_FP.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & HLF).
  destruct (hl_recs l) as [|r0 rs0] eqn:Er; [cbn in Hi; lia|].
  apply Forall_inv in HLF. destruct HLF as (Hr0in & _).
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W mc mdc _ _ HARc Hr0in) as (_ & Hr04096 & _).
  destruct HLvb as [(Hc0 & Hv0) | (Hcp & Hin & _)].
  - exfalso. clear - HLnc Hc0 Hi Er. unfold hl_n in *. rewrite Er in HLnc. cbn [length] in HLnc. lia.
  - destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W mc mdc _ _ HARc Hin) as (_ & Hv4096 & _).
    constructor; [cbn [fst]; clear - Hv4096; lia | constructor; [cbn [fst nth]; clear - Hr04096; lia | constructor]]. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (df_gx_call_xR B PST ARx RG LAWS HG R_trans [(dHA RG cx + 16, 16)] W regsc mc (BASE + AF_fr_list_drop) DRAIN_STK_x
    (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) ly1 S1 Hp1 mdc k1 LDROP_STK (ddw_FP l)
    (- DRAIN_FRAME) raw []
    (fun ly2 S2 Hp2 W2 regs2 mem2 md2 kk =>
       alist_at B ly2 S2 W2 mem2 (dHA RG cx + 16) (ldrop_list l 0%nat) false /\
       (exists b1 b2, ablocks B ly1 S1 = b1 ++ (fst (nth 0 (hl_recs l) (0, [])),
          Z.of_nat (length (snd (nth 0 (hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
       apres_kept B W mc W2 mem2 /\
       (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) mc (as_errno B + i)) /\
       mo_le MT S1 S2 (mo_free MT) /\ rp_RM RP S2 kr')
    Hsub HJ Hsp C16 Cneg CLD CBUD Hgp Htp Hra Hraw Hra4 (achain_low _ _ _ _ Hs0)).
  - intros HPRE1. eapply SRrG_mono.
    { exact (LDGR [(dHA RG cx + 16, 16)] HG1 HR1 HRO1 W ly1 S1 Hp1 regsc mc mdc []
        (dHA RG cx + 16) l false 0%nat HPRE1 H10 H11 HL Hi HLA8 ltac:(clear - HAr HGlo; lia) Hmv HZ1 HLAg HVg Hmo
        kr' HRM HCNT Hrom). }
    cbv beta. unfold ldrop_post_xR.
    intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPK & Herr & HAL & HBS & HMLE & HRM2).
    exists ly2, S2, Hp2, regs2, mem2, md2, 1.
    split; [rewrite Hra; reflexivity|]. split; [rewrite Hsp in HJ2; exact HJ2|]. split; [exact HP2|].
    split; [exact HAL|]. split; [exact HBS|]. split; [exact HPK|]. split; [exact Herr|].
    split; [exact HMLE | exact HRM2].
  - exact HFP. }
cbv beta.
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJa & HJb & HP & (HAL & HBS & HPK & Herr & HMLE & HRM2)).
assert (HAR2 : ARx ly2 S2 Hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJb).
apply (HK W2 ly2 S2 Hp2 (k1 + kk) regs2 mem2 md2).
- exact HJa.
- exact HP.
- (* a live block off the call's footprint: the callee's block clause keeps it, and it is alive *)
  intros p n i Hin Hno Hi'.
  destruct (df_keep_blk_xR B PST ARx RG LAWS BLKN HG R [(dHA RG cx + 16, 16)] LDROP_STK (dsp0 cx + - DRAIN_FRAME)
    (ddw_FP l) ly1 S1 Hp1 W mc mdc ly2 S2 Hp2 W2 mem2 md2 kk p n Hsub HARc HJb Hin Hno) as [Hin2 Hv].
  split; [exact (Hv i Hi') | intros _; exact (df_blk_wr_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p n HAR2 Hin2 i Hi')].
- (* an image byte off h->pending and off PST: the callee's image clause, its presence by apres_kept *)
  intros a Hia Ho He Hq Hn. split.
  + apply (df_keep_img_xR B PST ARx R [(dHA RG cx + 16, 16)] LDROP_STK (dsp0 cx + - DRAIN_FRAME) (ddw_FP l) ly1 S1 Hp1 W
      mc mdc ly2 S2 Hp2 W2 mem2 md2 kk).
    * exact HFPp.
    * exact HJb.
    * exact Hia.
    * exact Ho.
    * exact He.
    * exact Hq.
    * intros Hc. apply Hn. apply (proj1 (df_G1_in _ a)) in Hc. clear - Hc. lia.
  + exact (df_wr_img W W2 mc mem2 a Hia (HPK a Hia Ho He)).
- (* errno: ldrop_post_xR's view, and a writable segment's byte *)
  intros a Ha.
  assert (Hv : aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mc a).
  { replace a with (as_errno B + (a - as_errno B)) by ring. apply Herr. clear - Ha. lia. }
  assert (HeG : inG (G_DR B RG) a).
  { unfold G_DR, G_SL, inG. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha. lia. }
  split; [exact Hv|]. intros Hw.
  apply (df_err_wr W W2 mc mem2 a (proj1 (HG a HeG))); [|exact Hv|exact Hw].
  intros Hr. exact (proj1 (proj2 (proj2 (HROMO a Hr))) Ha).
- (* drain's frame: above the callee's window, kept by its stack clause; present by drain's journal *)
  intros a Ha. split.
  + apply (df_keep_hi_xR B PST ARx RG HG R [(dHA RG cx + 16, 16)] LDROP_STK (dsp0 cx + - DRAIN_FRAME) (ddw_FP l) ly1 S1
      Hp1 W mc mdc ly2 S2 Hp2 W2 mem2 md2 kk Hsub HJb a).
    * clear - HspR Ha HDS HDF C1. lia.
    * clear - Ha HLD. lia.
  + intros _. apply (apresent_writable SEGS).
    apply (df_gx_pres_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa).
    clear - Ha HDS HDF. lia.
- exact (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa HROMO PSTR
    Hrv0).
- exact HPK.
- exact (ddw_frames_of_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb).
- exact HAL.
- exact HBS.
- exact HMLE.
- exact HRM2.
Qed.

Theorem dr_drop_xR : dr_drop_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_drop_stmt_xR. intros cx Hpe kr s1 D W1 c1 HB HDE Kll Klr.
epose proof (dd_arm_close_xR B PST ARx MT RP MMAX RG) as DAC. ddw_sec DAC. specialize (DAC R). ddw_sec DAC.
epose proof (dd_DJ_xR B PST ARx MT RP MMAX RG) as DDJ. ddw_sec DDJ. specialize (DDJ R). ddw_sec DDJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
destruct HDE as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  Hc1 & Hsp & R3 & R4 & R8 & R9 & R18 & R23 & R15 & HFR & F96 & F112 & F168 & F192 & Hn0 & Hjunk & HM & HnzU &
  Hused & HDB & HSAME & Hcap & HU & Hsk & HHk & Hka & Hei & Hpend & Hoff & Hst & Hen & Hec & HH & HRS & HFUT & HBUDx).
subst c1.
pose proof HBUDx as (HBUD & HRMd & HCNT).
pose proof HM as (HJ & Hrom & Hpres & Hframes & HFRm & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & _ & HGB & HSAlo & HSAhi & HSA8 & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HDSx : DRAIN_STK_x = 17008) by reflexivity.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (HG16 & HG4 & HGc & HGapp & _).
change (req_size ATABLE) with 896 in HGc, HGapp.
pose proof HRS as (Href & HJ1 & H4096 & Hdwf & Hstrict & Hei1 & Hpne).
pose proof HJ1 as (_ & _ & _ & HNZ).
pose proof HEOK as (Heof & Hskp & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & _).
assert (HULEN : ulen s1 = re_used e1) by (unfold ulen; rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcap16 : re_cap e1 <= 16384) by (destruct Hcapr as [X|[X|X]]; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & HBin & Hjunkl & Hbgarr)]; [exfalso; lia|].
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
(* the source: h->pending's head record r0, its vector v *)
pose proof Hsrc as (A1 & A2 & A3 & A4 & AW & A6 & A7 & A8 & A9 & AL & AOFF & A40 & A48 & A56 & AOR & A16 & A17 &
  A18 & A19 & A20 & A21 & A22 & A23 & A24).
pose proof AL as (LV & LN & LC & LW & LNC & LBLK & LND & LNI & LF).
assert (Erecs : exists r0 rs0, hl_recs (hs_pending h1) = r0 :: rs0).
{ destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:E; [|exists r0, rs0; reflexivity].
  exfalso. try rewrite E in Hpend. cbn [map] in Hpend. exact (Hpne (eq_sym Hpend)). }
destruct Erecs as (r0 & rs0 & Erecs).
assert (Ehead : dhead s1 = bzs (snd r0) /\ dtail s1 = map (fun r => bzs (snd r)) rs0).
{ unfold dhead, dtail. rewrite <- Hpend, Erecs. cbn [map]. split; reflexivity. }
assert (Hn1 : 1 <= hl_n (hs_pending h1)) by (unfold hl_n; rewrite Erecs; cbn [length]; lia).
destruct LBLK as [(Hcv0 & _) | (Hcvp & Hvin & Hvjl & Hvg)]; [lia|].
set (v := hl_v (hs_pending h1)) in *.
set (vcap := hl_cap (hs_pending h1)) in *.
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 v (AREC * vcap) HAR Hvin) as (Hv16 & Hv4096 & Hvc & Hvapp & _).
pose proof (conj (BLKN ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hvin) (BLKM ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hvin)) as Hvn.
pose proof (req_size_pos (AREC * vcap) ltac:(unfold AREC; lia)) as (_ & Hvrq).
pose proof LF as LF0. rewrite Erecs in LF0. apply Forall_inv in LF0. destruct LF0 as (Hr0in & Hr0g & _ & Hr0l).
specialize (Hr0l eq_refl).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hr0in) as (_ & Hr04096 & Hr0c & _).
pose proof (conj (BLKN ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hr0in) (BLKM ly1 S1 Hp1 W1 m1 md1 _ _ HAR Hr0in)) as Hr0n.
assert (Hv0n : val_mem SEGS (arm W1 m1) (v + 8) 8 (Z.of_nat (length (snd r0)))).
{ rewrite Erecs in Hvg. cbn [map concat] in Hvg. rewrite <- app_assoc in Hvg. exact (ddw_v0n _ v r0 _ Hvg ltac:(lia)). }
destruct AOR as [(Hnil & _) | (r0' & rs0' & Er0 & Hoffr)]; [rewrite Erecs in Hnil; discriminate|].
rewrite Erecs in Er0. injection Er0 as <- <-.
assert (Hdn : dnum s1 = Z.min (Z.of_nat (length (snd r0)) - hs_off h1) (re_cap e1 - re_used e1)).
{ unfold dnum. rewrite (proj1 Ehead), Hoff, Hcap, HULEN. unfold bzs. rewrite length_map. reflexivity. }
(* the source slot HA = &g_s[j] *)
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
pose proof HGSB as (HGlo & HGhi & HGal). unfold IMG_TOP in HGhi.
assert (HAr : 0x10000 <= dHA RG cx /\ dHA RG cx + 96 <= 0x5fc000 /\ rg_s RG <= dHA RG cx /\
  dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; lia).
assert (HA8 : dHA RG cx mod 8 = 0).
{ rewrite HAe. unfold ASRC. replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with (rg_s RG + (12 * Z.of_nat (dxj cx)) * 8) by lia.
  rewrite Z.mod_add by lia. exact HGal. }
assert (GSI : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B)).
{ intros x Hx. destruct (HG x (proj1 (df_pu_gs B RG HRGD x Hx))) as (Gi & Gn & _). exact (conj Gi Gn). }
(* the regions are apart *)
assert (HvG : v <> dxG cx).
{ intros E. apply (df_pu_ne_in_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 (dxG cx, ATABLE) (v, AREC * vcap) _ HAR Hperm);
    [| cbn [fst]; exact (eq_sym E)].
  apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left.
  unfold alist_blks. fold v vcap. rewrite (proj2 (Z.eqb_neq vcap 0) ltac:(lia)). left. reflexivity. }
assert (D1 : v + 16 <= dHA RG cx + 16 \/ dHA RG cx + 40 <= v + 8).
{ assert (X : forall x, v + 8 <= x < v + 8 + 8 -> dHA RG cx + 16 <= x < dHA RG cx + 16 + 24 -> False).
  { intros x Hx1 Hx2. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR Hvin); [unfold AREC in *; lia|].
    exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))). }
  destruct (ddw_apart (v + 8) 8 (dHA RG cx + 16) 24 ltac:(lia) ltac:(lia) X); [left | right]; lia. }
assert (D2 : dxSA cx + 32 <= dHA RG cx + 16 \/ dHA RG cx + 40 <= dxSA cx + 16).
{ assert (X : forall x, dxSA cx + 16 <= x < dxSA cx + 16 + 16 -> dHA RG cx + 16 <= x < dHA RG cx + 16 + 24 -> False).
  { intros x Hx1 Hx2. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR GT);
      [change (req_size ATABLE) with 896; lia|].
    exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))). }
  destruct (ddw_apart (dxSA cx + 16) 16 (dHA RG cx + 16) 24 ltac:(lia) ltac:(lia) X); [left | right]; lia. }
assert (D3 : v + 16 <= dxSA cx + 16 \/ dxSA cx + 32 <= v + 8).
{ assert (X : forall x, v + 8 <= x < v + 8 + 8 -> dxSA cx + 16 <= x < dxSA cx + 16 + 16 -> False).
  { intros x Hx1 Hx2.
    apply (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 v (AREC * vcap) (dxG cx) ATABLE x HAR Hvin GT HvG);
      [unfold AREC in *; lia | change (req_size ATABLE) with 896; lia]. }
  destruct (ddw_apart (v + 8) 8 (dxSA cx + 16) 16 ltac:(lia) ltac:(lia) X); [left | right]; lia. }
(* the frame slots *)
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 & F176 &
  F184 & F200 & F208 & F216 & F224 & F232 & F240 & FS).
assert (Hsp0 : 2 ^ 46 <= dsp0 cx - DRAIN_FRAME /\ alloc_ceiling <= dsp0 cx - DRAIN_FRAME /\
  dsp0 cx - DRAIN_FRAME + 352 <= 2 ^ 47 /\ (dsp0 cx - DRAIN_FRAME) mod 16 = 0).
{ rewrite HDF. split; [lia|]. split; [lia|]. split; [lia|]. rewrite Zminus_mod, Hal16. reflexivity. }
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR GT
  HSAlo ltac:(change (req_size ATABLE) with 896; lia)) as RAS.
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 v (AREC * vcap) v 16 HAR Hvin
  ltac:(lia) ltac:(unfold AREC in *; lia)) as RAV.
pose proof (azs_range_addressable_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) 96 HAR
  (df_azs_sub B RG HGSB (rg_s RG) (4 * ASRC) (dHA RG cx) 96 HGSZ ltac:(lia) ltac:(unfold ASRC in *; lia))) as RAH.
assert (Hv16b : 16 <= req_size (AREC * vcap) /\ v + 16 <= alloc_ceiling)
  by (clear - Hvc Hvrq Hcvp; unfold AREC in *; lia).
assert (HAPS : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. clear - Hy HSAlo HSAhi HGapp C1 C2 C3 C4 C5.
  unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (HAPV : forall y, v <= y < v + 16 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. clear - Hy Hvapp Hv16b C1 C2 C3 C4 C5.
  unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
pose proof (dnk_entry_buf (arm W1 m1) (dxSA cx) e1 Hgarr Hpad1 ltac:(lia)) as V16.
pose proof (dnk_entry_used (arm W1 m1) (dxSA cx) e1 Hgarr Hpad1 ltac:(lia)) as V24.
destruct (ddw_seat W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dHA RG cx) (dnum s1) (dxSA cx) v (hs_off h1)
  (Z.of_nat (length (snd r0))) (re_buf e1) (re_used e1) Hsp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R23 R15
  F96 F112 F128 F136 F144 F168 F176 F192 F224 F232 F240 AOFF LV Hv0n V16 V24 AW Hawr
  ltac:(lia) ltac:(unfold IMG_TOP; lia) HA8 ltac:(lia) ltac:(lia) ltac:(lia) HSA8 ltac:(lia) (proj2 Hv16b)
  ltac:(rewrite Zmod_divides in Hv16 |- * by lia; destruct Hv16 as (c & Hc); exists (2 * c); lia)
  ltac:(lia) ltac:(lia) ltac:(lia) Hdb3 ltac:(lia) D1 D2 D3 RAH RAV RAS HAPV HAPS) as [HS SHOK].
remember (Eimg (Ereg regs1 (ddw_extra (dxSA cx) v (hs_off h1) (Z.of_nat (length (snd r0))) (re_buf e1) (re_used e1))))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (EX : forall i, (i < 7)%nat -> ew E (32 + i) =
  nth i (ddw_extra (dxSA cx) v (hs_off h1) (Z.of_nat (length (snd r0))) (re_buf e1) (re_used e1)) (Z_to_bv 64 0)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  do 7 (destruct i as [|i]; [exact (ew_Ereg_extra regs1 _ _)|]). lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 v) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (hs_off h1)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (Z.of_nat (length (snd r0)))) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_buf e1)) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 (re_used e1)) by exact (EX 6%nat ltac:(lia)).
clear HE EX.
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact Hsp).
assert (B23 : bv_unsigned (ew E 23) = dHA RG cx)
  by (rewrite (EREG 23%nat 23%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); rewrite R23;
      apply unsigned_lit_small; lia).
assert (B32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (B34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (FPE : forall y, dxSA cx <= y < dxSA cx + 56 ->
  inFP (dFP cx) y /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= y < b + req_size nb).
{ intros y Hy. split.
  - exists (dxSA cx, dxSA cx + AENT). split; [unfold dFP, dr_fp; left; reflexivity | cbn [fst snd]; unfold AENT; lia].
  - exists (dxG cx), ATABLE. split; [exact GT | change (req_size ATABLE) with 896; lia]. }
assert (GSW : forall y, dHA RG cx + 16 <= y < dHA RG cx + 40 -> inG (G_DR B RG) y)
  by (intros y Hy; exact (proj1 (df_pu_gs B RG HRGD y ltac:(unfold ASRC in *; lia)))).
unfold cfg_at. change (w64 (BASE + A_dr_fed)) with (Z_to_bv 64 (BASE + A_dr_fed)).
assert (E15 : ew E 15 = Z_to_bv 64 (dnum s1))
  by (rewrite (EREG 15%nat 15%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R15).
(* a ROM byte is an image byte, so it is off the table block (a live block holds no image byte) *)
assert (HoffG : forall y, in_img SEGS y -> ~ (dxSA cx + 24 <= y < dxSA cx + 32)).
{ intros y Hy Hs. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ y HAR GT); [|exact Hy].
  change (req_size ATABLE) with 896. lia. }
assert (Hlen0 : Z.of_nat (length (snd r0)) < 2 ^ 30) by lia.
(* the list's bytes are off both windows *)
assert (HPB : forall p q x, In (p, q) (alist_blks (hs_pending h1)) -> p <= x < p + req_size q ->
  0 <= x < 2 ^ 64 /\ ~ (dHA RG cx + 32 <= x < dHA RG cx + 40) /\ ~ (dxSA cx + 24 <= x < dxSA cx + 32)).
{ intros p q x Hpq Hx.
  assert (Hpq1 : In (p, q) (ablocks B ly1 S1)) by exact (ddw_alist_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ AL _ Hpq).
  assert (HpG : p <> dxG cx).
  { intros E0. apply (df_pu_ne_in_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 (dxG cx, ATABLE) (p, q) _ HAR Hperm);
      [| cbn [fst]; exact (eq_sym E0)].
    apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left. exact Hpq. }
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p q HAR Hpq1) as (_ & Hp4 & Hpc & _).
  split; [lia|]. split.
  - intros Hg. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p q x HAR Hpq1 Hx).
    exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
  - intros Hs. apply (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p q (dxG cx) ATABLE x HAR Hpq1 GT HpG Hx).
    change (req_size ATABLE) with 896. lia. }
paj_run_tok_xR RUNG HS HJ SHOK dj_Bspan.
{ ddw_awr B2 B23 B32 GSW FPE. }
lazymatch type of HS with context [restrict _ ?y] => rename y into msA end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
psrr_branch_tok RUNG BRR HS SHOK dj_Bspan.
- (* 0x83908 taken: off + n <> v[0].n, the head text stays (not dwhole s1) *)
  rewrite (ddw_bne E (dnum s1) (hs_off h1) (Z.of_nat (length (snd r0))) E15 E35 E36 ltac:(lia) ltac:(lia) ltac:(lia))
    in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hwh : dwhole s1 = false).
  { unfold dwhole. rewrite (proj1 Ehead), <- Hoff. unfold bzs. rewrite length_map. apply Z.eqb_neq. clear - Hc. lia. }
  assert (Hlt : hs_off h1 + dnum s1 < Z.of_nat (length (snd r0))) by (clear - Hdn Hc; lia).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK dj_Bspan A_dr_join.
  { ddw_awr B2 B23 B32 GSW FPE. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR2; rename HG0 into GR2; clear HF.
  (* the two runs wrote h->pending_off and s->used only *)
  assert (KL2 : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hy1 Hy2. etransitivity.
    - apply (aview_eq_of SEGS); apply FR2; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin.
    - apply (aview_eq_of SEGS); apply FR1; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin. }
  assert (KP2 : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hy))).
  assert (KK : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hy1 Hy2. split; [exact (KL2 y Hy Hy1 Hy2)|].
    unfold arm. exact (writable_kept (w_H W1) m1 (ms_mem msF) y (KP2 y)). }
  assert (Hromc : rom_view SEGS W1 (ms_mem msF)).
  { intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
    rewrite KL2; [exact (Hrom y Hy) | clear - Hyi; lia | intros Hg; exact (HGR y (GSW y ltac:(lia)) Hy)
      | exact (HoffG y (ex_intro _ sg0 (conj Hsg Hr)))]. }
  assert (AL2 : alist_at B ly1 S1 W1 (ms_mem msF) (dHA RG cx + 16) (hs_pending h1) false).
  { apply (alist_at_kept B ly1 S1 W1 m1 ly1 S1 W1 (ms_mem msF) _ _ _ AL).
    - apply (df_pu_alist_kept B RG ly1 S1 W1 W1 m1 (ms_mem msF) _ _ _ AL).
      + intros x Hx. apply KK; [lia | lia |]. intros Hs.
        apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
        exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
      + intros p q x Hpq Hx. destruct (HPB p q x Hpq Hx) as (X1 & X2 & X3). exact (KK x X1 X2 X3).
    - intros bb Hbb. exact (ddw_alist_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ AL bb Hbb). }
  (* the two stores: h->pending_off = off + n, s->used = used + n *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 4 _ HS eq_refl) as RG4
  end.
  cbn [ms_mem restrict] in RG1, RG4.
  assert (Voff : val_mem SEGS (arm W1 (ms_mem msF)) (dHA RG cx + 32) 8 (hs_off h1 + dnum s1)).
  { first [ unfold arm; eapply (field_of_region _ _ 23%nat (dHA RG cx) _ _ _ _ _ 32 8%N _ (hs_off h1 + dnum s1) RG1 B23);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | first [ rewrite (ddw_den_add _ 15 35 (dnum s1) (hs_off h1) E15 E35 ltac:(lia) ltac:(lia))
                    | rewrite (ddw_den_add _ 35 15 (hs_off h1) (dnum s1) E35 E15 ltac:(lia) ltac:(lia)) ]; f_equal; lia
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  assert (Vu : val_mem SEGS (arm W1 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + dnum s1)).
  { first [ unfold arm; eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 24 8%N _ (re_used e1 + dnum s1) RG4 B32);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | first [ rewrite (ddw_den_add _ 38 15 (re_used e1) (dnum s1) E38 E15 ltac:(lia) ltac:(lia))
                    | rewrite (ddw_den_add _ 15 38 (dnum s1) (re_used e1) E15 E38 ltac:(lia) ltac:(lia)) ]; f_equal; lia
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  assert (KX : forall y, 0 <= y < 2 ^ 64 -> ~ ddX RG cx (dsp0 cx - DRAIN_FRAME) (fun _ => False) y ->
    abyte_kept W1 m1 W1 (ms_mem msF) y).
  { intros y Hy Hx. unfold ddX in Hx.
    apply KK; [exact Hy | intros Hc'; apply Hx; left; clear - Hc'; lia | intros Hc'; apply Hx; right; left; exact Hc']. }
  assert (Hoff2 : (hl_recs (hs_pending h1) = [] /\ hs_off h1 + dnum s1 = 0) \/
    (exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= hs_off h1 + dnum s1 < Z.of_nat (length (snd r))))
    by (right; exists r0, rs0; split; [exact Erecs | clear - Hoffr Hn0 Hlt; lia]).
  pose proof (DAC cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 ly1 S1 Hp1 W1 (ms_mem msF) _ _ (dsp0 cx - DRAIN_FRAME) (fun _ => False) (hs_pending h1)
    (hs_off h1 + dnum s1) [] (dnum s1) HB HM HJ Hromc (fun y _ _ _ Hq => KP2 y Hq) eq_refl
    ltac:(clear - Hsp0; lia) (fun y Hy => False_ind _ Hy) (fun y Hy Hx _ => KX y Hy Hx)
    AL2 eq_refl eq_refl eq_refl (Permutation_refl _) Voff
    Hoff2
    Vu ltac:(clear - Hn0; lia) ltac:(clear - Hjunkl Hdn; lia) ltac:(clear - Hcpos; lia)) as HM2.
  pose proof HM2 as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  destruct HFUT as (tl2 & HLF & Htl).
  unfold ddrop in Htl. rewrite Hwh in Htl. cbn [app] in Htl. subst tl.
  rewrite Hwh in HLF.
  apply (JOINR cx Hpe kr s1 D 0%nat W1 _ HB); [|exact Kll | exact Klr].
  eapply (DDJ cx Hpe kr s1 D (ms_regs msF) ly1 S1 Hp1 W1 (ms_mem msF) _ _ e1 h1 (hs_pending h1)
    (hs_off h1 + dnum s1) out1 ev1 LB1 spent (jb + dnret (ddrop s1 a))%nat a (drain_b_c.da_out a) (drain_b_c.da_hp a)
    (drain_b_c.da_keys a) tl2).
  + unfold dregs_line.
    split; [unfold spZ; rewrite X2, (EREG 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]);
      exact Hsp|].
    split; [rewrite X3, (EREG 3%nat 3%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R3|].
    split; [rewrite X4, (EREG 4%nat 4%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R4|].
    split; [rewrite X21, E32; reflexivity|].
    split; [rewrite X20, E32, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, E32, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X8, (EREG 8%nat 8%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R8|].
    split; [rewrite X9, (EREG 9%nat 9%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R9|].
    split; [rewrite X18, (EREG 18%nat 18%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R18|].
    exact HFRF.
  + rewrite X26. reflexivity.
  + rewrite X24, E37. reflexivity.
  + exact HDB.
  + exact HM2.
  + exact Hjunk.
  + exact HSAME.
  + exact Hcap.
  + exact HU.
  + exact Hsk.
  + exact HHk.
  + exact Hka.
  + exact Hei.
  + exact Hst.
  + exact Hen.
  + exact Hec.
  + exact HH.
  + exact HRS.
  + reflexivity.
  + reflexivity.
  + rewrite Hwh. exact Hpend.
  + rewrite Hwh, Hoff. reflexivity.
  + exact HLF.
  + exact HBUDx.
- (* 0x83908 not taken: off + n = v[0].n, the head text is used up (dwhole s1): list_drop (&h->pending, 0) *)
  rewrite (ddw_bne E (dnum s1) (hs_off h1) (Z.of_nat (length (snd r0))) E15 E35 E36 ltac:(lia) ltac:(lia) ltac:(lia))
    in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hwh : dwhole s1 = true).
  { unfold dwhole. rewrite (proj1 Ehead), <- Hoff. unfold bzs. rewrite length_map. apply Z.eqb_eq. clear - Hc. lia. }
  (* the budget: list_drop's free is the first request of the round's rest *)
  assert (HCP : 0 <= drain_b_c.ds_cap s1) by (clear - H4096 HULEN HUlen; unfold ulen in *; lia).
  assert (HOC : 0 <= drain_b_c.ds_ocap s1).
  { destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & Hoc).
    clear - Hoc. destruct Hoc as [(E0 & _) | (P0 & _)]; lia. }
  assert (HEC : 0 <= drain_b_c.ds_ecap s1).
  { destruct (Z_lt_le_dec (drain_b_c.ds_ecap s1) 0) as [Hlt0|Hge]; [|exact Hge].
    pose proof (df_pcapm_neg B RG HGSB (dref s1) (drain_b_c.ds_en s1) _ Hlt0) as X.
    pose proof A22 as (_ & _ & _ & _ & Hnc22 & _). unfold hl_n in Hnc22.
    rewrite <- Hec in X. clear - X Hnc22. lia. }
  pose proof (df_tnn_drfut B RG HGSB cx s1 jb a tl HCP HEC HOC HFUT) as TNN.
  destruct HFUT as (tl2 & HLF & Htl).
  unfold ddrop in Htl. rewrite Hwh in Htl. rewrite Hwh in HLF. subst tl.
  apply Forall_app in TNN as [_ TN2].
  pose proof (df_tnn_cost B MT RG MTL HGSB tl2 TN2) as TC2.
  pose proof (mo_free_nonneg MT MTL) as F0.
  assert (HMO1 : mo_ok MT S1 (mo_free MT)).
  { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMok &
      _ & _).
    pose proof HBUD as (Bl & _ & Bc & _ & _).
    rewrite (ddw_tr_cost_app B MT RG) in Bc.
    lazymatch type of Bc with context [tr_cost MT (ListTr.list_drop_tra ?x ?y)] =>
      change (tr_cost MT (ListTr.list_drop_tra x y)) with (mo_free MT + 0) in Bc end.
    apply (mok_station MT (dxS cx) S1 _ spent _ MTL HMok Bl); [exact F0|]. clear - Bc TC2. lia. }
  (* the room and the count at the call: the cut's room less the free's charge, its counts at ldrop_pk *)
  assert (HRM1 : rp_RM RP S1 (Z.to_nat (mo_free MT_rk) + (Z.to_nat (tr_cost MT_rk tl2) + kr))).
  { refine (gs_rm_take RP S1 _ tl2 kr _ _ HRMd). unfold ListTr.list_drop_tra, tr_cost. cbn. lia. }
  assert (HCNT1 : cnt_ok_pk RP ldrop_pk (ablocks B ly1 S1)) by exact (gs_cnt_call RP _ _ HCNT).
  assert (Hr0G : fst r0 <> dxG cx).
  { intros E0. apply (df_pu_ne_in_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 (dxG cx, ATABLE)
      (fst r0, Z.of_nat (length (snd r0)) + 1) _ HAR Hperm); [| cbn [fst]; exact (eq_sym E0)].
    apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. right. apply in_or_app. left.
    unfold alist_blks. apply in_or_app. right. rewrite Erecs. left. reflexivity. }
  (* to the call: no store on this stretch *)
  paj_run_to_tok_xR RUNTOG HS HJ SHOK dj_Bspan AF_fr_list_drop.
  { ddw_awr B2 B23 B32 GSW FPE. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msC end.
  rename HFr into FR2; rename HG0 into GR2; clear HF.
  assert (KLC : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W1) (ms_mem msC) y = aview SEGS (w_H W1) m1 y).
  { intros y Hy Hy1 Hy2. etransitivity.
    - apply (aview_eq_of SEGS); apply FR2; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin.
    - apply (aview_eq_of SEGS); apply FR1; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [<- | Hin];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B23, ?B32 in Hr;
           clear - Hr Hy1 Hy2; lia |]); destruct Hin. }
  assert (KPC : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msC) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR2 (apresent_grows _ _ _ _ GR1 Hy))).
  assert (KKC : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> abyte_kept W1 m1 W1 (ms_mem msC) y).
  { intros y Hy Hy1 Hy2. split; [exact (KLC y Hy Hy1 Hy2)|].
    unfold arm. exact (writable_kept (w_H W1) m1 (ms_mem msC) y (KPC y)). }
  assert (HromC : rom_view SEGS W1 (ms_mem msC)).
  { intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
    rewrite KLC; [exact (Hrom y Hy) | clear - Hyi; lia | intros Hg; exact (HGR y (GSW y ltac:(lia)) Hy)
      | exact (HoffG y (ex_intro _ sg0 (conj Hsg Hr)))]. }
  assert (ALC : alist_at B ly1 S1 W1 (ms_mem msC) (dHA RG cx + 16) (hs_pending h1) false).
  { apply (alist_at_kept B ly1 S1 W1 m1 ly1 S1 W1 (ms_mem msC) _ _ _ AL).
    - apply (df_pu_alist_kept B RG ly1 S1 W1 W1 m1 (ms_mem msC) _ _ _ AL).
      + intros x Hx. apply KKC; [lia | lia |]. intros Hs.
        apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
        exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
      + intros p q x Hpq Hx. destruct (HPB p q x Hpq Hx) as (X1 & X2 & X3). exact (KKC x X1 X2 X3).
    - intros bb Hbb. exact (ddw_alist_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ AL bb Hbb). }
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst (ms_regs ?ms0) _ (ms_mem ?ms0) _; cfg_model := ?md0 |} _ =>
    set (rc0 := ms_regs ms0) in *; set (mc := ms_mem ms0) in *; set (mdc := md0) in * end.
  refine (ddw_ld_call_xR cx Hpe kr ly1 S1 Hp1 _ W1 mc mdc rc0 (getr rc0 1) (hs_pending h1)
    (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat _ HB HJ _ _ _ eq_refl _ _ _ _ _ ALC
    ltac:(rewrite Erecs; cbn [length]; lia) HMO1 HRM1 HCNT1 HromC _ _).
  { unfold spZ. rewrite Q2, (EREG 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). exact Hsp. }
  { rewrite Q3, (EREG 3%nat 3%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). rewrite R3. exact Hgp. }
  { rewrite Q4, (EREG 4%nat 4%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). rewrite R4. exact Htp. }
  { rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { rewrite T1, unsigned_lit_small by (clear - HBASE; lia). clear - HBASE. lia. }
  { unfold s0Z. rewrite Q8, (EREG 8%nat 8%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]). rewrite R8.
    unfold w64. rewrite unsigned_lit_small by (clear - HGlo HGhi; unfold ASRC in *; lia).
    clear - HGlo HGhi C1. unfold ASRC in *. lia. }
  { rewrite Q10, B23; reflexivity. }
  { rewrite Q11; reflexivity. }
  { (* the footprint: the vector and r0's text are source blocks, in dFP or new in the round *)
    intros y (r & Hr & Hry). cbn [ddw_FP In] in Hr. rewrite Erecs in Hr. cbn [nth] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hry.
    - apply (ddw_src_awr_xR cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 _ LB1 v (AREC * vcap) y HB HM); [|lia].
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks. fold v vcap.
      rewrite (proj2 (Z.eqb_neq vcap 0) ltac:(lia)). left. reflexivity.
    - apply (ddw_src_awr_xR cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 _ LB1 (fst r0)
        (Z.of_nat (length (snd r0)) + 1) y HB HM); [|lia].
      unfold asrc_blks. right. apply in_or_app. left. unfold alist_blks. apply in_or_app. right. rewrite Erecs. left.
      reflexivity. }
  intros W2 ly2 S2 Hp2 kk regs2 m2 md2 HJ2 HAP KB KI KE KF HROM2 HPK2 HFR2 HL2 HBS HMO HRM2.
  (* ---- back at 0x83918 ---- *)
  rewrite Erecs in HBS. cbn [nth fst snd] in HBS. destruct HBS as (b1 & b2 & EB1 & EB2).
  assert (KB' : forall p q i, In (p, q) (ablocks B ly1 S1) -> p <> v -> p <> fst r0 -> 0 <= i < req_size q ->
    abyte_kept W1 mc W2 m2 (p + i)).
  { intros p q i Hpq Hpv Hpr Hi. apply (KB p q i Hpq); [|exact Hi].
    intros i' Hi' (r & Hr & Hra). cbn [ddw_FP In] in Hr. rewrite Erecs in Hr. cbn [nth] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra.
    - apply (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p q v (AREC * vcap) (p + i') HAR Hpq Hvin Hpv); lia.
    - apply (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p q (fst r0) _ (p + i') HAR Hpq Hr0in Hpr); lia. }
  assert (GT2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)).
  { pose proof GT as GT0. rewrite EB2. rewrite EB1 in GT0. apply in_app_or in GT0 as [X | [X | X]]; apply in_or_app;
      [left; exact X | exfalso; injection X as X _; exact (Hr0G X) | right; exact X]. }
  rewrite T1.
  jafter_call_keep_pi HS 39%nat regs2 (mrestrict (w_H W2) m2) HAP [0; 1; 4]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B2; intros y Hy.
      + apply (mbyte_of_aview SEGS). apply (proj1 (KF y ltac:(clear - Hy HDF; lia))).
      + exfalso. clear - Hy. lia.
    - assert (KG : forall y, dHA RG cx + 32 <= y < dHA RG cx + 40 -> abyte_kept W1 mc W2 m2 y).
      { intros y Hy. destruct (df_pu_gs B RG HRGD y ltac:(unfold ASRC in *; lia)) as (HgG & Hne).
        destruct (HG y HgG) as (Hi & Ho & _). apply (KI y Hi Ho Hne (PSTG y ltac:(unfold ASRC in *; lia))).
        clear - Hy. lia. }
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B23; intros y Hy.
      + apply (mbyte_of_aview SEGS). exact (proj1 (KG y Hy)).
      + intros Hw. exact (proj2 (KG y ltac:(clear - Hy; lia)) Hw).
    - assert (KT : forall y, dxSA cx + 16 <= y < dxSA cx + 32 -> abyte_kept W1 mc W2 m2 y).
      { intros y Hy. replace y with (dxG cx + (y - dxG cx)) by lia.
        apply (KB' (dxG cx) ATABLE (y - dxG cx) GT (not_eq_sym HvG) (not_eq_sym Hr0G)).
        change (req_size ATABLE) with 896. lia. }
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B32; intros y Hy.
      + apply (mbyte_of_aview SEGS). exact (proj1 (KT y Hy)).
      + intros Hw. exact (proj2 (KT y ltac:(clear - Hy; lia)) Hw). }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex 39 ?lc) _ _ =>
    assert (OLDc : forall n, (n < 39)%nat -> ew (havoc Ex 39 lc) n = ew Ex n)
      by (intros n Hn; apply YN3v.ew_havoc_old; exact Hn);
    assert (HEIc : img_env VAL A_LIM (havoc Ex 39 lc)) by (apply img_env_havoc; [assumption | cbv; lia]);
    remember (havoc Ex 39 lc) as Ec eqn:HEc in HS, OLDc, HEIc
  end.
  clear HEc.
  assert (EREGc : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ec nn = getr regs1 r)
    by (intros nn r Hnn Hr; rewrite OLDc by lia; exact (EREG nn r Hnn Hr)).
  assert (B2c : bv_unsigned (ew Ec 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDc by lia; exact B2).
  assert (B23c : bv_unsigned (ew Ec 23) = dHA RG cx) by (rewrite OLDc by lia; exact B23).
  assert (B32c : bv_unsigned (ew Ec 32) = dxSA cx) by (rewrite OLDc by lia; exact B32).
  assert (E32c : ew Ec 32 = Z_to_bv 64 (dxSA cx)) by (rewrite OLDc by lia; exact E32).
  assert (E33c : ew Ec 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDc by lia; exact E33).
  assert (E15c : ew Ec 15 = Z_to_bv 64 (dnum s1)) by (rewrite OLDc by lia; exact E15).
  assert (E37c : ew Ec 37 = Z_to_bv 64 (re_buf e1)) by (rewrite OLDc by lia; exact E37).
  assert (E38c : ew Ec 38 = Z_to_bv 64 (re_used e1)) by (rewrite OLDc by lia; exact E38).
  assert (E23c : ew Ec 23 = Z_to_bv 64 (dHA RG cx)).
  { rewrite OLDc by lia. rewrite (EREG 23%nat 23%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]).
    exact R23. }
  assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
  assert (SHOK2 : sh_ok SEGS dj_Bx [mkSHE 23 0 96; mkSHE 32 0 56] Ec (mrestrict (w_H W2) m2)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (shent_ok_of_range SEGS (w_H W2) m2 Ec dj_Bx 23 (dHA RG cx) 96 (dHA RG cx) 0 96
        (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 m2 md2 (dHA RG cx) 96 HAR2
          (df_azs_sub B RG HGSB (rg_s RG) (4 * ASRC) (dHA RG cx) 96 HGSZ ltac:(lia) ltac:(unfold ASRC in *; lia)))).
      + unfold dj_Bx. apply (U_atom Ec 33 SHADOW_OFF E33c). unfold SHADOW_OFF; lia.
      + apply (U_atom Ec 23 (dHA RG cx) E23c). lia.
      + lia.
      + lia.
      + intros y Hy. change (Z.min 0 96) with 0 in Hy. change (Z.max 0 96) with 96 in Hy.
        unfold SHADOW_OFF. clear - Hy HAr. lia.
    - apply (shent_ok_of_range SEGS (w_H W2) m2 Ec dj_Bx 32 (dxSA cx) 56 (dxSA cx) 0 56
        (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 m2 md2 (dxG cx) ATABLE (dxSA cx) 56 HAR2 GT2
          HSAlo ltac:(change (req_size ATABLE) with 896; lia))).
      + unfold dj_Bx. apply (U_atom Ec 33 SHADOW_OFF E33c). unfold SHADOW_OFF; lia.
      + apply (U_atom Ec 32 (dxSA cx) E32c). lia.
      + lia.
      + lia.
      + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPS. lia. }
  assert (FPE2 : forall y, dxSA cx <= y < dxSA cx + 56 ->
    inFP (dFP cx) y /\ exists b nb, In (b, nb) (ablocks B ly2 S2) /\ b <= y < b + req_size nb).
  { intros y Hy. split; [exact (proj1 (FPE y Hy))|].
    exists (dxG cx), ATABLE. split; [exact GT2 | change (req_size ATABLE) with 896; lia]. }
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 dj_Bspan A_dr_join.
  { ddw_awr B2c B23c B32c GSW FPE2. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  assert (KL3 : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> aview SEGS (w_H W2) (ms_mem msF) y = aview SEGS (w_H W2) m2 y).
  { intros y Hy Hy1 Hy2.
    apply (aview_eq_of SEGS); apply FR3; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2c, ?B23c, ?B32c in Hr;
         clear - Hr Hy1 Hy2; lia |]); destruct Hin. }
  assert (KP3 : forall y, apresent (w_H W2) m2 y -> apresent (w_H W2) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 Hy)).
  assert (KK3 : forall y, 0 <= y < 2 ^ 64 -> ~ (dHA RG cx + 32 <= y < dHA RG cx + 40) ->
    ~ (dxSA cx + 24 <= y < dxSA cx + 32) -> abyte_kept W2 m2 W2 (ms_mem msF) y).
  { intros y Hy Hy1 Hy2. split; [exact (KL3 y Hy Hy1 Hy2)|].
    unfold arm. exact (writable_kept (w_H W2) m2 (ms_mem msF) y (KP3 y)). }
  assert (Hrom3 : rom_view SEGS W2 (ms_mem msF)).
  { intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
    rewrite KL3; [exact (HROM2 y Hy) | clear - Hyi; lia | intros Hg; exact (HGR y (GSW y ltac:(lia)) Hy)
      | exact (HoffG y (ex_intro _ sg0 (conj Hsg Hr)))]. }
  (* the list after list_drop, kept by the last run *)
  assert (HLB : forall b, In b (alist_blks (ldrop_list (hs_pending h1) 0%nat)) -> In b (alist_blks (hs_pending h1))).
  { intros bb Hbb. unfold alist_blks, ldrop_list in Hbb |- *. cbn [hl_cap hl_v hl_recs] in Hbb |- *.
    rewrite Erecs in Hbb |- *.
    cbn [firstn skipn app map] in Hbb |- *. apply in_app_or in Hbb as [X | X]; apply in_or_app; [left; exact X|].
    right. right. exact X. }
  assert (AL3 : alist_at B ly2 S2 W2 (ms_mem msF) (dHA RG cx + 16) (ldrop_list (hs_pending h1) 0%nat) false).
  { apply (alist_at_kept B ly2 S2 W2 m2 ly2 S2 W2 (ms_mem msF) _ _ _ HL2).
    - apply (df_pu_alist_kept B RG ly2 S2 W2 W2 m2 (ms_mem msF) _ _ _ HL2).
      + intros x Hx. apply KK3; [lia | lia |]. intros Hs.
        apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x HAR GT); [change (req_size ATABLE) with 896; lia|].
        exact (proj1 (GSI x ltac:(unfold ASRC in *; lia))).
      + intros p q x Hpq Hx. destruct (HPB p q x (HLB _ Hpq) Hx) as (X1 & X2 & X3). exact (KK3 x X1 X2 X3).
    - intros bb Hbb. exact (ddw_alist_blks_in B RG HGSB ly2 S2 W2 m2 _ _ _ HL2 bb Hbb). }
  (* the two stores: h->pending_off = 0, s->used = used + n *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG4
  end.
  cbn [ms_mem restrict] in RG1, RG4.
  assert (Voff : val_mem SEGS (arm W2 (ms_mem msF)) (dHA RG cx + 32) 8 0).
  { first [ unfold arm; eapply (field_of_region _ _ 23%nat (dHA RG cx) _ _ _ _ _ 32 8%N _ 0 RG1 B23c);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | reflexivity
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  assert (Vu : val_mem SEGS (arm W2 (ms_mem msF)) (dxSA cx + 24) 8 (re_used e1 + dnum s1)).
  { first [ unfold arm; eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 24 8%N _ (re_used e1 + dnum s1) RG4 B32c);
            [ cbn [In]; repeat (first [left; reflexivity | right])
            | first [ rewrite (ddw_den_add _ 38 15 (re_used e1) (dnum s1) E38c E15c ltac:(lia) ltac:(lia))
                    | rewrite (ddw_den_add _ 15 38 (dnum s1) (re_used e1) E15c E38c ltac:(lia) ltac:(lia)) ]; f_equal; lia
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
            | cbn; lia ]
          ]. }
  (* every byte DMEM_xR reads off DROP's writes is kept: the first two runs, the call, the last run *)
  set (XB := fun y => exists p q, In (p, q) (alist_blks (hs_pending h1)) /\ p <= y < p + req_size q).
  assert (KX : forall y, 0 <= y < 2 ^ 64 -> ~ ddX RG cx (dsp0 cx - DRAIN_FRAME - LDROP_STK) XB y ->
    (exists p q, In (p, q) (ablocks B ly1 S1) /\ p <= y < p + req_size q) \/
    (in_img SEGS y /\ ~ Exists (in_zr y) (as_owned_static B) /\ ~ Exists (in_zr y) PST) \/
    (dsp0 cx - DRAIN_FRAME <= y < dsp0 cx) ->
    abyte_kept W1 m1 W2 (ms_mem msF) y).
  { intros y Hy Hx HK. unfold ddX in Hx.
    assert (Hy1 : ~ (dHA RG cx + 32 <= y < dHA RG cx + 40)) by (intros Hc'; apply Hx; left; clear - Hc'; lia).
    assert (Hy2 : ~ (dxSA cx + 24 <= y < dxSA cx + 32)) by (intros Hc'; apply Hx; right; left; exact Hc').
    apply (df_bk_trans _ _ _ _ _ _ y (KKC y Hy Hy1 Hy2)).
    apply (df_bk_trans W1 W2 W2 mc m2 (ms_mem msF) y); [|exact (KK3 y Hy Hy1 Hy2)].
    destruct HK as [(p & q & Hpq & Hyq) | [(Hi & Ho & Hq) | Hfr]].
    - assert (Hpv : p <> v).
      { intros E0. subst p. apply Hx. right. right. left. unfold XB. exists v, (AREC * vcap).
        split; [|rewrite (ddw_blk_uniq_x ly1 S1 Hp1 W1 m1 md1 v (AREC * vcap) q HAR Hvin Hpq); exact Hyq].
        unfold alist_blks. fold v vcap. rewrite (proj2 (Z.eqb_neq vcap 0) ltac:(lia)). left. reflexivity. }
      assert (Hpr : p <> fst r0).
      { intros E0. subst p. apply Hx. right. right. left. unfold XB. exists (fst r0), (Z.of_nat (length (snd r0)) + 1).
        split; [|rewrite (ddw_blk_uniq_x ly1 S1 Hp1 W1 m1 md1 (fst r0) _ q HAR Hr0in Hpq); exact Hyq].
        unfold alist_blks. apply in_or_app. right. rewrite Erecs. left. reflexivity. }
      replace y with (p + (y - p)) by lia. apply (KB' p q (y - p) Hpq Hpv Hpr). lia.
    - destruct (Z_le_gt_dec (as_errno B) y) as [He1|He1]; [destruct (Z_lt_ge_dec y (as_errno B + 4)) as [He2|He2]|].
      + exact (KE y (conj He1 He2)).
      + apply (KI y Hi Ho); [clear - He2; lia | exact Hq | intros Hc'; apply Hx; left; clear - Hc'; lia].
      + apply (KI y Hi Ho); [clear - He1; lia | exact Hq | intros Hc'; apply Hx; left; clear - Hc'; lia].
    - exact (KF y Hfr). }
  (* C3: list_drop frees the head record, |dhead s1| + 1 bytes (ddrop's one request) *)
  assert (Hbb : blocks_bytes S2 + (Z.of_nat (length (dhead s1)) + 1) <= blocks_bytes S1).
  { rewrite (proj1 Ehead). unfold bzs. rewrite length_map.
    rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), EB1, EB2, !bsum_app, bsum_cons. cbn [snd].
    clear. lia. }
  assert (EB1' : ablocks B ly1 S1 = b1 ++ (fst r0, Z.of_nat (length (dhead s1)) + 1) :: b2).
  { rewrite EB1, (proj1 Ehead). unfold bzs. rewrite length_map. reflexivity. }
  pose proof (DAC cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 ly2 S2 Hp2 W2 (ms_mem msF) _ _ (dsp0 cx - DRAIN_FRAME - LDROP_STK) XB
    (ldrop_list (hs_pending h1) 0%nat) 0 [r0] (dnum s1) HB HM HJ2 Hrom3
    (fun y Hi Ho He Hq => KP3 y (HPK2 y Hi Ho He (KPC y Hq))) ltac:(rewrite HFR2; reflexivity)
    ltac:(clear - Hcl Hslo HDSx HDF; unfold LDROP_STK, LDROP_FRAME, ASTACK in *; lia) (fun y Hy => Hy) KX AL3 eq_refl eq_refl
    ltac:(cbn [ldrop_list hl_recs]; rewrite Erecs; reflexivity)
    ltac:(rewrite EB1, EB2; cbn [map app]; apply Permutation_sym, Permutation_middle) Voff
    ltac:(cbn [ldrop_list hl_recs]; rewrite Erecs; cbn [firstn skipn app];
          destruct rs0 as [|r1 rs1]; [left; split; reflexivity|];
          right; exists r1, rs1; split; [reflexivity|];
          pose proof LF as LF1; rewrite Erecs in LF1; apply Forall_inv_tail, Forall_inv in LF1;
          destruct LF1 as (_ & _ & _ & L1); specialize (L1 eq_refl); lia)
    Vu ltac:(clear - Hn0; lia) ltac:(clear - Hjunkl Hdn; lia) ltac:(clear - Hcpos; lia)) as HM2.
  pose proof HM2 as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  apply (JOINR cx Hpe kr s1 D 0%nat W2 _ HB); [|exact Kll | exact Klr].
  eapply (DDJ cx Hpe kr s1 D (ms_regs msF) ly2 S2 Hp2 W2 (ms_mem msF) _ _ e1 h1 (ldrop_list (hs_pending h1) 0%nat)
    0 out1 ev1 LB1 (spent + mo_free MT) (jb + dnret (ddrop s1 a))%nat
    (drain_b_c.DA (drain_b_c.da_out a) (drain_b_c.da_buf a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)
       (skipn 1 (drain_b_c.da_pend a)) (drain_b_c.da_ev a) (drain_b_c.da_erecs a))
    (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a) tl2).
  + unfold dregs_line.
    split; [unfold spZ; rewrite X2, (EREGc 2%nat 2%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]);
      exact Hsp|].
    split; [rewrite X3, (EREGc 3%nat 3%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R3|].
    split; [rewrite X4, (EREGc 4%nat 4%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R4|].
    split; [rewrite X21, E32c; reflexivity|].
    split; [rewrite X20, E32c, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32c, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, E32c, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X8, (EREGc 8%nat 8%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R8|].
    split; [rewrite X9, (EREGc 9%nat 9%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R9|].
    split; [rewrite X18, (EREGc 18%nat 18%bv) by (first [reflexivity | apply Nat.ltb_lt; reflexivity]); exact R18|].
    exact HFRF.
  + rewrite X26. reflexivity.
  + rewrite X24, E37c. reflexivity.
  + exact HDB.
  + exact HM2.
  + exact Hjunk.
  + exact HSAME.
  + exact Hcap.
  + exact HU.
  + exact Hsk.
  + exact HHk.
  + exact Hka.
  + exact Hei.
  + exact Hst.
  + exact Hen.
  + exact Hec.
  + exact HH.
  + exact HRS.
  + reflexivity.
  + reflexivity.
  + rewrite Hwh. cbn [ldrop_list hl_recs]. rewrite Erecs. cbn [firstn skipn app]. exact (eq_sym (proj2 Ehead)).
  + rewrite Hwh. reflexivity.
  + exact HLF.
  + exact (ddw_bud_x cx kr ly1 S1 ly2 S2 spent _ _ tl2 _ b1 b2 HBUDx HMO Hbb EB1' EB2 HRM2).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
(* the R premises at wle: the R free rule from the strict one (W_journal_x.v afree_cf_rule_c_xR_of_x), RO := True *)
Local Ltac wle_inst_r := first [ eassumption | intros; exact I | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2]
  | eapply afree_cf_rule_c_xR_of_x; eassumption ].
Lemma ddw_frames_of_x : forall G1 STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
frames S2 = frames Sc.
Proof. first [ eapply ddw_frames_of_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply ddw_frames_of_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
Lemma ddw_src_awr_x : forall cx Hpe kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 b nb a,
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
DMEM_x B PST ARx RG cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
In (b, nb) (asrc_blks h1) -> b <= a < b + req_size nb ->
(inFP (dFP cx) a /\ exists b' nb', In (b', nb') (ablocks B ly1 S1) /\ b' <= a < b' + req_size nb') \/
in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a.
Proof. first [ eapply ddw_src_awr_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply ddw_src_awr_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
Lemma ddw_ld_call_x : forall cx Hpe kr ly1 S1 Hp1 k1 (W : world SEGS) mc mdc regsc raw (l : hlist) (kr' : nat) Q,
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
ajournal_gx_x SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W mc mdc k1 ->
spZ regsc = dsp0 cx - DRAIN_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 (dHA RG cx + 16) -> getr regsc 11 = w64 (Z.of_nat 0) ->
alist_at B ly1 S1 W mc (dHA RG cx + 16) l false ->
(0 < length (hl_recs l))%nat ->
mo_ok MT S1 (mo_free MT) ->
rp_RM RP S1 (Z.to_nat (mo_free MT_rk) + kr') ->
cnt_ok_pk RP ldrop_pk (ablocks B ly1 S1) ->
rom_view SEGS W mc ->
(forall a, inFP (ddw_FP l) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) ->
(forall W2 ly2 S2 Hp2 kk regs2 m2 md2,
  ajournal_gx_x SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx)
    (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 kk ->
  aregs_preserved regsc regs2 ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> (forall i', 0 <= i' < req_size n -> ~ inFP (ddw_FP l) (p + i')) ->
     0 <= i < req_size n -> abyte_kept W mc W2 m2 (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ (dHA RG cx + 16 <= a < dHA RG cx + 32) -> abyte_kept W mc W2 m2 a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mc W2 m2 a) ->
  (forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W mc W2 m2 a) ->
  rom_view SEGS W2 m2 -> apres_kept B W mc W2 m2 -> frames S2 = frames S1 ->
  alist_at B ly2 S2 W2 m2 (dHA RG cx + 16) (ldrop_list l 0%nat) false ->
  (exists b1 b2, ablocks B ly1 S1 = b1 ++ (fst (nth 0 (hl_recs l) (0, [])),
     Z.of_nat (length (snd (nth 0 (hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) ->
  mo_le MT S1 S2 (mo_free MT) -> rp_RM RP S2 kr' ->
  SRr SEGS W2 (mkCfg (mkst regs2 raw m2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_list_drop)) mc (seg_rom SEGS)) mdc) Q.
Proof. first [ eapply ddw_ld_call_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply ddw_ld_call_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
Theorem dr_drop_x : dr_drop_stmt_x B PST ARx MT RP MMAX RG.
Proof. first [ eapply dr_drop_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply dr_drop_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
End cx.
End b.
End a.
