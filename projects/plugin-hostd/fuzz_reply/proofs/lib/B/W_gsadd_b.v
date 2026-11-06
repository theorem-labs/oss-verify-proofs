(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the second half of the GS-ADD arm of segment GS of the ASan+UBSan walk
   (image B, fuzz_reply.asan-ubsan) of fuzz_reply's drain (0x83c00 .. 0x83ca8, relay.c:115-118 inlined):
   gs_addb_stmt of lib/B/W_gsadd_cx.v.  Proves no function (kind: segment lemma of drain's image-B walk, GS piece
   gs_add).  The structure is image A's lib/A/W_gsaddb.v (a working branch 0c06ccc287f); every pc,
   register, frame slot and trap below is image B's own (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 0x83c00 .. 0x83ca8), and the
   same-image geometry agrees with the old-framework walk a working branch 89040c52421
   lib/B/Prog/drain_p_seen_add_b.v / drain_p_seen_add_b2.v.

   GAR (0x83c00) -> DLN (S q) (0x839d4), in runs around one call:
     run 1   0x83c00 .. 0x83c08  a0 = s8 (= buf + p), a1 = 192(sp) (= jj), jal strndup;
     strndup(buf + p, jj)        W_journal.v astrndup_cf_rule (ASTRNDUP); its result is a fresh block of jj + 1
                                 bytes at res >= 4096 (the rule's forced success), so the NULL arm at 0x83c0c is
                                 never taken (the result atom carries the fact 4096 <= res);
     run 2a  0x83c0c .. 0x83c74  the shadow bytes of &e->nheld (0x83c14 / 0x83c38, through 16(sp)) and of
                                 &e->held (0x83c2c, through s3) are covered by the shadow entry over the relay
                                 entry's bytes 40 .. 56; e->nheld = nheld + 1 (0x83c5c); stops at the PTR_SOVF
                                 check 0x83c74;
     run 2b  0x83c78 .. 0x839d4  the shadow byte of the new slot e->held + 8 nheld (0x83c90) is covered by the
                                 entry over that slot; s5 / s6 / s4 are reloaded from the frame (0x83c94 ..
                                 0x83c9c); the slot gets res (0x83ca4) and the walk jumps back to the line loop.
   The five UBSan traps of the arm (W_drain_cx.v's census rows 0x83bc4 .. 0x83c80) that lie in this half are
   0x83c28 ADDW1 (addiw +1 of nheld; blt), 0x83c60 NULL_BEQ (snez held; seqz slot; beq), 0x83c74 PTR_SOVF
   (sltu slot, held; slti nheld, 0; xor; xori 1; beqz), 0x83c78 NONNULL (beqz held) and 0x83c80 ALIGN8 (andi slot,
   7; bnez).  The seat carries the recipe's facts (lib/B/W_traps.v R1 / R2 / R4: held and the slot are pointer
   atoms 4096 .. ceiling with al2 3, the slot is an alias of held + (nheld << 3), nheld is an int32-safe atom), so
   the runner decides four of them; 0x83c74's sltu compares two atoms the runner does not order (R5), and the walk
   closes that trap edge with trap_ptr_sovf and trap_U_sltu_ge.
   The cut DLN (S q) is then the line loop after the begin's key was added: the relay entry's key list gains
   (res, the jj bytes of the line, []), the held keys gain firstn jj (dline s1 p q), and the meter is charged
   strndup's request RMalloc (jj + 1), the head of GARfut's owed trace.
   The Section header is lib/B/W_drain_gs.v's (= lib/B/W_drain_cx.v's), verbatim. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_place W_drain_cx W_drain_gs W_drain_gs_model W_traps W_gsadd_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* ---- The symbolic state at GAR (0x83c00). ----
   Atoms 0 .. 31 are the registers; the six extra atoms are 32 = SA (the relay entry; no register holds it at
   GAR, image B's GS stage clobbers s5 / s4 / s6), 33 = SHADOW_OFF (image B keeps the shadow base in the frame
   slot 240(sp), not in a register, so it is the value of a frame chunk), 34 = e->held (hp, the grown array),
   35 = e->nheld (nh), 36 = hp + 8 nh (the new slot) and 37 = jj (strndup's length, 192(sp)).
   s3 (19) carries the shadow address of &e->held as YCbn's match form ((SA + 40) >> 3) + SHADOW_OFF, so the
   check at 0x83c2c is decided; 16(sp) holds the same form for &e->nheld (0x83c14, 0x83c38).  The alias names
   the slot address the code builds out of two atoms (0x83c50 `add a1, a3, a1`). *)
Definition gb_ceil : Z := 140737479966720.   (* the literal bound of ASAN_CEIL; never the abstract one *)
Definition gb_shE (m : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 33 0).
Definition gb_slotE : sv := SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 3)).
Definition gb_frame : YP09.region := YP09.mkRegion (Some 2%nat) 16 248 16 16
  [ YP09.mkChunk 16 (CVal 8 (gb_shE 32 48));
    YP09.mkChunk 32 (CVal 8 (SOff 32 48));
    YP09.mkChunk 88 (CVal 8 (SOff 32 40));
    YP09.mkChunk 128 (CVal 8 (SOff 32 16));
    YP09.mkChunk 136 (CVal 8 (SOff 32 24));
    YP09.mkChunk 144 (CVal 8 (SOff 32 0));
    YP09.mkChunk 192 (CVal 8 (SOff 37 0));
    YP09.mkChunk 240 (CVal 8 (SOff 33 0)) ].
Definition gb_sa : YP09.region := YP09.mkRegion (Some 32%nat) 40 52 48 52
  [ YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 4 (SOff 35 0)) ].
Definition gb_slot : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 8 [].
Definition gb_regions : smem := [ gb_frame; gb_sa; gb_slot ].
Definition gb_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 4096 gb_ceil 3); (33%nat, mkAF SB SB 0);
  (34%nat, mkAF 4096 gb_ceil 3); (35%nat, mkAF 0 (2 ^ 26) 0); (36%nat, mkAF 4096 gb_ceil 3);
  (37%nat, mkAF 0 (2 ^ 26) 0) ] []
  [ (gb_slotE, SOff 36 0) ].
Definition gb_regs : list sv := sr_set sr_atoms 19%bv (gb_shE 32 40).
Definition ss_gb : sstate := mkSS A_dr_addb gb_regs gb_regions None gb_facts.
Definition gb_SH : list shent := [ mkSHE 32 40 56; mkSHE 36 0 8 ].
Definition gb_Bx : sv := SOff 33 0.
Definition gb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gb_extra (SA hp nh jj : Z) : list word := map (Z_to_bv 64) [SA; SHADOW_OFF; hp; nh; hp + 8 * nh; jj].
(* a separation fact kept folded in the main context, so that lia does not split on it (lia splits every
   disjunction it sees) *)
Definition gb_sep (a b c d : Z) : Prop := a <= b \/ c <= d.


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

(* the helpers W_gsadd_a.v shares need no Section hypothesis; clear them so that lia's proof term mentions none *)
Ltac gb_clr0 := repeat match goal with H : _ |- _ => clear H end.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ============================================================================================
   (1) small arithmetic of symbolic values
   ============================================================================================ *)
Lemma gb_den_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof using. gb_clr0. intros E e v <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma gb_U_add : forall E x y, 0 <= U E x + U E y < 2 ^ 64 -> U E (SAlu ALU_ADD x y) = U E x + U E y.
Proof using. gb_clr0.
intros E x y H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
Lemma gb_U_sll3 : forall E x, 0 <= U E x * 8 < 2 ^ 64 -> U E (SAlu ALU_SLL x (SLit 3)) = U E x * 8.
Proof.
intros E x H. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64. lia.
Qed.
Lemma gb_U_shE : forall E n v c, ew E n = w64 v -> ew E 33 = w64 SHADOW_OFF -> 0 <= v -> v + c < 2 ^ 47 -> 0 <= c ->
U E (gb_shE n c) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E n v c Hn H21 Hv Hvc Hvc0.
assert (Hd : 0 <= (v + c) / 8 <= v + c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (US : U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8)
  by (rewrite U_srl3, (U_atom_off E n v c Hn ltac:(lia) ltac:(lia)); reflexivity).
assert (UB : U E (SOff 33 0) = SHADOW_OFF) by (apply (U_atom E 33 _ H21); unfold SHADOW_OFF; lia).
unfold gb_shE. rewrite gb_U_add by (rewrite US, UB; unfold SHADOW_OFF; lia). rewrite US, UB. reflexivity.
Qed.

(* the live blocks are pairwise distinct (image A's lib/A/W_drain_linea.v la_ablocks_nodup) *)
Lemma gb_ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [pp nn] Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md pp nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. apply req_size_pos. lia. }
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.


Lemma gb_nd_app : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) ->
List.NoDup l1 /\ List.NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 H; cbn [app] in H.
- split; [constructor|]. split; [exact H|]. intros x [].
- apply NoDup_cons_iff in H as [Ha H]. destruct (IH l2 H) as (N1 & N2 & Hd).
  split; [constructor; [intros Hin; apply Ha; apply in_or_app; left; exact Hin | exact N1]|].
  split; [exact N2|]. intros x [<- | Hx] Hy; [apply Ha; apply in_or_app; right; exact Hy | exact (Hd x Hx Hy)].
Qed.

(* ============================================================================================
   (2) the entry seat at GAR, and its shadow entries
   ============================================================================================ *)
Lemma gb_seat : forall (W1 : world SEGS) regs1 m1 (SA sp hp nh jj : Z),
getr regs1 2 = w64 sp -> getr regs1 19 = w64 ((SA + 40) / 8 + SHADOW_OFF) ->
4096 <= SA -> SA + 56 <= gb_ceil -> SA mod 8 = 0 ->
4096 <= hp -> hp + 8 * nh + 8 <= gb_ceil -> hp mod 8 = 0 ->
0 <= nh <= 2 ^ 26 -> 0 <= jj <= 2 ^ 26 ->
2 ^ 46 <= sp -> sp + 352 <= 2 ^ 47 -> sp mod 16 = 0 -> SA + 56 <= sp -> hp + 8 * nh + 8 <= sp ->
(hp + 8 * nh + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * nh) ->
val_mem SEGS (arm W1 m1) (sp + 16) 8 ((SA + 48) / 8 + SHADOW_OFF) ->
val_mem SEGS (arm W1 m1) (sp + 32) 8 (SA + 48) ->
val_mem SEGS (arm W1 m1) (sp + 88) 8 (SA + 40) ->
val_mem SEGS (arm W1 m1) (sp + 128) 8 (SA + 16) ->
val_mem SEGS (arm W1 m1) (sp + 136) 8 (SA + 24) ->
val_mem SEGS (arm W1 m1) (sp + 144) 8 SA ->
val_mem SEGS (arm W1 m1) (sp + 192) 8 jj ->
val_mem SEGS (arm W1 m1) (sp + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (SA + 40) 8 hp ->
val_mem SEGS (arm W1 m1) (SA + 48) 4 nh ->
(forall o, 48 <= o < 52 -> writable_at SEGS (arm W1 m1) (SA + o)) ->
(forall o, 0 <= o < 8 -> writable_at SEGS (arm W1 m1) (hp + 8 * nh + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gb_extra SA hp nh jj))) ss_gb
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_addb)) m1 (seg_rom SEGS))).
Proof.
intros W1 regs1 m1 SA sp hp nh jj R2 R19 HSAlo HSAhi HSA8 Hhplo Hhphi Hhp8 Hnh Hjj Hsplo Hsphi Hsp16 HSAsp Hhpsp HD
  V16 V32 V88 V128 V136 V144 V192 V240 V40 V48 HW1 HW2.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gb_extra SA hp nh jj))).
assert (E2 : ew E 2 = w64 sp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact R2).
assert (E32 : ew E 32 = w64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = w64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = w64 hp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = w64 nh)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = w64 (hp + 8 * nh))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = w64 jj)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usa : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; unfold gb_ceil in *; lia).
assert (Ub : bv_unsigned (ew E 33) = SHADOW_OFF) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Uhp : bv_unsigned (ew E 34) = hp) by (rewrite E34; apply unsigned_lit_small; unfold gb_ceil in *; lia).
assert (Unh : bv_unsigned (ew E 35) = nh) by (rewrite E35; apply unsigned_lit_small; lia).
assert (Usl : bv_unsigned (ew E 36) = hp + 8 * nh) by (rewrite E36; apply unsigned_lit_small; unfold gb_ceil in *; lia).
assert (Ujj : bv_unsigned (ew E 37) = jj) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U34 : U E (SOff 34 0) = hp) by (apply (U_atom E 34 hp E34); unfold gb_ceil in *; lia).
assert (U35 : U E (SOff 35 0) = nh) by (apply (U_atom E 35 nh E35); lia).
assert (USL : U E (SAlu ALU_SLL (SOff 35 0) (SLit 3)) = nh * 8) by (rewrite gb_U_sll3; rewrite U35; [reflexivity | lia]).
assert (UAD : U E gb_slotE = hp + 8 * nh)
  by (unfold gb_slotE; rewrite gb_U_add; rewrite ?U34, ?USL; unfold gb_ceil in *; lia).
assert (HD48 : 0 <= (SA + 48) / 8 <= SA + 48)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (D16 : sv_denot E (gb_shE 32 48) = Z_to_bv 64 ((SA + 48) / 8 + SHADOW_OFF))
  by (apply gb_den_of_U; apply (gb_U_shE E 32 SA 48 E32 E33); unfold gb_ceil in *; lia).
assert (D19 : sv_denot E (gb_shE 32 40) = Z_to_bv 64 ((SA + 40) / 8 + SHADOW_OFF))
  by (apply gb_den_of_U; apply (gb_U_shE E 32 SA 40 E32 E33); unfold gb_ceil in *; lia).
assert (DSA : forall c, 0 <= c <= 48 -> sv_denot E (SOff 32 c) = Z_to_bv 64 (SA + c))
  by (intros c Hc; apply gb_den_of_U; exact (U_atom_off E 32 SA c E32 ltac:(unfold gb_ceil in *; lia) ltac:(unfold gb_ceil in *; lia))).
assert (D192 : sv_denot E (SOff 37 0) = Z_to_bv 64 jj) by (apply gb_den_of_U; exact (U_atom E 37 jj E37 ltac:(lia))).
assert (D240 : sv_denot E (SOff 33 0) = Z_to_bv 64 SHADOW_OFF)
  by (apply gb_den_of_U; exact (U_atom E 33 _ E33 ltac:(unfold SHADOW_OFF; lia))).
assert (D40 : sv_denot E (SOff 34 0) = Z_to_bv 64 hp) by (apply gb_den_of_U; exact U34).
assert (D48 : sv_denot E (SOff 35 0) = Z_to_bv 64 nh) by (apply gb_den_of_U; exact U35).
assert (DAL : sv_denot E gb_slotE = sv_denot E (SOff 36 0)).
{ rewrite (gb_den_of_U E gb_slotE _ UAD). symmetry. apply gb_den_of_U.
  apply (U_atom E 36 _ E36). unfold gb_ceil in *. lia. }
unfold ss_gb. apply pa_entry_st_ok_full.
- unfold gb_regs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite R19, D19; reflexivity].
- vm_compute. reflexivity.
- unfold gb_regions, gb_frame, gb_sa, gb_slot.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 16 8 _ ((SA + 48) / 8 + SHADOW_OFF));
      [exact D16 | unfold SHADOW_OFF, gb_ceil in *; zside | zside | exact V16].
    * apply (chunk_ok_val SEGS E _ sp 32 8 _ (SA + 48));
      [apply DSA; lia | unfold gb_ceil in *; zside | zside | exact V32].
    * apply (chunk_ok_val SEGS E _ sp 88 8 _ (SA + 40));
      [apply DSA; lia | unfold gb_ceil in *; zside | zside | exact V88].
    * apply (chunk_ok_val SEGS E _ sp 128 8 _ (SA + 16));
      [apply DSA; lia | unfold gb_ceil in *; zside | zside | exact V128].
    * apply (chunk_ok_val SEGS E _ sp 136 8 _ (SA + 24));
      [apply DSA; lia | unfold gb_ceil in *; zside | zside | exact V136].
    * apply (chunk_ok_val SEGS E _ sp 144 8 _ SA);
      [rewrite (DSA 0 ltac:(lia)), Z.add_0_r; reflexivity | unfold gb_ceil in *; zside | zside | exact V144].
    * apply (chunk_ok_val SEGS E _ sp 192 8 _ jj); [exact D192 | zside | zside | exact V192].
    * apply (chunk_ok_val SEGS E _ sp 240 8 _ SHADOW_OFF); [exact D240 | unfold SHADOW_OFF; zside | zside | exact V240].
  + rewrite Usa. split; [lia|]. split; [unfold gb_ceil in *; lia|]. split; [intros o Ho; exact (HW1 o Ho)|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 40 8 _ hp); [exact D40 | unfold gb_ceil in *; zside | zside | exact V40].
    * apply (chunk_ok_val SEGS E _ SA 48 4 _ nh); [exact D48 | zside | zside | exact V48].
  + rewrite Usl. split; [lia|]. split; [unfold gb_ceil in *; lia|]. split; [intros o Ho; exact (HW2 o Ho)|].
    apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold gb_regions, gb_frame, gb_sa, gb_slot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa, Usl.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [gb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Usa, Ub, Uhp, Unh, Usl, Ujj. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    assert (Hs8 : (hp + 8 * nh) mod 8 = 0) by (rewrite (Z.mul_comm 8 nh), Z.mod_add by lia; exact Hhp8).
    unfold SB, SHADOW_OFF, gb_ceil in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
  + cbn [gb_facts f_alias alias_ok]. split; [exact DAL | exact I].
Qed.

Lemma gb_shok : forall Ex ly S (W : world SEGS) mem md G SA hp kh nh,
AR SEGS B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 0 <= nh -> 8 * nh + 8 <= req_size kh ->
ew Ex 33 = w64 SHADOW_OFF -> ew Ex 32 = w64 SA -> ew Ex 36 = w64 (hp + 8 * nh) ->
sh_ok SEGS gb_Bx gb_SH Ex (mrestrict (w_H W) mem).
Proof.
intros Ex ly S W mem md G SA hp kh nh HAR Hin HGle HSAle Hhin Hnh Hkh E33 E32 E36.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks SEGS B LAWS ly S W mem md _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
destruct (al_blocks SEGS B LAWS ly S W mem md _ _ HAR Hhin) as (_ & H4096h & Hceilh & Happh & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in Hceil, Happ.
assert (UB : U Ex gb_Bx = SHADOW_OFF) by (unfold gb_Bx; apply (U_atom Ex 33 _ E33); unfold SHADOW_OFF; lia).
unfold sh_ok, gb_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) mem Ex gb_Bx 32 SA 56 SA 40 56).
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md G ATABLE); [exact HAR | exact Hin | lia |].
    rewrite RQT. unfold AENT, ATABLE in *. lia.
  + exact UB.
  + apply (U_atom Ex 32 SA E32). unfold AENT, ATABLE in *. lia.
  + lia.
  + lia.
  + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold AENT, ATABLE in HSAle. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem Ex gb_Bx 36 (hp + 8 * nh) 8 (hp + 8 * nh) 0 8).
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md hp kh); [exact HAR | exact Hhin | lia | lia].
  + exact UB.
  + apply (U_atom Ex 36 _ E36). lia.
  + lia.
  + lia.
  + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happh. unfold SHADOW_OFF. lia.
Qed.

(* ============================================================================================
   (3) the byte images of the relay entry's cells and of the held array's slots
   (image A's lib/A/W_gsadd_scratch.v (2), renamed)
   ============================================================================================ *)

Lemma gb_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof using. gb_clr0. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma gb_bzs_len : forall l, length (bzs l) = length l.
Proof using. gb_clr0. intros l. unfold bzs. apply length_map. Qed.
Lemma gb_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof using. gb_clr0. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.
Lemma gb_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof using. gb_clr0.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma gb_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof using. gb_clr0.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gb_nth_zle by exact Hk. rewrite gb_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma gb_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof using. gb_clr0.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.
Lemma gb_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof using. gb_clr0. intros mem b l b' H <-. exact H. Qed.
Lemma gb_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof using. gb_clr0.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.
Lemma gb_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof using. gb_clr0.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gb_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gb_nth_le_bytes by assumption. reflexivity.
Qed.
Lemma gb_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof using. gb_clr0.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite gb_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite gb_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite gb_le_byte1 by exact Hr. reflexivity.
Qed.
Lemma gb_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof using. gb_clr0.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma gb_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof using. gb_clr0.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac gb_len := rewrite ?length_app, ?gb_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].
Ltac gb_len_in H := rewrite ?length_app, ?gb_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes in H;
  cbn [length] in H.

Lemma gb_entry_hp : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_hp e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e).
Proof using. gb_clr0.
intros W m SA e Hp1 Hhp H.
unfold entry_bytes in H. rewrite !gb_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gb_le8_bytes (re_hp e) Hhp) in H.
apply (gb_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
apply (gb_garr8_at _ _ _ _ H). gb_len. lia.
Qed.
Lemma gb_entry_nheld : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_nheld e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 48) 4 (re_nheld e).
Proof using. gb_clr0.
intros W m SA e Hp1 Hnh H.
unfold entry_bytes in H. rewrite !gb_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gb_le4_bytes (re_nheld e) Hnh) in H.
apply (gb_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hnh|].
apply (gb_garr8_at _ _ _ _ H). gb_len. lia.
Qed.
Lemma gb_entry_store : forall (W : world SEGS) m (W' : world SEGS) m' SA e e',
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
re_fd e' = re_fd e -> re_eof e' = re_eof e -> re_skip e' = re_skip e -> re_pad1 e' = re_pad1 e ->
re_buf e' = re_buf e -> re_used e' = re_used e -> re_cap e' = re_cap e -> re_pad2 e' = re_pad2 e ->
0 <= re_hp e' < 2 ^ 64 -> 0 <= re_nheld e' < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 40) 8 (re_hp e') ->
val_mem SEGS (arm W' m') (SA + 48) 4 (re_nheld e') ->
(forall x, SA <= x < SA + 40 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 52 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes e')).
Proof using. gb_clr0.
intros W m W' m' SA e e' Hp1 Hp2 Efd Eeof Eskip Ep1 Ebuf Eused Ecap Ep2 Hhp Hnh H Vhp Vnh K1 K2.
unfold entry_bytes in H |- *. rewrite Efd, Eeof, Eskip, Ep1, Ebuf, Eused, Ecap, Ep2.
rewrite !gb_bzs_app, !app_assoc in H |- *.
apply garr8_app in H as [H HP2]. apply garr8_app in H as [H _]. apply garr8_app in H as [HZ _].
rewrite (gb_le8_bytes (re_hp e') Hhp), (gb_le4_bytes (re_nheld e') Hnh).
apply garr8_app. split; [apply garr8_app; split; [apply garr8_app; split|]|].
- apply (gb_garr8_kept W m); [exact HZ|]. intros x Hx. apply K1. gb_len_in Hx. lia.
- apply (gb_garr8_at _ (SA + 40)); [|gb_len; lia].
  apply gb_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hhp | exact Vhp].
- apply (gb_garr8_at _ (SA + 48)); [|gb_len; lia].
  apply gb_garr8_of_val; [change (8 * Z.of_nat 4) with 32; exact Hnh | exact Vnh].
- apply (gb_garr8_at _ (SA + 52)); [|gb_len; lia].
  apply (gb_garr8_kept W m).
  + apply (gb_garr8_at _ _ _ _ HP2). gb_len. lia.
  + intros x Hx. apply K2. gb_len_in Hx. lia.
Qed.
Lemma gb_ptrs_app : forall (W : world SEGS) m (W' : world SEGS) m' hp ks k,
0 <= key_addr k < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat (length ks)) 8 (key_addr k) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (ks ++ [k]))).
Proof.
intros W m W' m' hp ks k Hk H V K.
rewrite gs_key_ptrs_app, gb_bzs_app.
apply garr8_app. split.
- apply (gb_garr8_kept W m); [exact H|]. intros x Hx. apply K. rewrite gb_bzs_len, gs_key_ptrs_len in Hx. lia.
- apply (gb_garr8_at _ (hp + 8 * Z.of_nat (length ks))); [|rewrite gb_bzs_len, gs_key_ptrs_len; lia].
  rewrite (gb_le8_bytes _ Hk). apply gb_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hk | exact V].
Qed.



(* a byte of a garr8 run, as the ASan view reads it (image A's lib/A/W_drain_next.v dn_garr8_aview) *)
Lemma gb_garr8_aview : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j H Hj. unfold aview. pose proof (proj2 (H j Hj)) as Hr.
unfold arm in H. rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) base l j H Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.


(* the new block of an allocator call is disjoint from every block before it (image A's lib/A/W_lp_tail.v lpt_new_disj) *)
Lemma gb_new_disj : forall ly2 S2 (W2 : world SEGS) mem2 md2 lyc Sc res n b m,
AR SEGS B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> In (b, m) (ablocks B lyc Sc) ->
b + req_size m <= res \/ res + req_size n <= b.
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc res n b m HAR2 Ebl Hin. apply in_split in Hin as (l1 & l2 & E1).
pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.


(* ============================================================================================
   (5) the line loop's model after a begin whose key was not held (image A's lib/A/W_gsfree_scratch.v gsf_line / gsf_hist,
   for the add arm)
   ============================================================================================ *)
Lemma gba_line : forall cx s1 (p q jj : nat),
GSF s1 p q ->
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None ->
drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] /\
drlq s1 p = dline s1 p q :: drlq s1 (S q) /\
dskp s1 (S q) = false /\ dbound s1 (S q) /\ (0 < S q)%nat /\
dlno s1 (S q) = GSno cx s1 p q /\
dloc cx s1 (S q) = GSoc cx s1 p q /\
dlH cx s1 (S q) = dlH cx s1 p ++ [firstn jj (dline s1 p q)] /\
dlka cx s1 (S q) = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q).
Proof.
intros cx s1 p q jj HF Hge HI.
unfold GSF in HF. destruct HF as (HB & HPQ & HQ & HNZ & HK & HL).
destruct (gs_drl s1 p q HB HPQ HQ HNZ HK HL) as (E1 & E2 & E3).
destruct (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ 0 RelayRunF.adr0 [] Hge HI)
  as (S1 & _ & _).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
split.
{ unfold dbound. split; [lia|right]. replace (S q - 1)%nat with q by lia. exact HQ. }
split; [lia|].
split; [rewrite (gs_dlno s1 p q E1); unfold GSno; reflexivity|].
split; [rewrite (gs_dloc cx s1 p q E1); unfold GSoc; reflexivity|].
split; [rewrite (gs_dlH cx s1 p q E1); exact S1|].
exact (gs_dlka cx s1 p q E1).
Qed.

Lemma gba_hist : forall cx s1 D (p q jj : nat) h1 LB1 ka1,
GSF s1 p q ->
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None ->
DHIST cx (dvirt cx s1 false (dlH cx s1 p) ka1 (GSno cx s1 p q) (GSoc cx s1 p q)) (D ++ ddata s1) (D ++ ddata s1)
  (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p) h1 LB1
  (Z.of_nat (S (length (drlq s1 (S q))))) ->
DHIST cx (dvirt cx s1 false (dlH cx s1 p ++ [firstn jj (dline s1 p q)]) ka1 (GSno cx s1 p q) (GSoc cx s1 p q))
  (D ++ ddata s1) (D ++ ddata s1)
  (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) h1 LB1
  (Z.of_nat (length (drlq s1 (S q)))).
Proof.
intros cx s1 D p q jj h1 LB1 ka1 HF Hge HI HD.
pose proof (index_of_none _ _ HI) as Hnin.
unfold DHIST, dvirt, pstream in HD |- *.
cbn [drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_pend drain_b_c.ds_off] in HD |- *.
destruct HD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
do 7 (split; [assumption|]).
split.
{ apply NoDup_ListNoDup. apply NoDup_ListNoDup in D8.
  apply (Permutation_NoDup (Permutation_cons_append _ _)). constructor; [exact Hnin | exact D8]. }
split.
{ rewrite app_assoc, gs_upds_snoc. unfold upd. rewrite Hge. cbv beta iota.
  intros y. rewrite upd_in_begin, in_app_iff. cbn [In].
  split; intros Hy.
  - destruct Hy as [Hy | [Hy | []]]; [left; apply (D9 y); exact Hy | right; symmetry; exact Hy].
  - destruct Hy as [Hy | Hy]; [left; apply (D9 y); exact Hy | right; left; symmetry; exact Hy]. }
split; [|exact D11].
rewrite length_app. cbn [length]. lia.
Qed.
(* ============================================================================================
   (6) keeping bytes across the call: writability of an image byte and of a byte off the image
   ============================================================================================ *)
Lemma gb_find_segment_in : forall segs a n sg, find_segment segs a n = Some sg ->
In sg segs /\ Z.of_N (seg_base sg) <= a /\ a + n <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros segs a n sg. induction segs as [|s rest IH]; intros H; cbn in H; [discriminate|].
destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
- injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  split; [left; reflexivity | lia].
- destruct (IH H) as (Hin & H1 & H2). split; [right; exact Hin | lia].
Qed.

(* an image byte that is not read-only stays writable when its view is kept *)
Lemma gb_writable_view : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> ~ in_rom SEGS a -> aview SEGS (w_H Wb) m' a = aview SEGS (w_H Wa) m a ->
writable_at SEGS (arm Wa m) a -> writable_at SEGS (arm Wb m') a.
Proof.
intros Wa Wb m m' a Hi Hnr Hv Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold aview, mbyte in Hv. unfold writable_at, wview, arm, mrestrict in *. rewrite HA in Hw, Hv. rewrite HB in Hv |- *.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em'; [discriminate|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
unfold seg_rom, memory_read in Hv. cbn [Z.of_N] in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Hf; [|discriminate].
destruct (seg_readable sg); [|discriminate].
change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv.
destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Hb;
  [|cbn in Hv; discriminate].
destruct (seg_writable sg) eqn:Hws; [discriminate|].
exfalso. apply Hnr. destruct (gb_find_segment_in _ _ _ _ Hf) as (Hin & H1 & H2). rewrite Ha in H1, H2.
exists sg. split; [exact Hin|]. split; [exact Hws | lia].
Qed.

(* an image byte stays writable when its presence is kept (image A's lib/A/W_lp_tail.v lpt_writable_img) *)
Lemma gb_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (arm Wa m) a -> writable_at SEGS (arm Wb m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, arm, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* a byte off the image is writable exactly when it is present *)
Lemma gb_writable_noimg : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
~ in_img SEGS a -> 0 <= a < 2 ^ 64 -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (arm Wa m) a -> writable_at SEGS (arm Wb m') a.
Proof.
intros Wa Wb m m' a Hni Ha0 Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
assert (Hnf : find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1 = None).
{ destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Hf; [|reflexivity].
  exfalso. apply Hni. destruct (gb_find_segment_in _ _ _ _ Hf) as (Hin & H1 & H2). rewrite Ha in H1, H2.
  exists sg. split; [exact Hin | lia]. }
unfold writable_at, wview, arm, mrestrict in *.
destruct (w_H Wa (Z_to_bv 64 a)) eqn:HA; [rewrite Hnf in Hw; exfalso; exact (Hw eq_refl)|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|rewrite Hnf in Hw; exfalso; exact (Hw eq_refl)].
destruct (Hp (conj HA (ex_intro _ b Em))) as [HB [b2 Hb2]]. rewrite HB, Hb2. discriminate.
Qed.


Lemma gb_not_wrange : forall E rs aa,
Forall (fun r => ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= aa < base_val E (YP09.r_base r) + YP09.r_whi r)) rs ->
~ in_wrange E rs aa.
Proof using. gb_clr0. intros E rs aa HF (r & Hin & Hr). rewrite Forall_forall in HF. exact (HF r Hin Hr). Qed.

(* drain's frame (image B: 23 one-time slots and the 13 saves, all in [sp, sp + 352)), across a world change *)
Lemma gb_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof using. gb_clr0.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
  F19 & F20 & F21 & F22 & F23 & HS).
repeat (split; [apply V; [lia | unfold DRAIN_FRAME; lia | assumption]|]).
unfold dr_saved in *. intros i Hi. specialize (HS i Hi). unfold DR_SAVE_OFF in *.
replace (dsp0 cx - DRAIN_FRAME + 248 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (248 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

(* DLN's dregs_line from GAR's dregs_gs, the four pins the arm reloads (s5 / s4 / s6 from the frame, s11 never
   written) and the frame kept *)
Lemma gb_dregs_line : forall cx regs regs' (W : world SEGS) m (W' : world SEGS) m',
dregs_gs RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
getr regs' 21 = w64 (dxSA cx) -> getr regs' 20 = w64 (dxSA cx + 16) ->
getr regs' 22 = w64 (dxSA cx + 24) -> getr regs' 27 = w64 (dxSA cx + 32) ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
dregs_line RG cx regs' W' m'.
Proof.
intros cx regs regs' W m W' m' HR E2 E3 E4 E8 E9 E18 E21 E20 E22 E27 KF.
destruct HR as (Hsp & R3 & R4 & R8 & R9 & R18 & HFR).
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E8, E9, E18.
refine (conj Hsp (conj R3 (conj R4 (conj E21 (conj E20 (conj E22 (conj E27 (conj R8 (conj R9 (conj R18 _)))))))))).
exact (gb_frame_kept cx W m W' m' KF HFR).
Qed.

(* ============================================================================================
   (7) the footprints of the cut's representations, byte by byte: a global cell or a byte of one of the blocks
   the representation names (image A's lib/A/W_drain_next.v dn_*_fp_low, with the cell or the block kept apart)
   ============================================================================================ *)
Lemma gb_zpd_nth : forall l i j a b, zpairwise_disjoint l -> (i < j)%nat ->
nth_error l i = Some a -> nth_error l j = Some b -> zdisj a b.
Proof.
induction l as [|x l IH]; intros i j a b H Hij Hi Hj; [destruct i; discriminate|].
destruct H as [Hx H]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. apply nth_error_In in Hj.
  clear - Hx Hj. induction l as [|y l IHl]; [destruct Hj|]. destruct Hx as [Hy Hx].
  destruct Hj as [<- | Hj]; [exact Hy | exact (IHl Hx Hj)].
- cbn in Hi, Hj. exact (IH i j a b H ltac:(lia) Hi Hj).
Qed.

Lemma gb_bzs_len' : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma gb_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof using. gb_clr0.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma gb_alist_fp_cls : forall ly S W mem LA l lines,
alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
(LA <= a < LA + 16) \/ (exists b n, In (b, n) (alist_blks l) /\ b <= a < b + req_size n).
Proof.
intros ly S W mem LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; exact Ha|].
right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  rewrite gb_bzs_len', length_app, gb_recs_len in Ha.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l), (AREC * hl_cap l). split.
  + unfold alist_blks. apply in_or_app. left. destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; reflexivity].
  + pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
  rewrite gb_bzs_len', length_app in Ha. cbn [length] in Ha.
  exists (fst q), (Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
  + pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gb_asrc_fp_cls : forall ly S W mem HA h,
asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
(HA <= a < HA + ASRC) \/ (exists b n, In (b, n) (asrc_blks h) /\ b <= a < b + req_size n).
Proof.
intros ly S W mem HA h HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (SUB : forall LA l lines, alist_at B ly S W mem LA l lines -> HA <= LA -> LA + 16 <= HA + ASRC ->
  (forall b, In b (alist_blks l) -> In b (asrc_blks h)) ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (HA <= a < HA + ASRC) \/ (exists b n, In (b, n) (asrc_blks h) /\ b <= a < b + req_size n)).
{ intros LA l lines HL H1 H2 Hb r' Hr' a' Ha'.
  destruct (gb_alist_fp_cls ly S W mem LA l lines HL r' Hr' a' Ha') as [Hl | (b & n & Hin & Hb')]; [left; lia|].
  right. exists b, n. split; [exact (Hb _ Hin) | exact Hb']. }
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Ha. exact Ha.
- right. unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gb_bzs_len' in Ha.
  exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (SUB (HA + 16) (hs_pending h) false Hpend _ _ _ r Hr a Ha); [unfold ASRC; lia | unfold ASRC; lia |].
    intros b Hb. unfold asrc_blks. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (SUB (HA + 64) (hs_expected h) true Hexp _ _ _ r Hr a Ha); [unfold ASRC; lia | unfold ASRC; lia |].
      intros b Hb. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * refine (SUB (HA + 80) (hs_held h) true Hheld _ _ _ r Hr a Ha); [unfold ASRC; lia | unfold ASRC; lia |].
      intros b Hb. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

Definition GBGO : list (Z * Z) := [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].

Lemma gb_aout_fp_cls : forall ly S W mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
inG (G_DR B RG) a \/ inG GBGO a \/ (exists b n, In (b, n) (aout_blks cap out) /\ b <= a < b + req_size n).
Proof.
intros ly S W mem c O mx no cap out HOUT r Hr a Ha.
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> inG (G_DR B RG) a)
  by (intros x l Hin Hx; unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
assert (GO : forall x l, In (x, l) GBGO -> x <= a < x + l -> inG GBGO a)
  by (intros x l Hin Hx; unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- right; left. apply (GO (rg_send_max RG) 8); [unfold GBGO; cbn; tauto | lia].
- left. apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; cbn; tauto | lia].
- left. apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; cbn; tauto | lia].
- left. apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; cbn; tauto | lia].
- right; left. apply (GO (rg_client RG) 4); [unfold GBGO; cbn; tauto | lia].
- left. apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; cbn; tauto | lia].
- right; left. apply (GO (rg_send_dead RG) 1); [unfold GBGO; cbn; tauto | lia].
- left. apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; cbn; tauto | lia].
- left. apply (GL (as_errno B) 4); [unfold G_DR, G_SL; cbn; tauto | lia].
- right; right. destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []].
  cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  exists out, cap. split; [unfold aout_blks; rewrite Hc0; left; reflexivity|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ============================================================================================
   (8) the relay entry after the add: the key list gains the new key (garr8 from the ASan view, and the
   invariant aentry_okx)
   ============================================================================================ *)
Definition gb_e2 (e : rentry) (k : Z * list byte * list byte) : rentry :=
RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e)
   (re_pad2 e) (re_keys e ++ [k]) (re_U e) (re_junk e).

Lemma gb_e2_nheld : forall e k, re_nheld (gb_e2 e k) = re_nheld e + 1.
Proof. intros e k. unfold re_nheld, gb_e2. cbn [re_keys]. rewrite length_app. cbn [length]. lia. Qed.

Lemma gb_e2_blks : forall e k, aentry_blks (gb_e2 e k) =
  aentry_blks e ++ [(key_addr k, Z.of_nat (length (key_text k)) + 1)].
Proof.
intros e k. unfold aentry_blks, gb_e2. cbn [re_cap re_buf re_hp re_kh re_keys]. rewrite map_app, !app_assoc.
reflexivity.
Qed.

Lemma gb_garr8_of_aview : forall (W : world SEGS) m base l,
(forall j, (j < length l)%nat -> aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0)) ->
garr8 SEGS (arm W m) base l.
Proof.
intros W m base l H j Hj.
destruct (aview_byte SEGS (w_H W) m (base + Z.of_nat j) (nth j l 0) (H j Hj)) as (b & Hb & Hv & Hr).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. unfold arm. rewrite Hb.
rewrite gb_le_byte1 by exact Hr. f_equal. rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma gb_aentry_okx_add : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e k,
aentry_okx B ly S W m e ->
re_hp e <> 0 -> re_kh e = 8 * re_nheld e + 8 -> re_nheld e + 1 < 2 ^ 26 ->
In (re_hp e, re_kh e) (ablocks B ly' S') ->
garr8 SEGS (arm W' m') (re_hp e) (bzs (key_ptrs (re_keys e ++ [k]))) ->
(re_cap e <> 0 -> In (re_buf e, re_cap e) (ablocks B ly' S') /\
   forall x, re_buf e <= x < re_buf e + re_cap e -> abyte_kept W m W' m' x) ->
(forall k0, In k0 (re_keys e) -> In (key_addr k0, Z.of_nat (length (key_text k0)) + 1) (ablocks B ly' S') /\
   forall x, key_addr k0 <= x < key_addr k0 + Z.of_nat (length (key_text k0)) + 1 -> abyte_kept W m W' m' x) ->
~ In (key_addr k) (map key_addr (re_keys e)) ->
~ In (key_text k) (map key_text (re_keys e)) ->
In (key_addr k, Z.of_nat (length (key_text k)) + 1) (ablocks B ly' S') ->
garr8 SEGS (arm W' m') (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])) ->
~ In (Z_to_bv 8 0) (key_text k) -> 14 <= Z.of_nat (length (key_text k)) <= APARTIAL ->
aentry_okx B ly' S' W' m' (gb_e2 e k).
Proof.
intros ly S W m ly' S' W' m' e k (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14)
  Hhp Hkh Hnh Hhin Hptr Hbuf Hkeys Hna Hnt Hkin Hkg Hk0 Hkl.
unfold aentry_okx. rewrite gb_e2_nheld. unfold gb_e2.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  destruct (Hbuf ltac:(lia)) as (Hin' & HK).
  split; [exact Hc|]. split; [exact Hin'|]. split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply HK. rewrite gb_bzs_len', length_app in Hx. lia. }
split; [lia|].
split.
{ right. split; [exact Hhp|]. split; [exact Hhin|]. split; [lia|].
  destruct H11 as [(Hz & _) | (_ & _ & _ & Hk8 & _)]; [contradiction|]. split; [exact Hk8 | exact Hptr]. }
split.
{ apply NoDup_ListNoDup. apply NoDup_ListNoDup in H12. rewrite map_app. cbn [map].
  apply (Permutation_NoDup (Permutation_cons_append _ _)). constructor; [exact Hna | exact H12]. }
split.
{ apply NoDup_ListNoDup. apply NoDup_ListNoDup in H13. rewrite map_app. cbn [map].
  apply (Permutation_NoDup (Permutation_cons_append _ _)). constructor; [exact Hnt | exact H13]. }
apply Forall_app. split.
- rewrite Forall_forall in H14 |- *. intros k0 Hk. destruct (H14 k0 Hk) as (K1 & K2 & K3).
  destruct (Hkeys k0 Hk) as (Hin' & HK).
  split; [exact Hin'|]. split; [|exact K3].
  apply (akept_garr8 W m); [|exact K2].
  intros x Hx. apply HK. rewrite gb_bzs_len', length_app in Hx. cbn [length] in Hx. lia.
- constructor; [|constructor]. split; [exact Hkin|]. split; [exact Hkg|]. split; [exact Hk0 | exact Hkl].
Qed.

(* ============================================================================================
   (9) the cut's memory core after the add (image A's lib/A/W_drain_feed.v df_dmem_rebuild, with the relay entry replaced)
   ============================================================================================ *)
Lemma gb_dmem : forall cx ly S W m md k e h s out ev sent LB ly' S' (W' : world SEGS) m' md' k' e' s',
DMEM B RG cx ly S W m md k e h s out ev sent LB ->
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' W' m' md' k' ->
rom_view SEGS (dxW cx) (dxmem cx) ->
apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
garr8 SEGS (arm W' m') (dxSA cx) (bzs (entry_bytes e')) -> awr W' m' (dxSA cx) AENT ->
aentry_okx B ly' S' W' m' e' ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W m W' m' a) ->
akept W m W' m' (asrc_fp (dHA RG cx) h) -> (forall b, In b (asrc_blks h) -> In b (ablocks B ly' S')) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
(forall b, In b (aout_blks (drain_b_c.ds_ocap s) out) -> In b (ablocks B ly' S')) ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e' ++ asrc_blks h ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM B RG cx ly' S' W' m' md' k' e' h s' out ev sent LB.
Proof.
intros cx ly S W m md k e h s out ev sent LB ly' S' W' m' md' k' e' s' HD Eno Eoc HJ' Hrom0 KP KF KS Hent' Hawr' Hokx'
  KG KA HAin KO HOin HP'.
destruct HD as (HJ & Hrom & Hpres & Hfr & HFR & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
unfold DMEM. rewrite Eno, Eoc.
split; [exact HJ'|].
split; [exact (ajournal_gx_rom_view SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HROMO Hrom0)|].
split; [intros a H1 H2 H3 H4; exact (KP a H1 H2 H3 (Hpres a H1 H2 H3 H4))|].
split; [rewrite KF; exact Hfr|].
split; [exact (gb_frame_kept cx W m W' m' KS HFR)|].
split; [exact Hent'|].
split; [exact Hawr'|].
split; [exact Hokx'|].
split.
{ apply (asrc_at_kept B ly S W m ly' S' W' m' (dHA RG cx) h Hsrc KA HAin). }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Vo). exists f, o.
  assert (KI : forall x, rg_s RG + ASRC * Z.of_nat i <= x < rg_s RG + ASRC * Z.of_nat i + 8 ->
    abyte_kept W m W' m' x).
  { intros x Hx. apply KG. unfold ASRC in *. lia. }
  split; [|split; [|exact Vo]]; (apply (akept_vm W m); [intros x Hx; apply KI; simpl Z.of_nat in Hx; lia|]);
  assumption. }
split.
{ intros x Hx1 Hx2. destruct (Hgsk x Hx1 Hx2) as [E1 P1]. destruct (KG x Hx1) as [E2 P2].
  split; [rewrite E2; exact E1 | intros Hw; exact (P2 (P1 Hw))]. }
split; [exact (aout_at_kept B RG ly S W m ly' S' W' m' _ _ _ _ _ _ Hout KO HOin)|].
split; [exact Hlive | exact HP'].
Qed.


Lemma gb_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof using. gb_clr0.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
assert (Hx : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (Hg _ Hx). unfold mrestrict in Hg. rewrite Hh in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.

Lemma gb_nth_skipn : forall (l : list Z) m j, nth j (skipn m l) 0 = nth (m + j) l 0.
Proof.
induction l as [|x l IH]; intros m j; [rewrite skipn_nil; destruct j, m; reflexivity|].
destruct m as [|m]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
(* ============================================================================================
   (10) the cut DLN (S q) at the line loop's head, from what the walk leaves
   ============================================================================================ *)
Lemma gb_dln : forall cx s1 D (p q jj : nat) regs1 ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl tl2
  a jb' o' ha' ks' regs3 ly2 S2 (W2 : world SEGS) m3 md3 res,
DBASE B MT MMAX RG cx ->
dregs_gs RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
re_hp e1 <> 0 -> re_kh e1 = 8 * re_nheld e1 + 8 ->
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None ->
GSF s1 p q ->
GARB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (GSno cx s1 p q) (GSoc cx s1 p q)
  (seen_arr (dlH cx s1 p) (dline s1 p q)) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (drlq s1 (S q)) jb' o' ha' ks' tl2 ->
tl = RelayRunT.RMalloc (Z.of_nat jj + 1) :: tl2 ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 W2 m3 md3 (k1 + 1) ->
ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, Z.of_nat jj + 1)] ->
frames S2 = frames S1 ->
mo_le MT S1 S2 (mo_malloc MT (Z.of_nat jj + 1)) ->
getr regs3 2 = getr regs1 2 -> getr regs3 3 = getr regs1 3 -> getr regs3 4 = getr regs1 4 ->
getr regs3 8 = getr regs1 8 -> getr regs3 9 = getr regs1 9 -> getr regs3 18 = getr regs1 18 ->
getr regs3 21 = w64 (dxSA cx) -> getr regs3 20 = w64 (dxSA cx + 16) ->
getr regs3 22 = w64 (dxSA cx + 24) -> getr regs3 27 = w64 (dxSA cx + 32) ->
getr regs3 23 = getr regs1 23 ->
val_mem SEGS (arm W2 m3) (dxSA cx + 40) 8 (re_hp e1) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 48) 4 (re_nheld e1 + 1) ->
val_mem SEGS (arm W2 m3) (re_hp e1 + 8 * re_nheld e1) 8 res ->
(forall x, dxG cx <= x < dxG cx + ATABLE -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x) ->
(forall x, re_hp e1 <= x < re_hp e1 + 8 * re_nheld e1 -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x) ->
(forall b n x, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) -> (b, n) <> (re_hp e1, re_kh e1) ->
   b <= x < b + req_size n -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, inG (G_DR B RG) x -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, inG GBGO x -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x) ->
apres_kept B W1 m1 W2 m3 ->
(forall i, 0 <= i < Z.of_nat jj ->
   aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)) ->
aview SEGS (w_H W2) m3 (res + Z.of_nat jj) = Some 0 ->
DLN B MT MMAX RG cx s1 D (S q) W2 (cfg_at SEGS (BASE + A_dr_next) regs3 m3 md3).
Proof.
intros cx s1 D p q jj regs1 ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl tl2 a jb' o' ha' ks' regs3 ly2 S2 W2 m3 md3 res
  HB HRL R23 Hbnd Hcap0 Hhp0 Hkh Hges Hjj Hidx HGSF HCORE HDLF Htl HJf Hbl2 Hfrm2 Hmle2
  P2 P3 P4 P8 P9 P18 P21 P20 P22 P27 P23 VHP VNH VSL KT KH KB KG KO KF KP KN KNUL.
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRSTART & HBUD).
pose proof HDMEM as (HJ & HROM & HPRES & HFRS & HFRAME & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HSA8 & HGARR & HAWR0 & HENT0 & HJ4 & HSRC0 & HOTH0 & HFD0 & HSK0 &
  HSKU0 & HOUT0 & HROM0 & HPERM0 & HPS0 & HEC0 & HNH0 & HTM0 & HTA0 & HMOK).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJf) as HARf.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HLL : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
(* the model after the line *)
destruct (gba_line cx s1 p q jj HGSF Hges Hidx) as (E1 & E2 & E3 & Ebd & Esq & L1 & L2 & L3 & L4).
destruct (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ 0 RelayRunF.adr0 [] Hges Hidx)
  as (Sarr & _ & Ska).
pose proof HGSF as (HBd & HPQ & HQ & HNZ & HK & HL).
pose proof HLINK as (Lcap & LU & Lskip & Lkeys & Lka & Leintr & Lpend & Loff & Lref & Len & Lecap & Lwf).
assert (HUW : bzs (re_U e1) = dW s1) by (rewrite LU; reflexivity).
assert (HUL : length (re_U e1) = length (dW s1)) by (rewrite <- HUW; rewrite gb_bzs_len; reflexivity).
assert (LK : drain_b_c.keys_texts (re_keys e1) = dlH cx s1 p) by (rewrite Lkeys; reflexivity).
(* the relay entry's blocks *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KFk).
destruct KHP as [(Hz & _) | (_ & Hhin1 & Hkh1 & Hkh8 & HKP)]; [exfalso; exact (Hhp0 Hz)|].
destruct KBUF as [(Hc0 & _ & _) | (Hcpos & Hbin & Hjunk & Hbuf8)].
{ exfalso. apply (f_equal (@length Z)) in HUW. rewrite gb_bzs_len in HUW. unfold re_used in *. lia. }
assert (Hreqkh : req_size (re_kh e1) = re_kh e1) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
assert (Hreqc : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
assert (HIN1 : forall bn, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
  aout_blks (drain_b_c.ds_ocap (dvirt cx s1 false (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
    (GSno cx s1 p q) (GSoc cx s1 p q))) out1 ++ dxrest cx) -> In bn (ablocks B ly1 S1))
  by (intros bn Hbn; apply (Permutation_in _ (Permutation_sym HPERM)); exact Hbn).
assert (HIN2 : forall bn, In bn (ablocks B ly1 S1) -> In bn (ablocks B ly2 S2))
  by (intros bn Hbn; rewrite Hbl2; apply in_or_app; left; exact Hbn).
pose proof (Permutation_NoDup HPERM (gb_ablocks_nodup ly1 S1 W1 m1 md1 HAR1)) as NDall.
apply NoDup_cons_iff in NDall. destruct NDall as (Hni & NDr).
destruct (gb_nd_app _ _ NDr) as (NDe & _ & Hde).
assert (HEB : aentry_blks e1 = (re_buf e1, re_cap e1) :: (re_hp e1, re_kh e1) ::
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
{ unfold aentry_blks. destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. destruct (Z.eqb_spec (re_hp e1) 0); [contradiction|].
  reflexivity. }
assert (NDe' := NDe). rewrite HEB in NDe'. apply NoDup_cons_iff in NDe' as (Hbn1 & NDe'').
apply NoDup_cons_iff in NDe'' as (Hhn1 & _).
(* a block of the source or the output is neither the table nor the held array *)
assert (HOTHB : forall bn, In bn (asrc_blks h1 ++ aout_blks (GSoc cx s1 p q) out1 ++ dxrest cx) ->
  In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE) /\ bn <> (re_hp e1, re_kh e1)).
{ intros bn Hbn. split; [apply HIN1; right; apply in_or_app; right; exact Hbn|].
  split; [intros Heq; apply Hni; rewrite <- Heq; apply in_or_app; right; exact Hbn|].
  intros Heq. apply (Hde (re_hp e1, re_kh e1)); [rewrite HEB; right; left; reflexivity | rewrite <- Heq; exact Hbn]. }
assert (Hnhb : re_nheld e1 + 1 < 2 ^ 26).
{ pose proof HHIST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
  unfold dvirt in D10. cbn [drain_b_c.ds_H] in D10.
  rewrite <- LK, gs_keys_texts_len in D10. unfold re_nheld. lia. }
(* the buffer bytes, as the ASan view reads them at GAR *)
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite (gb_garr8_aview W1 m1 (re_buf e1) _ j Hbuf8) by (rewrite gb_bzs_len, length_app; lia).
  rewrite gb_bzs_app, app_nth1 by (rewrite gb_bzs_len; lia). rewrite HUW. reflexivity. }
(* the new key: (res, the jj bytes of the line, no slack) *)
set (nk := (res, firstn jj (skipn p (re_U e1)), @nil byte)).
assert (HTX' : bzs (key_text nk) = firstn jj (skipn p (dW s1))).
{ unfold key_text, nk. cbn [fst snd]. rewrite <- HUW. unfold bzs. rewrite <- firstn_map, <- skipn_map. reflexivity. }
assert (HTX : bzs (key_text nk) = firstn jj (dline s1 p q)).
{ rewrite HTX'. unfold dline. rewrite firstn_firstn, Nat.min_l by lia. reflexivity. }
assert (HTL : length (key_text nk) = jj).
{ rewrite <- gb_bzs_len, HTX'. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
assert (HKA : key_addr nk = res) by reflexivity.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 res (Z.of_nat jj + 1) HARf
  ltac:(rewrite Hbl2; apply in_or_app; right; left; reflexivity)) as (_ & Hr4096 & Hrceil & _).
assert (Hreqr : req_size (Z.of_nat jj + 1) = Z.of_nat jj + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat jj + 1) 0); lia).
rewrite Hreqr in Hrceil.
set (e2 := gb_e2 e1 nk).
set (spent' := spent + (mo_malloc MT (Z.of_nat jj + 1) + mo_free MT)).
unfold DLN.
exists regs3, ly2, S2, m3, md3, (k1 + 1), e2, h1, out1, ev1, LB1, spent', jb', a, o', ha', ks', tl2.
split; [reflexivity|].
split; [exact (gb_dregs_line cx regs1 regs3 W1 m1 W2 m3 HRL P2 P3 P4 P8 P9 P18 P21 P20 P22 P27 KF)|].
split; [rewrite P23, R23; unfold e2, gb_e2; cbn [re_buf]; unfold w64; f_equal; lia|].
split; [unfold e2, gb_e2; cbn [re_buf re_cap]; exact Hbnd|].
split; [unfold e2, gb_e2; cbn [re_cap]; exact Hcap0|].
split; [exact Ebd|].
split; [exact Esq|].
split.
2:{ rewrite L1, L2, L3, L4. rewrite Sarr in HDLF. exact HDLF. }
unfold DLC, LCORE. cbv zeta. rewrite E1, E3, L1, L2, L3, L4.
split.
{ (* the memory core *)
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hhin1) as (_ & Hh4096 & Hhceil & _).
  rewrite Hreqkh in Hhceil.
  assert (Hbt : (re_buf e1, re_cap e1) <> (dxG cx, ATABLE))
    by (intros Heq; apply Hni; rewrite <- Heq; apply in_or_app; left; rewrite HEB; left; reflexivity).
  assert (Hbh : (re_buf e1, re_cap e1) <> (re_hp e1, re_kh e1))
    by (intros Heq; apply Hbn1; rewrite Heq; left; reflexivity).
  assert (Hbin1 : In (re_buf e1, re_cap e1) (aentry_blks e1)) by (rewrite HEB; left; reflexivity).
  apply (gb_dmem cx ly1 S1 W1 m1 md1 k1 e1 h1 _ out1 ev1 _ LB1 ly2 S2 W2 m3 md3 (k1 + 1) e2 _ HDMEM eq_refl eq_refl
    HJf HROM0 KP Hfrm2 KF).
  - apply (gb_entry_store W1 m1 W2 m3 (dxSA cx) e1 e2 Kp1 Kp2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl).
    + unfold e2, gb_e2. cbn [re_hp]. lia.
    + unfold e2. rewrite gb_e2_nheld. unfold re_nheld in *. lia.
    + exact HENT.
    + exact VHP.
    + unfold e2. rewrite gb_e2_nheld. exact VNH.
    + intros xx Hxx. apply KT; unfold AENT, ATABLE in *; lia.
    + intros xx Hxx. apply KT; unfold AENT, ATABLE in *; lia.
  - intros i Hi. apply (apresent_writable SEGS).
    destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 _ _ HARf (HIN2 _ HGin1)) as (_ & _ & _ & _ & Hp & _).
    rewrite RQT in Hp. exact (proj1 (Hp (dxSA cx + i) ltac:(unfold AENT, ATABLE in *; lia))).
  - apply (gb_aentry_okx_add ly1 S1 W1 m1 ly2 S2 W2 m3 e1 nk HOKX Hhp0 Hkh Hnhb (HIN2 _ Hhin1)).
    + apply (gb_ptrs_app W1 m1 W2 m3 (re_hp e1) (re_keys e1) nk); [rewrite HKA; lia | exact HKP | |].
      * unfold re_nheld in VSL. rewrite HKA. exact VSL.
      * intros xx Hxx. apply KH. unfold re_nheld. exact Hxx.
    + intros _. split; [apply HIN2, HIN1; right; apply in_or_app; left; exact Hbin1|].
      intros xx Hxx. apply (KB (re_buf e1) (re_cap e1) xx (HIN1 _ (or_intror (in_or_app _ _ _ (or_introl Hbin1)))) Hbt Hbh).
      rewrite Hreqc. exact Hxx.
    + intros k0 Hk0.
      assert (Hk0b : In (key_addr k0, Z.of_nat (length (key_text k0)) + 1) (aentry_blks e1))
        by (rewrite HEB; right; right; apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk0).
      split; [apply HIN2, HIN1; right; apply in_or_app; left; exact Hk0b|].
      intros xx Hxx. apply (KB _ _ xx (HIN1 _ (or_intror (in_or_app _ _ _ (or_introl Hk0b))))).
      * intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. exact Hk0b.
      * intros Heq. apply Hhn1. rewrite <- Heq.
        apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk0.
      * pose proof (req_size_pos (Z.of_nat (length (key_text k0)) + 1) ltac:(lia)) as (_ & Hrq). lia.
    + rewrite HKA. intros Hin. apply in_map_iff in Hin as (k0 & Hk0a & Hk0).
      rewrite Forall_forall in KFk. destruct (KFk k0 Hk0) as (Hkb & _).
      pose proof (gb_new_disj ly2 S2 W2 m3 md3 ly1 S1 res _ _ _ HARf Hbl2 Hkb) as Dn.
      pose proof (req_size_pos (Z.of_nat (length (key_text k0)) + 1) ltac:(lia)) as (Hr1 & _).
      pose proof (req_size_pos (Z.of_nat jj + 1) ltac:(lia)) as (Hr2 & _). lia.
    + intros Hin. apply in_map_iff in Hin as (k0 & Hk0t & Hk0).
      apply (index_of_none _ _ Hidx). rewrite <- LK, <- HTX, <- Hk0t. unfold drain_b_c.keys_texts.
      apply (in_map (fun k => bzs (key_text k))). exact Hk0.
    + rewrite HKA, HTL, Hbl2. apply in_or_app. right. left. reflexivity.
    + rewrite HKA. apply gb_garr8_of_aview. intros j Hj. rewrite gb_bzs_app in Hj |- *.
      rewrite length_app, gb_bzs_len, HTL in Hj. cbn [length bzs map] in Hj.
      destruct (Nat.lt_ge_cases j jj) as [Hlt | Hge].
      * rewrite app_nth1 by (rewrite gb_bzs_len, HTL; exact Hlt). rewrite HTX', gsx_nth_firstn by exact Hlt.
        rewrite gb_nth_skipn. rewrite (KN (Z.of_nat j) ltac:(lia)).
        replace (re_buf e1 + Z.of_nat p + Z.of_nat j) with (re_buf e1 + Z.of_nat (p + j)) by lia. apply BV. lia.
      * assert (j = jj) as -> by lia. rewrite app_nth2 by (rewrite gb_bzs_len, HTL; lia).
        rewrite gb_bzs_len, HTL, Nat.sub_diag. change (bzs [Z_to_bv 8 0]) with [bz (Z_to_bv 8 0)]. cbn [nth].
        rewrite gb_bz_bv8. change (0 mod 256) with 0. exact KNUL.
    + intros Hin. apply (in_map bz) in Hin. change (map bz (key_text nk)) with (bzs (key_text nk)) in Hin.
      rewrite HTX, gb_bz_bv8 in Hin. change (0 mod 256) with 0 in Hin.
      pose proof (gs_dline_nz s1 p q HNZ) as Hnz. unfold nozero in Hnz. rewrite Forall_forall in Hnz.
      apply (Hnz 0); [rewrite <- (firstn_skipn jj (dline s1 p q)); apply in_or_app; left; exact Hin | reflexivity].
    + rewrite HTL. unfold APARTIAL. lia.
  - intros xx Hxx. apply KG. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros r Hr xx Hxx. destruct (gb_asrc_fp_cls ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r Hr xx Hxx) as [Hg | (b & n & Hin & Hbx)].
    + apply KG. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr, dHA in *. cbn [fst snd]. unfold ASRC in *. lia.
    + destruct (HOTHB (b, n) ltac:(apply in_or_app; left; exact Hin)) as (H1 & H2 & H3). exact (KB b n xx H1 H2 H3 Hbx).
  - intros bn Hbn. apply HIN2. exact (proj1 (HOTHB bn (in_or_app _ _ _ (or_introl Hbn)))).
  - intros r Hr xx Hxx. destruct (gb_aout_fp_cls ly1 S1 W1 m1 _ _ _ _ _ _ HOUT r Hr xx Hxx) as [Hg | [Hg | (b & n & Hin & Hbx)]];
      [exact (KG xx Hg) | exact (KO xx Hg) |].
    destruct (HOTHB (b, n) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin)) as (H1 & H2 & H3).
    exact (KB b n xx H1 H2 H3 Hbx).
  - intros bn Hbn. apply HIN2. exact (proj1 (HOTHB bn ltac:(apply in_or_app; right; apply in_or_app; left; exact Hbn))).
  - unfold e2. rewrite gb_e2_blks, Hbl2, HKA, HTL.
    eapply Permutation_trans; [apply Permutation_app_tail; exact HPERM|].
    cbn [app]. apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
    apply Permutation_sym. rewrite !app_assoc. apply Permutation_cons_append. }
split.
{ refine (conj Lcap (conj LU (conj Lskip (conj _ (conj Lka (conj Leintr (conj Lpend (conj Loff (conj Lref
    (conj Len (conj Lecap Lwf))))))))))).
  unfold e2, gb_e2. cbn [re_keys dvirt drain_b_c.ds_H]. rewrite gs_keys_texts_app, LK, HTX. reflexivity. }
split; [exact HSAME|].
split; [exact (gba_hist cx s1 D p q jj h1 LB1 _ HGSF Hges Hidx HHIST)|].
split; [exact HRSTART|].
pose proof HBUD as (Hle0 & Hsp0 & Hcost & Halloc & Hmax).
pose proof (mo_free_nonneg MT MTL) as Hf. pose proof (mo_malloc_nonneg MT MTL (Z.of_nat jj + 1) ltac:(lia)) as Hm.
unfold tr_cost in Hcost. unfold tr_max in Hmax. rewrite Htl in Hcost, Halloc, Hmax.
(* C3: strndup's one request RMalloc (jj + 1) opens the trace still owed (W_tr_peak.v tr_peak_malloc) *)
rewrite W_tr_peak.tr_peak_malloc in Halloc.
cbn [fold_right] in Hcost, Hmax.
unfold dbud. split.
{ apply (mle_weaken MT _ _ (spent + mo_malloc MT (Z.of_nat jj + 1)) _ MTL);
    [exact (mle_station MT (dxS cx) S1 S2 spent _ MTL Hle0 Hmle2) | unfold spent'; lia]. }
split; [unfold spent'; lia|].
split; [unfold spent', tr_cost; lia|].
split.
{ rewrite (blocks_bytes_bsum B ly2 S2), Hbl2, bsum_app, <- (blocks_bytes_bsum B ly1 S1). cbn [bsum fold_right snd].
  lia. }
unfold tr_max. lia.
Qed.

(* ============================================================================================
   THE SEGMENT
   ============================================================================================ *)
Theorem gs_addb : gs_addb_stmt B MT MMAX RG.
Proof.
unfold gs_addb_stmt. intros cx s1 D p q W1 c1 HB HGAR HN.
destruct HGAR as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & a & tl & jj &
  Hc1 & HRL & R27 & R23 & R24 & R19 & V16 & V192 & Hbnd & Hcap0 & Hhp0 & Hkh & HGARW & HROM1 & Hges & Hjj & Hidx &
  HGSF & HCORE & HFUT).
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRSTART & HBUD).
pose proof HDMEM as (HJ & HROM & HPRES & HFRS & HFRAME & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
pose proof HRL as (Usp & R3 & R4 & R8 & R9 & R18 & HFR2).
pose proof HFR2 as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 &
  F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & FSV).
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HSA8 & HGARR & HAWR0 & HENT0 & HJ4 & HSRC0 & HOTH0 & HFD0 & HSK0 &
  HSKU0 & HOUT0 & HROM0 & HPERM0 & HPS0 & HEC0 & HNH0 & HTM0 & HTA0 & HMOK).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
pose proof (ajournal_gx_AR SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 HJ) as HAR1.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK = 16880) by reflexivity.
assert (WF : DRAIN_FRAME = 352) by reflexivity.
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGapp, HGpres.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in HGle; lia).
assert (HSAhi : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
(* the relay entry's fields; the held array is the grown block *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KF).
clear K1 K2 K6.
assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
destruct KHP as [(Hz & _) | (_ & Hhin1 & Hkh1 & Hkh8 & HKP)]; [exfalso; exact (Hhp0 Hz)|].
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hhin1) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _).
assert (Hreqkh : req_size (re_kh e1) = re_kh e1) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
rewrite Hreqkh in Hhceil, Hhapp, Hhpres.
assert (Hhp8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite Hh16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }

(* ---- the model at the cut ---- *)
pose proof HGSF as (HBd & HPQ & HQ & HNZ & HK & HL).
pose proof HLINK as (Lcap & LU & Lskip & Lkeys & Lka & Leintr & Lpend & Loff & Lref & Len & Lecap & Lwf).
assert (HUW : bzs (re_U e1) = dW s1) by (rewrite LU; reflexivity).
assert (HUL : length (re_U e1) = length (dW s1)) by (rewrite <- HUW; rewrite gb_bzs_len; reflexivity).
assert (Hdwlen : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HUL; exact K7).
destruct KBUF as [(Hc0 & _ & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hbin) as (HB16 & HB4096 & HBceil & HBapp & HBpres & _).
assert (Hreqc : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite Hreqc in HBceil, HBapp, HBpres.
assert (Hlen : length (dline s1 p q) = (q - p)%nat) by (apply gs_dline_len; lia).
assert (Hlx : length (firstn jj (dline s1 p q)) = jj) by (apply firstn_length_le; lia).
destruct HFUT as (tl2 & jb' & o' & ha' & ks' & HDLF & Htl & Hcost2 & Halloc2).
rewrite Hlx in Htl.
pose proof HBUD as (Hle0 & Hsp0 & Hcost & Halloc & Hmax).
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite (gb_garr8_aview W1 m1 (re_buf e1) _ j Hbuf8) by (rewrite gb_bzs_len, length_app; lia).
  rewrite gb_bzs_app, app_nth1 by (rewrite gb_bzs_len; lia). rewrite HUW. reflexivity. }
(* the blocks of the entry, the source and the output are distinct from the table and from one another *)
pose proof (Permutation_NoDup HPERM (gb_ablocks_nodup ly1 S1 W1 m1 md1 HAR1)) as NDall.
apply NoDup_cons_iff in NDall. destruct NDall as (Hni & NDr).
destruct (gb_nd_app _ _ NDr) as (NDe & _ & Hde).
assert (HEB : aentry_blks e1 = (re_buf e1, re_cap e1) :: (re_hp e1, re_kh e1) ::
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
{ unfold aentry_blks. destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. destruct (Z.eqb_spec (re_hp e1) 0); [contradiction|].
  reflexivity. }
(* the held array is not the relay table's block *)
assert (Hhne : (re_hp e1, re_kh e1) <> (dxG cx, ATABLE)).
{ intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. unfold aentry_blks. apply in_or_app. right.
  apply in_or_app. left. destruct (Z.eqb_spec (re_hp e1) 0); [contradiction | left; reflexivity]. }
pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 Hhin1 HGin1 Hhne) as Dht.
unfold zdisjoint in Dht. cbn [fst snd] in Dht. rewrite Hreqkh, RQT in Dht.
change (gb_sep (re_hp e1 + re_kh e1) (dxG cx) (dxG cx + 896) (re_hp e1)) in Dht.
(* the buffer is neither the table nor the held array *)
assert (Hbt : (re_buf e1, re_cap e1) <> (dxG cx, ATABLE)).
{ intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. rewrite HEB. left. reflexivity. }
assert (Hbh : (re_buf e1, re_cap e1) <> (re_hp e1, re_kh e1)).
{ intros Heq. rewrite HEB in NDe. apply NoDup_cons_iff in NDe as [Hn _]. apply Hn. rewrite Heq. left. reflexivity. }
pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 Hbin HGin1 Hbt) as Dbt.
pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 Hbin Hhin1 Hbh) as Dbh.
unfold zdisjoint in Dbt, Dbh. cbn [fst snd] in Dbt, Dbh. rewrite Hreqc, RQT in Dbt. rewrite Hreqc, Hreqkh in Dbh.
change (gb_sep (re_buf e1 + re_cap e1) (dxG cx) (dxG cx + 896) (re_buf e1)) in Dbt.
change (gb_sep (re_buf e1 + re_cap e1) (re_hp e1) (re_hp e1 + re_kh e1) (re_buf e1)) in Dbh.
(* the frame base *)
assert (R2 : getr regs1 2 = w64 (dsp0 cx - DRAIN_FRAME)).
{ unfold w64. rewrite <- Usp. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hsp46 : 2 ^ 46 <= dsp0 cx - DRAIN_FRAME) by (rewrite WF; lia).
assert (Hsp47 : dsp0 cx - DRAIN_FRAME + 352 <= 2 ^ 47) by (rewrite WF; lia).
assert (Hsp16 : (dsp0 cx - DRAIN_FRAME) mod 16 = 0) by (rewrite WF, Zminus_mod, Hal16; reflexivity).
(* the two cells of the entry *)
assert (VH40 : val_mem SEGS (arm W1 m1) (dxSA cx + 40) 8 (re_hp e1))
  by (apply (gb_entry_hp W1 m1 _ e1 Kp1 ltac:(lia) HENT)).
assert (VH48 : val_mem SEGS (arm W1 m1) (dxSA cx + 48) 4 (re_nheld e1))
  by (apply (gb_entry_nheld W1 m1 _ e1 Kp1 ltac:(lia) HENT)).
assert (HW1 : forall oo, 48 <= oo < 52 -> writable_at SEGS (arm W1 m1) (dxSA cx + oo))
  by (intros oo Hoo; apply HAWR; unfold AENT; lia).
assert (HW2 : forall oo, 0 <= oo < 8 -> writable_at SEGS (arm W1 m1) (re_hp e1 + 8 * re_nheld e1 + oo)).
{ intros oo Hoo. apply (apresent_writable SEGS). exact (proj1 (Hhpres (re_hp e1 + 8 * re_nheld e1 + oo) ltac:(lia))). }
(* the seat *)
assert (HLL : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
assert (Hjj26 : 0 <= Z.of_nat jj <= 2 ^ 26) by lia.
pose proof (gb_seat W1 regs1 m1 (dxSA cx) (dsp0 cx - DRAIN_FRAME) (re_hp e1) (re_nheld e1) (Z.of_nat jj)
  R2 R19 HSAlo ltac:(unfold gb_ceil; lia) HSA8 Hh4096 ltac:(unfold gb_ceil; lia) Hhp8 ltac:(lia) Hjj26
  Hsp46 Hsp47 Hsp16 ltac:(rewrite WF; lia) ltac:(rewrite WF; lia) ltac:(unfold gb_sep in Dht; unfold AENT, ATABLE in *; lia)
  V16 F32 F88 F128 F136 F144 V192 F240 VH40 VH48 HW1 HW2) as HS.
remember (Eimg (Ereg regs1 (gb_extra (dxSA cx) (re_hp e1) (re_nheld e1) (Z.of_nat jj)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs1 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = w64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = w64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = w64 (re_hp e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = w64 (re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = w64 (re_hp e1 + 8 * re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = w64 (Z.of_nat jj))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
clear HE.
assert (E2 : ew E 2 = w64 (dsp0 cx - DRAIN_FRAME)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E3 : ew E 3 = getr regs1 3) by exact (EA 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs1 4) by exact (EA 4%nat ltac:(lia)).
assert (E8 : ew E 8 = w64 (rg_s RG)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E24 : ew E 24 = w64 (re_buf e1 + Z.of_nat p)) by exact (eq_trans (EA 24%nat ltac:(lia)) R24).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = re_hp e1 + 8 * re_nheld e1) by (rewrite E36; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS gb_Bx gb_SH E (mrestrict (w_H W1) m1)).
{ apply (gb_shok E ly1 S1 W1 m1 md1 (dxG cx) (dxSA cx) (re_hp e1) (re_kh e1) (re_nheld e1) HAR1 HGin1 HGle HSAle
    Hhin1 Hnh0 ltac:(rewrite Hreqkh; lia) E33 E32 E36). }
subst c1. unfold cfg_at.
(* run 1: 0x83c00 .. the jal to strndup at 0x83c08 *)
paj_run_tok RUN HS HJ SHOK gb_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U36 in Ha.
  left. split; [|lia].
  replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply HGARW; [exact Hhin1 | rewrite Hreqkh; lia]. }
rename HFr into HFr1, HG0 into HGr1. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms1)) |- _ => rename Hg into GR1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
(* the run wrote nothing outside its two windows *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * re_nheld e1 <= x < re_hp e1 + 8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W1) (ms_mem ms1) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_gb gb_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi gb_frame gb_sa gb_slot base_val] in Hr;
    rewrite ?U32, ?U36 in Hr; lia. }
assert (HARm : AR SEGS B ly1 S1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR; exact HJ).
(* strndup (e->buf + p, jj) *)
set (x := re_buf e1 + Z.of_nat p).
assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
assert (G3 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, E3, R3; exact Hgp).
assert (G4 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, E4, R4; exact Htp).
assert (G10 : getr (ms_regs ms1) 10 = w64 x) by (rewrite Q10, E24; reflexivity).
assert (G11 : getr (ms_regs ms1) 11 = w64 (Z.of_nat jj)) by (rewrite Q11, E37; reflexivity).
assert (NZ : forall i, 0 <= i < Z.of_nat jj -> exists b, aview SEGS (w_H W1) (ms_mem ms1) (x + i) = Some b /\ b <> 0).
{ intros i Hi. exists (nth (p + Z.to_nat i) (dW s1) 0).
  assert (Hidx' : (p + Z.to_nat i < length (dW s1))%nat) by lia.
  split.
  - rewrite KEEP1 by (unfold gb_sep in Dbt, Dbh; unfold x, AENT, ATABLE in *; lia).
    replace (x + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by (unfold x; lia).
    apply BV. exact Hidx'.
  - intros H0. apply (HNZ (p + Z.to_nat i)%nat ltac:(lia)). rewrite (nth_error_nth' (dW s1) 0 Hidx'). rewrite H0.
    reflexivity. }
assert (Hlive : blocks_bytes S1 + (Z.of_nat jj + 1) <= LIVE_MAX).
{ pose proof (W_tr_peak.tr_peak_nonneg tl2) as Hnn. rewrite Htl, W_tr_peak.tr_peak_malloc in Halloc. lia. }
assert (Hmok : mo_ok MT S1 (mo_malloc MT (Z.of_nat jj + 1))).
{ pose proof (mo_free_nonneg MT MTL) as Hf.
  unfold tr_cost in Hcost, Hcost2. rewrite Htl in Hcost. cbn [fold_right] in Hcost.
  apply (mok_station MT (dxS cx) S1 _ spent _ MTL HMOK Hle0); [apply (mo_malloc_nonneg MT MTL); lia | lia]. }
assert (HSTK0 : 0 <= DRAIN_STK) by lia.
destruct HJ as (HSTK1 & HXO1 & (memS1 & HJi1 & HAG1) & HOUT1). rewrite !Z.add_0_r in HJi1.
eapply SRr_bind.
{ eapply (ASTRNDUP W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS1
    (dxmd cx) [] ly1 S1 _ k1 x (Z.of_nat jj) (- DRAIN_FRAME) _ [] HJi1 G10 G11).
  - unfold x. lia.
  - lia.
  - unfold x. lia.
  - unfold tr_max in Hmax. rewrite Htl in Hmax. cbn [fold_right] in Hmax. lia.
  - exact Hlive.
  - exact NZ.
  - intros aa Ha. unfold x in Ha. unfold ASTACK. lia.
  - apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1)); [exact HARm | exact Hbin | unfold x; lia |].
    rewrite Hreqc. unfold x. lia.
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1));
      [exact HARm | exact Hbin | unfold x; lia | rewrite Hreqc; unfold x; lia].
  - intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1));
      [exact HARm | exact Hbin | unfold x; lia | rewrite Hreqc; unfold x; lia | exact Hpos].
  - rewrite Usp1. lia.
  - rewrite WF. reflexivity.
  - rewrite WF. lia.
  - rewrite WF, WS. unfold ASTACK. lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof HGSB as (Hg1 & Hg2 & _).
    apply (achain_chain_pre ly1 _ (spZ (ms_regs ms1)) (s0Z (ms_regs ms1)) [] (ms_regs ms1)).
    + apply achain_low. unfold s0Z. rewrite Q8, E8. unfold w64.
      rewrite unsigned_lit_small by (unfold ASRC, IMG_TOP in *; lia). unfold ASRC, IMG_TOP in *. lia.
    + rewrite Usp1. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - unfold raZ. cbn [spine map]. rewrite Q1. rewrite unsigned_lit_small by lia.
    match goal with |- In [?x] _ => replace x with (BASE + AF_fr_drain + 0x994) by (unfold AF_fr_drain; lia) end.
    exact HCTX_sd.
  - exact Hmok. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres10 & Hfrm2 & Hres4096 &
  Hbl2 & Hcpy & Hnul & Hkept2 & Hmle2 & Herr2 & Hpres2).
pose proof (proj1 HJ2i) as HAR2.
assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact HGin1).
assert (Hhin2 : In (re_hp e1, re_kh e1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hhin1).
assert (Hrin2 : In (res, Z.of_nat jj + 1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hreqr : req_size (Z.of_nat jj + 1) = Z.of_nat jj + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat jj + 1) 0); lia).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hrin2) as (Hr16 & _ & Hrceil & Hrapp & Hrpres & _).
rewrite Hreqr in Hrceil, Hrapp, Hrpres.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HGin2) as (_ & _ & _ & _ & HGpres2 & _).
rewrite RQT in HGpres2.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hhin2) as (_ & _ & _ & _ & Hhpres2 & _).
rewrite Hreqkh in Hhpres2.
pose proof (gb_new_disj ly2 S2 W2 mem2 md2 ly1 S1 res _ _ _ HAR2 Hbl2 HGin1) as DnG. rewrite RQT, Hreqr in DnG.
pose proof (gb_new_disj ly2 S2 W2 mem2 md2 ly1 S1 res _ _ _ HAR2 Hbl2 Hhin1) as Dnh. rewrite Hreqkh, Hreqr in Dnh.
change (gb_sep (dxG cx + 896) res (res + (Z.of_nat jj + 1)) (dxG cx)) in DnG.
change (gb_sep (re_hp e1 + re_kh e1) res (res + (Z.of_nat jj + 1)) (re_hp e1)) in Dnh.
destruct Hkept2 as (KS2 & KB2 & KI2 & KF2 & KP2 & KSP2).
(* the symbolic state after the call: the three regions are kept *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?E2, ?U32, ?U36.
  - rewrite unsigned_lit_small by lia. intros aa Ha. apply (mbyte_of_aview SEGS). apply KS2; [lia|]. unfold ASTACK. lia.
  - rewrite unsigned_lit_small by lia. intros aa Ha. lia.
  - intros aa Ha. apply (mbyte_of_aview SEGS).
    replace aa with (dxG cx + (aa - dxG cx)) by lia. apply (KB2 _ _ _ HGin1); [rewrite RQT; unfold AENT, ATABLE in *; lia|].
    cbv beta. rewrite Hreqr. unfold gb_sep in DnG. unfold AENT, ATABLE in *. lia.
  - intros aa Ha _. apply (apresent_writable SEGS). exact (proj1 (HGpres2 aa ltac:(unfold AENT, ATABLE in *; lia))).
  - intros aa Ha. apply (mbyte_of_aview SEGS).
    replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply (KB2 _ _ _ Hhin1); [rewrite Hreqkh; lia|].
    cbv beta. rewrite Hreqr. unfold gb_sep in Dnh. lia.
  - intros aa Ha _. apply (apresent_writable SEGS). exact (proj1 (Hhpres2 aa ltac:(lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea44 : ew Ea 44 = w64 res) by (rewrite HEa; exact Hres10).
clear HEa.
assert (HFa : afact_ok Ea 44 (mkAF 4096 gb_ceil 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea44. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite Hr16. unfold gb_ceil. lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 44%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ2 : ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1)).
{ apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
    (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 1) memS1); [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG1 | apply out_none]. }
assert (U32a : bv_unsigned (ew Ea 32) = dxSA cx) by (rewrite OLDa by lia; exact U32).
assert (U36a : bv_unsigned (ew Ea 36) = re_hp e1 + 8 * re_nheld e1) by (rewrite OLDa by lia; exact U36).
assert (SHOK2 : sh_ok SEGS gb_Bx gb_SH Ea (mrestrict (w_H W2) mem2)).
{ apply (gb_shok Ea ly2 S2 W2 mem2 md2 (dxG cx) (dxSA cx) (re_hp e1) (re_kh e1) (re_nheld e1) HAR2 HGin2 HGle HSAle
    Hhin2 Hnh0 ltac:(rewrite Hreqkh; lia)); rewrite OLDa by lia; assumption. }
(* run 2a: 0x83c0c .. the PTR_SOVF check at 0x83c74.  On the way the runner decides strndup's NULL arm
   (0x83c0c, the result atom's fact), the shadow checks of &e->nheld / &e->held (shadow entry over the entry),
   the ADDW1 trap 0x83c28 (nheld is an int32-safe atom) and the NULL_BEQ trap 0x83c60 (held and the slot are
   pointer atoms), and stores e->nheld = nheld + 1 (0x83c5c). *)
paj_run_tok RUN HS HJ2 SHOK2 gb_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U32a, ?U32b in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U36a, ?U36b in Ha.
  left. split; [|lia].
  replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply HGARW; [exact Hhin2 | rewrite Hreqkh; lia]. }
rename HFr into HFr2, HG0 into HGr2. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
match goal with Hg : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms2)) |- _ => rename Hg into GR2 end.
(* run 2a makes no fresh atom: the state after it is still over Ea *)
lazymatch type of HS with st_ok_pi _ _ Ea _ _ => idtac | _ => fail "gs_addb: run 2a changed the environment" end.
(* 0x83c74, PTR_SOVF (W_drain_cx.v census row GS 0x83c74): slti nheld,0 is folded to 0 by nheld's fact; the
   sltu slot, held compares two atoms the runner does not order (lib/B/W_traps.v R5), so the trap edge is closed
   by trap_ptr_sovf with trap_U_sltu_ge: the slot hp + 8 nh is not below hp *)
psrr_branch_tok RUN BR HS SHOK2 gb_Bspan; rename Hc into BZ.
{ exfalso.
  assert (Uh : U Ea (SOff 34 0) = re_hp e1)
    by (apply (U_atom Ea 34); [rewrite OLDa by lia; exact E34 | lia]).
  assert (Us : U Ea (SOff 36 0) = re_hp e1 + 8 * re_nheld e1)
    by (apply (U_atom Ea 36); [rewrite OLDa by lia; exact E36 | lia]).
  rewrite (trap_ptr_sovf Ea _ _ 0 (trap_U_sltu_ge Ea _ _ _ _ Uh Us ltac:(lia)) (U_lit Ea 0 ltac:(lia))) in BZ.
  discriminate. }
(* run 2b: 0x83c78 .. the line loop's head 0x839d4: NONNULL 0x83c78 and ALIGN8 0x83c80 decided (R1 / R2), the
   slot's shadow byte covered (0x83c90), s5 / s6 / s4 reloaded from 144 / 136 / 128 (sp), the slot gets res *)
paj_run_to_tok RUNTO HS HJ2 SHOK2 gb_Bspan A_dr_next.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U32a, ?U32a in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U36a, ?U36a in Ha.
  left. split; [|lia].
  replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply HGARW; [exact Hhin2 | rewrite Hreqkh; lia]. }
rename HFr into HFr3. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
match goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms2)) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hg into GR3 end.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARf.
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (27%bv : bv 5) P27.
assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs ms3) r = ew Ea k -> (k < 32)%nat ->
  ew E k = getr regs1 r -> getr (ms_regs ms3) r = getr regs1 r).
{ intros r k Hr Hk Hek. rewrite Hr. rewrite (OLDa k) by lia. exact Hek. }
assert (P21' : getr (ms_regs ms3) 21 = w64 (dxSA cx)).
{ rewrite P21. rewrite (OLDa 32%nat) by lia. exact E32. }
assert (P22' : getr (ms_regs ms3) 22 = w64 (dxSA cx + 24)) by (rewrite P22, U32a; reflexivity).
assert (P20' : getr (ms_regs ms3) 20 = w64 (dxSA cx + 16)) by (rewrite P20, U32a; reflexivity).
assert (P27' : getr (ms_regs ms3) 27 = w64 (dxSA cx + 32)).
{ rewrite P27. rewrite (OLDa 27%nat) by lia.
  rewrite (EA 27%nat ltac:(lia)). exact R27. }
(* the two cells and the slot the runs wrote *)
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSA.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RSL.
cbn [ms_mem restrict] in RSA, RSL.
assert (VHP : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (dxSA cx + 40) (N.to_nat 8) (re_hp e1)).
{ eapply (field_of_region Ea _ 32 (dxSA cx));
    [exact RSA | exact U32a | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  apply den_atom0; [rewrite OLDa by lia; exact E34 | lia]. }
assert (VNH : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (dxSA cx + 48) (N.to_nat 4) (re_nheld e1 + 1)).
{ eapply (field_of_region Ea _ 32 (dxSA cx));
    [exact RSA | exact U32a | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  apply (den_atom Ea 35 (re_nheld e1) 1); [rewrite OLDa by lia; exact E35 | lia | lia]. }
assert (VSL : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (re_hp e1 + 8 * re_nheld e1 + 0) (N.to_nat 8) res).
{ eapply (field_of_region Ea _ 36 (re_hp e1 + 8 * re_nheld e1));
    [exact RSL | exact U36a | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  apply den_atom0; [exact Ea44 | lia]. }
rewrite Z.add_0_r in VSL.
(* what the two runs kept: everything outside their two windows *)
assert (K3 : forall xx, 0 <= xx < 2 ^ 64 -> ~ (dxSA cx + 48 <= xx < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * re_nheld e1 <= xx < re_hp e1 + 8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W2) mem2 xx).
{ intros xx Hx H1 H2.
  rewrite (aview_kept_out Ea _ (w_H W2) (ms_mem ms2) (ms_mem ms3) HFr3 xx Hx).
  - apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms2) HFr2 xx Hx). apply gb_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U32a, ?U36a; lia.
  - apply gb_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U32a, ?U36a; lia. }
assert (GR23 : forall xx, apresent (w_H W2) mem2 xx -> apresent (w_H W2) (ms_mem ms3) xx)
  by (intros xx Hp; apply (gb_apresent_grows _ (ms_mem ms2) _ _ GR3); exact (gb_apresent_grows _ mem2 _ _ GR2 Hp)).
(* the view of an old block's byte outside the two windows is the view at GAR *)
assert (KVB : forall b n xx, In (b, n) (ablocks B ly1 S1) -> b <= xx < b + req_size n ->
  ~ (dxSA cx + 48 <= xx < dxSA cx + 52) -> ~ (re_hp e1 + 8 * re_nheld e1 <= xx < re_hp e1 + 8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
{ intros b n xx Hin Hx H1 H2.
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 b n HAR1 Hin) as (_ & Hb4 & Hbc & _).
  pose proof (gb_new_disj ly2 S2 W2 mem2 md2 ly1 S1 res _ _ _ HAR2 Hbl2 Hin) as Dn. rewrite Hreqr in Dn.
  rewrite K3 by lia.
  replace xx with (b + (xx - b)) by lia.
  rewrite (KB2 b n (xx - b) Hin ltac:(lia)) by (cbv beta; rewrite Hreqr; lia).
  replace (b + (xx - b)) with xx by lia. apply KEEP1; lia. }
assert (KT : forall xx, dxG cx <= xx < dxG cx + ATABLE -> ~ (dxSA cx + 48 <= xx < dxSA cx + 52) ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
{ intros xx Hx H1. apply (KVB (dxG cx) ATABLE xx HGin1); [rewrite RQT; unfold ATABLE in Hx; lia | exact H1 |].
  unfold gb_sep in Dht. unfold ATABLE in *. lia. }
assert (KH : forall xx, re_hp e1 <= xx < re_hp e1 + 8 * re_nheld e1 ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
{ intros xx Hx. apply (KVB (re_hp e1) (re_kh e1) xx Hhin1);
    [rewrite Hreqkh; lia | unfold gb_sep in Dht; unfold AENT, ATABLE in *; lia | lia]. }
assert (KB : forall b n xx, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) ->
  (b, n) <> (re_hp e1, re_kh e1) -> b <= xx < b + req_size n -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros b n xx Hin Hn1 Hn2 Hx.
  pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 b n _ _ HAR1 Hin HGin1 Hn1) as D1.
  pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 b n _ _ HAR1 Hin Hhin1 Hn2) as D2.
  unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2. rewrite RQT in D1. rewrite Hreqkh in D2.
  split.
  - apply (KVB b n xx Hin Hx); unfold AENT, ATABLE in *; lia.
  - intros _. apply (apresent_writable SEGS).
    destruct (al_blocks SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ b n HARf
      ltac:(rewrite Hbl2; apply in_or_app; left; exact Hin)) as (_ & _ & _ & _ & Hp & _).
    exact (proj1 (Hp xx Hx)). }
(* an image byte is outside both windows (they lie in heap blocks) *)
assert (NWI : forall xx, in_img SEGS xx ->
  ~ (dxSA cx + 48 <= xx < dxSA cx + 52) /\ ~ (re_hp e1 + 8 * re_nheld e1 <= xx < re_hp e1 + 8 * re_nheld e1 + 8)).
{ intros xx Hi. split.
  - intros Hw. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE xx HAR1 HGin1);
      [rewrite RQT; unfold AENT, ATABLE in *; lia | exact Hi].
  - intros Hw. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) xx HAR1 Hhin1);
      [rewrite Hreqkh; lia | exact Hi]. }
(* an image byte off the allocator's statics and off errno: present then present now *)
assert (PRES : forall xx, in_img SEGS xx -> ~ Exists (in_zr xx) (as_owned_static B) ->
  ~ (as_errno B <= xx < as_errno B + 4) -> apresent (w_H W1) m1 xx -> apresent (w_H W2) (ms_mem ms3) xx).
{ intros xx Hi Hno Hne Hp. apply GR23. apply Hpres2; [exact Hi | | | exact Hne | |].
  - intros Ho. apply Hno. exact (proj1 (al_owned_image _ _ LAWS ly1 S1 W1 m1 md1 xx HAR1 Hi) Ho).
  - intros Ho. apply Hno. exact (proj1 (al_owned_image _ _ LAWS ly2 S2 W2 mem2 md2 xx HAR2 Hi) Ho).
  - intros Hr. exact (blk_img SEGS B LAWS ly2 S2 W2 mem2 md2 res (Z.of_nat jj + 1) xx HAR2 Hrin2 Hr Hi).
  - exact (gb_apresent_grows _ m1 _ _ GR1 Hp). }
assert (KIMGP : forall xx, in_img SEGS xx -> ~ Exists (in_zr xx) (as_owned_static B) ->
  ~ (as_errno B <= xx < as_errno B + 4) -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hi Hno Hne. pose proof (pa_img_range xx Hi) as Hxr. destruct (NWI xx Hi) as (N1 & N2).
  assert (HV : aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
  { rewrite K3 by lia. rewrite (KI2 xx Hi Hno Hne). apply KEEP1; lia. }
  split; [exact HV|]. apply (gb_writable_img W1 W2 m1 (ms_mem ms3) xx Hi). exact (PRES xx Hi Hno Hne). }
assert (KG : forall xx, inG (G_DR B RG) xx -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hx. destruct (HG xx Hx) as (Hi & Hno & _).
  destruct (Z_le_gt_dec (as_errno B) xx) as [He1 | He1];
    [destruct (Z_lt_ge_dec xx (as_errno B + 4)) as [He2 | He2] | apply KIMGP; [exact Hi | exact Hno | lia]];
    [| apply KIMGP; [exact Hi | exact Hno | lia]].
  pose proof (pa_img_range xx Hi) as Hxr. destruct (NWI xx Hi) as (N1 & N2).
  assert (HV : aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
  { rewrite K3 by lia. replace xx with (as_errno B + (xx - as_errno B)) by lia.
    rewrite (Herr2 (xx - as_errno B)) by lia. replace (as_errno B + (xx - as_errno B)) with xx by lia.
    apply KEEP1; lia. }
  split; [exact HV | exact (gb_writable_view W1 W2 m1 (ms_mem ms3) xx Hi (HGR xx Hx) HV)]. }
assert (KO : forall xx, inG GBGO xx -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hx. destruct (HGO xx Hx) as (Hi & Hno & _). apply KIMGP; [exact Hi | exact Hno |].
  unfold GBGO, inG in Hx. apply Exists_exists in Hx as (r & Hr & Hxr). unfold in_zr in Hxr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hxr.
  - pose proof (gb_zpd_nth _ 3 11 _ _ HRGD ltac:(lia) eq_refl eq_refl) as Dz. unfold zdisj in Dz. cbn [fst snd] in Dz. lia.
  - pose proof (gb_zpd_nth _ 6 11 _ _ HRGD ltac:(lia) eq_refl eq_refl) as Dz. unfold zdisj in Dz. cbn [fst snd] in Dz. lia.
  - pose proof (gb_zpd_nth _ 7 11 _ _ HRGD ltac:(lia) eq_refl eq_refl) as Dz. unfold zdisj in Dz. cbn [fst snd] in Dz. lia. }
assert (KFRM : forall xx, dsp0 cx - DRAIN_FRAME <= xx < dsp0 cx -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hx. rewrite WF in Hx.
  split.
  - rewrite K3 by lia. rewrite KS2 by (unfold ASTACK in *; rewrite ?WF; lia). apply KEEP1; lia.
  - apply (gb_writable_noimg W1 W2 m1 (ms_mem ms3) xx); [intros Hi; pose proof (pa_img_range xx Hi); lia | lia |].
    intros Hp. apply GR23. apply KP2; [lia | unfold ASTACK in *; rewrite ?WF; lia |].
    exact (gb_apresent_grows _ m1 _ _ GR1 Hp). }
assert (KPR : apres_kept B W1 m1 W2 (ms_mem ms3)) by (intros xx Hi Hno Hne Hp; exact (PRES xx Hi Hno Hne Hp)).
(* the new key's bytes *)
assert (KN : forall i, 0 <= i < Z.of_nat jj ->
  aview SEGS (w_H W2) (ms_mem ms3) (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)).
{ intros i Hi. rewrite K3 by (unfold gb_sep in DnG, Dnh; unfold AENT, ATABLE in *; lia). rewrite (Hcpy i Hi). unfold x.
  apply KEEP1; unfold gb_sep in Dbt, Dbh; unfold AENT, ATABLE in *; lia. }
assert (KNUL : aview SEGS (w_H W2) (ms_mem ms3) (res + Z.of_nat jj) = Some 0).
{ rewrite K3 by (unfold gb_sep in DnG, Dnh; unfold AENT, ATABLE in *; lia). exact Hnul. }
apply (HN W2).
exact (gb_dln cx s1 D p q jj regs1 ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl tl2 a jb' o' ha' ks'
  (ms_regs ms3) ly2 S2 W2 (ms_mem ms3) _ res HB HRL R23 Hbnd Hcap0 Hhp0 Hkh Hges Hjj Hidx HGSF HCORE HDLF Htl HJ2 Hbl2
  Hfrm2 Hmle2
  (RK _ 2%nat P2 ltac:(lia) (EA 2%nat ltac:(lia))) (RK _ 3%nat P3 ltac:(lia) (EA 3%nat ltac:(lia)))
  (RK _ 4%nat P4 ltac:(lia) (EA 4%nat ltac:(lia))) (RK _ 8%nat P8 ltac:(lia) (EA 8%nat ltac:(lia)))
  (RK _ 9%nat P9 ltac:(lia) (EA 9%nat ltac:(lia))) (RK _ 18%nat P18 ltac:(lia) (EA 18%nat ltac:(lia)))
  P21' P20' P22' P27' (RK _ 23%nat P23 ltac:(lia) (EA 23%nat ltac:(lia)))
  VHP VNH VSL KT KH KB KG KO KFRM KPR KN KNUL).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30; the B twin of lib/A/W_gsaddb.v's Section cx at
   a working branch 50623273289): gs_addb_x proves lib/B/W_gsadd_cx.v's twin statement gs_addb_stmt_x over
   lib/B/W_drain_cx_x.v's Section variables (B PST ARx MT RP MMAX RG), the entry's ghost list Hp and budget kr after cx,
   a cut's own ghost list after its state (Hp1 at GAR, Hp2 after strndup).  Everything above this line is unchanged, so
   every AR statement of this file keeps its text and its Section list; the twin only adds names (the AR name with _x).
   The AR-free names of Section c above (the symbolic seat gb_seat, the byte images gb_entry_*, the model lemmas gba_*,
   the footprint lemmas gb_*_fp_cls, ...) are CITED with the Section variables they abstracted; the lemmas whose
   statements name AR, the journal, DMEM, GARB or DLN have their _x twin here: gb_ablocks_nodup_x (the sizes' sign is
   BLKN: the blocks law over ARx has no size conjunct), gb_shok_x, gb_new_disj_x, gb_dmem_x, gb_dln_x, gs_addb_x.
   THE ROOM ROUND at strndup (0x83c08, returning to 0x83c0c = drain + 0x994, its caller-context fact HCTX_sd): GARfut's
   trace is RMalloc (jj + 1) :: tl2.  W_drain_room_x.gs_rm_take takes the rule's room 1 out of MT_rk's charge 2 of that
   request; the rule runs at kr := MT_rk's charge of tl2 plus the entry's kr, so its post's room is dbud_x's room at
   tl2; the count premise is gs_cnt_call, the counts after the call gs_cnt_malloc (the blocks are the old ones with
   (res, jj + 1) appended).
   THE STRNDUP RULE's premises of lib/B/W_journal_x.v astrndup_cf_rule_c_x (a Theorem Labs lane's B twins a2a0be52faf of A's
   fc7fca230b0 and c96258ef05e of A's b9052387bcb): the live source block is gb_src_blk_x (the source
   [e->buf + p, e->buf + p + jj) lies in the relay entry's buffer block (re_buf e, re_cap e)); frame0_ok is
   gb_frame0_x (the call's sp is DRAIN_FRAME = 352 below drain's entry sp, which the journal keeps below the layout's
   top); its stack-bottom premise
   `ly_bot lyc + STRNDUP_FRAME_CF_x + MALLOC_BODY_FRAME_CF_x < spZ regsT` (the B kit c96258ef05e, the twin of A's
   b9052387bcb) is gb_stk_bot_x (A's gb_stkbot_x, 72187c66685): the walk's journal at DRAIN_STK_x = 17008 leaves
   ly_bot + 4368 below the call, the premise needs 2160 + 2144 = 4304. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx W_drain_cx_x W_drain_gs W_gsadd_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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
(* lib/B/W_drain_cx_x.v:154 *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* lib/B/W_drain_cx_x.v:156-216, the ones this file's proofs use, in that file's order and text *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
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
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
(* a Theorem Labs lane's shared texts (lib/A/W_gsaddb.v's Section cx), the three this file uses *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
(* strndup's site rule in its caller-context form over the generic journal (lib/B/W_drain_cx_x.v:219, :222, :226),
   with the one call-site fact this file uses (drain = 0x83278; jal strndup 0x83c08) *)
Variable CTX_S : list (list Z).
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.    (* strndup returns to 0x83c0c *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis ASTRNDUP_R : astrndup_cf_rule_c_xR SEGS B PST ARx MT MMAX RP CTX_S R (SIGMA WS_strndup).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
Local Notation DLN_R := (DLN_xR B PST ARx MT RP MMAX RG R).
Local Notation DMEM_R := (DMEM_xR B PST ARx RG R).
Local Notation GARB_R := (GARB_xR B PST ARx MT RP MMAX RG R).
Local Notation gs_addb_stmt_R := (gs_addb_stmt_xR B PST ARx MT RP MMAX RG R).
(* ---- gb_ablocks_nodup over ARx: the live blocks are pairwise distinct ---- *)
Lemma gb_ablocks_nodup_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [pp nn] Hin.
  pose proof (BLKN ly S Hp W mem md pp nn HAR Hin) as Hn.
  cbn [snd]. apply req_size_pos. lia. }
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* ---- gb_shok over ARx: the two shadow entries at GAR (and after strndup) ---- *)
Lemma gb_shok_x : forall Ex ly S Hp (W : world SEGS) mem md G SA hp kh nh,
ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 0 <= nh -> 8 * nh + 8 <= req_size kh ->
ew Ex 33 = w64 SHADOW_OFF -> ew Ex 32 = w64 SA -> ew Ex 36 = w64 (hp + 8 * nh) ->
sh_ok SEGS gb_Bx gb_SH Ex (mrestrict (w_H W) mem).
Proof.
intros Ex ly S Hp W mem md G SA hp kh nh HAR Hin HGle HSAle Hhin Hnh Hkh E33 E32 E36.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hhin) as (_ & H4096h & Hceilh & Happh & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in Hceil, Happ.
assert (UB : U Ex gb_Bx = SHADOW_OFF) by (unfold gb_Bx; apply (U_atom Ex 33 _ E33); unfold SHADOW_OFF; lia).
unfold sh_ok, gb_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) mem Ex gb_Bx 32 SA 56 SA 40 56).
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md G ATABLE);
      [exact HAR | exact Hin | lia |].
    rewrite RQT. unfold AENT, ATABLE in *. lia.
  + exact UB.
  + apply (U_atom Ex 32 SA E32). unfold AENT, ATABLE in *. lia.
  + lia.
  + lia.
  + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold AENT, ATABLE in HSAle. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem Ex gb_Bx 36 (hp + 8 * nh) 8 (hp + 8 * nh) 0 8).
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md hp kh);
      [exact HAR | exact Hhin | lia | lia].
  + exact UB.
  + apply (U_atom Ex 36 _ E36). lia.
  + lia.
  + lia.
  + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happh. unfold SHADOW_OFF. lia.
Qed.

(* ---- gb_new_disj over ARx: strndup's new block is disjoint from every block before it ---- *)
Lemma gb_new_disj_x : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 lyc Sc res n b m,
ARx ly2 S2 Hp2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> In (b, m) (ablocks B lyc Sc) ->
b + req_size m <= res \/ res + req_size n <= b.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 lyc Sc res n b m HAR2 Ebl Hin.
pose proof (gb_ablocks_nodup_x ly2 S2 Hp2 W2 mem2 md2 HAR2) as ND. rewrite Ebl in ND.
destruct (gb_nd_app _ _ ND) as (_ & _ & Hd).
assert (Hne : (b, m) <> (res, n)) by (intros Heq; apply (Hd (b, m) Hin); rewrite Heq; left; reflexivity).
pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m res n HAR2
  ltac:(rewrite Ebl; apply in_or_app; left; exact Hin) ltac:(rewrite Ebl; apply in_or_app; right; left; reflexivity)
  Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia.
Qed.

(* ---- THE STRNDUP RULE's frame0_ok premise at this walk's call.  Mirrored text: lib/A/W_journal_x.v astrndup_cf_rule_c_x
   at a working branch 50623273289 (W8's fc7fca230b0), after chain_pre:
     frame0_ok lyc regsT = true ->
   (B: lib/B/W_journal_x.v:992, a Theorem Labs lane's a2a0be52faf).  The call's sp = sp0 + o lies at least 16 below sp0,
   sp0 <= ly_top of the entry layout (the journal's astk_ok), and the journal keeps ly_top (its layout_le). ---- *)
Lemma gb_frame0_xR : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memT mdc k (o : Z)
  (regsT : bvmap 5 word),
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o + 16 < 0 -> frame0_ok lyc regsT = true.
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT HJ Hsp Ho.
pose proof HJ as (_ & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Htop & _) & _).
pose proof HLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
unfold frame0_ok. apply Z.ltb_lt. rewrite Hsp, Etop. lia.
Qed.

(* ---- THE STRNDUP RULE's live-source premise at this walk's call.  Mirrored text: lib/A/W_journal_x.v
   astrndup_cf_rule_c_x at a working branch 50623273289 (W8's fc7fca230b0), after shadow_hull_vis:
     (exists p m, In (p, m) (ablocks B lyc Sc) /\ p <= x /\ x + n <= p + req_size m) ->
   (B: lib/B/W_journal_x.v:986, a Theorem Labs lane's a2a0be52faf).  At drain's call the source is [e->buf + p, e->buf + p + jj),
   inside the relay entry's buffer block (re_buf e, re_cap e). ---- *)
Lemma gb_src_blk_x : forall ly S e (p jj : nat),
In (re_buf e, re_cap e) (ablocks B ly S) -> 0 < re_cap e -> Z.of_nat p + Z.of_nat jj <= re_cap e ->
exists p0 m0, In (p0, m0) (ablocks B ly S) /\ p0 <= re_buf e + Z.of_nat p /\
  re_buf e + Z.of_nat p + Z.of_nat jj <= p0 + req_size m0.
Proof.
intros ly S e p jj Hin Hc Hpj. exists (re_buf e), (re_cap e).
assert (Hrq : req_size (re_cap e) = re_cap e) by (unfold req_size; destruct (Z.eqb_spec (re_cap e) 0); lia).
split; [exact Hin|]. rewrite Hrq. lia.
Qed.

(* ---- THE STRNDUP RULE's third premise, the stack the strndup interceptor's inner malloc needs below the call.
   Mirrored text: lib/A/W_journal_x.v astrndup_cf_rule_c_x at a working branch b9052387bcb
   (:988), after the ACALL_PREFIX premise (B: lib/B/W_journal_x.v:989, the kit's c96258ef05e):
     ly_bot lyc + STRNDUP_FRAME_CF_x + MALLOC_BODY_FRAME_CF_x < spZ regsT ->
   with the Local constants STRNDUP_FRAME_CF_x := 2160 and MALLOC_BODY_FRAME_CF_x := 2144 (:46-47), left-nested, so the
   literal form below converts to it by delta.  The statement and proof are A's gb_stkbot_x (lib/A/W_gsaddb.v,
   a working branch 72187c66685).  B's own frames: ___interceptor_strndup 0x427b0 `addi sp,sp,-2032`,
   0x427e0 `addi sp,sp,-128` (2160, as A's 0x42758); __interceptor_malloc 0x5401c `addi sp,sp,-2032`, 0x54040
   `addi sp,sp,-96` (as A's 0x53fc4).  The journal's astk_ok puts ly_bot + STK + ACALL_PREFIX - ASTACK below sp0, and
   the journal keeps ly_top, so a call at sp0 + o has ly_bot + 4304 below it once STK covers ASTACK - o + 4304 -
   ACALL_PREFIX: 16944 at drain's strndup call (o = - DRAIN_FRAME = -352); lib/B/W_contract_x.v's DRAIN_STK_x :=
   DRAIN_STK + 128 = 17008 gives 4368 of room (DRAIN_STK = 16880 alone gives 4240). ---- *)
Lemma gb_stk_bot_xR : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memT mdc k (o : Z)
  (regsT : bvmap 5 word),
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> ASTACK - o + 2160 + 2144 <= STK + ACALL_PREFIX -> ly_bot lyc + 2160 + 2144 < spZ regsT.
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT HJ Hsp Ho.
destruct HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct Hstk as (_ & _ & _ & _ & _ & _ & Hbot & _).
unfold ly_bot in *. rewrite Etop. lia.
Qed.

(* ---- gb_dmem over DMEM_x: the cut's memory core after the add, with the relay entry replaced ---- *)
Lemma gb_dmem_xR : forall cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp' (W' : world SEGS) m' md' k' e' s',
DMEM_R cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' Hp' W' m' md' k' ->
rom_view SEGS (dxW cx) (dxmem cx) ->
apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
garr8 SEGS (arm W' m') (dxSA cx) (bzs (entry_bytes e')) -> awr W' m' (dxSA cx) AENT ->
aentry_okx B ly' S' W' m' e' ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W m W' m' a) ->
akept W m W' m' (asrc_fp (dHA RG cx) h) -> (forall b, In b (asrc_blks h) -> In b (ablocks B ly' S')) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
(forall b, In b (aout_blks (drain_b_c.ds_ocap s) out) -> In b (ablocks B ly' S')) ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e' ++ asrc_blks h ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM_R cx Hp ly' S' Hp' W' m' md' k' e' h s' out ev sent LB.
Proof.
intros cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp' W' m' md' k' e' s' HD Eno Eoc HJ' Hrom0 KP KF KS Hent'
  Hawr' Hokx' KG KA HAin KO HOin HP'.
destruct HD as (HJ & Hrom & Hpres & Hfr & HFR & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
unfold DMEM_xR. rewrite Eno, Eoc.
split; [exact HJ'|].
split; [eapply ajournal_gx_rom_view_xR;
  first [exact HJ' | exact HROMO | exact PSTR | exact Hrom0 | exact LAWS | exact pa_segs_low]|].
split; [intros a H1 H2 H3 H4; exact (KP a H1 H2 H3 (Hpres a H1 H2 H3 H4))|].
split; [rewrite KF; exact Hfr|].
split; [exact (gb_frame_kept RG cx W m W' m' KS HFR)|].
split; [exact Hent'|].
split; [exact Hawr'|].
split; [exact Hokx'|].
split.
{ apply (asrc_at_kept B ly S W m ly' S' W' m' (dHA RG cx) h Hsrc KA HAin). }
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Vo). exists f, o.
  assert (KI : forall x, rg_s RG + ASRC * Z.of_nat i <= x < rg_s RG + ASRC * Z.of_nat i + 8 ->
    abyte_kept W m W' m' x).
  { intros x Hx. apply KG. unfold ASRC in *. lia. }
  split; [|split; [|exact Vo]]; (apply (akept_vm W m); [intros x Hx; apply KI; simpl Z.of_nat in Hx; lia|]);
  assumption. }
split.
{ intros x Hx1 Hx2. destruct (Hgsk x Hx1 Hx2) as [E1 P1]. destruct (KG x Hx1) as [E2 P2].
  split; [rewrite E2; exact E1 | intros Hw; exact (P2 (P1 Hw))]. }
split; [exact (aout_at_kept B RG ly S W m ly' S' W' m' _ _ _ _ _ _ Hout KO HOin)|].
split; [exact Hlive | exact HP'].
Qed.

(* ---- gb_dln over ARx: the cut DLN_x (S q) at the line loop's head, from what the walk leaves; the room at the
   cut is strndup's post (HRM2), the counts the cut's after one block more (gs_cnt_malloc) ---- *)
Lemma gb_dln_xR : forall cx Hp kr s1 D (p q jj : nat) regs1 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl tl2 a jb' o' ha' ks' regs3 ly2 S2 Hp2 (W2 : world SEGS) m3 md3 res,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_gs RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
re_hp e1 <> 0 -> re_kh e1 = 8 * re_nheld e1 + 8 ->
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None ->
GSF s1 p q ->
GARB_R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (GSno cx s1 p q) (GSoc cx s1 p q)
  (seen_arr (dlH cx s1 p) (dline s1 p q)) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (drlq s1 (S q)) jb' o' ha' ks' tl2 ->
tl = RelayRunT.RMalloc (Z.of_nat jj + 1) :: tl2 ->
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 Hp2 W2 m3 md3 (k1 + 1) ->
ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, Z.of_nat jj + 1)] ->
frames S2 = frames S1 ->
mo_le MT S1 S2 (mo_malloc MT (Z.of_nat jj + 1)) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tl2) + kr) ->
getr regs3 2 = getr regs1 2 -> getr regs3 3 = getr regs1 3 -> getr regs3 4 = getr regs1 4 ->
getr regs3 8 = getr regs1 8 -> getr regs3 9 = getr regs1 9 -> getr regs3 18 = getr regs1 18 ->
getr regs3 21 = w64 (dxSA cx) -> getr regs3 20 = w64 (dxSA cx + 16) ->
getr regs3 22 = w64 (dxSA cx + 24) -> getr regs3 27 = w64 (dxSA cx + 32) ->
getr regs3 23 = getr regs1 23 ->
val_mem SEGS (arm W2 m3) (dxSA cx + 40) 8 (re_hp e1) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 48) 4 (re_nheld e1 + 1) ->
val_mem SEGS (arm W2 m3) (re_hp e1 + 8 * re_nheld e1) 8 res ->
(forall x, dxG cx <= x < dxG cx + ATABLE -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x) ->
(forall x, re_hp e1 <= x < re_hp e1 + 8 * re_nheld e1 -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x) ->
(forall b n x, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) -> (b, n) <> (re_hp e1, re_kh e1) ->
   b <= x < b + req_size n -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, inG (G_DR B RG) x -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, inG (GBGO RG) x -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x) ->
apres_kept B W1 m1 W2 m3 ->
(forall i, 0 <= i < Z.of_nat jj ->
   aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)) ->
aview SEGS (w_H W2) m3 (res + Z.of_nat jj) = Some 0 ->
DLN_R cx Hp kr s1 D (S q) W2 (cfg_at SEGS (BASE + A_dr_next) regs3 m3 md3).
Proof.
intros cx Hp kr s1 D p q jj regs1 ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl tl2 a jb' o' ha' ks' regs3 ly2 S2
  Hp2 W2 m3 md3 res
  HB HRL R23 Hbnd Hcap0 Hhp0 Hkh Hges Hjj Hidx HGSF HCORE HDLF Htl HJf Hbl2 Hfrm2 Hmle2 HRM2
  P2 P3 P4 P8 P9 P18 P21 P20 P22 P27 P23 VHP VNH VSL KT KH KB KG KO KF KP KN KNUL.
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRSTART & HBUD).
pose proof HDMEM as (HJ & HROM & HPRES & HFRS & HFRAME & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HSA8 & HGARR & HAWR0 & HENT0 & HJ4 & HSRC0 & HOTH0 & HFD0 & HSK0 &
  HSKU0 & HOUT0 & HROM0 & HPERM0 & HPS0 & HEC0 & HNH0 & HTM0 & HTA0 & HMOK & HRM0 & HCNT0).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJf) as HARf.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HLL : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
(* the model after the line *)
destruct (gba_line B RG HGSB cx s1 p q jj HGSF Hges Hidx) as (E1 & E2 & E3 & Ebd & Esq & L1 & L2 & L3 & L4).
destruct (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ 0 RelayRunF.adr0 [] Hges Hidx)
  as (Sarr & _ & Ska).
pose proof HGSF as (HBd & HPQ & HQ & HNZ & HK & HL).
pose proof HLINK as (Lcap & LU & Lskip & Lkeys & Lka & Leintr & Lpend & Loff & Lref & Len & Lecap & Lwf).
assert (HUW : bzs (re_U e1) = dW s1) by (rewrite LU; reflexivity).
assert (HUL : length (re_U e1) = length (dW s1)) by (rewrite <- HUW; rewrite gb_bzs_len; reflexivity).
assert (LK : drain_b_c.keys_texts (re_keys e1) = dlH cx s1 p) by (rewrite Lkeys; reflexivity).
(* the relay entry's blocks *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KFk).
destruct KHP as [(Hz & _) | (_ & Hhin1 & Hkh1 & Hkh8 & HKP)]; [exfalso; exact (Hhp0 Hz)|].
destruct KBUF as [(Hc0 & _ & _) | (Hcpos & Hbin & Hjunk & Hbuf8)].
{ exfalso. apply (f_equal (@length Z)) in HUW. rewrite gb_bzs_len in HUW. unfold re_used in *. lia. }
assert (Hreqkh : req_size (re_kh e1) = re_kh e1) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
assert (Hreqc : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
assert (HIN1 : forall bn, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
  aout_blks (drain_b_c.ds_ocap (dvirt cx s1 false (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
    (GSno cx s1 p q) (GSoc cx s1 p q))) out1 ++ dxrest cx) -> In bn (ablocks B ly1 S1))
  by (intros bn Hbn; apply (Permutation_in _ (Permutation_sym HPERM)); exact Hbn).
assert (HIN2 : forall bn, In bn (ablocks B ly1 S1) -> In bn (ablocks B ly2 S2))
  by (intros bn Hbn; rewrite Hbl2; apply in_or_app; left; exact Hbn).
pose proof (Permutation_NoDup HPERM (gb_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR1)) as NDall.
apply NoDup_cons_iff in NDall. destruct NDall as (Hni & NDr).
destruct (gb_nd_app _ _ NDr) as (NDe & _ & Hde).
assert (HEB : aentry_blks e1 = (re_buf e1, re_cap e1) :: (re_hp e1, re_kh e1) ::
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
{ unfold aentry_blks. destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. destruct (Z.eqb_spec (re_hp e1) 0); [contradiction|].
  reflexivity. }
assert (NDe' := NDe). rewrite HEB in NDe'. apply NoDup_cons_iff in NDe' as (Hbn1 & NDe'').
apply NoDup_cons_iff in NDe'' as (Hhn1 & _).
(* a block of the source or the output is neither the table nor the held array *)
assert (HOTHB : forall bn, In bn (asrc_blks h1 ++ aout_blks (GSoc cx s1 p q) out1 ++ dxrest cx) ->
  In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE) /\ bn <> (re_hp e1, re_kh e1)).
{ intros bn Hbn. split; [apply HIN1; right; apply in_or_app; right; exact Hbn|].
  split; [intros Heq; apply Hni; rewrite <- Heq; apply in_or_app; right; exact Hbn|].
  intros Heq. apply (Hde (re_hp e1, re_kh e1)); [rewrite HEB; right; left; reflexivity | rewrite <- Heq; exact Hbn]. }
assert (Hnhb : re_nheld e1 + 1 < 2 ^ 26).
{ pose proof HHIST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
  unfold dvirt in D10. cbn [drain_b_c.ds_H] in D10.
  rewrite <- LK, gs_keys_texts_len in D10. unfold re_nheld. lia. }
(* the buffer bytes, as the ASan view reads them at GAR *)
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite (gb_garr8_aview B RG W1 m1 (re_buf e1) _ j Hbuf8) by (rewrite gb_bzs_len, length_app; lia).
  rewrite gb_bzs_app, app_nth1 by (rewrite gb_bzs_len; lia). rewrite HUW. reflexivity. }
(* the new key: (res, the jj bytes of the line, no slack) *)
set (nk := (res, firstn jj (skipn p (re_U e1)), @nil byte)).
assert (HTX' : bzs (key_text nk) = firstn jj (skipn p (dW s1))).
{ unfold key_text, nk. cbn [fst snd]. rewrite <- HUW. unfold bzs. rewrite <- firstn_map, <- skipn_map. reflexivity. }
assert (HTX : bzs (key_text nk) = firstn jj (dline s1 p q)).
{ rewrite HTX'. unfold dline. rewrite firstn_firstn, Nat.min_l by lia. reflexivity. }
assert (HTL : length (key_text nk) = jj).
{ rewrite <- gb_bzs_len, HTX'. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
assert (HKA : key_addr nk = res) by reflexivity.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m3 md3 res (Z.of_nat jj + 1) HARf
  ltac:(rewrite Hbl2; apply in_or_app; right; left; reflexivity)) as (_ & Hr4096 & Hrceil & _).
assert (Hreqr : req_size (Z.of_nat jj + 1) = Z.of_nat jj + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat jj + 1) 0); lia).
rewrite Hreqr in Hrceil.
set (e2 := gb_e2 e1 nk).
set (spent' := spent + (mo_malloc MT (Z.of_nat jj + 1) + mo_free MT)).
unfold DLN_xR.
exists regs3, ly2, S2, Hp2, m3, md3, (k1 + 1), e2, h1, out1, ev1, LB1, spent', jb', a, o', ha', ks', tl2.
split; [reflexivity|].
split; [exact (gb_dregs_line RG cx regs1 regs3 W1 m1 W2 m3 HRL P2 P3 P4 P8 P9 P18 P21 P20 P22 P27 KF)|].
split; [rewrite P23, R23; unfold e2, gb_e2; cbn [re_buf]; unfold w64; f_equal; lia|].
split; [unfold e2, gb_e2; cbn [re_buf re_cap]; exact Hbnd|].
split; [unfold e2, gb_e2; cbn [re_cap]; exact Hcap0|].
split; [exact Ebd|].
split; [exact Esq|].
split.
2:{ rewrite L1, L2, L3, L4. rewrite Sarr in HDLF. exact HDLF. }
unfold DLC_xR, LCORE_xR. cbv zeta. rewrite E1, E3, L1, L2, L3, L4.
split.
{ (* the memory core *)
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hhin1) as (_ & Hh4096 & Hhceil & _).
  rewrite Hreqkh in Hhceil.
  assert (Hbt : (re_buf e1, re_cap e1) <> (dxG cx, ATABLE))
    by (intros Heq; apply Hni; rewrite <- Heq; apply in_or_app; left; rewrite HEB; left; reflexivity).
  assert (Hbh : (re_buf e1, re_cap e1) <> (re_hp e1, re_kh e1))
    by (intros Heq; apply Hbn1; rewrite Heq; left; reflexivity).
  assert (Hbin1 : In (re_buf e1, re_cap e1) (aentry_blks e1)) by (rewrite HEB; left; reflexivity).
  apply (gb_dmem_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 _ out1 ev1 _ LB1 ly2 S2 Hp2 W2 m3 md3 (k1 + 1) e2 _ HDMEM
    eq_refl eq_refl HJf HROM0 KP Hfrm2 KF).
  - apply (gb_entry_store W1 m1 W2 m3 (dxSA cx) e1 e2 Kp1 Kp2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl).
    + unfold e2, gb_e2. cbn [re_hp]. lia.
    + unfold e2. rewrite (gb_e2_nheld B RG). unfold re_nheld in *. lia.
    + exact HENT.
    + exact VHP.
    + unfold e2. rewrite (gb_e2_nheld B RG). exact VNH.
    + intros xx Hxx. apply KT; unfold AENT, ATABLE in *; lia.
    + intros xx Hxx. apply KT; unfold AENT, ATABLE in *; lia.
  - intros i Hi. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m3 md3 _ _ HARf (HIN2 _ HGin1)) as (_ & _ & _ & _ & Hpr & _).
    rewrite RQT in Hpr. exact (proj1 (Hpr (dxSA cx + i) ltac:(unfold AENT, ATABLE in *; lia))).
  - apply (gb_aentry_okx_add B RG HGSB ly1 S1 W1 m1 ly2 S2 W2 m3 e1 nk HOKX Hhp0 Hkh Hnhb (HIN2 _ Hhin1)).
    + apply (gb_ptrs_app B RG W1 m1 W2 m3 (re_hp e1) (re_keys e1) nk); [rewrite HKA; lia | exact HKP | |].
      * unfold re_nheld in VSL. rewrite HKA. exact VSL.
      * intros xx Hxx. apply KH. unfold re_nheld. exact Hxx.
    + intros _. split; [apply HIN2, HIN1; right; apply in_or_app; left; exact Hbin1|].
      intros xx Hxx. apply (KB (re_buf e1) (re_cap e1) xx (HIN1 _ (or_intror (in_or_app _ _ _ (or_introl Hbin1)))) Hbt Hbh).
      rewrite Hreqc. exact Hxx.
    + intros k0 Hk0.
      assert (Hk0b : In (key_addr k0, Z.of_nat (length (key_text k0)) + 1) (aentry_blks e1))
        by (rewrite HEB; right; right; apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk0).
      split; [apply HIN2, HIN1; right; apply in_or_app; left; exact Hk0b|].
      intros xx Hxx. apply (KB _ _ xx (HIN1 _ (or_intror (in_or_app _ _ _ (or_introl Hk0b))))).
      * intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. exact Hk0b.
      * intros Heq. apply Hhn1. rewrite <- Heq.
        apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk0.
      * pose proof (req_size_pos (Z.of_nat (length (key_text k0)) + 1) ltac:(lia)) as (_ & Hrq). lia.
    + rewrite HKA. intros Hin. apply in_map_iff in Hin as (k0 & Hk0a & Hk0).
      rewrite Forall_forall in KFk. destruct (KFk k0 Hk0) as (Hkb & _).
      pose proof (gb_new_disj_x ly2 S2 Hp2 W2 m3 md3 ly1 S1 res _ _ _ HARf Hbl2 Hkb) as Dn.
      pose proof (req_size_pos (Z.of_nat (length (key_text k0)) + 1) ltac:(lia)) as (Hr1 & _).
      pose proof (req_size_pos (Z.of_nat jj + 1) ltac:(lia)) as (Hr2 & _). lia.
    + intros Hin. apply in_map_iff in Hin as (k0 & Hk0t & Hk0).
      apply (index_of_none _ _ Hidx). rewrite <- LK, <- HTX, <- Hk0t. unfold drain_b_c.keys_texts.
      apply (in_map (fun k => bzs (key_text k))). exact Hk0.
    + rewrite HKA, HTL, Hbl2. apply in_or_app. right. left. reflexivity.
    + rewrite HKA. apply (gb_garr8_of_aview B RG). intros j Hj. rewrite gb_bzs_app in Hj |- *.
      rewrite length_app, gb_bzs_len, HTL in Hj. cbn [length bzs map] in Hj.
      destruct (Nat.lt_ge_cases j jj) as [Hlt | Hge].
      * rewrite app_nth1 by (rewrite gb_bzs_len, HTL; exact Hlt). rewrite HTX', gsx_nth_firstn by exact Hlt.
        rewrite gb_nth_skipn. rewrite (KN (Z.of_nat j) ltac:(lia)).
        replace (re_buf e1 + Z.of_nat p + Z.of_nat j) with (re_buf e1 + Z.of_nat (p + j)) by lia. apply BV. lia.
      * assert (j = jj) as -> by lia. rewrite app_nth2 by (rewrite gb_bzs_len, HTL; lia).
        rewrite gb_bzs_len, HTL, Nat.sub_diag. change (bzs [Z_to_bv 8 0]) with [bz (Z_to_bv 8 0)]. cbn [nth].
        rewrite gb_bz_bv8. change (0 mod 256) with 0. exact KNUL.
    + intros Hin. apply (in_map bz) in Hin. change (map bz (key_text nk)) with (bzs (key_text nk)) in Hin.
      rewrite HTX, gb_bz_bv8 in Hin. change (0 mod 256) with 0 in Hin.
      pose proof (gs_dline_nz s1 p q HNZ) as Hnz. unfold nozero in Hnz. rewrite Forall_forall in Hnz.
      apply (Hnz 0); [rewrite <- (firstn_skipn jj (dline s1 p q)); apply in_or_app; left; exact Hin | reflexivity].
    + rewrite HTL. unfold APARTIAL. lia.
  - intros xx Hxx. apply KG. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros r Hr xx Hxx.
    destruct (gb_asrc_fp_cls B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r Hr xx Hxx) as [Hg | (b & n & Hin & Hbx)].
    + apply KG. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr, dHA in *. cbn [fst snd]. unfold ASRC in *. lia.
    + destruct (HOTHB (b, n) ltac:(apply in_or_app; left; exact Hin)) as (H1 & H2 & H3). exact (KB b n xx H1 H2 H3 Hbx).
  - intros bn Hbn. apply HIN2. exact (proj1 (HOTHB bn (in_or_app _ _ _ (or_introl Hbn)))).
  - intros r Hr xx Hxx.
    destruct (gb_aout_fp_cls B MMAX RG HGSB HMMAX HSD HSM ly1 S1 W1 m1 _ _ _ _ _ _ HOUT r Hr xx Hxx)
      as [Hg | [Hg | (b & n & Hin & Hbx)]]; [exact (KG xx Hg) | exact (KO xx Hg) |].
    destruct (HOTHB (b, n) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin)) as (H1 & H2 & H3).
    exact (KB b n xx H1 H2 H3 Hbx).
  - intros bn Hbn. apply HIN2. exact (proj1 (HOTHB bn ltac:(apply in_or_app; right; apply in_or_app; left; exact Hbn))).
  - unfold e2. rewrite gb_e2_blks, Hbl2, HKA, HTL.
    eapply Permutation_trans; [apply Permutation_app_tail; exact HPERM|].
    cbn [app]. apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
    apply Permutation_sym. rewrite !app_assoc. apply Permutation_cons_append. }
split.
{ refine (conj Lcap (conj LU (conj Lskip (conj _ (conj Lka (conj Leintr (conj Lpend (conj Loff (conj Lref
    (conj Len (conj Lecap Lwf))))))))))).
  unfold e2, gb_e2. cbn [re_keys dvirt drain_b_c.ds_H]. rewrite gs_keys_texts_app, LK, HTX. reflexivity. }
split; [exact HSAME|].
split; [exact (gba_hist B RG cx s1 D p q jj h1 LB1 _ HGSF Hges Hidx HHIST)|].
split; [exact HRSTART|].
pose proof HBUD as ((Hle0 & Hsp0 & Hcost & Halloc & Hmax) & HRM1 & HCNT1).
pose proof (mo_free_nonneg MT MTL) as Hf. pose proof (mo_malloc_nonneg MT MTL (Z.of_nat jj + 1) ltac:(lia)) as Hm.
unfold tr_cost in Hcost. unfold tr_max in Hmax. rewrite Htl in Hcost, Halloc, Hmax, HCNT1.
(* C3: strndup's one request RMalloc (jj + 1) opens the trace still owed (W_tr_peak.v tr_peak_malloc) *)
rewrite W_tr_peak.tr_peak_malloc in Halloc.
cbn [fold_right] in Hcost, Hmax.
unfold dbud_x. split; [|split].
- unfold dbud. split.
  { apply (mle_weaken MT _ _ (spent + mo_malloc MT (Z.of_nat jj + 1)) _ MTL);
      [exact (mle_station MT (dxS cx) S1 S2 spent _ MTL Hle0 Hmle2) | unfold spent'; lia]. }
  split; [unfold spent'; lia|].
  split; [unfold spent', tr_cost; lia|].
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), Hbl2, bsum_app, <- (blocks_bytes_bsum B ly1 S1). cbn [bsum fold_right snd].
    lia. }
  unfold tr_max. lia.
- (* the room at the cut: strndup's post *)
  exact HRM2.
- (* the counts at the cut: one block more, the head request's peak dropped *)
  apply (gs_cnt_malloc RP (Z.of_nat jj + 1) tl2 (ablocks B ly1 S1) (ablocks B ly2 S2) res); [|exact HCNT1].
  rewrite Hbl2. apply Permutation_sym, Permutation_cons_append.
Qed.

(* ============================================================================================
   THE SEGMENT over ARx
   ============================================================================================ *)
Theorem gs_addb_xR : gs_addb_stmt_R.
Proof.
unfold gs_addb_stmt_xR. intros cx Hp kr s1 D p q W1 c1 HB HGAR HN.
destruct HGAR as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & a & tl & jj &
  Hc1 & HRL & R27 & R23 & R24 & R19 & V16 & V192 & Hbnd & Hcap0 & Hhp0 & Hkh & HGARW & HROM1 & Hges & Hjj & Hidx &
  HGSF & HCORE & HFUT).
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRSTART & HBUD).
pose proof HDMEM as (HJ & HROM & HPRES & HFRS & HFRAME & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
pose proof HRL as (Usp & R3 & R4 & R8 & R9 & R18 & HFR2).
pose proof HFR2 as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 &
  F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & FSV).
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HSA8 & HGARR & HAWR0 & HENT0 & HJ4 & HSRC0 & HOTH0 & HFD0 & HSK0 &
  HSKU0 & HOUT0 & HROM0 & HPERM0 & HPS0 & HEC0 & HNH0 & HTM0 & HTA0 & HMOK & HRM0 & HCNT0).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 HJ) as HAR1.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK_x = 17008) by reflexivity.
assert (WF : DRAIN_FRAME = 352) by reflexivity.
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGapp, HGpres.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in HGle; lia).
assert (HSAhi : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
(* the relay entry's fields; the held array is the grown block *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KF).
clear K1 K2 K6.
assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
destruct KHP as [(Hz & _) | (_ & Hhin1 & Hkh1 & Hkh8 & HKP)]; [exfalso; exact (Hhp0 Hz)|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hhin1) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _).
assert (Hreqkh : req_size (re_kh e1) = re_kh e1) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
rewrite Hreqkh in Hhceil, Hhapp, Hhpres.
assert (Hhp8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite Hh16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }

(* ---- the model at the cut ---- *)
pose proof HGSF as (HBd & HPQ & HQ & HNZ & HK & HL).
pose proof HLINK as (Lcap & LU & Lskip & Lkeys & Lka & Leintr & Lpend & Loff & Lref & Len & Lecap & Lwf).
assert (HUW : bzs (re_U e1) = dW s1) by (rewrite LU; reflexivity).
assert (HUL : length (re_U e1) = length (dW s1)) by (rewrite <- HUW; rewrite gb_bzs_len; reflexivity).
assert (Hdwlen : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HUL; exact K7).
destruct KBUF as [(Hc0 & _ & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hbin) as (HB16 & HB4096 & HBceil & HBapp & HBpres & _).
assert (Hreqc : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite Hreqc in HBceil, HBapp, HBpres.
assert (Hlen : length (dline s1 p q) = (q - p)%nat) by (apply gs_dline_len; lia).
assert (Hlx : length (firstn jj (dline s1 p q)) = jj) by (apply firstn_length_le; lia).
destruct HFUT as (tl2 & jb' & o' & ha' & ks' & HDLF & Htl & Hcost2 & Halloc2).
rewrite Hlx in Htl.
pose proof HBUD as ((Hle0 & Hsp0 & Hcost & Halloc & Hmax) & HRM1 & HCNT1).
assert (BV : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hj. rewrite (gb_garr8_aview B RG W1 m1 (re_buf e1) _ j Hbuf8) by (rewrite gb_bzs_len, length_app; lia).
  rewrite gb_bzs_app, app_nth1 by (rewrite gb_bzs_len; lia). rewrite HUW. reflexivity. }
(* the blocks of the entry, the source and the output are distinct from the table and from one another *)
pose proof (Permutation_NoDup HPERM (gb_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR1)) as NDall.
apply NoDup_cons_iff in NDall. destruct NDall as (Hni & NDr).
destruct (gb_nd_app _ _ NDr) as (NDe & _ & Hde).
assert (HEB : aentry_blks e1 = (re_buf e1, re_cap e1) :: (re_hp e1, re_kh e1) ::
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
{ unfold aentry_blks. destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. destruct (Z.eqb_spec (re_hp e1) 0); [contradiction|].
  reflexivity. }
(* the held array is not the relay table's block *)
assert (Hhne : (re_hp e1, re_kh e1) <> (dxG cx, ATABLE)).
{ intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. unfold aentry_blks. apply in_or_app. right.
  apply in_or_app. left. destruct (Z.eqb_spec (re_hp e1) 0); [contradiction | left; reflexivity]. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 Hhin1 HGin1 Hhne) as Dht.
unfold zdisjoint in Dht. cbn [fst snd] in Dht. rewrite Hreqkh, RQT in Dht.
change (gb_sep (re_hp e1 + re_kh e1) (dxG cx) (dxG cx + 896) (re_hp e1)) in Dht.
(* the buffer is neither the table nor the held array *)
assert (Hbt : (re_buf e1, re_cap e1) <> (dxG cx, ATABLE)).
{ intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. rewrite HEB. left. reflexivity. }
assert (Hbh : (re_buf e1, re_cap e1) <> (re_hp e1, re_kh e1)).
{ intros Heq. rewrite HEB in NDe. apply NoDup_cons_iff in NDe as [Hn _]. apply Hn. rewrite Heq. left. reflexivity. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 Hbin HGin1 Hbt) as Dbt.
pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 Hbin Hhin1 Hbh) as Dbh.
unfold zdisjoint in Dbt, Dbh. cbn [fst snd] in Dbt, Dbh. rewrite Hreqc, RQT in Dbt. rewrite Hreqc, Hreqkh in Dbh.
change (gb_sep (re_buf e1 + re_cap e1) (dxG cx) (dxG cx + 896) (re_buf e1)) in Dbt.
change (gb_sep (re_buf e1 + re_cap e1) (re_hp e1) (re_hp e1 + re_kh e1) (re_buf e1)) in Dbh.
(* the frame base *)
assert (R2 : getr regs1 2 = w64 (dsp0 cx - DRAIN_FRAME)).
{ unfold w64. rewrite <- Usp. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hsp46 : 2 ^ 46 <= dsp0 cx - DRAIN_FRAME) by (rewrite WF; lia).
assert (Hsp47 : dsp0 cx - DRAIN_FRAME + 352 <= 2 ^ 47) by (rewrite WF; lia).
assert (Hsp16 : (dsp0 cx - DRAIN_FRAME) mod 16 = 0) by (rewrite WF, Zminus_mod, Hal16; reflexivity).
(* the two cells of the entry *)
assert (VH40 : val_mem SEGS (arm W1 m1) (dxSA cx + 40) 8 (re_hp e1))
  by (apply (gb_entry_hp W1 m1 _ e1 Kp1 ltac:(lia) HENT)).
assert (VH48 : val_mem SEGS (arm W1 m1) (dxSA cx + 48) 4 (re_nheld e1))
  by (apply (gb_entry_nheld W1 m1 _ e1 Kp1 ltac:(lia) HENT)).
assert (HW1 : forall oo, 48 <= oo < 52 -> writable_at SEGS (arm W1 m1) (dxSA cx + oo))
  by (intros oo Hoo; apply HAWR; unfold AENT; lia).
assert (HW2 : forall oo, 0 <= oo < 8 -> writable_at SEGS (arm W1 m1) (re_hp e1 + 8 * re_nheld e1 + oo)).
{ intros oo Hoo. apply (apresent_writable SEGS). exact (proj1 (Hhpres (re_hp e1 + 8 * re_nheld e1 + oo) ltac:(lia))). }
(* the seat *)
assert (HLL : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
assert (Hjj26 : 0 <= Z.of_nat jj <= 2 ^ 26) by lia.
pose proof (gb_seat B RG HGSB W1 regs1 m1 (dxSA cx) (dsp0 cx - DRAIN_FRAME) (re_hp e1) (re_nheld e1) (Z.of_nat jj)
  R2 R19 HSAlo ltac:(unfold gb_ceil; lia) HSA8 Hh4096 ltac:(unfold gb_ceil; lia) Hhp8 ltac:(lia) Hjj26
  Hsp46 Hsp47 Hsp16 ltac:(rewrite WF; lia) ltac:(rewrite WF; lia) ltac:(unfold gb_sep in Dht; unfold AENT, ATABLE in *; lia)
  V16 F32 F88 F128 F136 F144 V192 F240 VH40 VH48 HW1 HW2) as HS.
remember (Eimg (Ereg regs1 (gb_extra (dxSA cx) (re_hp e1) (re_nheld e1) (Z.of_nat jj)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs1 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = w64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = w64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = w64 (re_hp e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = w64 (re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = w64 (re_hp e1 + 8 * re_nheld e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = w64 (Z.of_nat jj))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
clear HE.
assert (E2 : ew E 2 = w64 (dsp0 cx - DRAIN_FRAME)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E3 : ew E 3 = getr regs1 3) by exact (EA 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs1 4) by exact (EA 4%nat ltac:(lia)).
assert (E8 : ew E 8 = w64 (rg_s RG)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E24 : ew E 24 = w64 (re_buf e1 + Z.of_nat p)) by exact (eq_trans (EA 24%nat ltac:(lia)) R24).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = re_hp e1 + 8 * re_nheld e1) by (rewrite E36; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS gb_Bx gb_SH E (mrestrict (w_H W1) m1)).
{ apply (gb_shok_x E ly1 S1 Hp1 W1 m1 md1 (dxG cx) (dxSA cx) (re_hp e1) (re_kh e1) (re_nheld e1) HAR1 HGin1 HGle HSAle
    Hhin1 Hnh0 ltac:(rewrite Hreqkh; lia) E33 E32 E36). }
subst c1. unfold cfg_at.
(* run 1: 0x83c00 .. the jal to strndup at 0x83c08 *)
paj_run_tok_xR RUNG HS HJ SHOK gb_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U36 in Ha.
  left. split; [|lia].
  replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply HGARW; [exact Hhin1 | rewrite Hreqkh; lia]. }
rename HFr into HFr1, HG0 into HGr1. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms1)) |- _ => rename Hg into GR1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
(* the run wrote nothing outside its two windows *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * re_nheld e1 <= x < re_hp e1 + 8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W1) (ms_mem ms1) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_gb gb_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi gb_frame gb_sa gb_slot base_val] in Hr;
    rewrite ?U32, ?U36 in Hr; lia. }
assert (HARm : ARx ly1 S1 Hp1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR_xR; exact HJ).
(* strndup (e->buf + p, jj) *)
set (x := re_buf e1 + Z.of_nat p).
assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
assert (G3 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, E3, R3; exact Hgp).
assert (G4 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, E4, R4; exact Htp).
assert (G10 : getr (ms_regs ms1) 10 = w64 x) by (rewrite Q10, E24; reflexivity).
assert (G11 : getr (ms_regs ms1) 11 = w64 (Z.of_nat jj)) by (rewrite Q11, E37; reflexivity).
assert (NZ : forall i, 0 <= i < Z.of_nat jj -> exists b, aview SEGS (w_H W1) (ms_mem ms1) (x + i) = Some b /\ b <> 0).
{ intros i Hi. exists (nth (p + Z.to_nat i) (dW s1) 0).
  assert (Hidx' : (p + Z.to_nat i < length (dW s1))%nat) by lia.
  split.
  - rewrite KEEP1 by (unfold gb_sep in Dbt, Dbh; unfold x, AENT, ATABLE in *; lia).
    replace (x + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by (unfold x; lia).
    apply BV. exact Hidx'.
  - intros H0. apply (HNZ (p + Z.to_nat i)%nat ltac:(lia)). rewrite (nth_error_nth' (dW s1) 0 Hidx'). rewrite H0.
    reflexivity. }
assert (Hlive : blocks_bytes S1 + (Z.of_nat jj + 1) <= LIVE_MAX).
{ pose proof (W_tr_peak.tr_peak_nonneg tl2) as Hnn. rewrite Htl, W_tr_peak.tr_peak_malloc in Halloc. lia. }
assert (Hmok : mo_ok MT S1 (mo_malloc MT (Z.of_nat jj + 1))).
{ pose proof (mo_free_nonneg MT MTL) as Hf.
  unfold tr_cost in Hcost, Hcost2. rewrite Htl in Hcost. cbn [fold_right] in Hcost.
  apply (mok_station MT (dxS cx) S1 _ spent _ MTL HMOK Hle0); [apply (mo_malloc_nonneg MT MTL); lia | lia]. }
(* the room round: MT_rk charges strndup's request 2, the rule takes 1; the rest is dbud_x's room at tl2 *)
assert (HRMc : rp_RM RP S1 (1 + (Z.to_nat (tr_cost MT_rk tl2) + kr))).
{ apply (gs_rm_take RP S1 [RelayRunT.RMalloc (Z.of_nat jj + 1)] tl2 kr 1); [unfold tr_cost; cbn; lia|].
  rewrite Htl in HRM1. exact HRM1. }
assert (HSTK0 : 0 <= DRAIN_STK_x) by lia.
destruct HJ as (HSTK1 & HXO1 & (memS1 & HJi1 & HAG1) & HOUT1). rewrite !Z.add_0_r in HJi1.
(* frame0_ok at this call (gb_frame0_xR), the rule's premise after chain_pre: sp = dsp0 cx - 352 *)
assert (HF0 : frame0_ok ly1 (ms_regs ms1) = true)
  by (apply (gb_frame0_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (- DRAIN_FRAME) (ms_regs ms1) HJi1);
      [rewrite Usp1; lia | rewrite WF; lia]).
(* strndup's source in a live block (gb_src_blk_x), the rule's premise after shadow_hull_vis *)
assert (HSRCB : exists p0 m0, In (p0, m0) (ablocks B ly1 S1) /\ p0 <= x /\ x + Z.of_nat jj <= p0 + req_size m0)
  by exact (gb_src_blk_x ly1 S1 e1 p jj Hbin ltac:(lia) ltac:(lia)).
eapply (SRrG_bind SEGS R R_trans).
{ eapply (ASTRNDUP_R W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) memS1
    (dxmd cx) [] ly1 S1 Hp1 _ k1 x (Z.of_nat jj) (- DRAIN_FRAME) _ [] (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat
    HJi1 G10 G11).
  - unfold x. lia.
  - lia.
  - unfold x. lia.
  - unfold tr_max in Hmax. rewrite Htl in Hmax. cbn [fold_right] in Hmax. lia.
  - exact Hlive.
  - (* the count premise: the live counts, from dbud_x's *)
    exact (gs_cnt_call RP _ _ HCNT1).
  - exact NZ.
  - intros aa Ha. unfold x in Ha. unfold ASTACK. lia.
  - apply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat md1)
      (re_buf e1) (re_cap e1)); [exact HARm | exact Hbin | unfold x; lia |].
    rewrite Hreqc. unfold x. lia.
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms1)
      (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1));
      [exact HARm | exact Hbin | unfold x; lia | rewrite Hreqc; unfold x; lia].
  - intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms1)
      (with_vm_backing (m_vm_lazy md1) mat md1) (re_buf e1) (re_cap e1));
      [exact HARm | exact Hbin | unfold x; lia | rewrite Hreqc; unfold x; lia | exact Hpos].
  - (* the source lies in a live block: the relay entry's buffer *)
    exact HSRCB.
  - rewrite Usp1. lia.
  - rewrite WF. reflexivity.
  - rewrite WF. lia.
  - rewrite WF, WS. unfold ASTACK. lia.
  - (* the stack room below the call, from the inner journal *)
    eapply aj_stack_room_xR with (o := - DRAIN_FRAME); [exact HJi1 | rewrite Usp1; lia | rewrite WF, WS; unfold ASTACK; lia].
  - (* the strndup interceptor's inner malloc below the call (the rule's third premise, 2160 + 2144 = 4304): the
       journal at DRAIN_STK_x leaves 4368 bytes above ly_bot at this call (gb_stk_bot_xR) *)
    apply (gb_stk_bot_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (- DRAIN_FRAME) (ms_regs ms1) HJi1);
      [rewrite Usp1; lia | rewrite WF, WS; unfold ASTACK; lia].
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof HGSB as (Hg1 & Hg2 & _).
    apply (achain_chain_pre ly1 _ (spZ (ms_regs ms1)) (s0Z (ms_regs ms1)) [] (ms_regs ms1)).
    + apply achain_low. unfold s0Z. rewrite Q8, E8. unfold w64.
      rewrite unsigned_lit_small by (unfold ASRC, IMG_TOP in *; lia). unfold ASRC, IMG_TOP in *. lia.
    + rewrite Usp1. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* frame0_ok: drain's frame lies below the entry layout's top *)
    exact HF0.
  - (* the caller-context fact: drain's chain is cut here, so the trace is the return address alone (HCTX_sd) *)
    unfold raZ. cbn [spine map]. rewrite Q1. rewrite unsigned_lit_small by lia.
    match goal with |- In [?x] _ => replace x with (BASE + AF_fr_drain + 0x994) by (unfold AF_fr_drain; lia) end.
    exact HCTX_sd.
  - (* the rule's room *)
    exact HRMc.
  - exact Hmok. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres10 & Hfrm2 & Hres4096 &
  Hbl2 & Hcpy & Hnul & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
pose proof (proj1 HJ2i) as HAR2.
assert (HGin2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact HGin1).
assert (Hhin2 : In (re_hp e1, re_kh e1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hhin1).
assert (Hrin2 : In (res, Z.of_nat jj + 1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hreqr : req_size (Z.of_nat jj + 1) = Z.of_nat jj + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat jj + 1) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hrin2) as (Hr16 & _ & Hrceil & Hrapp & Hrpres & _).
rewrite Hreqr in Hrceil, Hrapp, Hrpres.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 HGin2) as (_ & _ & _ & _ & HGpres2 & _).
rewrite RQT in HGpres2.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hhin2) as (_ & _ & _ & _ & Hhpres2 & _).
rewrite Hreqkh in Hhpres2.
pose proof (gb_new_disj_x ly2 S2 Hp2 W2 mem2 md2 ly1 S1 res _ _ _ HAR2 Hbl2 HGin1) as DnG. rewrite RQT, Hreqr in DnG.
pose proof (gb_new_disj_x ly2 S2 Hp2 W2 mem2 md2 ly1 S1 res _ _ _ HAR2 Hbl2 Hhin1) as Dnh. rewrite Hreqkh, Hreqr in Dnh.
change (gb_sep (dxG cx + 896) res (res + (Z.of_nat jj + 1)) (dxG cx)) in DnG.
change (gb_sep (re_hp e1 + re_kh e1) res (res + (Z.of_nat jj + 1)) (re_hp e1)) in Dnh.
destruct Hkept2 as (KS2 & KB2 & KI2 & KF2 & KP2 & KSP2).
(* the symbolic state after the call: the three regions are kept *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?E2, ?U32, ?U36.
  - rewrite unsigned_lit_small by lia. intros aa Ha. apply (mbyte_of_aview SEGS). apply KS2; [lia|]. unfold ASTACK. lia.
  - rewrite unsigned_lit_small by lia. intros aa Ha. lia.
  - intros aa Ha. apply (mbyte_of_aview SEGS).
    replace aa with (dxG cx + (aa - dxG cx)) by lia. apply (KB2 _ _ _ HGin1); [rewrite RQT; unfold AENT, ATABLE in *; lia|].
    cbv beta. rewrite Hreqr. unfold gb_sep in DnG. unfold AENT, ATABLE in *. lia.
  - intros aa Ha _. apply (apresent_writable SEGS). exact (proj1 (HGpres2 aa ltac:(unfold AENT, ATABLE in *; lia))).
  - intros aa Ha. apply (mbyte_of_aview SEGS).
    replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply (KB2 _ _ _ Hhin1); [rewrite Hreqkh; lia|].
    cbv beta. rewrite Hreqr. unfold gb_sep in Dnh. lia.
  - intros aa Ha _. apply (apresent_writable SEGS). exact (proj1 (Hhpres2 aa ltac:(lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea44 : ew Ea 44 = w64 res) by (rewrite HEa; exact Hres10).
clear HEa.
assert (HFa : afact_ok Ea 44 (mkAF 4096 gb_ceil 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea44. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite Hr16. unfold gb_ceil. lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 44%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ2 : ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx)
  (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx)
    (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 1) memS1);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG1 | intros aa Haa; lia]. }
assert (U32a : bv_unsigned (ew Ea 32) = dxSA cx) by (rewrite OLDa by lia; exact U32).
assert (U36a : bv_unsigned (ew Ea 36) = re_hp e1 + 8 * re_nheld e1) by (rewrite OLDa by lia; exact U36).
assert (SHOK2 : sh_ok SEGS gb_Bx gb_SH Ea (mrestrict (w_H W2) mem2)).
{ apply (gb_shok_x Ea ly2 S2 Hp2 W2 mem2 md2 (dxG cx) (dxSA cx) (re_hp e1) (re_kh e1) (re_nheld e1) HAR2 HGin2 HGle HSAle
    Hhin2 Hnh0 ltac:(rewrite Hreqkh; lia)); rewrite OLDa by lia; assumption. }
(* run 2a: 0x83c0c .. the PTR_SOVF check at 0x83c74.  On the way the runner decides strndup's NULL arm
   (0x83c0c, the result atom's fact), the shadow checks of &e->nheld / &e->held (shadow entry over the entry),
   the ADDW1 trap 0x83c28 (nheld is an int32-safe atom) and the NULL_BEQ trap 0x83c60 (held and the slot are
   pointer atoms), and stores e->nheld = nheld + 1 (0x83c5c). *)
paj_run_tok_xR RUNG HS HJ2 SHOK2 gb_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U32a, ?U32b in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U36a, ?U36b in Ha.
  left. split; [|lia].
  replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply HGARW; [exact Hhin2 | rewrite Hreqkh; lia]. }
rename HFr into HFr2, HG0 into HGr2. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
match goal with Hg : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms2)) |- _ => rename Hg into GR2 end.
(* run 2a makes no fresh atom: the state after it is still over Ea *)
lazymatch type of HS with st_ok_pi _ _ Ea _ _ => idtac | _ => fail "gs_addb_xR: run 2a changed the environment" end.
(* 0x83c74, PTR_SOVF (W_drain_cx.v census row GS 0x83c74): slti nheld,0 is folded to 0 by nheld's fact; the
   sltu slot, held compares two atoms the runner does not order (lib/B/W_traps.v R5), so the trap edge is closed
   by trap_ptr_sovf with trap_U_sltu_ge: the slot hp + 8 nh is not below hp *)
psrr_branch_tok RUNG BRR HS SHOK2 gb_Bspan; rename Hc into BZ.
{ exfalso.
  assert (Uh : U Ea (SOff 34 0) = re_hp e1)
    by (apply (U_atom Ea 34); [rewrite OLDa by lia; exact E34 | lia]).
  assert (Us : U Ea (SOff 36 0) = re_hp e1 + 8 * re_nheld e1)
    by (apply (U_atom Ea 36); [rewrite OLDa by lia; exact E36 | lia]).
  rewrite (trap_ptr_sovf Ea _ _ 0 (trap_U_sltu_ge Ea _ _ _ _ Uh Us ltac:(lia)) (U_lit Ea 0 ltac:(lia))) in BZ.
  discriminate. }
(* run 2b: 0x83c78 .. the line loop's head 0x839d4: NONNULL 0x83c78 and ALIGN8 0x83c80 decided (R1 / R2), the
   slot's shadow byte covered (0x83c90), s5 / s6 / s4 reloaded from 144 / 136 / 128 (sp), the slot gets res *)
paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 gb_Bspan A_dr_next.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U32a, ?U32a in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U36a, ?U36a in Ha.
  left. split; [|lia].
  replace aa with (re_hp e1 + (aa - re_hp e1)) by lia. apply HGARW; [exact Hhin2 | rewrite Hreqkh; lia]. }
rename HFr into HFr3. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
match goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms2)) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hg into GR3 end.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARf.
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (27%bv : bv 5) P27.
assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs ms3) r = ew Ea k -> (k < 32)%nat ->
  ew E k = getr regs1 r -> getr (ms_regs ms3) r = getr regs1 r).
{ intros r k Hr Hk Hek. rewrite Hr. rewrite (OLDa k) by lia. exact Hek. }
assert (P21' : getr (ms_regs ms3) 21 = w64 (dxSA cx)).
{ rewrite P21. rewrite (OLDa 32%nat) by lia. exact E32. }
assert (P22' : getr (ms_regs ms3) 22 = w64 (dxSA cx + 24)) by (rewrite P22, U32a; reflexivity).
assert (P20' : getr (ms_regs ms3) 20 = w64 (dxSA cx + 16)) by (rewrite P20, U32a; reflexivity).
assert (P27' : getr (ms_regs ms3) 27 = w64 (dxSA cx + 32)).
{ rewrite P27. rewrite (OLDa 27%nat) by lia.
  rewrite (EA 27%nat ltac:(lia)). exact R27. }
(* the two cells and the slot the runs wrote *)
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSA.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RSL.
cbn [ms_mem restrict] in RSA, RSL.
assert (VHP : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (dxSA cx + 40) (N.to_nat 8) (re_hp e1)).
{ eapply (field_of_region Ea _ 32 (dxSA cx));
    [exact RSA | exact U32a | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  apply den_atom0; [rewrite OLDa by lia; exact E34 | lia]. }
assert (VNH : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (dxSA cx + 48) (N.to_nat 4) (re_nheld e1 + 1)).
{ eapply (field_of_region Ea _ 32 (dxSA cx));
    [exact RSA | exact U32a | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  apply (den_atom Ea 35 (re_nheld e1) 1); [rewrite OLDa by lia; exact E35 | lia | lia]. }
assert (VSL : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (re_hp e1 + 8 * re_nheld e1 + 0) (N.to_nat 8) res).
{ eapply (field_of_region Ea _ 36 (re_hp e1 + 8 * re_nheld e1));
    [exact RSL | exact U36a | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  apply den_atom0; [exact Ea44 | lia]. }
rewrite Z.add_0_r in VSL.
(* what the two runs kept: everything outside their two windows *)
assert (K3 : forall xx, 0 <= xx < 2 ^ 64 -> ~ (dxSA cx + 48 <= xx < dxSA cx + 52) ->
  ~ (re_hp e1 + 8 * re_nheld e1 <= xx < re_hp e1 + 8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W2) mem2 xx).
{ intros xx Hx H1 H2.
  rewrite (aview_kept_out Ea _ (w_H W2) (ms_mem ms2) (ms_mem ms3) HFr3 xx Hx).
  - apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms2) HFr2 xx Hx). apply gb_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U32a, ?U36a; lia.
  - apply gb_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U32a, ?U36a; lia. }
assert (GR23 : forall xx, apresent (w_H W2) mem2 xx -> apresent (w_H W2) (ms_mem ms3) xx)
  by (intros xx Hq; apply (gb_apresent_grows _ (ms_mem ms2) _ _ GR3); exact (gb_apresent_grows _ mem2 _ _ GR2 Hq)).
(* the view of an old block's byte outside the two windows is the view at GAR *)
assert (KVB : forall b n xx, In (b, n) (ablocks B ly1 S1) -> b <= xx < b + req_size n ->
  ~ (dxSA cx + 48 <= xx < dxSA cx + 52) -> ~ (re_hp e1 + 8 * re_nheld e1 <= xx < re_hp e1 + 8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
{ intros b n xx Hin Hx H1 H2.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 b n HAR1 Hin) as (_ & Hb4 & Hbc & _).
  pose proof (gb_new_disj_x ly2 S2 Hp2 W2 mem2 md2 ly1 S1 res _ _ _ HAR2 Hbl2 Hin) as Dn. rewrite Hreqr in Dn.
  rewrite K3 by lia.
  replace xx with (b + (xx - b)) by lia.
  rewrite (KB2 b n (xx - b) Hin ltac:(lia)) by (cbv beta; rewrite Hreqr; lia).
  replace (b + (xx - b)) with xx by lia. apply KEEP1; lia. }
assert (KT : forall xx, dxG cx <= xx < dxG cx + ATABLE -> ~ (dxSA cx + 48 <= xx < dxSA cx + 52) ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
{ intros xx Hx H1. apply (KVB (dxG cx) ATABLE xx HGin1); [rewrite RQT; unfold ATABLE in Hx; lia | exact H1 |].
  unfold gb_sep in Dht. unfold ATABLE in *. lia. }
assert (KH : forall xx, re_hp e1 <= xx < re_hp e1 + 8 * re_nheld e1 ->
  aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
{ intros xx Hx. apply (KVB (re_hp e1) (re_kh e1) xx Hhin1);
    [rewrite Hreqkh; lia | unfold gb_sep in Dht; unfold AENT, ATABLE in *; lia | lia]. }
assert (KB : forall b n xx, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) ->
  (b, n) <> (re_hp e1, re_kh e1) -> b <= xx < b + req_size n -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros b n xx Hin Hn1 Hn2 Hx.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n _ _ HAR1 Hin HGin1 Hn1) as D1.
  pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n _ _ HAR1 Hin Hhin1 Hn2) as D2.
  unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2. rewrite RQT in D1. rewrite Hreqkh in D2.
  split.
  - apply (KVB b n xx Hin Hx); unfold AENT, ATABLE in *; lia.
  - intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 (ms_mem ms3) _ b n HARf
      ltac:(rewrite Hbl2; apply in_or_app; left; exact Hin)) as (_ & _ & _ & _ & Hq & _).
    exact (proj1 (Hq xx Hx)). }
(* an image byte is outside both windows (they lie in heap blocks) *)
assert (NWI : forall xx, in_img SEGS xx ->
  ~ (dxSA cx + 48 <= xx < dxSA cx + 52) /\ ~ (re_hp e1 + 8 * re_nheld e1 <= xx < re_hp e1 + 8 * re_nheld e1 + 8)).
{ intros xx Hi. split.
  - intros Hw. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE xx HAR1 HGin1);
      [rewrite RQT; unfold AENT, ATABLE in *; lia | exact Hi].
  - intros Hw. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) xx HAR1 Hhin1);
      [rewrite Hreqkh; lia | exact Hi]. }
(* an image byte off the allocator's statics and off errno: present then present now *)
assert (PRES : forall xx, in_img SEGS xx -> ~ Exists (in_zr xx) (as_owned_static B) ->
  ~ (as_errno B <= xx < as_errno B + 4) -> apresent (w_H W1) m1 xx -> apresent (w_H W2) (ms_mem ms3) xx).
{ intros xx Hi Hno Hne Hq. apply GR23. apply Hpres2; [exact Hi | | | exact Hne | |].
  - intros Ho. apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 xx HAR1 Hi) Ho).
  - intros Ho. apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 xx HAR2 Hi) Ho).
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res (Z.of_nat jj + 1) xx HAR2 Hrin2 Hr Hi).
  - exact (gb_apresent_grows _ m1 _ _ GR1 Hq). }
assert (KIMGP : forall xx, in_img SEGS xx -> ~ Exists (in_zr xx) (as_owned_static B) ->
  ~ (as_errno B <= xx < as_errno B + 4) -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hi Hno Hne. pose proof (pa_img_range xx Hi) as Hxr. destruct (NWI xx Hi) as (N1 & N2).
  assert (HV : aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
  { rewrite K3 by lia. rewrite (KI2 xx Hi Hno Hne). apply KEEP1; lia. }
  split; [exact HV|]. apply (gb_writable_img B RG W1 W2 m1 (ms_mem ms3) xx Hi). exact (PRES xx Hi Hno Hne). }
assert (KG : forall xx, inG (G_DR B RG) xx -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hx. destruct (HG xx Hx) as (Hi & Hno & _).
  destruct (Z_le_gt_dec (as_errno B) xx) as [He1 | He1];
    [destruct (Z_lt_ge_dec xx (as_errno B + 4)) as [He2 | He2] | apply KIMGP; [exact Hi | exact Hno | lia]];
    [| apply KIMGP; [exact Hi | exact Hno | lia]].
  pose proof (pa_img_range xx Hi) as Hxr. destruct (NWI xx Hi) as (N1 & N2).
  assert (HV : aview SEGS (w_H W2) (ms_mem ms3) xx = aview SEGS (w_H W1) m1 xx).
  { rewrite K3 by lia. replace xx with (as_errno B + (xx - as_errno B)) by lia.
    rewrite (Herr2 (xx - as_errno B)) by lia. replace (as_errno B + (xx - as_errno B)) with xx by lia.
    apply KEEP1; lia. }
  split; [exact HV | exact (gb_writable_view B RG W1 W2 m1 (ms_mem ms3) xx Hi (HGR xx Hx) HV)]. }
assert (KO : forall xx, inG (GBGO RG) xx -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hx. destruct (HGO xx Hx) as (Hi & Hno & _). apply KIMGP; [exact Hi | exact Hno |].
  unfold GBGO, inG in Hx. apply Exists_exists in Hx as (r & Hr & Hxr). unfold in_zr in Hxr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hxr.
  - pose proof (gb_zpd_nth B RG _ 3 11 _ _ HRGD ltac:(lia) eq_refl eq_refl) as Dz. unfold zdisj in Dz. cbn [fst snd] in Dz. lia.
  - pose proof (gb_zpd_nth B RG _ 6 11 _ _ HRGD ltac:(lia) eq_refl eq_refl) as Dz. unfold zdisj in Dz. cbn [fst snd] in Dz. lia.
  - pose proof (gb_zpd_nth B RG _ 7 11 _ _ HRGD ltac:(lia) eq_refl eq_refl) as Dz. unfold zdisj in Dz. cbn [fst snd] in Dz. lia. }
assert (KFRM : forall xx, dsp0 cx - DRAIN_FRAME <= xx < dsp0 cx -> abyte_kept W1 m1 W2 (ms_mem ms3) xx).
{ intros xx Hx. rewrite WF in Hx.
  split.
  - rewrite K3 by lia. rewrite KS2 by (unfold ASTACK in *; rewrite ?WF; lia). apply KEEP1; lia.
  - apply (gb_writable_noimg B RG W1 W2 m1 (ms_mem ms3) xx); [intros Hi; pose proof (pa_img_range xx Hi); lia | lia |].
    intros Hq. apply GR23. apply KP2; [lia | unfold ASTACK in *; rewrite ?WF; lia |].
    exact (gb_apresent_grows _ m1 _ _ GR1 Hq). }
assert (KPR : apres_kept B W1 m1 W2 (ms_mem ms3)) by (intros xx Hi Hno Hne Hq; exact (PRES xx Hi Hno Hne Hq)).
(* the new key's bytes *)
assert (KN : forall i, 0 <= i < Z.of_nat jj ->
  aview SEGS (w_H W2) (ms_mem ms3) (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)).
{ intros i Hi. rewrite K3 by (unfold gb_sep in DnG, Dnh; unfold AENT, ATABLE in *; lia). rewrite (Hcpy i Hi). unfold x.
  apply KEEP1; unfold gb_sep in Dbt, Dbh; unfold AENT, ATABLE in *; lia. }
assert (KNUL : aview SEGS (w_H W2) (ms_mem ms3) (res + Z.of_nat jj) = Some 0).
{ rewrite K3 by (unfold gb_sep in DnG, Dnh; unfold AENT, ATABLE in *; lia). exact Hnul. }
apply (HN W2).
exact (gb_dln_xR cx Hp kr s1 D p q jj regs1 ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl tl2 a jb' o' ha' ks'
  (ms_regs ms3) ly2 S2 Hp2 W2 (ms_mem ms3) _ res HB HRL R23 Hbnd Hcap0 Hhp0 Hkh Hges Hjj Hidx HGSF HCORE HDLF Htl HJ2
  Hbl2 Hfrm2 Hmle2 HRM2
  (RK _ 2%nat P2 ltac:(lia) (EA 2%nat ltac:(lia))) (RK _ 3%nat P3 ltac:(lia) (EA 3%nat ltac:(lia)))
  (RK _ 4%nat P4 ltac:(lia) (EA 4%nat ltac:(lia))) (RK _ 8%nat P8 ltac:(lia) (EA 8%nat ltac:(lia)))
  (RK _ 9%nat P9 ltac:(lia) (EA 9%nat ltac:(lia))) (RK _ 18%nat P18 ltac:(lia) (EA 18%nat ltac:(lia)))
  P21' P20' P22' P27' (RK _ 23%nat P23 ltac:(lia) (EA 23%nat ltac:(lia)))
  VHP VNH VSL KT KH KB KG KO KFRM KPR KN KNUL).
Qed.

End wR.
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Lemma gb_frame0_x : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memT mdc k (o : Z)
  (regsT : bvmap 5 word),
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o + 16 < 0 -> frame0_ok lyc regsT = true.
Proof. eapply (gb_frame0_xR (@wle SEGS)); wle_inst. Qed.
Lemma gb_stk_bot_x : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memT mdc k (o : Z)
  (regsT : bvmap 5 word),
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> ASTACK - o + 2160 + 2144 <= STK + ACALL_PREFIX -> ly_bot lyc + 2160 + 2144 < spZ regsT.
Proof. eapply (gb_stk_bot_xR (@wle SEGS)); wle_inst. Qed.
Lemma gb_dmem_x : forall cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp' (W' : world SEGS) m' md' k' e' s',
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
ajournal_gx_x SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' Hp' W' m' md' k' ->
rom_view SEGS (dxW cx) (dxmem cx) ->
apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
garr8 SEGS (arm W' m') (dxSA cx) (bzs (entry_bytes e')) -> awr W' m' (dxSA cx) AENT ->
aentry_okx B ly' S' W' m' e' ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W m W' m' a) ->
akept W m W' m' (asrc_fp (dHA RG cx) h) -> (forall b, In b (asrc_blks h) -> In b (ablocks B ly' S')) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
(forall b, In b (aout_blks (drain_b_c.ds_ocap s) out) -> In b (ablocks B ly' S')) ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e' ++ asrc_blks h ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM_x B PST ARx RG cx Hp ly' S' Hp' W' m' md' k' e' h s' out ev sent LB.
Proof. eapply (gb_dmem_xR (@wle SEGS)); wle_inst. Qed.
Lemma gb_dln_x : forall cx Hp kr s1 D (p q jj : nat) regs1 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl tl2 a jb' o' ha' ks' regs3 ly2 S2 Hp2 (W2 : world SEGS) m3 md3 res,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_gs RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
re_hp e1 <> 0 -> re_kh e1 = 8 * re_nheld e1 + 8 ->
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None ->
GSF s1 p q ->
GARB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (GSno cx s1 p q) (GSoc cx s1 p q)
  (seen_arr (dlH cx s1 p) (dline s1 p q)) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (drlq s1 (S q)) jb' o' ha' ks' tl2 ->
tl = RelayRunT.RMalloc (Z.of_nat jj + 1) :: tl2 ->
ajournal_gx_x SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 Hp2 W2 m3 md3 (k1 + 1) ->
ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, Z.of_nat jj + 1)] ->
frames S2 = frames S1 ->
mo_le MT S1 S2 (mo_malloc MT (Z.of_nat jj + 1)) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tl2) + kr) ->
getr regs3 2 = getr regs1 2 -> getr regs3 3 = getr regs1 3 -> getr regs3 4 = getr regs1 4 ->
getr regs3 8 = getr regs1 8 -> getr regs3 9 = getr regs1 9 -> getr regs3 18 = getr regs1 18 ->
getr regs3 21 = w64 (dxSA cx) -> getr regs3 20 = w64 (dxSA cx + 16) ->
getr regs3 22 = w64 (dxSA cx + 24) -> getr regs3 27 = w64 (dxSA cx + 32) ->
getr regs3 23 = getr regs1 23 ->
val_mem SEGS (arm W2 m3) (dxSA cx + 40) 8 (re_hp e1) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 48) 4 (re_nheld e1 + 1) ->
val_mem SEGS (arm W2 m3) (re_hp e1 + 8 * re_nheld e1) 8 res ->
(forall x, dxG cx <= x < dxG cx + ATABLE -> ~ (dxSA cx + 48 <= x < dxSA cx + 52) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x) ->
(forall x, re_hp e1 <= x < re_hp e1 + 8 * re_nheld e1 -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x) ->
(forall b n x, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) -> (b, n) <> (re_hp e1, re_kh e1) ->
   b <= x < b + req_size n -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, inG (G_DR B RG) x -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, inG (GBGO RG) x -> abyte_kept W1 m1 W2 m3 x) ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x) ->
apres_kept B W1 m1 W2 m3 ->
(forall i, 0 <= i < Z.of_nat jj ->
   aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)) ->
aview SEGS (w_H W2) m3 (res + Z.of_nat jj) = Some 0 ->
DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 (cfg_at SEGS (BASE + A_dr_next) regs3 m3 md3).
Proof. eapply (gb_dln_xR (@wle SEGS)); wle_inst. Qed.
Theorem gs_addb_x : gs_addb_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_addb_xR (@wle SEGS)); wle_inst. Qed.
End cx.
End bx.
End ax.
