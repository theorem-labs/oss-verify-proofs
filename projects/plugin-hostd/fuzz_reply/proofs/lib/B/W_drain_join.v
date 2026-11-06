(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_join.v, the MEMCHR JOIN of the image-B (fuzz_reply.asan-ubsan)
   walk of fuzz_reply's drain.  Proves no function (kind: segment lemma): the stage lemma dr_memchr_join, over
   lib/B/W_drain_cx.v's cut predicates (a working branch 789597341d1; that file is not edited).
   B's line loop re-enters at 0x8395c, and both DLL (0x8399c) and DLR (0x83e34) are reached from the ONE memchr at
   0x83990 (W_drain_cx.v:38-40), so DROP (DE 0x838a0 -> 0x8395c, with p = 0) and NEXT (DLN 0x839d4 -> 0x8395c) both
   end in the cut DJ below and take dr_memchr_join.  DJ is DLN's text (dregs_line, dinband, dbound, DLC, dlfut) with
   the pc 0x8395c, s8 = buf + p in place of DLN's s7 = buf + p - 1, and s10 = 384 (DLL / DLR's own conjunct).
   The walk, from fuzz_reply.asan-ubsan's objdump:
     0x8395c  ld a0,232(sp); lbu a0,0(a0); bnez a0 -> 0x84028   shadow check of s->used (SA + 24), NOT TAKEN
     0x83968  ld a0,224(sp); lbu a0,0(a0); bnez a0 -> 0x84030   shadow check of s->buf (SA + 16), NOT TAKEN
     0x83974  ld s3,0(s4); ld s9,0(s6)                          s3 = s->buf, s9 = s->used
     0x8397c  sub a0,s3,s8; add s9,a0,s9                        s9 = used - p
     0x83984  mv a0,s8; mv a1,zero; mv a2,s9; jal memchr        memchr (buf + p, 0, used - p)   (AMEMCHR)
     0x83994  beqz a0 -> 0x83e34                                no NUL from p on: DLR p
     0x83998  mv s7,a0                                          the NUL at q: DLL p q, s7 = buf + q
   No UBSan trap on this stretch (W_drain_cx.v:121-185 lists none here); the two shadow checks are decided by the
   runner from the table block's shadow (sh_ok of [SA, SA + 56)).
   STRUCTURE PORTED FROM the older halts-level walk of the same image, a working branch
   1c09e330abe lib/B/Prog/drain_p_line_test.v (the memchr test: one site, found / not found) and
   lib/B/Prog/drain_p_lsh.v (the line head's shadow checks); nothing is copied, the vocabulary (SRr over AR, journal
   ajournal_gx, symbolic seats) is this framework's, and the memchr call follows lib/B/W_next_line.v:581-707.
   ARx FORM (an internal work row): Section cx states the cut DJ_x and proves dr_memchr_join_x : dr_memchr_join_stmt_x over any
   allocator relation ARx (W_drain_cx_x.v's cut predicates, Section c header plus HP0), its journal at W_contract_x.v's
   DRAIN_STK_x; the AR walk (Section c) is unchanged.  The memchr call takes W_sites_x.v's amemchr_realizesM_x through
   dj_aentry_of_memchrM_x, the ARx twin of W_next_line.v's aentry_of_memchrM. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_dnrk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps W_next_line.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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

(* ------------------------------------------------------------------ the symbolic state at 0x8395c *)
(* Atoms 0..31: the registers, with s4 = SA + 16 and s6 = SA + 24 pinned; 32 = SA, 33 = SHADOW_OFF, 34 = s->buf,
   35 = s->used.  The frame region holds the two shadow-address slots the walk reads (224(sp), 232(sp)) in the
   shadow form the runner's tok_load recognises; the entry region holds s->buf and s->used. *)
Definition A_dr_join : Z := AF_fr_drain + 0x6e4.
Definition dj_Bx : sv := SOff 33 0.
Definition dj_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition dj_shg (c : Z) : cval := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 c) (SLit 3)) (SOff 33 0)).
Definition dj_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 352 0 0 [YP09.mkChunk 224 (dj_shg 16); YP09.mkChunk 232 (dj_shg 24)].
Definition dj_ent : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 56 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))].
Definition dj_regs : list sv := sr_set (sr_set sr_atoms 20%bv (SOff 32 16)) 22%bv (SOff 32 24).
Definition dj_PTRF : afact := mkAF 4096 140737479966720 3.
Definition dj_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (24%nat, mkAF 4096 140737479966720 0); (32%nat, dj_PTRF);
            (33%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (34%nat, dj_PTRF); (35%nat, mkAF 0 16384 0) ] [] [].
Definition dj_ss : sstate := mkSS A_dr_join dj_regs [dj_frame; dj_ent] None dj_facts.
Definition dj_SH : list shent := [mkSHE 32 0 56].
Definition dj_extra (SA buf used : Z) : list word := map (Z_to_bv 64) [SA; SHADOW_OFF; buf; used].

Lemma dj_den_sh : forall E SA c, ew E 32 = Z_to_bv 64 SA -> ew E 33 = Z_to_bv 64 SHADOW_OFF ->
  0 <= SA -> SA + c < 2 ^ 60 -> 0 <= c ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 c) (SLit 3)) (SOff 33 0)) = Z_to_bv 64 (shadow_addr (SA + c)).
Proof.
intros E SA c H32 H33 H0 H1 Hc.
assert (H8 : 0 <= (SA + c) / 8 <= SA + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 32 SA c H32 ltac:(lia) ltac:(lia)), U_SLit, (zcanon_id 3) by (unfold M64; lia).
rewrite (U_atom E 33 SHADOW_OFF H33 ltac:(unfold SHADOW_OFF; lia)).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((SA + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma dj_negmul : forall a b c,
alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 18446744073709551615)) (Z_to_bv 64 b))
  (Z_to_bv 64 c) = Z_to_bv 64 (b - a + c).
Proof.
intros a b c. apply bv_eq. rewrite !alu64_unsigned, mul_div_unsigned. cbn [zalu_raw zmd_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Zmult_mod. rewrite <- (Zplus_mod (a * 18446744073709551615) b (2 ^ 64)).
rewrite <- (Zplus_mod (a * 18446744073709551615 + b) c (2 ^ 64)).
replace (a * 18446744073709551615 + b + c) with (b - a + c + a * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.

(* the bytes of the relay's buffer, as a reader sees them *)
Lemma dj_buf_byte : forall H (mem : word -> option byte) base l l2 j,
garr8 SEGS (mrestrict H mem) base (l ++ l2) -> (j < length l)%nat ->
aview SEGS H mem (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H mem base l l2 j Hg Hj.
assert (Hj2 : (j < length (l ++ l2))%nat) by (rewrite length_app; lia).
pose proof (garr8_mbyte SEGS _ _ _ j Hg Hj2) as Hm. pose proof (proj2 (Hg j Hj2)) as Hr.
rewrite app_nth1 in Hm, Hr by exact Hj.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* the first NUL at or after p, or none *)
Lemma dj_scan : forall (l : list Z) (p : nat), (p <= length l)%nat ->
(exists q, (p <= q < length l)%nat /\ nth_error l q = Some 0 /\ forall i, (p <= i < q)%nat -> nth_error l i <> Some 0) \/
(forall i, (p <= i)%nat -> nth_error l i <> Some 0).
Proof.
intros l. assert (G : forall n p, (length l - p = n)%nat -> (p <= length l)%nat ->
  (exists q, (p <= q < length l)%nat /\ nth_error l q = Some 0 /\ forall i, (p <= i < q)%nat -> nth_error l i <> Some 0) \/
  (forall i, (p <= i)%nat -> nth_error l i <> Some 0)).
{ induction n as [|n IH]; intros p Hn Hp.
  - right. intros i Hi. rewrite (proj2 (nth_error_None l i)) by lia. discriminate.
  - destruct (nth_error l p) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
    assert (Hpl : (p < length l)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
    destruct (Z.eq_dec b 0) as [-> | Hb].
    + left. exists p. split; [lia|]. split; [exact Eb|]. intros i Hi; lia.
    + destruct (IH (S p) ltac:(lia) ltac:(lia)) as [(q & Hq & Hq0 & Hqn) | Hnz].
      * left. exists q. split; [lia|]. split; [exact Hq0|].
        intros i Hi. destruct (Nat.eq_dec i p) as [-> | Hne]; [rewrite Eb; intros E; injection E; lia|].
        apply Hqn. lia.
      * right. intros i Hi. destruct (Nat.eq_dec i p) as [-> | Hne]; [rewrite Eb; intros E; injection E; lia|].
        apply Hnz. lia. }
intros p Hp. exact (G _ p eq_refl Hp).
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

(* ------------------------------------------------------------------ the cut at 0x8395c *)
Definition DJ (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_join) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 26 = w64 DR_SCAN_END /\
getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\
DLC B MT MMAX RG cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

Definition dr_memchr_join_stmt : Prop :=
forall cx s1 D p W1 c1,
DBASE B MT MMAX RG cx -> DJ cx s1 D p W1 c1 ->
(forall q W2 c2, DLL B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DLR B MT MMAX RG cx s1 D p W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Lemma dj_seat : forall (W1 : world SEGS) regs1 m1 sp SA buf used x,
spZ regs1 = sp -> 2 ^ 46 <= sp -> alloc_ceiling <= sp -> sp + 352 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 20 = w64 (SA + 16) -> getr regs1 22 = w64 (SA + 24) -> getr regs1 24 = w64 x ->
val_mem SEGS (arm W1 m1) (sp + 224) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W1 m1) (sp + 232) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W1 m1) (SA + 16) 8 buf -> val_mem SEGS (arm W1 m1) (SA + 24) 8 used ->
4096 <= SA -> SA + 56 <= alloc_ceiling -> SA mod 8 = 0 ->
4096 <= buf <= 140737479966720 -> buf mod 8 = 0 -> 0 <= used <= 16384 -> 4096 <= x <= 140737479966720 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56 ->
(forall y, SA <= y < SA + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dj_extra SA buf used))) dj_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_join)) m1 (seg_rom SEGS))) /\
sh_ok SEGS dj_Bx dj_SH (Eimg (Ereg regs1 (dj_extra SA buf used))) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 sp SA buf used x Hsp Hs1 Hs0 Hs2 Hs16 R20 R22 R24 F224 F232 V16 V24 HSA1 HSA2 HSA8 Hb1 Hb8 Hu Hx RA HAPP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (dj_extra SA buf used))).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 buf) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 used) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E24 : ew E 24 = Z_to_bv 64 x) by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (U24 : bv_unsigned (ew E 24) = x) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U34 : bv_unsigned (ew E 34) = buf) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = used) by (rewrite E35; apply unsigned_lit_small; lia).
split.
- apply pa_entry_st_ok_full.
  + unfold dj_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |] |
      intros X; discriminate X |].
    * rewrite R20. rewrite (den_atom E 32 SA 16 E32) by lia. reflexivity.
    * rewrite R22. rewrite (den_atom E 32 SA 24 E32) by lia. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, dj_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS E _ sp 224 8 _ (shadow_addr (SA + 16)));
           [exact (dj_den_sh E SA 16 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia)) | | zside | exact F224].
         change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_addr, SHADOW_OFF.
         split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
         assert ((SA + 16) / 8 <= SA + 16) by (apply Z.div_le_upper_bound; lia). lia.
      -- apply (chunk_ok_val SEGS E _ sp 232 8 _ (shadow_addr (SA + 24)));
           [exact (dj_den_sh E SA 24 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia)) | | zside | exact F232].
         change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_addr, SHADOW_OFF.
         split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
         assert ((SA + 24) / 8 <= SA + 24) by (apply Z.div_le_upper_bound; lia). lia.
    * unfold region_ok, dj_ent. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 34 0) buf);
           [exact (den_atom0 E 34 buf E34 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact V16].
      -- apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 35 0) used);
           [exact (den_atom0 E 35 used E35 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact V24].
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, dj_frame, dj_ent.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
    split; [split; [right; lia | exact I] | split; exact I].
  + split; [|split; [exact I | exact I]].
    unfold dj_facts, dj_PTRF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U24, U32, U33, U34, U35.
    assert (M16 : sp mod 2 ^ 4 = 0) by (change (2 ^ 4) with 16; exact Hs16).
    assert (M8a : SA mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact HSA8).
    assert (M8b : buf mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Hb8).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
      unfold SHADOW_OFF in *; lia.
- unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 32 SA 56 SA 0 56 RA).
  + unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
  + apply (U_atom E 32 SA E32). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia.
Qed.

Theorem dr_memchr_join : dr_memchr_join_stmt.
Proof.
intros cx s1 D p W1 c1 HB HDJ Kll Klr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDJ as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hc1 & HRG & R26 & R24 & HDB & HCAP & Hbnd & HDLC & HFUT).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HDLC as HLC. unfold DLC, LCORE in HLC.
destruct HLC as (HM & HL & HSAME & HH & HRS & HBUD).
pose proof HM as (HJ & Hrom & _ & _ & _ & Hgarr & Hawr & HEOK & _ & _ & _ & _ & _ & Hperm).
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
pose proof HEOK as (Heof & Hskp & Hp1 & Hp2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & _).
destruct Hbufc as [(Hc0 & _) | (Hcpos & HBin & Hjunk & Hbgarr)]; [lia|].
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (HB16 & HB4 & HBc & HBapp & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
pose proof HL as (_ & HU & _).
cbn [dvirt drain_b_c.ds_u] in HU.
assert (HUL : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcap16 : re_cap e1 <= 16384) by (destruct Hcapr as [H|[H|H]]; lia).
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
pose proof Hbnd as (Hpl & _).
assert (Husd : 0 <= re_used e1 <= re_cap e1) by lia.
pose proof (dnk_entry_buf (arm W1 m1) (dxSA cx) e1 Hgarr Hp1 ltac:(lia)) as V16.
pose proof (dnk_entry_used (arm W1 m1) (dxSA cx) e1 Hgarr Hp1 ltac:(lia)) as V24.
pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F224 & F232 & _).
pose proof (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR GT
  HSAlo ltac:(change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia)) as RA.
assert (HAPP : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT, ATABLE in *. lia. }
destruct (dj_seat W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_used e1) (re_buf e1 + Z.of_nat p)
  Hsp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; rewrite HDF; reflexivity)
  R20 R22 R24 F224 F232 V16 V24 ltac:(lia) ltac:(unfold AENT, ATABLE in *; lia) HSA8
  ltac:(lia) Hdb3 ltac:(lia) ltac:(lia) RA HAPP) as [HS SHOK].
remember (Eimg (Ereg regs1 (dj_extra (dxSA cx) (re_buf e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (dj_extra (dxSA cx) (re_buf e1) (re_used e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
paj_run_tok RUN HS HJ SHOK dj_Bspan. { apply awr_ok_x_of0; awr_ok_tac. }
lazymatch goal with HS0 : st_ok _ _ _ (restrict _ ?x) |- _ => rename x into msC end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (KL : forall x, aview SEGS (w_H W1) (ms_mem msC) x = aview SEGS (w_H W1) m1 x).
{ intros x; apply (aview_eq_of SEGS); apply FR1; intros (r & Hin & Hr);
  cbn [ss_mem dj_ss In] in Hin; destruct Hin as [<- | [<- | []]];
  unfold dj_frame, dj_ent in Hr; cbn [YP09.r_wlo YP09.r_whi] in Hr; lia. }
assert (KP : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msC) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR1 Hp)).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (E24 : ew E 24 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (Usp0 : spZ (ms_regs msC) = dsp0 cx - DRAIN_FRAME).
{ unfold spZ at 1. rewrite Q2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]). exact Hsp. }
set (x := re_buf e1 + Z.of_nat p) in *.
set (n := re_used e1 - Z.of_nat p).
assert (Hxn : x + n = re_buf e1 + re_used e1) by (unfold x, n; lia).
assert (Hn0 : 0 <= n <= 16384) by (unfold n; lia).
(* the bytes of the line memchr reads *)
assert (BYTE : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) (ms_mem msC) (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hjl. rewrite KL. unfold bzs in Hbgarr. rewrite map_app in Hbgarr. fold (bzs (re_U e1)) in Hbgarr.
  rewrite HU in Hbgarr. exact (dj_buf_byte (w_H W1) m1 (re_buf e1) (dW s1) _ j Hbgarr Hjl). }
assert (FB : exists k, first_byte SEGS W1 (ms_mem msC) x n 0 k /\
  ((k < n /\ (Z.to_nat k + p < length (dW s1))%nat /\ nth_error (dW s1) (Z.to_nat k + p) = Some 0 /\
    (forall i, (p <= i < Z.to_nat k + p)%nat -> nth_error (dW s1) i <> Some 0)) \/
   (k = n /\ forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0))).
{ destruct (dj_scan (dW s1) p Hpl) as [(q & Hq & Hq0 & Hqn) | Hnz].
  - exists (Z.of_nat (q - p)). split.
    + split; [unfold n; lia|]. split.
      * intros i Hi. exists (nth (p + Z.to_nat i) (dW s1) 0).
        split; [unfold x; replace (re_buf e1 + Z.of_nat p + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by lia;
          apply BYTE; lia|].
        intros E0. apply (Hqn (p + Z.to_nat i)%nat ltac:(lia)).
        rewrite (nth_error_nth' (dW s1) 0) by lia. rewrite E0. reflexivity.
      * intros _. unfold x. replace (re_buf e1 + Z.of_nat p + Z.of_nat (q - p)) with (re_buf e1 + Z.of_nat q) by lia.
        rewrite BYTE by lia. f_equal. apply nth_error_nth. exact Hq0.
    + left. rewrite Nat2Z.id. split; [unfold n; lia|]. replace (q - p + p)%nat with q by lia.
      split; [lia|]. split; [exact Hq0|]. exact Hqn.
  - exists n. split.
    + split; [lia|]. split; [|intros Hc; lia].
      intros i Hi. exists (nth (p + Z.to_nat i) (dW s1) 0).
      split; [unfold x; replace (re_buf e1 + Z.of_nat p + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by lia;
        apply BYTE; unfold n in Hi; lia|].
      intros E0. apply (Hnz (p + Z.to_nat i)%nat ltac:(lia)).
      rewrite (nth_error_nth' (dW s1) 0) by (unfold n in Hi; lia). rewrite E0. reflexivity.
    + right. split; [reflexivity | exact Hnz]. }
destruct FB as (k & Hfb & Hcase).
assert (Hkn : 0 <= k <= n) by exact (proj1 Hfb).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
assert (Hromc : rom_view SEGS W1 (ms_mem msC)) by (intros y Hy; rewrite KL; exact (Hrom y Hy)).
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 [] (2 * ESTACK) (SIGMA WS_memchr) (fun _ => False)
    (fun regs' (_ : word -> option byte) => getr regs' 10 = if k <? n then w64 (x + k) else w64 0)
    W1 (ms_regs msC) (ms_mem msC) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) []
    ly1 S1 _ k1 (-352) (Z_to_bv 64 (BASE + 5712))).
  - exact HG.
  - reflexivity.
  - exact HJ.
  - rewrite Usp0, HDF. lia.
  - reflexivity.
  - lia.
  - unfold ESTACK; lia.
  - rewrite HDS. unfold ESTACK; lia.
  - rewrite Q3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]). rewrite R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]). rewrite R4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros y. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE2 _.
    apply (W_next_line.aentry_of_memchrM B 0x10350 0x10370 _ (2 * ESTACK) ly1 S1 W1 (ms_regs msC) (ms_mem msC) _
      x 0 n k AMEMCHR ltac:(unfold ESTACK; lia) HPRE2).
    + rewrite Q10, E24. reflexivity.
    + rewrite Q11. reflexivity.
    + rewrite Q12, E24, E34, E35, dj_negmul. unfold n, x, w64. f_equal. lia.
    + lia.
    + lia.
    + unfold x; lia.
    + lia.
    + intros y Hy. split.
      * replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
        rewrite BYTE by (unfold x, n in Hy; lia). discriminate.
      * rewrite Usp0. unfold x, n, ESTACK in *. lia.
    + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, x, n in *.
      lia.
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) x n HARC HBin);
        [unfold x; lia | unfold x, n in *; lia].
    + intros Hpos.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) x n HARC HBin);
        [unfold x; lia | unfold x, n in *; lia | exact Hpos].
    + exact (consts_view_of_rom_view SEGS 0x10350 0x10370 W1 (ms_mem msC) HCROM Hromc).
    + exact Hfb. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR10 & Hfr2 & Hpres2).
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (B32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (FR2 : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx + -352 - 2 * ESTACK <= y < dsp0 cx + -352) ->
  aview SEGS (w_H W1) mem2 y = aview SEGS (w_H W1) (ms_mem msC) y)
  by (intros y Hy Hno; exact (Hfr2 y Hy (fun F => F) Hno)).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 2%nat (dsp0 cx - DRAIN_FRAME));
      [exact B2 | intros y Hy; apply FR2; [lia | unfold ESTACK; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 32%nat (dxSA cx));
      [exact B32 | intros y Hy; apply FR2; [lia | unfold ESTACK, AENT, ATABLE in *; lia] | exact Hpres2]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (E32a : ew Ea 32 = Z_to_bv 64 (dxSA cx)) by (rewrite OLDa by lia; exact E32).
assert (E33a : ew Ea 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E33).
prreg HS (10%bv : bv 5) R10a.
assert (F40 : ew Ea 40 = if k <? n then w64 (x + k) else w64 0) by (rewrite <- R10a; exact HR10).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (SHOK2 : sh_ok SEGS dj_Bx dj_SH Ea (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dj_Bx 32 (dxSA cx) 56 (dxSA cx) 0 56
    (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem2 md2 (dxG cx) ATABLE (dxSA cx) 56 HAR2 GT
      HSAlo ltac:(change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia))).
  + unfold dj_Bx. apply (U_atom Ea 33 SHADOW_OFF E33a). unfold SHADOW_OFF; lia.
  + apply (U_atom Ea 32 (dxSA cx) E32a). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia. }
assert (KM : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) mem2 y = aview SEGS (w_H W1) m1 y)
  by (intros y Hy Hno; rewrite FR2 by (unfold ESTACK in *; lia); apply KL).
assert (KPM : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) mem2 y) by (intros y Hy; apply Hpres2, KP, Hy).
assert (Hlo : alloc_ceiling <= dsp0 cx - DRAIN_FRAME - 2 * ESTACK) by (unfold ESTACK; lia).
(* 0x83994 beqz a0: memchr's result *)
psrr_branch_tok RUN BR HS SHOK2 dj_Bspan.
- (* a0 = 0: no NUL from p on; 0x83e34 is DLR *)
  assert (Hk : k = n).
  { destruct Hcase as [(Hlt & _) | (Heq & _)]; [exfalso | exact Heq].
    rewrite branch_eq_U in Hc. rewrite (U_lit Ea 0) in Hc by lia.
    rewrite (proj2 (Z.ltb_lt k n) Hlt) in F40.
    rewrite (U_atom Ea 40 (x + k) F40) in Hc by (unfold x, n in *; lia).
    apply Z.eqb_eq in Hc. unfold x in Hc. lia. }
  destruct Hcase as [(Hlt & _) | (_ & Hnz)]; [lia|]. clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dj_Bspan A_dr_rest; [apply awr_ok_x_of0; awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  assert (KL3 : forall y, aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) mem2 y).
  { intros y; apply (aview_eq_of SEGS); apply FR3; intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 (KPM y Hy))).
  assert (KF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy Hno; rewrite KL3; exact (KM y Hy Hno)).
  pose proof (dnk_DMEM_call B MT MMAX RG LAWS HG HRGD HGSB HMMAX HV9 HSD HSM cx ly1 S1 W1 m1 (ms_mem msF) md1 _ k1 _
    e1 h1 _ out1 ev1 _ LB1 _ HB HM HJ2 Hlo KF KPF) as HMF.
  pose proof HMF as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ea nn = getr regs1 r)
    by (intros nn r Hn Hr; rewrite OLDa by lia; exact (EREG nn r Hn Hr)).
  assert (HRL : dregs_line RG cx (ms_regs msF) W1 (ms_mem msF)).
  { unfold dregs_line.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X20, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    exact HFRF. }
  assert (H25 : getr (ms_regs msF) 25 = w64 (Z.of_nat (length (dW s1) - p))).
  { rewrite X25, !OLDa by lia. rewrite E24, E34, E35, dj_negmul. unfold w64. f_equal.
    rewrite Nat2Z.inj_sub by lia. lia. }
  assert (H19 : getr (ms_regs msF) 19 = w64 (re_buf e1)) by (rewrite X19, OLDa by lia; exact E34).
  assert (H24 : getr (ms_regs msF) 24 = w64 (re_buf e1 + Z.of_nat p))
    by (rewrite X24, (KEPT 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
  assert (H26 : getr (ms_regs msF) 26 = w64 DR_SCAN_END)
    by (rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26).
  assert (HLC : DLC B MT MMAX RG cx s1 D p ly1 S1 W1 (ms_mem msF) _ _ e1 h1 out1 ev1 LB1 spent tl)
    by (unfold DLC, LCORE; exact (conj HMF (conj HL (conj HSAME (conj HH (conj HRS HBUD)))))).
  apply Klr.
  exists (ms_regs msF), ly1, S1, (ms_mem msF). eexists. eexists.
  exists e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [reflexivity|]. split; [exact HRL|]. split; [exact H26|]. split; [exact H24|]. split; [exact H25|].
  split; [exact H19|]. split; [exact HDB|]. split; [exact HCAP|]. split; [exact Hbnd|].
  split; [exact Hnz|]. split; [exact HLC | exact HFUT].
- (* a0 <> 0: the NUL at q = p + k; 0x8399c is DLL *)
  assert (Hk : k < n).
  { destruct Hcase as [(Hlt & _) | (Heq & _)]; [exact Hlt | exfalso].
    rewrite branch_eq_U in Hc. rewrite (U_lit Ea 0) in Hc by lia.
    rewrite Heq, Z.ltb_irrefl in F40. unfold w64 in F40.
    rewrite (U_atom Ea 40 0 F40) in Hc by lia. cbn in Hc. discriminate Hc. }
  destruct Hcase as [(_ & Hq1 & Hq0 & Hqn) | (Heq & _)]; [|lia]. clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dj_Bspan A_dr_line; [apply awr_ok_x_of0; awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  assert (KL3 : forall y, aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) mem2 y).
  { intros y; apply (aview_eq_of SEGS); apply FR3; intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 (KPM y Hy))).
  assert (KF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy Hno; rewrite KL3; exact (KM y Hy Hno)).
  pose proof (dnk_DMEM_call B MT MMAX RG LAWS HG HRGD HGSB HMMAX HV9 HSD HSM cx ly1 S1 W1 m1 (ms_mem msF) md1 _ k1 _
    e1 h1 _ out1 ev1 _ LB1 _ HB HM HJ2 Hlo KF KPF) as HMF.
  pose proof HMF as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ea nn = getr regs1 r)
    by (intros nn r Hn Hr; rewrite OLDa by lia; exact (EREG nn r Hn Hr)).
  assert (HRL : dregs_line RG cx (ms_regs msF) W1 (ms_mem msF)).
  { unfold dregs_line.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X20, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    exact HFRF. }
  assert (H25 : getr (ms_regs msF) 25 = w64 (Z.of_nat (length (dW s1) - p))).
  { rewrite X25, !OLDa by lia. rewrite E24, E34, E35, dj_negmul. unfold w64. f_equal.
    rewrite Nat2Z.inj_sub by lia. lia. }
  assert (H19 : getr (ms_regs msF) 19 = w64 (re_buf e1)) by (rewrite X19, OLDa by lia; exact E34).
  assert (H24 : getr (ms_regs msF) 24 = w64 (re_buf e1 + Z.of_nat p))
    by (rewrite X24, (KEPT 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
  assert (H26 : getr (ms_regs msF) 26 = w64 DR_SCAN_END)
    by (rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26).
  assert (HLC : DLC B MT MMAX RG cx s1 D p ly1 S1 W1 (ms_mem msF) _ _ e1 h1 out1 ev1 LB1 spent tl)
    by (unfold DLC, LCORE; exact (conj HMF (conj HL (conj HSAME (conj HH (conj HRS HBUD)))))).
  prreg HS (23%bv : bv 5) X23.
  apply (Kll (Z.to_nat k + p)%nat).
  exists (ms_regs msF), ly1, S1, (ms_mem msF). eexists. eexists.
  exists e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [reflexivity|]. split; [exact HRL|]. split; [exact H26|].
  split; [rewrite X23, F40, (proj2 (Z.ltb_lt k n) Hk); unfold w64, x; f_equal; lia|].
  split; [exact H24|]. split; [exact H19|]. split; [exact H25|].
  split; [exact HDB|]. split; [exact HCAP|]. split; [exact Hbnd|].
  split; [lia|]. split; [exact Hq0|]. split; [exact Hqn|]. split; [exact HLC | exact HFUT].
Qed.

End c.

(* ---- THE GENERIC JOIN (an internal work row): the cut at 0x8395c and the memchr join over any allocator relation ARx with its
   laws, at the room texts.  The Section is W_drain_cx_x.v's Section c - its variables B PST ARx MT RP MMAX RG in that
   order, each hypothesis that file's text - with the allocator rules in their caller-context forms (this segment
   calls no allocator, so no call-site fact HCTX_* is stated), and after LAWS the generic-relation fact HP0 (no hidden
   head in any ARx state, a Theorem Labs lane's ruling: the table's and the buffer's shadow facts are W_journal_x.v's
   range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x).  DJ_x is DJ's text with DLC -> DLC_x and the
   cut's ghost list Hp1 an existential after S1; dr_memchr_join_stmt_x is dr_memchr_join_stmt's with the cut
   predicates, DBASE and dPOST at the entry's Hp and kr. ---- *)
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
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
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

(* The carriers of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, and every carrier or spec it names -> its R twin;
   every other token is the strict text's. The strict <name> is <name>R at R := wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

Definition DJ_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_join) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 26 = w64 DR_SCAN_END /\
getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\
DLC_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

Definition dr_memchr_join_stmt_xR : Prop :=
forall cx Hp kr s1 D p W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DJ_xR cx Hp kr s1 D p W1 c1 ->
(forall q W2 c2, DLL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, DLR_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.

(* ------------------------------------------------------------------ the cut at 0x8395c, over ARx *)
Definition DJ_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS)
(c1 : config) : Prop :=
DJ_xR (@wle SEGS) cx Hp kr s1 D p W1 c1.

Definition dr_memchr_join_stmt_x : Prop :=
dr_memchr_join_stmt_xR (@wle SEGS).

(* Section c's dj_seat (AR-free), restated so that no Section generalization is relied on *)
Lemma dj_seat_x : forall (W1 : world SEGS) regs1 m1 sp SA buf used x,
spZ regs1 = sp -> 2 ^ 46 <= sp -> alloc_ceiling <= sp -> sp + 352 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 20 = w64 (SA + 16) -> getr regs1 22 = w64 (SA + 24) -> getr regs1 24 = w64 x ->
val_mem SEGS (arm W1 m1) (sp + 224) 8 (shadow_addr (SA + 16)) ->
val_mem SEGS (arm W1 m1) (sp + 232) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W1 m1) (SA + 16) 8 buf -> val_mem SEGS (arm W1 m1) (SA + 24) 8 used ->
4096 <= SA -> SA + 56 <= alloc_ceiling -> SA mod 8 = 0 ->
4096 <= buf <= 140737479966720 -> buf mod 8 = 0 -> 0 <= used <= 16384 -> 4096 <= x <= 140737479966720 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56 ->
(forall y, SA <= y < SA + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dj_extra SA buf used))) dj_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_join)) m1 (seg_rom SEGS))) /\
sh_ok SEGS dj_Bx dj_SH (Eimg (Ereg regs1 (dj_extra SA buf used))) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 sp SA buf used x Hsp Hs1 Hs0 Hs2 Hs16 R20 R22 R24 F224 F232 V16 V24 HSA1 HSA2 HSA8 Hb1 Hb8 Hu Hx RA HAPP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (dj_extra SA buf used))).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 buf) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 used) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E24 : ew E 24 = Z_to_bv 64 x) by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (U24 : bv_unsigned (ew E 24) = x) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U34 : bv_unsigned (ew E 34) = buf) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = used) by (rewrite E35; apply unsigned_lit_small; lia).
split.
- apply pa_entry_st_ok_full.
  + unfold dj_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |] |
      intros X; discriminate X |].
    * rewrite R20. rewrite (den_atom E 32 SA 16 E32) by lia. reflexivity.
    * rewrite R22. rewrite (den_atom E 32 SA 24 E32) by lia. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, dj_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS E _ sp 224 8 _ (shadow_addr (SA + 16)));
           [exact (dj_den_sh E SA 16 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia)) | | zside | exact F224].
         change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_addr, SHADOW_OFF.
         split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
         assert ((SA + 16) / 8 <= SA + 16) by (apply Z.div_le_upper_bound; lia). lia.
      -- apply (chunk_ok_val SEGS E _ sp 232 8 _ (shadow_addr (SA + 24)));
           [exact (dj_den_sh E SA 24 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia)) | | zside | exact F232].
         change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_addr, SHADOW_OFF.
         split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
         assert ((SA + 24) / 8 <= SA + 24) by (apply Z.div_le_upper_bound; lia). lia.
    * unfold region_ok, dj_ent. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS E _ SA 16 8 (SOff 34 0) buf);
           [exact (den_atom0 E 34 buf E34 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact V16].
      -- apply (chunk_ok_val SEGS E _ SA 24 8 (SOff 35 0) used);
           [exact (den_atom0 E 35 used E35 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact V24].
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, dj_frame, dj_ent.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
    split; [split; [right; lia | exact I] | split; exact I].
  + split; [|split; [exact I | exact I]].
    unfold dj_facts, dj_PTRF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U24, U32, U33, U34, U35.
    assert (M16 : sp mod 2 ^ 4 = 0) by (change (2 ^ 4) with 16; exact Hs16).
    assert (M8a : SA mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact HSA8).
    assert (M8b : buf mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Hb8).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
      unfold SHADOW_OFF in *; lia.
- unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 32 SA 56 SA 0 56 RA).
  + unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
  + apply (U_atom E 32 SA E32). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia.
Qed.
(* W_next_line.v's first_byte_unique and aentry_of_memchrM, over ARx (W_sites_x.v amemchr_realizesM_x / aentry_post_x) *)
Lemma dj_first_byte_unique_x : forall (W : world SEGS) mem x n c k k',
first_byte SEGS W mem x n c k -> first_byte SEGS W mem x n c k' -> k = k'.
Proof.
intros W mem x n c k k' (Hk & Hb & Hf) (Hk' & Hb' & Hf').
destruct (Z.lt_trichotomy k k') as [Hlt | [Heq | Hgt]]; [exfalso | exact Heq | exfalso].
- destruct (Hb' k ltac:(lia)) as (b & Eb & Hne). rewrite (Hf ltac:(lia)) in Eb. injection Eb as <-. exact (Hne eq_refl).
- destruct (Hb k' ltac:(lia)) as (b & Eb & Hne). rewrite (Hf' ltac:(lia)) in Eb. injection Eb as <-. exact (Hne eq_refl).
Qed.
Lemma dj_aentry_of_memchrM_x : forall lo hi pc stk ly S Hq W regs mem md x c n k,
amemchr_realizesM_x SEGS B ARx lo hi pc -> ESTACK <= stk ->
ecall_pre_x SEGS B ARx ly S Hq W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok SEGS W regs mem x n -> amem_range x n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n) ->
consts_view SEGS lo hi W mem -> first_byte SEGS W mem x n c k ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post_x ARx stk ly S Hq W regs mem md (fun _ => False)
 (fun regs' _ => getr regs' 10 = if k <? n then w64 (x + k) else w64 0)).
Proof.
intros lo hi pc stk ly S Hq W regs mem md x c n k HM Hstk HPRE H10 H11 H12 Hc Hn Hx Hxn Hsrc Hmr Hra Hhv Hcv Hfb.
eapply SRr_mono; [exact (HM ly S Hq W regs mem md x c n HPRE H10 H11 H12 Hc Hn Hx Hxn Hsrc Hmr Hra Hhv Hcv)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hcfg & HAR' & HP' & Hsm & (k' & Hfb' & H10') & Hfr & Hpr).
split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hcfg|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsm|].
split; [rewrite (dj_first_byte_unique_x W mem x n c k k' Hfb Hfb'); exact H10'|].
split; [intros a Ha _ Hs; apply Hfr; [exact Ha | intros Hc'; apply Hs; lia]|].
exact Hpr.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the memchr join at a world relation R.  DJ_x / DLL_x / DLR_x / DLC_x /
   LCORE_x / DMEM_x / dPOST_x -> their R twins (W_drain_cx_x.v and the Section wR above), ajournal_gx_x ->
   ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the runs and the branch -> their SRrG forms (W_journal_x.v
   paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR), the memchr entry -> W_sites_x.v aj_gx_entry_at_xR (the
   memchr contract stays strict), dnk_DMEM_call_x -> dnk_DMEM_call_xR.  dr_memchr_join_x below is it at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PI).

(* R twin of dr_memchr_join_x *)
Theorem dr_memchr_join_xR : dr_memchr_join_stmt_xR R.
Proof.
intros cx Hpe kr s1 D p W1 c1 HB HDJ Kll Klr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDJ as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hc1 & HRG & R26 & R24 & HDB & HCAP & Hbnd & HDLC & HFUT).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HDLC as HLC. unfold DLC_xR, LCORE_xR in HLC.
destruct HLC as (HM & HL & HSAME & HH & HRS & HBUD).
pose proof HM as (HJ & Hrom & _ & _ & _ & Hgarr & Hawr & HEOK & _ & _ & _ & _ & _ & Hperm).
pose proof HJ as HAR. eapply ajournal_gx_AR_xR in HAR.
pose proof HB as (Hafn & _ & HGB & HSAlo & HSAhi & HSA8 & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (HG16 & HG4 & HGc & HGapp & _).
change (req_size ATABLE) with 896 in HGc, HGapp.
pose proof HEOK as (Heof & Hskp & Hp1' & Hp2' & Hfd & Hcapr & HUlen & Husedr & Hbufc & _).
destruct Hbufc as [(Hc0 & _) | (Hcpos & HBin & Hjunk & Hbgarr)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (HB16 & HB4 & HBc & HBapp & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
pose proof HL as (_ & HU & _).
cbn [dvirt drain_b_c.ds_u] in HU.
assert (HUL : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcap16 : re_cap e1 <= 16384) by (destruct Hcapr as [H|[H|H]]; lia).
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
pose proof Hbnd as (Hpl & _).
assert (Husd : 0 <= re_used e1 <= re_cap e1) by lia.
pose proof (dnk_entry_buf (arm W1 m1) (dxSA cx) e1 Hgarr Hp1' ltac:(lia)) as V16.
pose proof (dnk_entry_used (arm W1 m1) (dxSA cx) e1 Hgarr Hp1' ltac:(lia)) as V24.
pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F224 & F232 & _).
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR GT
  HSAlo ltac:(change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia)) as RA.
assert (HAPP : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT, ATABLE in *. lia. }
destruct (dj_seat_x W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_used e1) (re_buf e1 + Z.of_nat p)
  Hsp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; rewrite HDF; reflexivity)
  R20 R22 R24 F224 F232 V16 V24 ltac:(lia) ltac:(unfold AENT, ATABLE in *; lia) HSA8
  ltac:(lia) Hdb3 ltac:(lia) ltac:(lia) RA HAPP) as [HS SHOK].
remember (Eimg (Ereg regs1 (dj_extra (dxSA cx) (re_buf e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (dj_extra (dxSA cx) (re_buf e1) (re_used e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
paj_run_tok_xR RUNR HS HJ SHOK dj_Bspan. { apply awr_ok_x_of0; awr_ok_tac. }
lazymatch goal with HS0 : st_ok _ _ _ (restrict _ ?x) |- _ => rename x into msC end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (KL : forall x, aview SEGS (w_H W1) (ms_mem msC) x = aview SEGS (w_H W1) m1 x).
{ intros x; apply (aview_eq_of SEGS); apply FR1; intros (r & Hin & Hr);
  cbn [ss_mem dj_ss In] in Hin; destruct Hin as [<- | [<- | []]];
  unfold dj_frame, dj_ent in Hr; cbn [YP09.r_wlo YP09.r_whi] in Hr; lia. }
assert (KP : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msC) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR1 Hp)).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (E24 : ew E 24 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
assert (Usp0 : spZ (ms_regs msC) = dsp0 cx - DRAIN_FRAME).
{ unfold spZ at 1. rewrite Q2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]). exact Hsp. }
set (x := re_buf e1 + Z.of_nat p) in *.
set (n := re_used e1 - Z.of_nat p).
assert (Hxn : x + n = re_buf e1 + re_used e1) by (unfold x, n; lia).
assert (Hn0 : 0 <= n <= 16384) by (unfold n; lia).
(* the bytes of the line memchr reads *)
assert (BYTE : forall j, (j < length (dW s1))%nat ->
  aview SEGS (w_H W1) (ms_mem msC) (re_buf e1 + Z.of_nat j) = Some (nth j (dW s1) 0)).
{ intros j Hjl. rewrite KL. unfold bzs in Hbgarr. rewrite map_app in Hbgarr. fold (bzs (re_U e1)) in Hbgarr.
  rewrite HU in Hbgarr. exact (dj_buf_byte (w_H W1) m1 (re_buf e1) (dW s1) _ j Hbgarr Hjl). }
assert (FB : exists k, first_byte SEGS W1 (ms_mem msC) x n 0 k /\
  ((k < n /\ (Z.to_nat k + p < length (dW s1))%nat /\ nth_error (dW s1) (Z.to_nat k + p) = Some 0 /\
    (forall i, (p <= i < Z.to_nat k + p)%nat -> nth_error (dW s1) i <> Some 0)) \/
   (k = n /\ forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0))).
{ destruct (dj_scan (dW s1) p Hpl) as [(q & Hq & Hq0 & Hqn) | Hnz].
  - exists (Z.of_nat (q - p)). split.
    + split; [unfold n; lia|]. split.
      * intros i Hi. exists (nth (p + Z.to_nat i) (dW s1) 0).
        split; [unfold x; replace (re_buf e1 + Z.of_nat p + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by lia;
          apply BYTE; lia|].
        intros E0. apply (Hqn (p + Z.to_nat i)%nat ltac:(lia)).
        rewrite (nth_error_nth' (dW s1) 0) by lia. rewrite E0. reflexivity.
      * intros _. unfold x. replace (re_buf e1 + Z.of_nat p + Z.of_nat (q - p)) with (re_buf e1 + Z.of_nat q) by lia.
        rewrite BYTE by lia. f_equal. apply nth_error_nth. exact Hq0.
    + left. rewrite Nat2Z.id. split; [unfold n; lia|]. replace (q - p + p)%nat with q by lia.
      split; [lia|]. split; [exact Hq0|]. exact Hqn.
  - exists n. split.
    + split; [lia|]. split; [|intros Hc; lia].
      intros i Hi. exists (nth (p + Z.to_nat i) (dW s1) 0).
      split; [unfold x; replace (re_buf e1 + Z.of_nat p + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by lia;
        apply BYTE; unfold n in Hi; lia|].
      intros E0. apply (Hnz (p + Z.to_nat i)%nat ltac:(lia)).
      rewrite (nth_error_nth' (dW s1) 0) by (unfold n in Hi; lia). rewrite E0. reflexivity.
    + right. split; [reflexivity | exact Hnz]. }
destruct FB as (k & Hfb & Hcase).
assert (Hkn : 0 <= k <= n) by exact (proj1 Hfb).
pose proof HJ as HARC. eapply ajournal_gx_AR_xR in HARC.
assert (Hromc : rom_view SEGS W1 (ms_mem msC)) by (intros y Hy; rewrite KL; exact (Hrom y Hy)).
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 [] (2 * ESTACK) (SIGMA WS_memchr) (fun _ => False)
    (fun regs' (_ : word -> option byte) => getr regs' 10 = if k <? n then w64 (x + k) else w64 0)
    W1 (ms_regs msC) (ms_mem msC) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) []
    ly1 S1 Hp1 _ k1 (-352) (Z_to_bv 64 (BASE + 5712))).
  - exact HG.
  - reflexivity.
  - exact HJ.
  - rewrite Usp0, HDF. lia.
  - reflexivity.
  - lia.
  - unfold ESTACK; lia.
  - rewrite HDS. unfold ESTACK; lia.
  - rewrite Q3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]). rewrite R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]). rewrite R4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros y. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE2 _.
    apply (dj_aentry_of_memchrM_x 0x10350 0x10370 _ (2 * ESTACK) ly1 S1 Hp1 W1 (ms_regs msC) (ms_mem msC) _
      x 0 n k AMEMCHR ltac:(unfold ESTACK; lia) HPRE2).
    + rewrite Q10, E24. reflexivity.
    + rewrite Q11. reflexivity.
    + rewrite Q12, E24, E34, E35, dj_negmul. unfold n, x, w64. f_equal. lia.
    + lia.
    + lia.
    + unfold x; lia.
    + lia.
    + intros y Hy. split.
      * replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
        rewrite BYTE by (unfold x, n in Hy; lia). discriminate.
      * rewrite Usp0. unfold x, n, ESTACK in *. lia.
    + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, x, n in *.
      lia.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1)
        x n HARC HBin); [unfold x; lia | unfold x, n in *; lia].
    + intros Hpos.
      apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1)
        x n HARC HBin); [unfold x; lia | unfold x, n in *; lia | exact Hpos].
    + exact (consts_view_of_rom_view SEGS 0x10350 0x10370 W1 (ms_mem msC) HCROM Hromc).
    + exact Hfb. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR10 & Hfr2 & Hpres2).
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (B32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (FR2 : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx + -352 - 2 * ESTACK <= y < dsp0 cx + -352) ->
  aview SEGS (w_H W1) mem2 y = aview SEGS (w_H W1) (ms_mem msC) y)
  by (intros y Hy Hno; exact (Hfr2 y Hy (fun F => F) Hno)).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 2%nat (dsp0 cx - DRAIN_FRAME));
      [exact B2 | intros y Hy; apply FR2; [lia | unfold ESTACK; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 32%nat (dxSA cx));
      [exact B32 | intros y Hy; apply FR2; [lia | unfold ESTACK, AENT, ATABLE in *; lia] | exact Hpres2]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (E32a : ew Ea 32 = Z_to_bv 64 (dxSA cx)) by (rewrite OLDa by lia; exact E32).
assert (E33a : ew Ea 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E33).
prreg HS (10%bv : bv 5) R10a.
assert (F40 : ew Ea 40 = if k <? n then w64 (x + k) else w64 0) by (rewrite <- R10a; exact HR10).
pose proof HJ2 as HAR2. eapply ajournal_gx_AR_xR in HAR2.
assert (SHOK2 : sh_ok SEGS dj_Bx dj_SH Ea (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dj_Bx 32 (dxSA cx) 56 (dxSA cx) 0 56
    (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mem2 md2 (dxG cx) ATABLE (dxSA cx) 56 HAR2 GT
      HSAlo ltac:(change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia))).
  + unfold dj_Bx. apply (U_atom Ea 33 SHADOW_OFF E33a). unfold SHADOW_OFF; lia.
  + apply (U_atom Ea 32 (dxSA cx) E32a). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia. }
assert (KM : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) mem2 y = aview SEGS (w_H W1) m1 y)
  by (intros y Hy Hno; rewrite FR2 by (unfold ESTACK in *; lia); apply KL).
assert (KPM : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) mem2 y) by (intros y Hy; apply Hpres2, KP, Hy).
assert (Hlo : alloc_ceiling <= dsp0 cx - DRAIN_FRAME - 2 * ESTACK) by (unfold ESTACK; lia).
(* 0x83994 beqz a0: memchr's result *)
psrr_branch_tok RUNR BRR HS SHOK2 dj_Bspan.
- (* a0 = 0: no NUL from p on; 0x83e34 is DLR *)
  assert (Hk : k = n).
  { destruct Hcase as [(Hlt & _) | (Heq & _)]; [exfalso | exact Heq].
    rewrite branch_eq_U in Hc. rewrite (U_lit Ea 0) in Hc by lia.
    rewrite (proj2 (Z.ltb_lt k n) Hlt) in F40.
    rewrite (U_atom Ea 40 (x + k) F40) in Hc by (unfold x, n in *; lia).
    apply Z.eqb_eq in Hc. unfold x in Hc. lia. }
  destruct Hcase as [(Hlt & _) | (_ & Hnz)]; [lia|]. clear Hc.
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 dj_Bspan A_dr_rest; [apply awr_ok_x_of0; awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  assert (KL3 : forall y, aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) mem2 y).
  { intros y; apply (aview_eq_of SEGS); apply FR3; intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 (KPM y Hy))).
  assert (KF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy Hno; rewrite KL3; exact (KM y Hy Hno)).
  pose proof (dnk_DMEM_call_xR B PST ARx MT RP MMAX RG LAWS HG HGO HRGD HGSB HMMAX HSD HSM R cx Hpe kr ly1 S1 Hp1 W1 m1
    (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1 _ HB HM HJ2 Hlo KF KPF) as HMF.
  pose proof HMF as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ea nn = getr regs1 r)
    by (intros nn r Hn Hr; rewrite OLDa by lia; exact (EREG nn r Hn Hr)).
  assert (HRL : dregs_line RG cx (ms_regs msF) W1 (ms_mem msF)).
  { unfold dregs_line.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X20, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    exact HFRF. }
  assert (H25 : getr (ms_regs msF) 25 = w64 (Z.of_nat (length (dW s1) - p))).
  { rewrite X25, !OLDa by lia. rewrite E24, E34, E35, dj_negmul. unfold w64. f_equal.
    rewrite Nat2Z.inj_sub by lia. lia. }
  assert (H19 : getr (ms_regs msF) 19 = w64 (re_buf e1)) by (rewrite X19, OLDa by lia; exact E34).
  assert (H24 : getr (ms_regs msF) 24 = w64 (re_buf e1 + Z.of_nat p))
    by (rewrite X24, (KEPT 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
  assert (H26 : getr (ms_regs msF) 26 = w64 DR_SCAN_END)
    by (rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26).
  assert (HLC : DLC_xR B PST ARx MT RP MMAX RG R cx Hpe kr s1 D p ly1 S1 Hp1 W1 (ms_mem msF) _ _ e1 h1 out1 ev1 LB1 spent tl)
    by (unfold DLC_xR, LCORE_xR; exact (conj HMF (conj HL (conj HSAME (conj HH (conj HRS HBUD)))))).
  apply Klr.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF). eexists. eexists.
  exists e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [reflexivity|]. split; [exact HRL|]. split; [exact H26|]. split; [exact H24|]. split; [exact H25|].
  split; [exact H19|]. split; [exact HDB|]. split; [exact HCAP|]. split; [exact Hbnd|].
  split; [exact Hnz|]. split; [exact HLC | exact HFUT].
- (* a0 <> 0: the NUL at q = p + k; 0x8399c is DLL *)
  assert (Hk : k < n).
  { destruct Hcase as [(Hlt & _) | (Heq & _)]; [exact Hlt | exfalso].
    rewrite branch_eq_U in Hc. rewrite (U_lit Ea 0) in Hc by lia.
    rewrite Heq, Z.ltb_irrefl in F40. unfold w64 in F40.
    rewrite (U_atom Ea 40 0 F40) in Hc by lia. cbn in Hc. discriminate Hc. }
  destruct Hcase as [(_ & Hq1 & Hq0 & Hqn) | (Heq & _)]; [|lia]. clear Hc.
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 dj_Bspan A_dr_line; [apply awr_ok_x_of0; awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR3; rename HG0 into GR3; clear HF.
  assert (KL3 : forall y, aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) mem2 y).
  { intros y; apply (aview_eq_of SEGS); apply FR3; intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 (KPM y Hy))).
  assert (KF : forall y, 0 <= y < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy Hno; rewrite KL3; exact (KM y Hy Hno)).
  pose proof (dnk_DMEM_call_xR B PST ARx MT RP MMAX RG LAWS HG HGO HRGD HGSB HMMAX HSD HSM R cx Hpe kr ly1 S1 Hp1 W1 m1
    (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1 _ HB HM HJ2 Hlo KF KPF) as HMF.
  pose proof HMF as (_ & _ & _ & _ & HFRF & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ea nn = getr regs1 r)
    by (intros nn r Hn Hr; rewrite OLDa by lia; exact (EREG nn r Hn Hr)).
  assert (HRL : dregs_line RG cx (ms_regs msF) W1 (ms_mem msF)).
  { unfold dregs_line.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X20, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    exact HFRF. }
  assert (H25 : getr (ms_regs msF) 25 = w64 (Z.of_nat (length (dW s1) - p))).
  { rewrite X25, !OLDa by lia. rewrite E24, E34, E35, dj_negmul. unfold w64. f_equal.
    rewrite Nat2Z.inj_sub by lia. lia. }
  assert (H19 : getr (ms_regs msF) 19 = w64 (re_buf e1)) by (rewrite X19, OLDa by lia; exact E34).
  assert (H24 : getr (ms_regs msF) 24 = w64 (re_buf e1 + Z.of_nat p))
    by (rewrite X24, (KEPT 24%nat 24%bv) by (first [lia | reflexivity]); exact R24).
  assert (H26 : getr (ms_regs msF) 26 = w64 DR_SCAN_END)
    by (rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26).
  assert (HLC : DLC_xR B PST ARx MT RP MMAX RG R cx Hpe kr s1 D p ly1 S1 Hp1 W1 (ms_mem msF) _ _ e1 h1 out1 ev1 LB1 spent tl)
    by (unfold DLC_xR, LCORE_xR; exact (conj HMF (conj HL (conj HSAME (conj HH (conj HRS HBUD)))))).
  prreg HS (23%bv : bv 5) X23.
  apply (Kll (Z.to_nat k + p)%nat).
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF). eexists. eexists.
  exists e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
  split; [reflexivity|]. split; [exact HRL|]. split; [exact H26|].
  split; [rewrite X23, F40, (proj2 (Z.ltb_lt k n) Hk); unfold w64, x; f_equal; lia|].
  split; [exact H24|]. split; [exact H19|]. split; [exact H25|].
  split; [exact HDB|]. split; [exact HCAP|]. split; [exact Hbnd|].
  split; [lia|]. split; [exact Hq0|]. split; [exact Hqn|]. split; [exact HLC | exact HFUT].
Qed.
End wR.
(* the strict texts are the R twins above at R := wle: each R premise at wle is the strict hypothesis of the same
   name, and the three laws hold for wle *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

Theorem dr_memchr_join_x : dr_memchr_join_stmt_x.
Proof.
eapply (dr_memchr_join_xR (@wle SEGS)); wle_inst.
Qed.

End cx.
End b.
End a.
